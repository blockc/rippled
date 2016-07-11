//------------------------------------------------------------------------------
/*
    This file is part of rippled: https://github.com/ripple/rippled
    Copyright (c) 2012, 2013 Ripple Labs Inc.

    Permission to use, copy, modify, and/or distribute this software for any
    purpose  with  or without fee is hereby granted, provided that the above
    copyright notice and this permission notice appear in all copies.

    THE  SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
    WITH  REGARD  TO  THIS  SOFTWARE  INCLUDING  ALL  IMPLIED  WARRANTIES  OF
    MERCHANTABILITY  AND  FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR
    ANY  SPECIAL ,  DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
    WHATSOEVER  RESULTING  FROM  LOSS  OF USE, DATA OR PROFITS, WHETHER IN AN
    ACTION  OF  CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF
    OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
*/
//==============================================================================

#include <BeastConfig.h>
#include <ripple/app/ledger/InboundLedgers.h>
#include <ripple/app/ledger/LedgerMaster.h>
#include <ripple/app/ledger/LedgerTiming.h>
#include <ripple/app/ledger/LedgerToJson.h>
#include <ripple/app/ledger/LocalTxs.h>
#include <ripple/app/ledger/OpenLedger.h>
#include <ripple/app/ledger/impl/DisputedTx.h>
#include <ripple/app/ledger/impl/LedgerConsensusImp.h>
#include <ripple/app/ledger/impl/TransactionAcquire.h>
#include <ripple/app/main/Application.h>
#include <ripple/app/misc/AmendmentTable.h>
#include <ripple/app/misc/CanonicalTXSet.h>
#include <ripple/app/misc/HashRouter.h>
#include <ripple/app/misc/NetworkOPs.h>
#include <ripple/app/misc/TxQ.h>
#include <ripple/app/misc/Validations.h>
#include <ripple/app/tx/apply.h>
#include <ripple/basics/contract.h>
#include <ripple/basics/CountedObject.h>
#include <ripple/basics/Log.h>
#include <ripple/core/Config.h>
#include <ripple/core/JobQueue.h>
#include <ripple/core/LoadFeeTrack.h>
#include <ripple/core/TimeKeeper.h>
#include <ripple/json/to_string.h>
#include <ripple/overlay/Overlay.h>
#include <ripple/overlay/predicates.h>
#include <ripple/protocol/st.h>
#include <ripple/protocol/Feature.h>
#include <ripple/beast/core/LexicalCast.h>
#include <ripple/basics/make_lock.h>
#include <type_traits>

namespace ripple {

LedgerConsensusImp::LedgerConsensusImp (
        Application& app,
        ConsensusImp& consensus,
        InboundTransactions& inboundTransactions,
        LocalTxs& localtx,
        LedgerMaster& ledgerMaster,
        FeeVote& feeVote)
    : _app (app)
    , _consensus (consensus)
    , _inboundTransactions (inboundTransactions)
    , _localTX (localtx)
    , _ledgerMaster (ledgerMaster)
    , _feeVote (feeVote)
    , _state (State::open)
    , _closeTime {}
    , _valPublic (_app.config().VALIDATION_PUB)
    , _valSecret (_app.config().VALIDATION_PRIV)
    , _consensusFail (false)
    , _currentMSeconds (0)
    , _closePercent (0)
    , _closeResolution (30)
    , _haveCloseTimeConsensus (false)
    , _consensusStartTime (std::chrono::steady_clock::now ())
    , _previousProposers (0)
    , _previousMSeconds (0)
    , _j (app.journal ("LedgerConsensus"))
{
    JLOG (_j.debug()) << "Creating consensus object";
}

Json::Value LedgerConsensusImp::getJson (bool full)
{
    Json::Value ret (Json::objectValue);
    std::lock_guard<std::recursive_mutex> _(_lock);

    ret["proposing"] = _proposing;
    ret["validating"] = _validating;
    ret["proposers"] = static_cast<int> (_peerPositions.size ());

    if (_haveCorrectLCL)
    {
        ret["synched"] = true;
        ret["ledger_seq"] = _previousLedger->info().seq + 1;
        ret["close_granularity"] = _closeResolution.count();
    }
    else
        ret["synched"] = false;

    switch (_state)
    {
    case State::open:
        ret[jss::state] = "open";
        break;

    case State::establish:
        ret[jss::state] = "consensus";
        break;

    case State::processing:
        ret[jss::state] = "processing";
        break;

    case State::accepted:
        ret[jss::state] = "accepted";
        break;
    }

    int v = _disputes.size ();

    if ((v != 0) && !full)
        ret["disputes"] = v;

    if (_ourPosition)
        ret["our_position"] = _ourPosition->getJson ();

    if (full)
    {
        using Int = Json::Value::Int;
        ret["current_ms"] = static_cast<Int>(_currentMSeconds.count());
        ret["close_percent"] = _closePercent;
        ret["close_resolution"] = _closeResolution.count();
        ret["have_time_consensus"] = _haveCloseTimeConsensus;
        ret["previous_proposers"] = _previousProposers;
        ret["previous_mseconds"] = static_cast<Int>(_previousMSeconds.count());

        if (! _peerPositions.empty ())
        {
            Json::Value ppj (Json::objectValue);

            for (auto& pp : _peerPositions)
            {
                ppj[to_string (pp.first)] = pp.second->getJson ();
            }
            ret["peer_positions"] = std::move(ppj);
        }

        if (! _acquired.empty ())
        {
            // acquired
            Json::Value acq (Json::objectValue);
            for (auto& at : _acquired)
            {
                if (at.second)
                    acq[to_string (at.first)] = "acquired";
                else
                    acq[to_string (at.first)] = "failed";
            }
            ret["acquired"] = std::move(acq);
        }

        if (! _disputes.empty ())
        {
            Json::Value dsj (Json::objectValue);
            for (auto& dt : _disputes)
            {
                dsj[to_string (dt.first)] = dt.second->getJson ();
            }
            ret["disputes"] = std::move(dsj);
        }

        if (! _closeTimes.empty ())
        {
            Json::Value ctj (Json::objectValue);
            for (auto& ct : _closeTimes)
            {
                ctj[std::to_string(ct.first.time_since_epoch().count())] = ct.second;
            }
            ret["close_times"] = std::move(ctj);
        }

        if (! _deadNodes.empty ())
        {
            Json::Value dnj (Json::arrayValue);
            for (auto const& dn : _deadNodes)
            {
                dnj.append (to_string (dn));
            }
            ret["dead_nodes"] = std::move(dnj);
        }
    }

    return ret;
}

uint256 LedgerConsensusImp::getLCL ()
{
    std::lock_guard<std::recursive_mutex> _(_lock);

    return _prevLedgerHash;
}

// Called when:
// 1) We take our initial position
// 2) We take a new position
// 3) We acquire a position a validator took
//
// We store it, notify peers that we have it,
// and update our tracking if any validators currently
// propose it/
void LedgerConsensusImp::mapCompleteInternal (
    uint256 const& hash,
    std::shared_ptr<SHAMap> const& map,
    bool acquired)
{
    if (acquired)
    {
        JLOG (_j.trace()) << "We have acquired txs " << hash;
    }

    if (!map)  // If the map was invalid
    {
        JLOG (_j.warn())
            << "Tried to acquire invalid transaction map: "
            << hash;
        _acquired[hash] = map;
        return;
    }

    assert (hash == map->getHash ().as_uint256());

    auto it = _acquired.find (hash);

    // If we have already acquired this transaction set
    if (it != _acquired.end ())
    {
        if (it->second)
            return; // we already have this map

        // We previously failed to acquire this map, now we have it
        _acquired.erase (hash);
    }

    // We now have a map that we did not have before

    if (! acquired)
    {
        // Put the map where others can get it
        _inboundTransactions.giveSet (hash, map, false);
    }

    // Inform directly-connected peers that we have this transaction set
    sendHaveTxSet (hash, true);

    if (_ourPosition && (! _ourPosition->isBowOut ())
        && (hash != _ourPosition->getCurrentHash ()))
    {
        // this will create disputed transactions
        auto it2 = _acquired.find (_ourPosition->getCurrentHash ());

        if (it2 == _acquired.end())
            LogicError ("We cannot find our own position!");

        assert ((it2->first == _ourPosition->getCurrentHash ())
            && it2->second);
        _compares.insert(hash);
        // Our position is not the same as the acquired position
        createDisputes (it2->second, map);
    }
    else if (! _ourPosition)
    {
        JLOG (_j.debug())
            << "Not creating disputes: no position yet.";
    }
    else if (_ourPosition->isBowOut ())
    {
        JLOG (_j.warn())
            << "Not creating disputes: not participating.";
    }
    else
    {
        JLOG (_j.debug())
            << "Not creating disputes: identical position.";
    }

    _acquired[hash] = map;

    // Adjust tracking for each peer that takes this position
    std::vector<NodeID> peers;
    auto const mapHash = map->getHash ().as_uint256();
    for (auto& it : _peerPositions)
    {
        if (it.second->getCurrentHash () == mapHash)
            peers.push_back (it.second->getPeerID ());
    }

    if (!peers.empty ())
    {
        adjustCount (map, peers);
    }
    else if (acquired)
    {
        JLOG (_j.warn())
            << "By the time we got the map " << hash
            << " no peers were proposing it";
    }
}

void LedgerConsensusImp::gotMap (
    uint256 const& hash,
    std::shared_ptr<SHAMap> const& map)
{
    std::lock_guard<std::recursive_mutex> _(_lock);

    try
    {
        mapCompleteInternal (hash, map, true);
    }
    catch (SHAMapMissingNode const& mn)
    {
        leaveConsensus();
        JLOG (_j.error()) <<
            "Missing node processing complete map " << mn;
        Rethrow();
    }
}

void LedgerConsensusImp::checkLCL ()
{
    uint256 netLgr = _prevLedgerHash;
    int netLgrCount = 0;

    uint256 favoredLedger = _prevLedgerHash; // Don't jump forward
    uint256 priorLedger;

    if (_haveCorrectLCL)
        priorLedger = _previousLedger->info().parentHash; // don't jump back

    // Get validators that are on our ledger, or  "close" to being on
    // our ledger.
    hash_map<uint256, ValidationCounter> vals =
        _app.getValidations ().getCurrentValidations(
            favoredLedger, priorLedger,
            _ledgerMaster.getValidLedgerIndex ());

    for (auto& it : vals)
    {
        if ((it.second.first > netLgrCount) ||
            ((it.second.first == netLgrCount) && (it.first == _prevLedgerHash)))
        {
           netLgr = it.first;
           netLgrCount = it.second.first;
        }
    }

    if (netLgr != _prevLedgerHash)
    {
        // LCL change
        const char* status;

        switch (_state)
        {
        case State::open:
            status = "open";
            break;

        case State::establish:
            status = "establish";
            break;

        case State::processing:
            status = "processing";
            break;

        case State::accepted:
            status = "accepted";
            break;

        default:
            status = "unknown";
        }

        JLOG (_j.warn())
            << "View of consensus changed during " << status
            << " (" << netLgrCount << ") status="
            << status << ", "
            << (_haveCorrectLCL ? "CorrectLCL" : "IncorrectLCL");
        JLOG (_j.warn()) << _prevLedgerHash
            << " to " << netLgr;
        JLOG (_j.warn())
            << ripple::getJson (*_previousLedger);

        if (auto stream = _j.debug())
        {
            for (auto& it : vals)
                stream
                    << "V: " << it.first << ", " << it.second.first;
            stream << getJson (true);
        }

        if (_haveCorrectLCL)
            _app.getOPs ().consensusViewChange ();

        handleLCL (netLgr);
    }
    else if (_previousLedger->info().hash != _prevLedgerHash)
        handleLCL (netLgr);
}

// Handle a change in the LCL during a consensus round
void LedgerConsensusImp::handleLCL (uint256 const& lclHash)
{
    assert (lclHash != _prevLedgerHash ||
            _previousLedger->info().hash != lclHash);

    if (_prevLedgerHash != lclHash)
    {
        // first time switching to this ledger
        _prevLedgerHash = lclHash;

        if (_haveCorrectLCL && _proposing && _ourPosition)
        {
            JLOG (_j.info()) << "Bowing out of consensus";
            _ourPosition->bowOut ();
            propose ();
        }

        // Stop proposing because we are out of sync
        _proposing = false;
        _peerPositions.clear ();
        _disputes.clear ();
        _compares.clear ();
        _closeTimes.clear ();
        _deadNodes.clear ();
        // To get back in sync:
        playbackProposals ();
    }

    if (_previousLedger->info().hash == _prevLedgerHash)
        return;

    // we need to switch the ledger we're working from
    auto buildLCL = _ledgerMaster.getLedgerByHash (_prevLedgerHash);
    if (! buildLCL)
    {
        if (_acquiringLedger != lclHash)
        {
            // need to start acquiring the correct consensus LCL
            JLOG (_j.warn()) <<
                "Need consensus ledger " << _prevLedgerHash;

            // Tell the ledger acquire system that we need the consensus ledger
            _acquiringLedger = _prevLedgerHash;

            auto app = &_app;
            auto hash = _acquiringLedger;
            _app.getJobQueue().addJob (
                jtADVANCE, "getConsensusLedger",
                [app, hash] (Job&) {
                    app->getInboundLedgers().acquire(
                        hash, 0, InboundLedger::fcCONSENSUS);
                });

            _haveCorrectLCL = false;
        }
        return;
    }

    assert (!buildLCL->open() && buildLCL->isImmutable ());
    assert (buildLCL->info().hash == lclHash);
    JLOG (_j.info()) <<
        "Have the consensus ledger " << _prevLedgerHash;
    startRound (
        lclHash,
        buildLCL,
        _closeTime,
        _previousProposers,
        _previousMSeconds);
    _proposing = false;
}

void LedgerConsensusImp::timerEntry ()
{
    std::lock_guard<std::recursive_mutex> _(_lock);

    try
    {
       if ((_state != State::processing) && (_state != State::accepted))
           checkLCL ();

        using namespace std::chrono;
        _currentMSeconds = duration_cast<milliseconds>
                           (steady_clock::now() - _consensusStartTime);

        _closePercent = _currentMSeconds * 100 /
            std::max<milliseconds> (
                _previousMSeconds, AV_MIN_CONSENSUS_TIME);

        switch (_state)
        {
        case State::open:
            statePreClose ();

            if (_state != State::establish) return;

            // Fall through

        case State::establish:
            stateEstablish ();
            return;

        case State::processing:
            // We are processing the finished ledger
            // logic of calculating next ledger advances us out of this state
            // nothing to do
            return;

        case State::accepted:
            // NetworkOPs needs to setup the next round
            // nothing to do
            return;
        }

        assert (false);
    }
    catch (SHAMapMissingNode const& mn)
    {
        leaveConsensus ();
        JLOG (_j.error()) <<
           "Missing node during consensus process " << mn;
        Rethrow();
    }
}

void LedgerConsensusImp::statePreClose ()
{
    // it is shortly before ledger close time
    bool anyTransactions = ! _app.openLedger().empty();
    int proposersClosed = _peerPositions.size ();
    int proposersValidated
        = _app.getValidations ().getTrustedValidationCount
        (_prevLedgerHash);

    // This computes how long since last ledger's close time
    using namespace std::chrono;
    milliseconds sinceClose;
    {
        bool previousCloseCorrect = _haveCorrectLCL
            && getCloseAgree (_previousLedger->info())
            && (_previousLedger->info().closeTime !=
                (_previousLedger->info().parentCloseTime + 1s));

        auto closeTime = previousCloseCorrect
            ? _previousLedger->info().closeTime // use consensus timing
            : _consensus.getLastCloseTime(); // use the time we saw

        auto now = _app.timeKeeper().closeTime();
        if (now >= closeTime)
            sinceClose = now - closeTime;
        else
            sinceClose = -milliseconds{closeTime - now};
    }

    auto const idleInterval = std::max<seconds>(LEDGER_IDLE_INTERVAL,
        2 * _previousLedger->info().closeTimeResolution);

    // Decide if we should close the ledger
    if (shouldCloseLedger (anyTransactions
        , _previousProposers, proposersClosed, proposersValidated
        , _previousMSeconds, sinceClose, _currentMSeconds
        , idleInterval, _app.journal ("LedgerTiming")))
    {
        closeLedger ();
    }
}

void LedgerConsensusImp::stateEstablish ()
{
    // Give everyone a chance to take an initial position
    if (_currentMSeconds < LEDGER_MIN_CONSENSUS)
        return;

    updateOurPositions ();

    // Nothing to do if we don't have consensus.
    if (!haveConsensus ())
        return;

    if (!_haveCloseTimeConsensus)
    {
        JLOG (_j.info()) <<
            "We have TX consensus but not CT consensus";
        return;
    }

    JLOG (_j.info()) <<
        "Converge cutoff (" << _peerPositions.size () << " participants)";
    _state = State::processing;
    beginAccept (false);
}

bool LedgerConsensusImp::haveConsensus ()
{
    // CHECKME: should possibly count unacquired TX sets as disagreeing
    int agree = 0, disagree = 0;
    uint256 ourPosition = _ourPosition->getCurrentHash ();

    // Count number of agreements/disagreements with our position
    for (auto& it : _peerPositions)
    {
        if (!it.second->isBowOut ())
        {
            if (it.second->getCurrentHash () == ourPosition)
            {
                ++agree;
            }
            else
            {
                JLOG (_j.debug()) << to_string (it.first)
                    << " has " << to_string (it.second->getCurrentHash ());
                ++disagree;
                if (_compares.count(it.second->getCurrentHash()) == 0)
                { // Make sure we have generated disputes
                    uint256 hash = it.second->getCurrentHash();
                    JLOG (_j.debug())
                        << "We have not compared to " << hash;
                    auto it1 = _acquired.find (hash);
                    auto it2 = _acquired.find(_ourPosition->getCurrentHash ());
                    if ((it1 != _acquired.end()) && (it2 != _acquired.end())
                        && (it1->second) && (it2->second))
                    {
                        _compares.insert(hash);
                        createDisputes(it2->second, it1->second);
                    }
                }
            }
        }
    }
    int currentValidations = _app.getValidations ()
        .getNodesAfter (_prevLedgerHash);

    JLOG (_j.debug())
        << "Checking for TX consensus: agree=" << agree
        << ", disagree=" << disagree;

    // Determine if we actually have consensus or not
    auto ret = checkConsensus (_previousProposers, agree + disagree, agree,
        currentValidations, _previousMSeconds, _currentMSeconds, _proposing,
        _app.journal ("LedgerTiming"));

    if (ret == ConsensusState::No)
        return false;

    // There is consensus, but we need to track if the network moved on
    // without us.
    if (ret == ConsensusState::MovedOn)
        _consensusFail = true;
    else
        _consensusFail = false;

    return true;
}

std::shared_ptr<SHAMap> LedgerConsensusImp::getTransactionTree (
    uint256 const& hash)
{
    std::lock_guard<std::recursive_mutex> _(_lock);

    auto it = _acquired.find (hash);
    if (it != _acquired.end() && it->second)
        return it->second;

    auto set = _inboundTransactions.getSet (hash, true);

    if (set)
        _acquired[hash] = set;

    return set;
}

bool LedgerConsensusImp::peerPosition (LedgerProposal::ref newPosition)
{
    std::lock_guard<std::recursive_mutex> _(_lock);

    auto const peerID = newPosition->getPeerID ();

    if (newPosition->getPrevLedger() != _prevLedgerHash)
    {
        JLOG (_j.debug()) << "Got proposal for "
            << newPosition->getPrevLedger ()
            << " but we are on " << _prevLedgerHash;
        return false;
    }

    if (_deadNodes.find (peerID) != _deadNodes.end ())
    {
        JLOG (_j.info())
            << "Position from dead node: " << to_string (peerID);
        return false;
    }

    LedgerProposal::pointer& currentPosition = _peerPositions[peerID];

    if (currentPosition)
    {
        assert (peerID == currentPosition->getPeerID ());

        if (newPosition->getProposeSeq ()
            <= currentPosition->getProposeSeq ())
        {
            return false;
        }
    }

    if (newPosition->isBowOut ())
    {
        JLOG (_j.info())
            << "Peer bows out: " << to_string (peerID);
        for (auto& it : _disputes)
            it.second->unVote (peerID);
        _peerPositions.erase (peerID);
        _deadNodes.insert (peerID);
        return true;
    }

    if (newPosition->isInitial ())
    {
        // Record the close time estimate
        JLOG (_j.trace())
            << "Peer reports close time as "
            << newPosition->getCloseTime().time_since_epoch().count();
        ++_closeTimes[newPosition->getCloseTime()];
    }

    JLOG (_j.trace()) << "Processing peer proposal "
        << newPosition->getProposeSeq () << "/"
        << newPosition->getCurrentHash ();
    currentPosition = newPosition;

    std::shared_ptr<SHAMap> set
        = getTransactionTree (newPosition->getCurrentHash ());

    if (set)
    {
        for (auto& it : _disputes)
            it.second->setVote (peerID, set->hasItem (it.first));
    }
    else
    {
        JLOG (_j.debug())
            << "Don't have tx set for peer";
    }

    return true;
}

void LedgerConsensusImp::simulate (
    boost::optional<std::chrono::milliseconds> consensusDelay)
{
    std::lock_guard<std::recursive_mutex> _(_lock);

    JLOG (_j.info()) << "Simulating consensus";
    closeLedger ();
    _currentMSeconds = consensusDelay.value_or(100ms);
    beginAccept (true);
    JLOG (_j.info()) << "Simulation complete";
}

void LedgerConsensusImp::accept (std::shared_ptr<SHAMap> set)
{
    // put our set where others can get it later
    if (set->getHash ().isNonZero ())
       _consensus.takePosition (_previousLedger->info().seq, set);

    auto closeTime = _ourPosition->getCloseTime();
    bool closeTimeCorrect;

    auto replay = _ledgerMaster.releaseReplay();
    if (replay)
    {
        // replaying, use the time the ledger we're replaying closed
        closeTime = replay->closeTime_;
        closeTimeCorrect = ((replay->closeFlags_ & sLCF_NoConsensusTime) == 0);
    }
    else if (closeTime == NetClock::time_point{})
    {
        // We agreed to disagree on the close time
        closeTime = _previousLedger->info().closeTime + 1s;
        closeTimeCorrect = false;
    }
    else
    {
        // We agreed on a close time
        closeTime = effectiveCloseTime (closeTime);
        closeTimeCorrect = true;
    }

    JLOG (_j.debug())
        << "Report: Prop=" << (_proposing ? "yes" : "no")
        << " val=" << (_validating ? "yes" : "no")
        << " corLCL=" << (_haveCorrectLCL ? "yes" : "no")
        << " fail=" << (_consensusFail ? "yes" : "no");
    JLOG (_j.debug())
        << "Report: Prev = " << _prevLedgerHash
        << ":" << _previousLedger->info().seq;
    JLOG (_j.debug())
        << "Report: TxSt = " << set->getHash ()
        << ", close " << closeTime.time_since_epoch().count()
        << (closeTimeCorrect ? "" : "X");

    // Put transactions into a deterministic, but unpredictable, order
    CanonicalTXSet retriableTxs (set->getHash ().as_uint256());

    std::shared_ptr<Ledger const> sharedLCL;
    {
        // Build the new last closed ledger
        auto buildLCL = std::make_shared<Ledger>(
            *_previousLedger,
            _app.timeKeeper().closeTime());
        auto const v2_enabled = buildLCL->rules().enabled(featureSHAMapV2,
                                                       _app.config().features);
        auto v2_transition = false;
        if (v2_enabled && !buildLCL->stateMap().is_v2())
        {
            buildLCL->make_v2();
            v2_transition = true;
        }

        // Set up to write SHAMap changes to our database,
        //   perform updates, extract changes
        JLOG (_j.debug())
            << "Applying consensus set transactions to the"
            << " last closed ledger";

        {
            OpenView accum(&*buildLCL);
            assert(!accum.open());
            if (replay)
            {
                // Special case, we are replaying a ledger close
                for (auto& tx : replay->txns_)
                    applyTransaction (_app, accum, tx.second, false, tapNO_CHECK_SIGN, _j);
            }
            else
            {
                // Normal case, we are not replaying a ledger close
                applyTransactions (_app, set.get(), accum,
                    *buildLCL, retriableTxs, tapNONE);
            }
            // Update fee computations.
            _app.getTxQ().processValidatedLedger(_app, accum,
                _currentMSeconds > 5s);

            accum.apply(*buildLCL);
        }

        // retriableTxs will include any transactions that
        // made it into the consensus set but failed during application
        // to the ledger.

        buildLCL->updateSkipList ();

        {
            // Write the final version of all modified SHAMap
            // nodes to the node store to preserve the new LCL

            int asf = buildLCL->stateMap().flushDirty (
                hotACCOUNT_NODE, buildLCL->info().seq);
            int tmf = buildLCL->txMap().flushDirty (
                hotTRANSACTION_NODE, buildLCL->info().seq);
            JLOG (_j.debug()) << "Flushed " <<
                asf << " accounts and " <<
                tmf << " transaction nodes";
        }
        buildLCL->unshare();

        // Accept ledger
        buildLCL->setAccepted(closeTime, _closeResolution,
                            closeTimeCorrect, _app.config());

        // And stash the ledger in the ledger master
        if (_ledgerMaster.storeLedger (buildLCL))
            JLOG (_j.debug())
                << "Consensus built ledger we already had";
        else if (_app.getInboundLedgers().find (buildLCL->info().hash))
            JLOG (_j.debug())
                << "Consensus built ledger we were acquiring";
        else
            JLOG (_j.debug())
                << "Consensus built new ledger";
        sharedLCL = std::move(buildLCL);
    }

    uint256 const newLCLHash = sharedLCL->info().hash;
    JLOG (_j.debug())
        << "Report: NewL  = " << newLCLHash
        << ":" << sharedLCL->info().seq;
    // Tell directly connected peers that we have a new LCL
    statusChange (protocol::neACCEPTED_LEDGER, *sharedLCL);

    if (_validating &&
        ! _ledgerMaster.isCompatible (*sharedLCL,
            _app.journal("LedgerConsensus").warn(),
            "Not validating"))
    {
        _validating = false;
    }

    if (_validating && ! _consensusFail)
    {
        // Build validation
        auto v = std::make_shared<STValidation> (newLCLHash,
            _consensus.validationTimestamp(_app.timeKeeper().now()),
            _valPublic, _proposing);
        v->setFieldU32 (sfLedgerSequence, sharedLCL->info().seq);
        addLoad(v);  // Our network load

        if (((sharedLCL->info().seq + 1) % 256) == 0)
        // next ledger is flag ledger
        {
            // Suggest fee changes and new features
            _feeVote.doValidation (sharedLCL, *v);
            _app.getAmendmentTable ().doValidation (sharedLCL, *v);
        }

        auto const signingHash = v->sign (_valSecret);
        v->setTrusted ();
        // suppress it if we receive it - FIXME: wrong suppression
        _app.getHashRouter ().addSuppression (signingHash);
        _app.getValidations ().addValidation (v, "local");
        _consensus.setLastValidation (v);
        Blob validation = v->getSigned ();
        protocol::TMValidation val;
        val.set_validation (&validation[0], validation.size ());
        // Send signed validation to all of our directly connected peers
        _app.overlay().send(val);
        JLOG (_j.info())
            << "CNF Val " << newLCLHash;
    }
    else
        JLOG (_j.info())
            << "CNF buildLCL " << newLCLHash;

    // See if we can accept a ledger as fully-validated
    _ledgerMaster.consensusBuilt (sharedLCL, getJson (true));

    {
        // Apply disputed transactions that didn't get in
        //
        // The first crack of transactions to get into the new
        // open ledger goes to transactions proposed by a validator
        // we trust but not included in the consensus set.
        //
        // These are done first because they are the most likely
        // to receive agreement during consensus. They are also
        // ordered logically "sooner" than transactions not mentioned
        // in the previous consensus round.
        //
        bool anyDisputes = false;
        for (auto& it : _disputes)
        {
            if (!it.second->getOurVote ())
            {
                // we voted NO
                try
                {
                    JLOG (_j.debug())
                        << "Test applying disputed transaction that did"
                        << " not get in";
                    SerialIter sit (it.second->peekTransaction().slice());

                    auto txn = std::make_shared<STTx const>(sit);

                    retriableTxs.insert (txn);

                    anyDisputes = true;
                }
                catch (std::exception const&)
                {
                    JLOG (_j.debug())
                        << "Failed to apply transaction we voted NO on";
                }
            }
        }

        // Build new open ledger
        auto lock = make_lock(
            _app.getMasterMutex(), std::defer_lock);
        auto sl = make_lock(
            _ledgerMaster.peekMutex (), std::defer_lock);
        std::lock(lock, sl);

        auto const localTx = _localTX.getTxSet();
        auto const oldOL = _ledgerMaster.getCurrentLedger();

        auto const lastVal = _ledgerMaster.getValidatedLedger();
        boost::optional<Rules> rules;
        if (lastVal)
            rules.emplace(*lastVal);
        else
            rules.emplace();
        _app.openLedger().accept(_app, *rules,
            sharedLCL, localTx, anyDisputes, retriableTxs, tapNONE,
                "consensus",
                    [&](OpenView& view, beast::Journal j)
                    {
                        // Stuff the ledger with transactions from the queue.
                        return _app.getTxQ().accept(_app, view);
                    });
    }

    _ledgerMaster.switchLCL (sharedLCL);

    assert (_ledgerMaster.getClosedLedger()->info().hash == sharedLCL->info().hash);
    assert (_app.openLedger().current()->info().parentHash == sharedLCL->info().hash);

    if (_validating)
    {
        // see how close our close time is to other node's
        //  close time reports, and update our clock.
        JLOG (_j.info())
            << "We closed at " << _closeTime.time_since_epoch().count();
        using usec64_t = std::chrono::duration<std::uint64_t>;
        usec64_t closeTotal = _closeTime.time_since_epoch();
        int closeCount = 1;

        for (auto const& p : _closeTimes)
        {
            // FIXME: Use median, not average
            JLOG (_j.info())
                << beast::lexicalCastThrow <std::string> (p.second)
                << " time votes for "
                << beast::lexicalCastThrow <std::string>
                       (p.first.time_since_epoch().count());
            closeCount += p.second;
            closeTotal += usec64_t(p.first.time_since_epoch()) * p.second;
        }

        closeTotal += usec64_t(closeCount / 2);  // for round to nearest
        closeTotal /= closeCount;
        using duration = std::chrono::duration<std::int32_t>;
        using time_point = std::chrono::time_point<NetClock, duration>;
        auto offset = time_point{closeTotal} -
                      std::chrono::time_point_cast<duration>(_closeTime);
        JLOG (_j.info())
            << "Our close offset is estimated at "
            << offset.count() << " (" << closeCount << ")";
        _app.timeKeeper().adjustCloseTime(offset);
    }

    // we have accepted a new ledger
    bool correct;
    {
        std::lock_guard<std::recursive_mutex> _(_lock);

        _state = State::accepted;
        correct = _haveCorrectLCL;
    }

    endConsensus (correct);
}

void LedgerConsensusImp::createDisputes (
    std::shared_ptr<SHAMap> const& m1,
    std::shared_ptr<SHAMap> const& m2)
{
    if (m1->getHash() == m2->getHash())
        return;

    JLOG (_j.debug()) << "createDisputes "
        << m1->getHash() << " to " << m2->getHash();
    SHAMap::Delta differences;
    m1->compare (*m2, differences, 16384);

    int dc = 0;
    // for each difference between the transactions
    for (auto& pos : differences)
    {
        ++dc;
        // create disputed transactions (from the ledger that has them)
        if (pos.second.first)
        {
            // transaction is only in first map
            assert (!pos.second.second);
            addDisputedTransaction (pos.first
                , pos.second.first->peekData ());
        }
        else if (pos.second.second)
        {
            // transaction is only in second map
            assert (!pos.second.first);
            addDisputedTransaction (pos.first
                , pos.second.second->peekData ());
        }
        else // No other disagreement over a transaction should be possible
            assert (false);
    }
    JLOG (_j.debug()) << dc << " differences found";
}

void LedgerConsensusImp::addDisputedTransaction (
    uint256 const& txID,
    Blob const& tx)
{
    if (_disputes.find (txID) != _disputes.end ())
        return;

    JLOG (_j.debug()) << "Transaction "
        << txID << " is disputed";

    bool ourVote = false;

    // Update our vote on the disputed transaction
    if (_ourPosition)
    {
        auto mit (_acquired.find (_ourPosition->getCurrentHash ()));

        if (mit != _acquired.end ())
            ourVote = mit->second->hasItem (txID);
        else
            assert (false); // We don't have our own position?
    }

    auto txn = std::make_shared<DisputedTx> (txID, tx, ourVote, _j);
    _disputes[txID] = txn;

    // Update all of the peer's votes on the disputed transaction
    for (auto& pit : _peerPositions)
    {
        auto cit (_acquired.find (pit.second->getCurrentHash ()));

        if ((cit != _acquired.end ()) && cit->second)
        {
            txn->setVote (pit.first, cit->second->hasItem (txID));
        }
    }

    // If we didn't relay this transaction recently, relay it to all peers
    if (_app.getHashRouter ().shouldRelay (txID))
    {
        protocol::TMTransaction msg;
        msg.set_rawtransaction (& (tx.front ()), tx.size ());
        msg.set_status (protocol::tsNEW);
        msg.set_receivetimestamp (
            _app.timeKeeper().now().time_since_epoch().count());
        _app.overlay ().foreach (send_always (
            std::make_shared<Message> (
                msg, protocol::mtTRANSACTION)));
    }
}

void LedgerConsensusImp::adjustCount (std::shared_ptr<SHAMap> const& map,
                  const std::vector<NodeID>& peers)
{
    for (auto& it : _disputes)
    {
        bool setHas = map->hasItem (it.second->getTransactionID ());
        for (auto const& pit : peers)
            it.second->setVote (pit, setHas);
    }
}

void LedgerConsensusImp::leaveConsensus ()
{
    if (_proposing)
    {
        if (_ourPosition && ! _ourPosition->isBowOut ())
        {
            _ourPosition->bowOut();
            propose();
        }
        _proposing = false;
    }
}

void LedgerConsensusImp::propose ()
{
    JLOG (_j.trace()) << "We propose: " <<
        (_ourPosition->isBowOut ()
            ? std::string ("bowOut")
            : to_string (_ourPosition->getCurrentHash ()));
    protocol::TMProposeSet prop;

    prop.set_currenttxhash (_ourPosition->getCurrentHash ().begin ()
        , 256 / 8);
    prop.set_previousledger (_ourPosition->getPrevLedger ().begin ()
        , 256 / 8);
    prop.set_proposeseq (_ourPosition->getProposeSeq ());
    prop.set_closetime(_ourPosition->getCloseTime().time_since_epoch().count());

    prop.set_nodepubkey (_valPublic.data(), _valPublic.size());

    _ourPosition->setSignature (
        signDigest (
            _valPublic,
            _valSecret,
            _ourPosition->getSigningHash()));

    auto sig = _ourPosition->getSignature();
    prop.set_signature (sig.data(), sig.size());

    _app.overlay().send(prop);
}

void LedgerConsensusImp::sendHaveTxSet (uint256 const& hash, bool direct)
{
    protocol::TMHaveTransactionSet msg;
    msg.set_hash (hash.begin (), 256 / 8);
    msg.set_status (direct ? protocol::tsHAVE : protocol::tsCAN_GET);
    _app.overlay ().foreach (send_always (
        std::make_shared <Message> (
            msg, protocol::mtHAVE_SET)));
}

void LedgerConsensusImp::statusChange (
    protocol::NodeEvent event, ReadView const& ledger)
{
    protocol::TMStatusChange s;

    if (!_haveCorrectLCL)
        s.set_newevent (protocol::neLOST_SYNC);
    else
        s.set_newevent (event);

    s.set_ledgerseq (ledger.info().seq);
    s.set_networktime (_app.timeKeeper().now().time_since_epoch().count());
    s.set_ledgerhashprevious(ledger.info().parentHash.begin (),
        std::decay_t<decltype(ledger.info().parentHash)>::bytes);
    s.set_ledgerhash (ledger.info().hash.begin (),
        std::decay_t<decltype(ledger.info().hash)>::bytes);

    std::uint32_t uMin, uMax;
    if (! _ledgerMaster.getFullValidatedRange (uMin, uMax))
    {
        uMin = 0;
        uMax = 0;
    }
    else
    {
        // Don't advertise ledgers we're not willing to serve
        std::uint32_t early = _ledgerMaster.getEarliestFetch ();
        if (uMin < early)
           uMin = early;
    }
    s.set_firstseq (uMin);
    s.set_lastseq (uMax);
    _app.overlay ().foreach (send_always (
        std::make_shared <Message> (
            s, protocol::mtSTATUS_CHANGE)));
    JLOG (_j.trace()) << "send status change to peer";
}

void LedgerConsensusImp::takeInitialPosition (
    std::shared_ptr<ReadView const> const& initialLedger)
{
    std::shared_ptr<SHAMap> initialSet = std::make_shared <SHAMap> (
        SHAMapType::TRANSACTION, _app.family(), SHAMap::version{1});
    initialSet->setUnbacked ();

    // Build SHAMap containing all transactions in our open ledger
    for (auto const& tx : initialLedger->txs)
    {
        Serializer s (2048);
        tx.first->add(s);
        initialSet->addItem (
            SHAMapItem (tx.first->getTransactionID(), std::move (s)), true, false);
    }

    if ((_app.config().standalone() || (_proposing && _haveCorrectLCL))
            && ((_previousLedger->info().seq % 256) == 0))
    {
        // previous ledger was flag ledger, add pseudo-transactions
        auto const validations =
            _app.getValidations().getValidations (
                _previousLedger->info().parentHash);

        auto const count = std::count_if (
            validations.begin(), validations.end(),
            [](auto const& v)
            {
                return v.second->isTrusted();
            });

        if (count >= _ledgerMaster.getMinValidations())
        {
            _feeVote.doVoting (
                _previousLedger,
                validations,
                initialSet);
            _app.getAmendmentTable ().doVoting (
                _previousLedger,
                validations,
                initialSet);
        }
    }

    // Set should be immutable snapshot
    initialSet = initialSet->snapShot (false);

    // Tell the ledger master not to acquire the ledger we're probably building
    _ledgerMaster.setBuildingLedger (_previousLedger->info().seq + 1);

    auto txSet = initialSet->getHash ().as_uint256();
    JLOG (_j.info()) << "initial position " << txSet;
    mapCompleteInternal (txSet, initialSet, false);

    _ourPosition = std::make_shared<LedgerProposal> (
        initialLedger->info().parentHash, txSet, _closeTime);

    for (auto& it : _disputes)
    {
        it.second->setOurVote (initialLedger->txExists (it.first));
    }

    // if any peers have taken a contrary position, process disputes
    hash_set<uint256> found;

    for (auto& it : _peerPositions)
    {
        uint256 set = it.second->getCurrentHash ();

        if (found.insert (set).second)
        {
            auto iit (_acquired.find (set));

            if (iit != _acquired.end ())
            {
                _compares.insert(iit->second->getHash().as_uint256());
                createDisputes (initialSet, iit->second);
            }
        }
    }

    if (_proposing)
        propose ();
}

/** How many of the participants must agree to reach a given threshold?

    Note that the number may not precisely yield the requested percentage.
    For example, with with size = 5 and percent = 70, we return 3, but
    3 out of 5 works out to 60%. There are no security implications to
    this.

    @param participants the number of participants (i.e. validators)
    @param the percent that we want to reach

    @return the number of participants which must agree
*/
static
int
participantsNeeded (int participants, int percent)
{
    int result = ((participants * percent) + (percent / 2)) / 100;

    return (result == 0) ? 1 : result;
}

NetClock::time_point
LedgerConsensusImp::effectiveCloseTime(NetClock::time_point closeTime)
{
    if (closeTime == NetClock::time_point{})
        return closeTime;

    return std::max<NetClock::time_point>(
        roundCloseTime (closeTime, _closeResolution),
        (_previousLedger->info().closeTime + 1s));
}

void LedgerConsensusImp::updateOurPositions ()
{
    // Compute a cutoff time
    auto peerCutoff
        = std::chrono::steady_clock::now ();
    auto ourCutoff
        = peerCutoff - PROPOSE_INTERVAL;
    peerCutoff -= PROPOSE_FRESHNESS;

    bool changes = false;
    std::shared_ptr<SHAMap> ourPosition;
    //  std::vector<uint256> addedTx, removedTx;

    // Verify freshness of peer positions and compute close times
    std::map<NetClock::time_point, int> closeTimes;
    auto it = _peerPositions.begin ();

    while (it != _peerPositions.end ())
    {
        if (it->second->isStale (peerCutoff))
        {
            // peer's proposal is stale, so remove it
            auto const& peerID = it->second->getPeerID ();
            JLOG (_j.warn())
                << "Removing stale proposal from " << peerID;
            for (auto& dt : _disputes)
                dt.second->unVote (peerID);
            it = _peerPositions.erase (it);
        }
        else
        {
            // proposal is still fresh
            ++closeTimes[effectiveCloseTime(it->second->getCloseTime())];
            ++it;
        }
    }

    // Update votes on disputed transactions
    for (auto& it : _disputes)
    {
        // Because the threshold for inclusion increases,
        //  time can change our position on a dispute
        if (it.second->updateVote (_closePercent, _proposing))
        {
            if (!changes)
            {
                ourPosition = _acquired[_ourPosition->getCurrentHash ()]
                    ->snapShot (true);
                assert (ourPosition);
                changes = true;
            }

            if (it.second->getOurVote ()) // now a yes
            {
                ourPosition->addItem (SHAMapItem (it.first
                    , it.second->peekTransaction ()), true, false);
                //              addedTx.push_back(it.first);
            }
            else // now a no
            {
                ourPosition->delItem (it.first);
                //              removedTx.push_back(it.first);
            }
        }
    }

    int neededWeight;

    if (_closePercent < AV_MID_CONSENSUS_TIME)
        neededWeight = AV_INIT_CONSENSUS_PCT;
    else if (_closePercent < AV_LATE_CONSENSUS_TIME)
        neededWeight = AV_MID_CONSENSUS_PCT;
    else if (_closePercent < AV_STUCK_CONSENSUS_TIME)
        neededWeight = AV_LATE_CONSENSUS_PCT;
    else
        neededWeight = AV_STUCK_CONSENSUS_PCT;

    NetClock::time_point closeTime = {};
    _haveCloseTimeConsensus = false;

    if (_peerPositions.empty ())
    {
        // no other times
        _haveCloseTimeConsensus = true;
        closeTime = effectiveCloseTime(_ourPosition->getCloseTime());
    }
    else
    {
        int participants = _peerPositions.size ();
        if (_proposing)
        {
            ++closeTimes[effectiveCloseTime(_ourPosition->getCloseTime())];
            ++participants;
        }

        // Threshold for non-zero vote
        int threshVote = participantsNeeded (participants,
            neededWeight);

        // Threshold to declare consensus
        int const threshConsensus = participantsNeeded (
            participants, AV_CT_CONSENSUS_PCT);

        JLOG (_j.info()) << "Proposers:"
            << _peerPositions.size () << " nw:" << neededWeight
            << " thrV:" << threshVote << " thrC:" << threshConsensus;

        for (auto const& it : closeTimes)
        {
            JLOG (_j.debug()) << "CCTime: seq "
                << _previousLedger->info().seq + 1 << ": "
                << it.first.time_since_epoch().count()
                << " has " << it.second << ", "
                << threshVote << " required";

            if (it.second >= threshVote)
            {
                // A close time has enough votes for us to try to agree
                closeTime = it.first;
                threshVote = it.second;

                if (threshVote >= threshConsensus)
                    _haveCloseTimeConsensus = true;
            }
        }

        if (!_haveCloseTimeConsensus)
        {
            JLOG (_j.debug()) << "No CT consensus:"
                << " Proposers:" << _peerPositions.size ()
                << " Proposing:" << (_proposing ? "yes" : "no")
                << " Thresh:" << threshConsensus
                << " Pos:" << closeTime.time_since_epoch().count();
        }
    }

    // Temporarily send a new proposal if there's any change to our
    // claimed close time. Once the new close time code is deployed
    // to the full network, this can be relaxed to force a change
    // only if the rounded close time has changed.
    if (!changes &&
            ((closeTime != _ourPosition->getCloseTime())
            || _ourPosition->isStale (ourCutoff)))
    {
        // close time changed or our position is stale
        ourPosition = _acquired[_ourPosition->getCurrentHash ()]
            ->snapShot (true);
        assert (ourPosition);
        changes = true; // We pretend our position changed to force
    }                   //   a new proposal

    if (changes)
    {
        ourPosition = ourPosition->snapShot (false);

        auto newHash = ourPosition->getHash ().as_uint256();
        JLOG (_j.info())
            << "Position change: CTime "
            << closeTime.time_since_epoch().count()
            << ", tx " << newHash;

        if (_ourPosition->changePosition(newHash, closeTime))
        {
            if (_proposing)
                propose ();

            mapCompleteInternal (newHash, ourPosition, false);
        }
    }
}

void LedgerConsensusImp::playbackProposals ()
{
    auto proposals = _consensus.getStoredProposals (_prevLedgerHash);

    for (auto& proposal : proposals)
    {
        if (peerPosition (proposal))
        {
            // Now that we know this proposal
            // is useful, relay it
            protocol::TMProposeSet prop;

            prop.set_proposeseq (
                proposal->getProposeSeq ());
            prop.set_closetime (
                proposal->getCloseTime ().time_since_epoch().count());

            prop.set_currenttxhash (
                proposal->getCurrentHash().begin(), 256 / 8);
            prop.set_previousledger (
                proposal->getPrevLedger().begin(), 256 / 8);

            auto const pk = proposal->getPublicKey().slice();
            prop.set_nodepubkey (pk.data(), pk.size());

            auto const sig = proposal->getSignature();
            prop.set_signature (sig.data(), sig.size());

            _app.overlay().relay (
                prop, proposal->getSuppressionID ());
        }
    }
}

void LedgerConsensusImp::closeLedger ()
{
    checkOurValidation ();
    _state = State::establish;
    _consensusStartTime = std::chrono::steady_clock::now ();
    _closeTime = _app.timeKeeper().closeTime();
    _consensus.setLastCloseTime(_closeTime);
    statusChange (protocol::neCLOSING_LEDGER, *_previousLedger);
    _ledgerMaster.applyHeldTransactions ();
    takeInitialPosition (_app.openLedger().current());
}

void LedgerConsensusImp::checkOurValidation ()
{
    // This only covers some cases - Fix for the case where we can't ever
    // acquire the consensus ledger
    if (! _haveCorrectLCL || ! _valPublic.size ()
        || _app.getOPs ().isNeedNetworkLedger ())
    {
        return;
    }

    auto lastValidation = _consensus.getLastValidation ();

    if (lastValidation)
    {
        if (lastValidation->getFieldU32 (sfLedgerSequence)
            == _previousLedger->info().seq)
        {
            return;
        }
        if (lastValidation->getLedgerHash () == _prevLedgerHash)
            return;
    }

    auto v = std::make_shared<STValidation> (_previousLedger->info().hash,
        _consensus.validationTimestamp(_app.timeKeeper().now()),
        _valPublic, false);
    addLoad(v);
    v->setTrusted ();
    auto const signingHash = v->sign (_valSecret);
        // FIXME: wrong supression
    _app.getHashRouter ().addSuppression (signingHash);
    _app.getValidations ().addValidation (v, "localMissing");
    Blob validation = v->getSigned ();
    protocol::TMValidation val;
    val.set_validation (&validation[0], validation.size ());
    _consensus.setLastValidation (v);
    JLOG (_j.warn()) << "Sending partial validation";
}

void LedgerConsensusImp::beginAccept (bool synchronous)
{
    auto consensusSet = _acquired[_ourPosition->getCurrentHash ()];

    if (!consensusSet)
    {
        JLOG (_j.fatal())
            << "We don't have a consensus set";
        abort ();
    }

    _consensus.newLCL (_peerPositions.size (), _currentMSeconds);

    if (synchronous)
        accept (consensusSet);
    else
    {
        _app.getJobQueue().addJob (jtACCEPT, "acceptLedger",
            std::bind (&LedgerConsensusImp::accept, shared_from_this (),
                       consensusSet));
    }
}

void LedgerConsensusImp::endConsensus (bool correctLCL)
{
    _app.getOPs ().endConsensus (correctLCL);
}

void LedgerConsensusImp::startRound (
    LedgerHash const& prevLCLHash,
    std::shared_ptr<Ledger const> const& prevLedger,
    NetClock::time_point closeTime,
    int previousProposers,
    std::chrono::milliseconds previousConvergeTime)
{
    std::lock_guard<std::recursive_mutex> _(_lock);

    if (_state == State::processing)
    {
        // We can't start a new round while we're processing
        return;
    }

    _state = State::open;
    _closeTime = closeTime;
    _prevLedgerHash = prevLCLHash;
    _previousLedger = prevLedger;
    _ourPosition.reset();
    _consensusFail = false;
    _currentMSeconds = 0ms;
    _closePercent = 0;
    _haveCloseTimeConsensus = false;
    _consensusStartTime = std::chrono::steady_clock::now();
    _previousProposers = previousProposers;
    _previousMSeconds = previousConvergeTime;
    _inboundTransactions.newRound (_previousLedger->info().seq);

    _peerPositions.clear();
    _acquired.clear();
    _disputes.clear();
    _compares.clear();
    _closeTimes.clear();
    _deadNodes.clear();

    _closeResolution = getNextLedgerTimeResolution (
        _previousLedger->info().closeTimeResolution,
        getCloseAgree (_previousLedger->info()),
        _previousLedger->info().seq + 1);

    if (_valPublic.size () && ! _app.getOPs ().isNeedNetworkLedger ())
    {
        // If the validation keys were set, and if we need a ledger,
        // then we want to validate, and possibly propose a ledger.
        JLOG (_j.info())
            << "Entering consensus process, validating";
        _validating = true;
        // Propose if we are in sync with the network
        _proposing =
            _app.getOPs ().getOperatingMode () == NetworkOPs::omFULL;
    }
    else
    {
        // Otherwise we just want to monitor the validation process.
        JLOG (_j.info())
            << "Entering consensus process, watching";
        _proposing = _validating = false;
    }

    _haveCorrectLCL = (_previousLedger->info().hash == _prevLedgerHash);

    if (! _haveCorrectLCL)
    {
        // If we were not handed the correct LCL, then set our state
        // to not proposing.
        _consensus.setProposing (false, false);
        handleLCL (_prevLedgerHash);

        if (! _haveCorrectLCL)
        {
            JLOG (_j.info())
                << "Entering consensus with: "
                << _previousLedger->info().hash;
            JLOG (_j.info())
                << "Correct LCL is: " << prevLCLHash;
        }
    }
    else
    {
        // update the network status table as to whether we're
        // proposing/validating
        _consensus.setProposing (_proposing, _validating);
    }

    playbackProposals ();
    if (_peerPositions.size() > (_previousProposers / 2))
    {
        // We may be falling behind, don't wait for the timer
        // consider closing the ledger immediately
        timerEntry ();
    }

}

void LedgerConsensusImp::addLoad(STValidation::ref val)
{
    std::uint32_t fee = std::max(
        _app.getFeeTrack().getLocalFee(),
        _app.getFeeTrack().getClusterFee());

    if (fee > _app.getFeeTrack().getLoadBase())
        val->setFieldU32(sfLoadFee, fee);
}

//------------------------------------------------------------------------------
std::shared_ptr <LedgerConsensus>
make_LedgerConsensus (
    Application& app,
    ConsensusImp& consensus,
    InboundTransactions& inboundTransactions,
    LocalTxs& localtx,
    LedgerMaster& ledgerMaster,
    FeeVote& feeVote)
{
    return std::make_shared <LedgerConsensusImp> (app, consensus,
        inboundTransactions, localtx, ledgerMaster, feeVote);
}

//------------------------------------------------------------------------------

int
applyTransaction (Application& app, OpenView& view,
    std::shared_ptr<STTx const> const& txn,
        bool retryAssured, ApplyFlags flags,
            beast::Journal j)
{
    // Returns false if the transaction has need not be retried.
    if (retryAssured)
        flags = flags | tapRETRY;

    JLOG (j.debug()) << "TXN "
        << txn->getTransactionID ()
        //<< (engine.view().open() ? " open" : " closed")
        // because of the optional in engine
        << (retryAssured ? "/retry" : "/final");
    JLOG (j.trace()) << txn->getJson (0);

    try
    {
        auto const result = apply(app,
            view, *txn, flags, j);
        if (result.second)
        {
            JLOG (j.debug())
                << "Transaction applied: " << transHuman (result.first);
            return LedgerConsensusImp::resultSuccess;
        }

        if (isTefFailure (result.first) || isTemMalformed (result.first) ||
            isTelLocal (result.first))
        {
            // failure
            JLOG (j.debug())
                << "Transaction failure: " << transHuman (result.first);
            return LedgerConsensusImp::resultFail;
        }

        JLOG (j.debug())
            << "Transaction retry: " << transHuman (result.first);
        return LedgerConsensusImp::resultRetry;
    }
    catch (std::exception const&)
    {
        JLOG (j.warn()) << "Throws";
        return LedgerConsensusImp::resultFail;
    }
}

void applyTransactions (
    Application& app,
    SHAMap const* set,
    OpenView& view,
    ReadView const& checkLedger,
    CanonicalTXSet& retriableTxs,
    ApplyFlags flags)
{

    auto j = app.journal ("LedgerConsensus");
    if (set)
    {
        for (auto const& item : *set)
        {
            if (checkLedger.txExists (item.key()))
                continue;

            // The transaction isn't in the check ledger, try to apply it
            JLOG (j.debug()) <<
                "Processing candidate transaction: " << item.key();
            std::shared_ptr<STTx const> txn;
            try
            {
                txn = std::make_shared<STTx const>(SerialIter{item.slice()});
            }
            catch (std::exception const&)
            {
                JLOG (j.warn()) << "  Throws";
            }

            if (txn)
            {
                // All transactions execute in canonical order
                retriableTxs.insert (txn);
            }
        }
    }

    bool certainRetry = true;
    // Attempt to apply all of the retriable transactions
    for (int pass = 0; pass < LEDGER_TOTAL_PASSES; ++pass)
    {
        JLOG (j.debug()) << "Pass: " << pass << " Txns: "
            << retriableTxs.size ()
            << (certainRetry ? " retriable" : " final");
        int changes = 0;

        auto it = retriableTxs.begin ();

        while (it != retriableTxs.end ())
        {
            try
            {
                switch (applyTransaction (app, view,
                    it->second, certainRetry, flags, j))
                {
                case LedgerConsensusImp::resultSuccess:
                    it = retriableTxs.erase (it);
                    ++changes;
                    break;

                case LedgerConsensusImp::resultFail:
                    it = retriableTxs.erase (it);
                    break;

                case LedgerConsensusImp::resultRetry:
                    ++it;
                }
            }
            catch (std::exception const&)
            {
                JLOG (j.warn())
                    << "Transaction throws";
                it = retriableTxs.erase (it);
            }
        }

        JLOG (j.debug()) << "Pass: "
            << pass << " finished " << changes << " changes";

        // A non-retry pass made no changes
        if (!changes && !certainRetry)
            return;

        // Stop retriable passes
        if (!changes || (pass >= LEDGER_RETRY_PASSES))
            certainRetry = false;
    }

    // If there are any transactions left, we must have
    // tried them in at least one final pass
    assert (retriableTxs.empty() || !certainRetry);
}

} // ripple
