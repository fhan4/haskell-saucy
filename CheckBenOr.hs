 {-# LANGUAGE ScopedTypeVariables, ImplicitParams, FlexibleContexts,
 PartialTypeSignatures, RankNTypes
  #-} 

{-
    BenOr QuickChecking
    ===================

  - here, unlike in ACast, a structured environment loops and sends Ones then Twos the maybe TwoD 
    messages .
  - we see if we can determing 

-}

module CheckBenOr where

import ProcessIO
import StaticCorruptions
import Async
import Multisession
import Multicast
import TokenWrapper
import BenOr
import TestTools

import Safe
import Control.Concurrent.MonadIO
import Control.Monad (forever, forM)
import Control.Monad.Loops (whileM_)
import Data.IORef.MonadIO
import Data.Data (toConstr, Data)
import Data.Map.Strict (Map)
import Data.Set (Set)
import Data.List ((\\), elemIndex, delete)
import Test.QuickCheck
import Test.QuickCheck.Monadic
import qualified Data.Set as Set
import qualified Data.Map.Strict as Map

data BenOrCmd = CmdBenOrP2F PID Bool | CmdOne SID PID Int Bool MulticastTokens | CmdTwo SID PID Int MulticastTokens | CmdTwoD SID PID Int Bool MulticastTokens deriving (Show, Eq, Read)

type BenOrInput = (BenOrCmd, Tokens)
type BenOrConfig = (SID, [PID], CruptList, Int)

performBenOrEnv 
  :: (MonadEnvironment m) => 
  BenOrConfig -> [Either BenOrInput AsyncInput] ->
  (Environment BenOrF2P ((ClockP2F BenOrP2F), CarryTokens Int)
     --(SttCruptA2Z (SID, (MulticastF2P BenOrMsg, TransferTokens Int)) 
     (SttCruptA2Z (SID, (MulticastF2P BenOrMsg, CarryTokens Int)) 
                  (Either (ClockF2A (SID, ((BenOrMsg, TransferTokens Int), CarryTokens Int)))
                          (SID, (MulticastF2A BenOrMsg, TransferTokens Int))))
     ((SttCruptZ2A (ClockP2F (SID, ((BenOrMsg, TransferTokens Int), CarryTokens Int))) 
                  (Either ClockA2F (SID, (MulticastA2F BenOrMsg, TransferTokens Int)))), CarryTokens Int) Void
     (ClockZ2F) Transcript m)
performBenOrEnv benOrConfig cmdList z2exec (p2z, z2p) (a2z, z2a) (f2z, z2f) pump outp = do
    let (sid :: SID, parties :: [PID], crupt :: Map PID (), t :: Int) = benOrConfig 
    writeChan z2exec $ SttCrupt_SidCrupt sid crupt

    (lastOut, transcript, clockChan) <- envReadOut p2z a2z
        
    () <- readChan pump 
  
    writeChan z2a $ ((SttCruptZ2A_A2F $ Left ClockA2F_GetCount), SendTokens 1000)
    readChan clockChan
    let n = length parties

    forMseq_ cmdList $ \cmd -> do 
        envExecAsyncCmd z2p z2a z2f clockChan pump cmd envExecBenOrCmd
    writeChan outp =<< readIORef transcript

-- TODO: here the integer here is the round number. Therefore we need to parameterize this with a range or rounds. Maybe this way we an see if it reaches consensus or there's a better way to give round numbers and iteratively increase the possible round numbers. 

{- In BenOr the ssids only need to be difference because the round number isn't encoded in them.
  therefore we can jut generate random ssid numbers for each message without caring too much about it -}
--benOrGenerator :: Int -> Int -> [Gen SID] -> [PID] -> [Gen Bool] -> Int -> Int -> Gen [Either BenOrInput AsyncInput]
benOrGenerator :: Int -> Int -> (String -> SID) -> [PID] -> [Gen Bool] -> Int -> Int -> Gen [Either BenOrInput AsyncInput]
benOrGenerator n numQueue ssid parties inputs round dts = frequency $
  [ (1, return []), 
    (10, if n==0 then return []
         else if numQueue==0 then (benOrGenerator n 0 ssid parties inputs round dts)
         else (:) <$> (choose (0,numQueue-1) >>= \i -> return (Right (CmdDeliver i, 0))) <*> (benOrGenerator (n-1) (numQueue-1) ssid parties inputs round dts)),
    (5, if n==0 then return [] else (:) <$> 
        ((shuffle parties) >>= 
          (\pl -> oneof inputs >>= 
            (\i -> (choose (0, 999999) :: Gen Int) >>=
              (\s -> return (Left (CmdOne (ssid (show s)) (pl !! 0) round i dts, 0)))))) <*> (benOrGenerator (n-1) numQueue ssid parties inputs round dts)),
    (5, if n==0 then return [] else (:) <$>
        ((shuffle parties) >>= 
          (\pl -> oneof inputs >>= 
            (\i -> (choose (0, 999999) :: Gen Int) >>=
              (\s -> return (Left (CmdTwo (ssid (show s)) (pl !! 0) round 0, 0)))))) <*> (benOrGenerator (n-1) numQueue ssid parties inputs round dts)),
    (5, if n==0 then return [] else (:) <$>
        ((shuffle parties) >>= 
          (\pl -> oneof inputs >>= 
            (\i -> (choose (0, 999999) :: Gen Int) >>=
              (\s -> return (Left (CmdTwoD (ssid (show s)) (pl !! 0) round i 0, 0)))))) <*> (benOrGenerator (n-1) numQueue ssid parties inputs round dts)) 
  ]


envExecBenOrCmd :: (MonadITM m) =>
  (Chan (PID, ((ClockP2F BenOrP2F), CarryTokens Int))) ->
  (Chan ((SttCruptZ2A (ClockP2F (SID, ((BenOrMsg, TransferTokens Int), CarryTokens Int))) (Either _ (SID, (MulticastA2F BenOrMsg, TransferTokens Int)))), CarryTokens Int)) ->
  (Chan ()) -> (Either BenOrInput _) -> m ()
envExecBenOrCmd z2p z2a pump cmd = do
  case cmd of
      Left ((CmdBenOrP2F pid' x'), st') -> do
          writeChan z2p $ (pid', ((ClockP2F_Through $ BenOrP2F_Input x'), SendTokens 32))
          readChan pump
      Left ((CmdOne ssid' pid' r' x' dt'), st') -> do
          writeChan z2a $ ((SttCruptZ2A_A2F $ Right (ssid', (MulticastA2F_Deliver pid' (One r' x'), DeliverTokensWithMessage 0))), SendTokens 0)
          readChan pump
      Left ((CmdTwo ssid' pid' r' dt'), st') -> do
          writeChan z2a $ ((SttCruptZ2A_A2F $ Right (ssid', (MulticastA2F_Deliver pid' (Two r'), DeliverTokensWithMessage 0))), SendTokens 0)
          readChan pump
      Left ((CmdTwoD ssid' pid' r' x' dt'), st') -> do
          writeChan z2a $ ((SttCruptZ2A_A2F $ Right (ssid', (MulticastA2F_Deliver pid' (TwoD r' x'), DeliverTokensWithMessage 0))), SendTokens 0)
          readChan pump

propUEnvBenOrSafety
  :: (MonadEnvironment m) => Int ->
  Environment BenOrF2P ((ClockP2F BenOrP2F), CarryTokens Int)
     --(SttCruptA2Z (SID, (MulticastF2P BenOrMsg, TransferTokens Int)) 
     (SttCruptA2Z (SID, (MulticastF2P BenOrMsg, CarryTokens Int)) 
                  (Either (ClockF2A (SID, ((BenOrMsg, TransferTokens Int), CarryTokens Int)))
                          (SID, (MulticastF2A BenOrMsg, TransferTokens Int))))
     ((SttCruptZ2A (ClockP2F (SID, ((BenOrMsg, TransferTokens Int), CarryTokens Int))) 
                  (Either ClockA2F (SID, (MulticastA2F BenOrMsg, TransferTokens Int)))), CarryTokens Int) Void
     (ClockZ2F) (BenOrConfig, [Either BenOrInput AsyncInput], Transcript) m
propUEnvBenOrSafety importAmt z2exec (p2z, z2p) (a2z, z2a) (f2z, z2f) pump outp = do
  let extendRight conf = show ("", conf)
  
  let parties = ["Alice", "Bob", "Carol", "Dave", "Eve", "Frank"] :: [PID]
  let t = 1 :: Int
  let crupt = "Alice" :: PID
  let honest = parties \\ [crupt]
  let sssid = "sidTestACast"
  let sid = (sssid, show (parties, t, ""))
  
  writeChan z2exec $ SttCrupt_SidCrupt sid (Map.fromList [(crupt, ())])
  
  cmdList <- newIORef []  
  thingsHappened <- newIORef 0

  (lastOut, transcript, clockChan) <- envReadOut p2z a2z

  () <- readChan pump
  modifyIORef cmdList $ (++) [Right (CmdGetCount, 1000)]
  writeChan z2a $ ((SttCruptZ2A_A2F $ Left ClockA2F_GetCount), SendTokens 1000)
  c <- readChan clockChan 
  
  let inputs = do [return True, return False]
 
  let checkQueue n = do
        modifyIORef cmdList $ (++ [Right (CmdGetCount, 0)])
        writeChan z2a $ (SttCruptZ2A_A2F (Left ClockA2F_GetCount), SendTokens 0)
        
        c <- readChan clockChan
        liftIO $ putStrLn $ "Z[testEnvACastIdeal]: Events remaining: " ++ show c
        return (c > 0)

  let inputTokens = importAmt
  -- Give somehonest parties some inputs
  -- choose input values for the honest parties
  -- should create 6 One messages each 
  forMseq_ honest $ \h -> do
    -- choose a boolean
    x <- liftIO $ generate chooseAny
    modifyIORef cmdList $ (++ [Left $ (CmdBenOrP2F h x, inputTokens)])
    writeChan z2p $ (h, ((ClockP2F_Through $ BenOrP2F_Input x), SendTokens inputTokens))
    readChan pump
  

  -- go in some limited number of rounds    
  firstInp <- newIORef []
  forMseq_ [1..30] $ \r -> do
    modifyIORef cmdList $ (++) [Right (CmdGetCount, 0)]
    writeChan z2a $ ((SttCruptZ2A_A2F $ Left ClockA2F_GetCount), SendTokens 0)
    c <- readChan clockChan 
    --inps <- liftIO $ generate $ benOrGenerator (max 20 c) c (multicastSid sssid crupt parties) parties inputs r 64
    inps <- liftIO $ generate $ benOrGenerator 30 c (multicastSid sssid crupt parties) parties inputs r inputTokens

    forMseq_ inps $ \i -> do
      --modifyIORef debugLog $ (++ [Left i])
      modifyIORef cmdList $ (++ [i])
      envExecAsyncCmd z2p z2a z2f clockChan pump i envExecBenOrCmd

  tr <- readIORef transcript
  cl <- readIORef cmdList
  
  writeChan outp ((sid, parties, (Map.fromList [(crupt,())]), t), cl, tr)

prop_uBenOrTest = monadicIO $ do
    let prot () = protBenOr
    (config', c', t') <- run $ runITMinIO 120 $ execUC 
      (propUEnvBenOrSafety 64)
      (runAsyncP $ prot ()) 
      (runAsyncF $ bangFAsync fMulticastToken) 
      dummyAdversaryToken
    outputs <- newIORef Set.empty
    forMseq_ [0..(length t')-1] $ \i -> do
        case (t' !! i) of 
            Right (pid, BenOrF2P_Deliver m) -> do
                liftIO $ putStrLn $ "\n\t ############### GOT SOME output " ++ show (t' !! i) ++ "\n"
                modifyIORef outputs $ Set.insert m
            Right _ -> return ()
            Left m -> return ()
    o <- readIORef outputs

    printYellow ("[Config]\n\n" ++ show config')
    printYellow ("[Inputs]\n\n" ++ show c')

  -- asserting size is 0 check causes test to fail when some party
  -- has decided a value (the point being to check how common it is
  -- for all parties to decide something
    assert ( (Set.size o) <= 1 )


{- 
  Propert compare structure agnostic of import 
-}
prop_uBenOrCompare = monadicIO $ do
  let prot () = protBenOr
  
  (config', c', t') <- run $ runITMinIO 120 $ execUC 
    (propUEnvBenOrSafety 1000)
    (runAsyncP $ prot ()) 
    (runAsyncF $ bangFAsync fMulticastToken) 
    dummyAdversaryToken
  
  numOutputs <- newIORef 0
  forMseq_ [0..(length t')-1] $ \i -> do
      case (t' !! i) of 
          Right (pid, BenOrF2P_Deliver m) -> do
              modifyIORef numOutputs $ (+) 1
          _ -> return ()

  n <- readIORef numOutputs
  monitor (collect n)

propEnvBenOrLivenessObserve
  :: (MonadEnvironment m) => Tokens ->
  Environment BenOrF2P ((ClockP2F BenOrP2F), CarryTokens Int)
     --(SttCruptA2Z (SID, (MulticastF2P BenOrMsg, TransferTokens Int)) 
     (SttCruptA2Z (SID, (MulticastF2P BenOrMsg, CarryTokens Int)) 
                  (Either (ClockF2A (SID, ((BenOrMsg, TransferTokens Int), CarryTokens Int)))
                          (SID, (MulticastF2A BenOrMsg, TransferTokens Int))))
     ((SttCruptZ2A (ClockP2F (SID, ((BenOrMsg, TransferTokens Int), CarryTokens Int))) 
                  (Either ClockA2F (SID, (MulticastA2F BenOrMsg, TransferTokens Int)))), CarryTokens Int) Void
     (ClockZ2F) (BenOrConfig, Transcript) m
propEnvBenOrLivenessObserve inputTokens z2exec (p2z, z2p) (a2z, z2a) (f2z, z2f) pump outp = do
{- The goal here is to have a crupt party to just observe how any rounds
    it takes for the protocol to terminte. We just look at the latest round
    received before all honest parties terminate.
  - OPTION 1: we can condition only on test cases where everyone terminates
              to observe only how many rounds it takes. -}
  let extendRight conf = show ("", conf)
  
  let parties = ["Alice", "Bob", "Carol", "Dave", "Eve", "Frank"] :: [PID]
  let t = 1 :: Int
  let crupt = "Alice" :: PID
  let honest = parties \\ [crupt]
  let sssid = "sidTestACast"
  let sid = (sssid, show (parties, t, ""))

  writeChan z2exec $ SttCrupt_SidCrupt sid (Map.fromList [(crupt, ())])
  thingsHappened <- newIORef 0

  (lastOut, transcript, clockChan) <- envReadOut p2z a2z
  
  () <- readChan pump
  writeChan z2a $ ((SttCruptZ2A_A2F $ Left ClockA2F_GetCount), SendTokens 1000)
  c <- readChan clockChan 

  finalRound <- newIORef 0
  let lastRound ctr party = do
              t <- readIORef transcript
              forMseq_ (deleteNth 0 (reverse t)) $ \msg -> do
                case msg of
                  Left (SttCruptA2Z_P2A (pid, (s, (MulticastF2P_Deliver m, stk)))) -> 
                    case m of
                      One r b -> readIORef finalRound >>= writeIORef finalRound . max r
                      Two r -> readIORef finalRound >>= writeIORef finalRound . max r
                      TwoD r b -> readIORef finalRound >>= writeIORef finalRound . max r
                  _ -> return () 
  
  let checkQueue = do
        writeChan z2a $ (SttCruptZ2A_A2F (Left ClockA2F_GetCount), SendTokens 0)
        c <- readChan clockChan
        liftIO $ putStrLn $ "Z[testEnvACastIdeal]: Events remaining: " ++ show c
        return (c > 0)
        
  -- choose input values for the honest parties
  -- should create 6 One messages each 
  forMseq_ honest $ \h -> do
    -- choose a boolean
    x <- liftIO $ generate chooseAny
    writeChan z2p $ (h, ((ClockP2F_Through $ BenOrP2F_Input x), SendTokens inputTokens))
    readChan pump
    
  whileM_ checkQueue $ do
    writeChan z2a $ ((SttCruptZ2A_A2F $ Left ClockA2F_GetCount), SendTokens 0)
    c <- readChan clockChan
    idx <- liftIO $ generate $ choose (0,c-1)
    writeChan z2a $ ((SttCruptZ2A_A2F $ Left (ClockA2F_Deliver idx)), SendTokens 0)
    readChan pump
  
  tr <- readIORef transcript 
  writeChan outp ((sid, parties, (Map.fromList [(crupt,())]), t), tr)

prop_benOrObserve = monadicIO $ do
  let prot () = protBenOr
  (config', t') <- run $ runITMinIO 120 $ execUC 
    (propEnvBenOrLivenessObserve 1000000)
    (runAsyncP $ prot ()) 
    (runAsyncF $ bangFAsync fMulticastToken) 
    dummyAdversaryToken
 
  finalRound <- newIORef 0
  commitRound <- newIORef 0 
  numOutputs <- newIORef 0
  forMseq_ t' $ \out -> do
      case out of
        Left (SttCruptA2Z_P2A (pid, (s, (MulticastF2P_Deliver m, stk)))) ->
          case m of
            One r b -> readIORef finalRound >>= writeIORef finalRound . max r
            Two r -> readIORef finalRound >>= writeIORef finalRound . max r
            TwoD r b -> readIORef finalRound >>= writeIORef finalRound . max r
        Right (pid, BenOrF2P_Deliver m) -> do
          readIORef finalRound >>= writeIORef commitRound  
          modifyIORef numOutputs $ (+) 1
        _ -> return ()

  n <- readIORef numOutputs
  pre $ (n == 5)
  cr <- readIORef commitRound
  monitor (collect cr)

{- this environment generator is quite structured towards the BenOr protocol where
   where inputs are given, some messages are delivered thenmessages are sent by corrupt parties
   according to where they are expected by the protocl. 
   The next steps are:
    1. Create a generic environment that is agnostic to the protocol and takes in 
      some type of corrut party messages, some type of honest party messages,
      and randomly chooses from them. Run until interesting things happen. 
      First check how often something interesting happens.
    2. create a grammar for correlating state/output to the possible inputs, both
      corrupt and honest, that the environment can give.
-}
propEnvBenOrLiveness
  :: (MonadEnvironment m) => Tokens ->
  Environment BenOrF2P ((ClockP2F BenOrP2F), CarryTokens Int)
     --(SttCruptA2Z (SID, (MulticastF2P BenOrMsg, TransferTokens Int)) 
     (SttCruptA2Z (SID, (MulticastF2P BenOrMsg, CarryTokens Int)) 
                  (Either (ClockF2A (SID, ((BenOrMsg, TransferTokens Int), CarryTokens Int)))
                          (SID, (MulticastF2A BenOrMsg, TransferTokens Int))))
     ((SttCruptZ2A (ClockP2F (SID, ((BenOrMsg, TransferTokens Int), CarryTokens Int))) 
                  (Either ClockA2F (SID, (MulticastA2F BenOrMsg, TransferTokens Int)))), CarryTokens Int) Void
     (ClockZ2F) (BenOrConfig, [Either BenOrInput AsyncInput], Transcript) m
propEnvBenOrLiveness inputTokens z2exec (p2z, z2p) (a2z, z2a) (f2z, z2f) pump outp = do
  let extendRight conf = show ("", conf)
  
  let parties = ["Alice", "Bob", "Carol", "Dave", "Eve", "Frank"] :: [PID]
  let t = 1 :: Int
  let crupt = "Alice" :: PID
  let honest = parties \\ [crupt]
  let sssid = "sidTestACast"
  let sid = (sssid, show (parties, t, ""))

  writeChan z2exec $ SttCrupt_SidCrupt sid (Map.fromList [(crupt, ())])

  -- compute ssids
  --let ssidAlice1 = ("sidTestACast", show ("Alice", ["Alice", "Bob", "Carol", "Dave"], "1"))
  --let ssidAlice2 = ("sidTestACast", show ("Alice", ["Alice", "Bob", "Carol", "Dave"], "2"))
  --let ssidAlice3 = ("sidTestACast", show ("Alice", ["Alice", "Bob", "Carol", "Dave"], "3"))
  
  cmdList <- newIORef []  
  thingsHappened <- newIORef 0

  (lastOut, transcript, clockChan) <- envReadOut p2z a2z

  counter <- newIORef 0
  let multicastSid c ps p = (show c, show (p, ps, ""))

  () <- readChan pump
  writeChan z2a $ ((SttCruptZ2A_A2F $ Left ClockA2F_GetCount), SendTokens 1000)
  c <- readChan clockChan 
  modifyIORef cmdList $ (++) [Right (CmdGetCount, 1000)]
  
  --let inputTokens = 64

  -- choose input values for the honest parties
  -- should create 6 One messages each 
  forMseq_ honest $ \h -> do
    -- choose a boolean
    x <- liftIO $ generate chooseAny
    writeChan z2p $ (h, ((ClockP2F_Through $ BenOrP2F_Input x), SendTokens inputTokens))
    () <- readChan pump
    modifyIORef cmdList $ (++) [Left $ (CmdBenOrP2F h x, inputTokens)]

  -- send out adversary One messages  
  -- send a message TO ALL HONEST PARTIES
  --let cruptssid = multicastSid sssid crupt parties "1"
  ctr <- readIORef counter
  modifyIORef counter $ (+) 1
  let cruptssid = multicastSid ctr "Alice" parties
  forMseq_ honest $ \hp -> do
    -- choose a bit
    x <- liftIO $ generate chooseAny
    writeChan z2a $ ((SttCruptZ2A_A2F $ Right (cruptssid, (MulticastA2F_Deliver hp (One 1 x), DeliverTokensWithMessage 0))), SendTokens 0)
    () <- readChan pump 
    modifyIORef cmdList $ (++) [Left (CmdOne cruptssid hp 1 x 0, 0)]

  -- do some series of make progresses and delivers
  writeIORef thingsHappened 0
  getCmdChan <- newChan
  () <- envDeliverOrProgressAll thingsHappened clockChan 10 getCmdChan z2exec (p2z, z2p) (a2z, z2a) (f2z, z2f) pump outp
  theList <- readChan getCmdChan
  modifyIORef cmdList $ (++) theList

  -- send out adversary Two messages  
  --let cruptssid = multicastSid sssid crupt parties "2"
  forMseq_ honest $ \hp -> do
    -- choose a bit
    x :: Bool <- liftIO $ generate chooseAny
    b :: Bool <- liftIO $ generate chooseAny
    if b then do
      writeChan z2a $ ((SttCruptZ2A_A2F $ Right (cruptssid, (MulticastA2F_Deliver hp (Two 1), DeliverTokensWithMessage 0))), SendTokens 0)
      modifyIORef cmdList $ (++) [Left (CmdTwo cruptssid hp 1 0, 0)]
    else do
      writeChan z2a $ ((SttCruptZ2A_A2F $ Right (cruptssid, (MulticastA2F_Deliver hp (TwoD 1 x), DeliverTokensWithMessage 0))), SendTokens 0)
      modifyIORef cmdList $ (++) [Left (CmdTwoD cruptssid hp 1 x 0, 0)]
    () <- readChan pump 
    return ()

  -- do some series of make progresses and delivers
  writeIORef thingsHappened 0
  getCmdChan <- newChan
  () <- envDeliverOrProgressAll thingsHappened clockChan 10 getCmdChan z2exec (p2z, z2p) (a2z, z2a) (f2z, z2f) pump outp
  theList <- readChan getCmdChan
  modifyIORef cmdList $ (++) theList
 
  -- deliver the rest 
  getCmdChan <- newChan
  () <- envDeliverAll clockChan 10 getCmdChan z2exec (p2z, z2p) (a2z, z2a) (f2z, z2f) pump outp
  theList <- readChan getCmdChan
  modifyIORef cmdList $ (++) theList

  writeChan z2a $ ((SttCruptZ2A_A2F $ Left ClockA2F_GetCount), SendTokens 0)
  c <- readChan clockChan
  modifyIORef cmdList $ (++) [Right (CmdGetCount, 0)]
 
  if (c /= 0) then error " stil not done wtf "
  else return ()

  tr <- readIORef transcript
  cl <- readIORef cmdList
  writeChan outp ((sid, parties, (Map.fromList [(crupt,())]), t), reverse cl, tr)

-- runs tests on the real world protocol only
-- no simulation checking
-- this test runs the Liveness environment with some x import tokens
-- and the test "fails" when import is exhausted and no value has been decided
-- by any party
prop_benOrLiveness = monadicIO $ do
    let prot () = protBenOr
    (config', c', t') <- run $ runITMinIO 120 $ execUC 
      (propEnvBenOrLiveness 64)
      (runAsyncP $ prot ()) 
      (runAsyncF $ bangFAsync fMulticastToken) 
      dummyAdversaryToken
    outputs <- newIORef Set.empty
    forMseq_ t' $ \out -> do
        case out of 
            Right (pid, BenOrF2P_Deliver m) -> do
                modifyIORef outputs $ Set.insert m
            _ -> return ()
    o <- readIORef outputs

    printYellow ("[Config]\n\n" ++ show config')
    printYellow ("[Inputs]\n\n" ++ show c')

  -- asserting size is 0 check causes test to fail when some party
  -- has decided a value (the point being to check how common it is
  -- for all parties to decide something
  -- assert ( (Set.size o) == 0 )
    monitor (collect (Set.size o))

{- This property shows how `collect` is used to report, at the end of the test, reports statistics
    about the number of parties that decided some value over the 100 test cases. This property
    doesn't test anything. The point here is to use thie  -}
prop_benOrCollectDecisions ns = monadicIO $ do
  let prot () = protBenOr
  forMseq_ ns $ \imp -> do
    (config', c', t') <- run $ runITMinIO 120 $ execUC 
      (propEnvBenOrLiveness imp)
      (runAsyncP $ prot ()) 
      (runAsyncF $ bangFAsync fMulticastToken) 
      dummyAdversaryToken
    
    numOutputs <- newIORef 0
    forMseq_ [0..(length t')-1] $ \i -> do
        case (t' !! i) of 
            Right (pid, BenOrF2P_Deliver m) -> do
                modifyIORef numOutputs $ (+) 1
            _ -> return ()

    n <- readIORef numOutputs
    monitor (collect (imp, n))

propEnvBenOrAllHonest
  :: (MonadEnvironment m) =>
  Environment BenOrF2P ((ClockP2F BenOrP2F), CarryTokens Int)
     --(SttCruptA2Z (SID, (MulticastF2P BenOrMsg, TransferTokens Int)) 
     (SttCruptA2Z (SID, (MulticastF2P BenOrMsg, CarryTokens Int)) 
                  (Either (ClockF2A (SID, ((BenOrMsg, TransferTokens Int), CarryTokens Int)))
                          (SID, (MulticastF2A BenOrMsg, TransferTokens Int))))
     ((SttCruptZ2A (ClockP2F (SID, ((BenOrMsg, TransferTokens Int), CarryTokens Int))) 
                  (Either ClockA2F (SID, (MulticastA2F BenOrMsg, TransferTokens Int)))), CarryTokens Int) Void
     (ClockZ2F) (BenOrConfig, [Either BenOrInput AsyncInput], Transcript) m
propEnvBenOrAllHonest z2exec (p2z, z2p) (a2z, z2a) (f2z, z2f) pump outp = do
  let extendRight conf = show ("", conf)
  
  let parties = ["Alice", "Bob", "Carol", "Dave", "Eve", "Frank"] :: [PID]
  let t = 1 :: Int
  let honest = parties
  let sssid = "sidTestBenOr"
  let sid = (sssid, show (parties, t, ""))

  writeChan z2exec $ SttCrupt_SidCrupt sid Map.empty
  
  cmdList <- newIORef []  
  thingsHappened <- newIORef 0

  (lastOut, transcript, clockChan) <- envReadOut p2z a2z

  () <- readChan pump
  writeChan z2a $ ((SttCruptZ2A_A2F $ Left ClockA2F_GetCount), SendTokens 1000)
  c <- readChan clockChan 
  modifyIORef cmdList $ (++) [Right (CmdGetCount, 1000)]
  
  let inputTokens = 64
  
  -- choose input values for the honest parties
  -- should create 6 One messages each 
  liftIO $ putStrLn $ "Honest: " ++ show honest
  forMseq_ honest $ \h -> do
    -- choose a boolean
    x <- liftIO $ generate chooseAny
    writeChan z2p $ (h, ((ClockP2F_Through $ BenOrP2F_Input x), SendTokens inputTokens))
    () <- readChan pump
    modifyIORef cmdList $ (++) [Left $ (CmdBenOrP2F h x, inputTokens)]
  
  -- deliver all the ones scheduled form the above inputs
  writeIORef thingsHappened 0
  getCmdChan <- newChan
  () <- envDeliverOrProgressAll thingsHappened clockChan 10 getCmdChan z2exec (p2z, z2p) (a2z, z2a) (f2z, z2f) pump outp
  theList <- readChan getCmdChan
  modifyIORef cmdList $ (++) theList

  -- deliver all the twos
  writeIORef thingsHappened 0
  getCmdChan <- newChan
  () <- envDeliverOrProgressAll thingsHappened clockChan 10 getCmdChan z2exec (p2z, z2p) (a2z, z2a) (f2z, z2f) pump outp
  theList <- readChan getCmdChan
  modifyIORef cmdList $ (++) theList

  writeChan z2a $ ((SttCruptZ2A_A2F $ Left ClockA2F_GetCount), SendTokens 0)
  c <- readChan clockChan
  modifyIORef cmdList $ (++) [Right (CmdGetCount, 0)]
 
  if (c /= 0) then error " stil not done wtf "
  else return ()

  tr <- readIORef transcript
  cl <- readIORef cmdList

  writeChan outp ((sid, parties, Map.empty, t), reverse cl, tr)
  
-- runs tests on the real world protocol only
-- no simulation checking
prop_benOrAllHonest= monadicIO $ do
    let prot () = protBenOr
    (config', c', t') <- run $ runITMinIO 120 $ execUC 
      propEnvBenOrAllHonest
      (runAsyncP $ prot ()) 
      (runAsyncF $ bangFAsync fMulticastToken) 
      dummyAdversaryToken
    outputs <- newIORef Set.empty
    forMseq_ [0..(length t')-1] $ \i -> do
        case (t' !! i) of 
            Right (pid, BenOrF2P_Deliver m) -> do
                liftIO $ putStrLn $ "\n\t ############### GOT SOME output " ++ show (t' !! i) ++ "\n"
                modifyIORef outputs $ Set.insert m
            Right _ -> return ()
            Left m -> return ()
    o <- readIORef outputs

    printYellow ("[Config]\n\n" ++ show config')
    printYellow ("[Inputs]\n\n" ++ show c')
    assert ( (Set.size o) == 0 )
