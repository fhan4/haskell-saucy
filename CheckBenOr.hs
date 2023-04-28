 {-# LANGUAGE ScopedTypeVariables, ImplicitParams, FlexibleContexts,
 PartialTypeSignatures, RankNTypes
  #-} 

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

    transcript <- newIORef []
    fork $ forever $ do
      (pid, m) <- readChan p2z
      modifyIORef transcript (++ [Right (pid, m)])
      --printEnvIdeal $ "[testEnvACast]: pid[" ++ pid ++ "] output " ++ show m
      ?pass

    clockChan <- newChan
    fork $ forever $ do
      mb <- readChan a2z
      modifyIORef transcript (++ [Left mb])
      case mb of
        SttCruptA2Z_F2A (Left (ClockF2A_Pass)) -> do
          printEnvReal $ "Pass"
          ?pass
        SttCruptA2Z_F2A (Left (ClockF2A_Count c)) ->
          writeChan clockChan c
        SttCruptA2Z_P2A (pid, m) -> do
          case m of
            _ -> do
              printEnvReal $ "[" ++pid++ "] (corrupt) received: " ++ show m
          ?pass
        SttCruptA2Z_F2A (Left (ClockF2A_Leaks l)) -> do
          --printEnvIdeal $ "[testEnvACastBroken leaks]: " ++ show l
          ?pass
        SttCruptA2Z_F2A (Left (ClockF2A_Advance)) -> do
          printEnvReal $ "Forced Clock advance"
          ?pass
        _ -> error $ "Help!" ++ show mb
        
    () <- readChan pump 
  
    writeChan z2a $ ((SttCruptZ2A_A2F $ Left ClockA2F_GetCount), SendTokens 1000)
    readChan clockChan
    let n = length parties

    forMseq_ cmdList $ \cmd -> do 
        envExecAsyncCmd z2p z2a z2f clockChan pump cmd envExecBenOrCmd
        --case cmd of
        --    Left ((CmdBenOrP2F pid' x'), st') -> do
        --        writeChan z2p $ (pid', ((ClockP2F_Through $ BenOrP2F_Input x'), SendTokens 32))
        --        readChan pump
        --    Left ((CmdOne ssid' pid' r' x' dt'), st') -> do
        --        writeChan z2a $ ((SttCruptZ2A_A2F $ Right (ssid', (MulticastA2F_Deliver pid' (One r' x'), DeliverTokensWithMessage 0))), SendTokens 0)
        --        readChan pump
        --    Left ((CmdTwo ssid' pid' r' dt'), st') -> do
        --        writeChan z2a $ ((SttCruptZ2A_A2F $ Right (ssid', (MulticastA2F_Deliver pid' (Two r'), DeliverTokensWithMessage 0))), SendTokens 0)
        --        readChan pump
        --    Left ((CmdTwoD ssid' pid' r' x' dt'), st') -> do
        --        writeChan z2a $ ((SttCruptZ2A_A2F $ Right (ssid', (MulticastA2F_Deliver pid' (TwoD r' x'), DeliverTokensWithMessage 0))), SendTokens 0)
        --        readChan pump
        --    Right ((CmdDeliver idx'), st') -> do
        --        writeChan z2a $ ((SttCruptZ2A_A2F $ Left (ClockA2F_Deliver idx')), SendTokens 0)
        --        readChan pump
        --    Right ((CmdGetCount), st') -> do     
        --        writeChan z2a $ ((SttCruptZ2A_A2F $ Left ClockA2F_GetCount), SendTokens 0)
        --        readChan clockChan
        --        return ()
        --    Right ((CmdMakeProgress), _) -> do
        --        writeChan z2f ClockZ2F_MakeProgress
        --        readChan pump
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
  :: (MonadEnvironment m) =>
  Environment BenOrF2P ((ClockP2F BenOrP2F), CarryTokens Int)
     --(SttCruptA2Z (SID, (MulticastF2P BenOrMsg, TransferTokens Int)) 
     (SttCruptA2Z (SID, (MulticastF2P BenOrMsg, CarryTokens Int)) 
                  (Either (ClockF2A (SID, ((BenOrMsg, TransferTokens Int), CarryTokens Int)))
                          (SID, (MulticastF2A BenOrMsg, TransferTokens Int))))
     ((SttCruptZ2A (ClockP2F (SID, ((BenOrMsg, TransferTokens Int), CarryTokens Int))) 
                  (Either ClockA2F (SID, (MulticastA2F BenOrMsg, TransferTokens Int)))), CarryTokens Int) Void
     (ClockZ2F) (BenOrConfig, [Either BenOrInput AsyncInput], Transcript) m
propUEnvBenOrSafety z2exec (p2z, z2p) (a2z, z2a) (f2z, z2f) pump outp = do
  let extendRight conf = show ("", conf)
  
  let parties = ["Alice", "Bob", "Carol", "Dave", "Eve", "Frank"] :: [PID]
  let t = 1 :: Int
  let crupt = "Alice" :: PID
  let honest = parties \\ [crupt]
  let sssid = "sidTestACast"
  let sid = (sssid, show (parties, t, ""))
  
  writeChan z2exec $ SttCrupt_SidCrupt sid (Map.fromList [(crupt, ())])
  
  transcript <- newIORef []
  cmdList <- newIORef []  
  debugLog <- newIORef []
  thingsHappened <- newIORef 0

  fork $ forever $ do
    (pid, m) <- readChan p2z
    modifyIORef transcript (++ [Right (pid, m)])
    modifyIORef debugLog $ (++ [Right (Right (pid,m))])
    modifyIORef thingsHappened $ (+) 1
    printEnvIdeal $ "[testEnvACast]: pid[" ++ pid ++ "] output " ++ show m
    ?pass

  clockChan <- newChan

  fork $ forever $ do
    mb <- readChan a2z
    modifyIORef transcript (++ [Left mb])
    modifyIORef debugLog $ (++ [Right (Left mb)])
    case mb of
      SttCruptA2Z_F2A (Left (ClockF2A_Pass)) -> do
        printEnvReal $ "Pass"
        modifyIORef thingsHappened $ (+) 1
        ?pass
      SttCruptA2Z_F2A (Left (ClockF2A_Count c)) ->
        writeChan clockChan c
      SttCruptA2Z_P2A (pid, m) -> do
        case m of
          _ -> do
            printEnvReal $ "[" ++pid++ "] (corrupt) received: " ++ show m
            modifyIORef thingsHappened $ (+) 1
        ?pass
      SttCruptA2Z_F2A (Left (ClockF2A_Leaks l)) -> do
        --printEnvIdeal $ "[testEnvACastBroken leaks]: " ++ show l
        ?pass
      SttCruptA2Z_F2A (Left (ClockF2A_Advance)) -> do
        printEnvReal $ "Forced Clock advance"
        ?pass
      _ -> error $ "Help!" ++ show mb

  () <- readChan pump
  modifyIORef cmdList $ (++) [Right (CmdGetCount, 1000)]
  modifyIORef debugLog $ (++ [Left (Right (CmdGetCount, 1000))])
  writeChan z2a $ ((SttCruptZ2A_A2F $ Left ClockA2F_GetCount), SendTokens 1000)
  c <- readChan clockChan 
  
  let inputs = do [return True, return False]
 
  let checkQueue n = do
        modifyIORef debugLog $ (++ [Left (Right (CmdGetCount, 0))])
        modifyIORef cmdList $ (++ [Right (CmdGetCount, 0)])
        writeChan z2a $ (SttCruptZ2A_A2F (Left ClockA2F_GetCount), SendTokens 0)
        
        c <- readChan clockChan
        liftIO $ putStrLn $ "Z[testEnvACastIdeal]: Events remaining: " ++ show c
        return (c > 0)

  let inputTokens = 64
  -- Give somehonest parties some inputs
  -- choose input values for the honest parties
  -- should create 6 One messages each 
  forMseq_ honest $ \h -> do
    -- choose a boolean
    x <- liftIO $ generate chooseAny
    modifyIORef cmdList $ (++ [Left $ (CmdBenOrP2F h x, inputTokens)])
    modifyIORef debugLog $ (++ [Left (Left (CmdBenOrP2F h x, inputTokens))])
    writeChan z2p $ (h, ((ClockP2F_Through $ BenOrP2F_Input x), SendTokens inputTokens))
    readChan pump
  

  -- go in some limited number of rounds    
  firstInp <- newIORef []
  forMseq_ [1..20] $ \r -> do
    modifyIORef cmdList $ (++) [Right (CmdGetCount, 0)]
    modifyIORef debugLog $ (++ [Left (Right (CmdGetCount, 0))])
    writeChan z2a $ ((SttCruptZ2A_A2F $ Left ClockA2F_GetCount), SendTokens 0)
    c <- readChan clockChan 
    inps <- liftIO $ generate $ benOrGenerator (max 40 c) c (multicastSid sssid crupt parties) parties inputs r 64

    forMseq_ inps $ \i -> do
      modifyIORef debugLog $ (++ [Left i])
      modifyIORef cmdList $ (++ [i])
      envExecAsyncCmd z2p z2a z2f clockChan pump i envExecBenOrCmd

  tr <- readIORef transcript
  cl <- readIORef cmdList
  
  writeChan outp ((sid, parties, (Map.fromList [(crupt,())]), t), cl, tr)

prop_uBenOrTest = monadicIO $ do
    let prot () = protBenOr
    (config', c', t') <- run $ runITMinIO 120 $ execUC 
      propUEnvBenOrSafety
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



{- this environment generator is quite structured towards the BenOr protocol where
   where inputs are given, some messages are delivered then messages are sent by corrupt parties
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
  
  transcript <- newIORef []
  cmdList <- newIORef []  
  thingsHappened <- newIORef 0

  fork $ forever $ do
    (pid, m) <- readChan p2z
    modifyIORef transcript (++ [Right (pid, m)])
    modifyIORef thingsHappened $ (+) 1
    printEnvIdeal $ "[testEnvACast]: pid[" ++ pid ++ "] output " ++ show m
    ?pass

  clockChan <- newChan

  fork $ forever $ do
    mb <- readChan a2z
    modifyIORef transcript (++ [Left mb])
    case mb of
      SttCruptA2Z_F2A (Left (ClockF2A_Pass)) -> do
        printEnvReal $ "Pass"
        modifyIORef thingsHappened $ (+) 1
        ?pass
      SttCruptA2Z_F2A (Left (ClockF2A_Count c)) ->
        writeChan clockChan c
      SttCruptA2Z_P2A (pid, m) -> do
        case m of
          _ -> do
            printEnvReal $ "[" ++pid++ "] (corrupt) received: " ++ show m
            modifyIORef thingsHappened $ (+) 1
        ?pass
      SttCruptA2Z_F2A (Left (ClockF2A_Leaks l)) -> do
        --printEnvIdeal $ "[testEnvACastBroken leaks]: " ++ show l
        ?pass
      SttCruptA2Z_F2A (Left (ClockF2A_Advance)) -> do
        printEnvReal $ "Forced Clock advance"
        ?pass
      _ -> error $ "Help!" ++ show mb

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
  let cruptssid = multicastSid sssid crupt parties "1"
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
  let cruptssid = multicastSid sssid crupt parties "2"
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
    assert ( (Set.size o) == 0 )

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
  
  transcript <- newIORef []
  cmdList <- newIORef []  
  thingsHappened <- newIORef 0

  fork $ forever $ do
    (pid, m) <- readChan p2z
    modifyIORef transcript (++ [Right (pid, m)])
    modifyIORef thingsHappened $ (+) 1
    printEnvIdeal $ "[testEnvACast]: pid[" ++ pid ++ "] output " ++ show m
    ?pass

  clockChan <- newChan

  fork $ forever $ do
    mb <- readChan a2z
    modifyIORef transcript (++ [Left mb])
    case mb of
      SttCruptA2Z_F2A (Left (ClockF2A_Pass)) -> do
        printEnvReal $ "Pass"
        modifyIORef thingsHappened $ (+) 1
        ?pass
      SttCruptA2Z_F2A (Left (ClockF2A_Count c)) ->
        writeChan clockChan c
      SttCruptA2Z_P2A (pid, m) -> do
        case m of
          _ -> do
            printEnvReal $ "[" ++pid++ "] (corrupt) received: " ++ show m
            modifyIORef thingsHappened $ (+) 1
        ?pass
      SttCruptA2Z_F2A (Left (ClockF2A_Leaks l)) -> do
        --printEnvIdeal $ "[testEnvACastBroken leaks]: " ++ show l
        ?pass
      SttCruptA2Z_F2A (Left (ClockF2A_Advance)) -> do
        printEnvReal $ "Forced Clock advance"
        ?pass
      _ -> error $ "Help!" ++ show mb

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
