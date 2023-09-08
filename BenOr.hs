{-# LANGUAGE ScopedTypeVariables, ImplicitParams, FlexibleContexts, Rank2Types,
PartialTypeSignatures
 #-} 

module BenOr where

import ProcessIO
import StaticCorruptions
import Async
import Multisession
import Multicast
import TokenWrapper


import Safe
import Control.Concurrent.MonadIO
import Control.Monad (forever, forM)
import Control.Monad.Loops (whileM_)
import Data.IORef.MonadIO
import Data.Map.Strict (Map, (!))
import Data.List (elemIndex, delete)
import System.Random (randomRIO)
import qualified Data.Map.Strict as Map

import TestTools (envReadOut, envMapQueue, multicastSid)

type RoundNo = Int
data BenOrMsg = One RoundNo Bool | Two RoundNo | TwoD RoundNo Bool deriving (Show, Eq, Read)


-- Give (fBang fMulticast) a nicer interface
manyMulticast :: MonadProtocol m =>
     PID -> [PID]
     -- -> (Chan (SID, (MulticastF2P t, TransferTokens Int)), Chan (SID, ((t, TransferTokens Int), CarryTokens Int)))
     -> (Chan (SID, (MulticastF2P t, CarryTokens Int)), Chan (SID, ((t, TransferTokens Int), CarryTokens Int)))
     -- -> m (Chan (PID, (t, TransferTokens Int)), Chan ((t, TransferTokens Int), CarryTokens Int), Chan ())
     -> m (Chan (PID, (t, CarryTokens Int)), Chan ((t, TransferTokens Int), CarryTokens Int), Chan ())
manyMulticast pid parties (f2p, p2f) = do
  p2f' <- newChan
  f2p' <- newChan
  cOK <- newChan

  -- Handle writing
  fork $ forMseq_ [0..] $ \(ctr :: Integer) -> do
       m <- readChan p2f'
       let ssid = (show ctr, show (pid, parties, ""))
       writeChan p2f (ssid, m)

  -- Handle reading (messages delivered in any order)
  fork $ forever $ do
    (ssid, mf) <- readChan f2p
    let (pidS :: PID, _ :: [PID], _ :: String) = readNote "manyMulti" $ snd ssid
    case mf of
      --(MulticastF2P_OK, DeliverTokensWithMessage _) -> do
      (MulticastF2P_OK, SendTokens _) -> do
                     require (pidS == pid) "ok delivered to wrong pid"
                     writeChan cOK ()
      --(MulticastF2P_Deliver m, DeliverTokensWithMessage t) -> do
      (MulticastF2P_Deliver m, SendTokens t) -> do
                     writeChan f2p' (pidS, (m, SendTokens t))
                     --writeChan f2p' (pidS, (m, DeliverTokensWithMessage t))
  return (f2p', p2f', cOK)

readBangMulticast pid parties f2p = do
  c <- newChan
  fork $ forever $ do
    forMseq_ [0..] 

writeBangSequential p2f = do
  c <- newChan
  fork $ do
    forMseq_ [0..] $ \(ctr :: Integer) -> do
        m <- readChan c
        let ssid' = ("", show ctr)
        writeChan p2f (ssid', m)
  return c

readBangAnyOrder f2p = do
  c <- newChan
  fork $ forever $ do
    (_, m) <- readChan f2p
    writeChan c m
  return c

data BenOrP2F = BenOrP2F_Input Bool deriving Show
data BenOrF2P = BenOrF2P_OK | BenOrF2P_Deliver Bool deriving (Show, Eq)

type Transcript = [Either
                         (SttCruptA2Z
                            --(SID, (MulticastF2P BenOrMsg, TransferTokens Int))
                            (SID, (MulticastF2P BenOrMsg, CarryTokens Int))
                            (Either
                               (ClockF2A (SID, ((BenOrMsg, TransferTokens Int), CarryTokens Int)))
                               (SID, (MulticastF2A BenOrMsg, TransferTokens Int))))
                         (PID, BenOrF2P)]

data BenOrOneVariant = BenOrOneSmall | BenOrOneLarge | BenOrOneCorrect deriving (Show, Eq)
data BenOrTwoDVariant = BenOrTwoDSmall | BenOrTwoDLarge | BenOrTwoDCorrect deriving (Show, Eq)
data BenOrDecideVariant = BenOrDecideSmall | BenOrDecideLarge | BenOrDecideCorrect deriving (Show, Eq)

protBenOr :: MonadAsyncP m => 
    Protocol ((ClockP2F BenOrP2F), CarryTokens Int) BenOrF2P
                                             (SID, (MulticastF2P BenOrMsg, CarryTokens Int)) --TransferTokens Int))
                                             (SID, ((BenOrMsg, TransferTokens Int), CarryTokens Int)) m
protBenOr (z2p, p2z) (f2p, p2f) = do
  let (parties :: [PID], t :: Int, sssid :: String) = readNote "protACast" $ snd ?sid
  let n = length parties
  let oneThreshold = n-t--1
  let sendTwoDThreshold = ((n+t) `div` 2)
  let decideThreshold = n-t--1
  let decideWhich = t
  (protBenOrBroken oneThreshold sendTwoDThreshold decideThreshold decideWhich (z2p, p2z) (f2p, p2f))

protBenOrBreak :: MonadAsyncP m => BenOrOneVariant -> BenOrTwoDVariant -> BenOrDecideVariant -> Int ->
    Protocol ((ClockP2F BenOrP2F), CarryTokens Int) BenOrF2P
                                             (SID, (MulticastF2P BenOrMsg, CarryTokens Int)) --TransferTokens Int))
                                             (SID, ((BenOrMsg, TransferTokens Int), CarryTokens Int)) m
protBenOrBreak oneVariant twoDVariant decideVariant liveCoin (z2p, p2z) (f2p, p2f) = do
  let (parties :: [PID], t :: Int, sssid :: String) = readNote "protACast" $ snd ?sid
  let n = length parties
  r <- randomRIO (0,100)

  let oneThreshold = case oneVariant of
                      BenOrOneSmall -> n-t-1
                      BenOrOneLarge -> n-t+1
                      BenOrOneCorrect -> n-t
  let sendTwoDThreshold = case twoDVariant of
                            BenOrTwoDSmall -> ((n+t) `div` 2)-1
                            BenOrTwoDLarge -> ((n+t) `div` 2)+1
                            BenOrTwoDCorrect -> (if r < liveCoin then ((n+t) `div` 2) + 1 else (n+t) `div` 2)
  let (decideThreshold, decideWhich) = case decideVariant of
                                         BenOrDecideSmall -> (n-t-1, t)
                                         BenOrDecideLarge -> (n-t+1, t+2)
                                         BenOrDecideCorrect -> (n-t, t+1) 
  (protBenOrBroken oneThreshold sendTwoDThreshold decideThreshold decideWhich (z2p, p2z) (f2p, p2f))

protBenOrBroken :: MonadAsyncP m => Int -> Int -> Int -> Int -> 
    Protocol ((ClockP2F BenOrP2F), CarryTokens Int) BenOrF2P
                                             (SID, (MulticastF2P BenOrMsg, CarryTokens Int)) --TransferTokens Int))
                                             (SID, ((BenOrMsg, TransferTokens Int), CarryTokens Int)) m
protBenOrBroken oneThreshold sendTwoDThreshold decideThreshold decideWhich
                  (z2p, p2z) (f2p, p2f) = do
  let (parties :: [PID], t :: Int, sssid :: String) = readNote "protACast" $ snd ?sid

  tokens <- newIORef 0

  -- Require means print the error then pass
  let require cond msg = 
        if not cond then do
          liftIO $ putStrLn $ "ERROR ERROR ERROR: " ++ msg
          ?pass
          readChan =<< newChan -- block without returning
        else return ()
  
  {- TESTING MODS -}
  f2p' <- newChan
  z2p' <- newChan
  failed <- newIORef False

  let require cond msg = do
          if not cond then do
            liftIO $ putStrLn $ msg
            ?pass
            writeIORef failed True
            return False
          else return True

  fork $ forever $ do
    m <- readChan f2p
    f <- readIORef failed
    if f then ?pass
    else writeChan f2p' m

  fork $ forever $ do
    m <- readChan z2p
    f <- readIORef failed
    if f then ?pass
    else writeChan z2p' m

  -- Prepare channels
  (recvC, multicastC, cOK) <- manyMulticast ?pid parties (f2p', p2f) --(f2p, p2f)
  
  let multicast (x, DeliverTokensWithMessage st) = do
        tk <- readIORef tokens
        let neededTokens = (length parties) * (st+1)
        writeIORef tokens (max 0 (tk-neededTokens))
        writeChan multicastC ((x, DeliverTokensWithMessage st), SendTokens (min tk neededTokens))
        readChan cOK
  let recv = readChan recvC -- :: m (ACastMsg t)
   
  round <- newIORef (1 :: Int)

  (mf, SendTokens a) <- readChan z2p' --z2p
  require (a>0) "Sending 0 tokens with input"
  tk <- readIORef tokens
  writeIORef tokens (tk+a)

  let n = length parties

  numOne1 <- newIORef 0
  numOne0 <- newIORef 0
  numTwo1 <- newIORef 0
  numTwo0 <- newIORef 0
  numTwos <- newIORef 0

  alreadyOned <- newIORef False
  ones <- newIORef (Map.empty :: Map PID ())
  twos <- newIORef (Map.empty :: Map PID ())
  decision <- newIORef False
  decided <- newIORef False

  case mf of
    ClockP2F_Pass -> ?pass
    ClockP2F_Through (BenOrP2F_Input m) -> do
      -- TODO: maybe here we should add our own to the count instead
      -- of only agreeing when we receive our own back but it doesn't
      -- really matter we're not aiming for the most efficient implementation
      -- of BenOr for this paper.
      liftIO $ putStrLn $ "[BenOr " ++ show ?pid ++ "] Submitting input"
      r <- readIORef round
      liftIO $ putStrLn $ "[ " ++ show ?pid ++ "] Round 1"
      multicast (One r m, DeliverTokensWithMessage 0)
      writeIORef decision m
      writeChan p2z BenOrF2P_OK

  fork $ forever $ do
    m <- readChan z2p
    ?pass

  let newRoundFrom r = do
            liftIO $ putStrLn $ "\t[ " ++ show ?pid ++ " ] new round " ++ show r ++ " -> " ++ show (r+1)
            d <- readIORef decision
            modifyIORef round $ (+) 1
            writeIORef ones Map.empty
            writeIORef twos Map.empty
            writeIORef alreadyOned False
            writeIORef numOne1 0
            writeIORef numOne0 0
            writeIORef numTwo0 0 
            writeIORef numTwo1 0
            writeIORef numTwos 0
            multicast (One (r+1) d, DeliverTokensWithMessage 0)
            return ()

  let isTimeToDecide = do
            r <- readIORef round
            nts <- readIORef numTwos
            -- crit threshold of twos just to check others
            --if (nts == (n-t)) then do
            --if (nts == (n-t-1)) then do
            if (nts == decideThreshold) then do
              liftIO $ putStrLn $ "\t[ " ++ show ?pid ++ " ] N-t achieved"
              nt0 <- readIORef numTwo0
              nt1 <- readIORef numTwo1 
              -- if at least one honest then set x_p = True / False for next round
              --if (nt0 >= t+1) then writeIORef decision False
              liftIO $ putStrLn $ "nt0: " ++ show nt0 ++ " nt1: " ++ show nt1 
              if (nt0 >= decideWhich) then writeIORef decision False
              --else if (nt1 >= t+1) then writeIORef decision True
              else if (nt1 >= decideWhich) then writeIORef decision True
              else return ()
              newRoundFrom r
              -- if threshold then decide that value
              --if (nt0 >= ((n+t) `div` 2)) then do
              --if (nt0 >= ((n+t) `div` 2)-1) then do
              --if (nt0 >= (sendTwoDThreshold-1)) then do
              if (nt0 >= (sendTwoDThreshold)) then do
                writeIORef decision False
                return True
              --else if (nt1 >= ((n+t) `div` 2)) then do
              --else if (nt1 >= ((n+t) `div` 2)-1) then do
              --else if (nt1 >= (sendTwoDThreshold-1)) then do
              else if (nt1 >= (sendTwoDThreshold)) then do
                writeIORef decision True
                return True
              else do
                b <- ?getBit
                writeIORef decision b
                liftIO $ putStrLn $ "\t[ " ++ show ?pid ++ " ] random choice " ++ show b
                return False
            else return False

  -- Here we substract 1 from oneThreshold and decideThreshold so that we count `this` party's message
  -- itself without relying on the adversary to deliver it
  fork $ forever $ do
    r <- readIORef round
    --(pid', (m, DeliverTokensWithMessage a)) <- recv 
    (pid', (m, SendTokens a)) <- recv 
    liftIO $ putStrLn $ "[BenOr " ++ show ?pid ++ "] " ++ show (pid', m) ++ " from fMulticast with " ++ show a ++ " tokens."
    if (a < 0) then error "negative tokens"
    else do
      modifyIORef tokens $ (+) a
    dec <- readIORef decided 
    if dec then ?pass
    else do
      case m of
        One r' x -> do
          --require (r' == r) $ "message for wrong round. expected " ++ show r ++ " got " ++ show r'
          --if (r' == r) then do
          os <- readIORef ones
          -- TODO we do not consider this a failure
          if (not $ Map.member pid' os) then do
            printBlue $ show pid' ++ show "-->" ++ show ?pid ++ show ": " ++ show m
            modifyIORef ones $ Map.insert pid' ()
            if (x == False) then do
              modifyIORef numOne0 $ (+) 1
            else if (x == True) then
              modifyIORef numOne1 $ (+) 1
            else error "not a 0 or 1"

            total <- (readIORef numOne0 >>= \n0 -> readIORef numOne1 >>= (\n1 -> return (n0 + n1)))
            --if total == (n - t) then do
            --if total == (n - t - 1) then do
            if (total == oneThreshold) then do
              liftIO $ putStrLn $ "[BenOr " ++ show ?pid ++ "] reached 1 N-t"
              num0 <- readIORef numOne0
              num1 <- readIORef numOne1
              writeIORef alreadyOned True
              -- TODO: maybe we dont' send any import and rely on Z for giving enough to everyone
{- this is  urnd smaller and shoult be > not >= -}
              --if (num0 >= ((n+t) `div` 2)) then do
              --if (num0 >= sendTwoDThreshold) then do
              if (num0 > sendTwoDThreshold) then do
                liftIO $ putStrLn $ "reached TD for 0"
                multicast $ ((TwoD r False ), DeliverTokensWithMessage 0)
                ?pass
              --else if (num1 >= ((n+t) `div` 2)) then do
              --else if (num1 >= sendTwoDThreshold) then do
              else if (num1 > sendTwoDThreshold) then do
                liftIO $ putStrLn $ "reached TD for 1"
                multicast $ ((TwoD r True ), DeliverTokensWithMessage 0)
                ?pass
              else do
                liftIO $ putStrLn $ "[BenOr " ++ show ?pid++ "] 2,*"
                multicast $ ((Two r), DeliverTokensWithMessage 0)
                ?pass
            else ?pass
          else ?pass
          --else ?pass
        Two r' -> do
          --require (r' == r) $ "message for wrong round. expected " ++ show r ++ " got " ++ show r'
          --if (r' == r) then do 
          --readIORef alreadyOned >>= \a -> require a "Two message out of order"
          -- TODO: the code doesn't consider this a failure
          ao <- readIORef alreadyOned
          if ao then do
            ts <- readIORef twos
            -- TODO: don't consider this a failure, just ignore
            if (not $ Map.member pid' ts) then do
              printBlue $ show pid' ++ show "-->" ++ show ?pid ++ show ": " ++ show m
              modifyIORef twos $ Map.insert pid' ()
              modifyIORef numTwos $ ((+) 1)
      
              t <- isTimeToDecide 
              if t then do
                d <- readIORef decision
                writeIORef decided True
                writeChan p2z (BenOrF2P_Deliver d)
              else ?pass
            else ?pass
          else ?pass
          --else ?pass
        TwoD r' x -> do
          --require (r' == r) $ "message for wrong round. expected " ++ show r ++ " got " ++ show r'
          --if (r' == r) then do
          --readIORef alreadyOned >>= \a -> require a "Two message out of order"
          ao <- readIORef alreadyOned
          if ao then do 
            ts <- readIORef twos
            -- TODO not a failure
            if (not $ Map.member pid' ts) then do
              printBlue $ show pid' ++ show "-->" ++ show ?pid ++ show ": " ++ show m
              modifyIORef twos $ Map.insert pid' ()
              modifyIORef numTwos $ ((+) 1)

              if x then modifyIORef numTwo1 $ (+) 1
              else modifyIORef numTwo0 $ (+) 1      
 
              t <- isTimeToDecide 
              if t then do
                d <- readIORef decision
                writeIORef decided True
                writeChan p2z (BenOrF2P_Deliver d)
              else ?pass
            else ?pass
          else ?pass
          --else ?pass
  return ()

testEnvBenOr
  :: (MonadEnvironment m) => Int -> 
  Environment BenOrF2P ((ClockP2F BenOrP2F), CarryTokens Int)
    --(SttCruptA2Z (SID, (MulticastF2P BenOrMsg, TransferTokens Int))
    (SttCruptA2Z (SID, (MulticastF2P BenOrMsg, CarryTokens Int))
                 (Either (ClockF2A (SID, ((BenOrMsg, TransferTokens Int), CarryTokens Int)))
                         (SID, (MulticastF2A BenOrMsg, TransferTokens Int))))
    ((SttCruptZ2A (ClockP2F (SID, ((BenOrMsg, TransferTokens Int), CarryTokens Int)))
                  (Either ClockA2F (SID, (MulticastA2F BenOrMsg, TransferTokens Int)))), CarryTokens Int) Void
    ClockZ2F Transcript m
testEnvBenOr numTokens z2exec (p2z, z2p) (a2z, z2a) (f2z, z2f) pump outp = do
  let sid = ("sidTestACast", show (["Alice", "Bob", "Carol", "Dave", "Eve", "Frank"], 1::Integer, ""))
  --writeChan z2exec $ SttCrupt_SidCrupt sid $ Map.empty
  writeChan z2exec $ SttCrupt_SidCrupt sid $ Map.fromList [("Alice",())]

  (lastOut, transcript, clockChan) <- envReadOut p2z a2z

  () <- readChan pump
  --writeChan z2p $ ("Alice", ((ClockP2F_Through $ BenOrP2F_Input True), SendTokens numTokens))
 
  --() <- readChan pump
  writeChan z2p $ ("Bob", ((ClockP2F_Through $ BenOrP2F_Input True), SendTokens numTokens))
 
  () <- readChan pump
  writeChan z2p $ ("Carol", ((ClockP2F_Through $ BenOrP2F_Input True), SendTokens numTokens))

  () <- readChan pump
  writeChan z2p $ ("Dave", ((ClockP2F_Through $ BenOrP2F_Input True), SendTokens numTokens))
  
  () <- readChan pump
  writeChan z2p $ ("Eve", ((ClockP2F_Through $ BenOrP2F_Input True), SendTokens numTokens))

  () <- readChan pump
  writeChan z2p $ ("Frank", ((ClockP2F_Through $ BenOrP2F_Input True), SendTokens numTokens))

  () <- readChan pump
  writeChan z2a $ ((SttCruptZ2A_A2F (Left ClockA2F_GetCount)), SendTokens 0)
  c <- readChan clockChan 

  -- everyone's multicasts of the ONE message
  forMseq_ [1..36] $ \x -> do
    writeChan z2a $ ((SttCruptZ2A_A2F (Left (ClockA2F_Deliver 0))), SendTokens 0)
    readChan pump

  -- everyone's TWO messages
  forMseq_ [1..36] $ \x -> do
    writeChan z2a $ ((SttCruptZ2A_A2F (Left (ClockA2F_Deliver 0))), SendTokens 0)
    readChan pump

  -- everyone's ONE message round 2
  forMseq_ [1..36] $ \x -> do
    writeChan z2a $ ((SttCruptZ2A_A2F (Left (ClockA2F_Deliver 0))), SendTokens 0)
    readChan pump
  
  -- everyone's TWO messages
  forMseq_ [1..36] $ \x -> do
    writeChan z2a $ ((SttCruptZ2A_A2F (Left (ClockA2F_Deliver 0))), SendTokens 0)
    readChan pump

  let checkQueue = do
        writeChan z2a $ ((SttCruptZ2A_A2F (Left ClockA2F_GetCount)), SendTokens 1)
        c <- readChan clockChan
        return (c > 0)

  () <- readChan pump
  whileM_ checkQueue $ do
    writeChan z2a $ ((SttCruptZ2A_A2F (Left ClockA2F_GetCount)), SendTokens 0)
    c <- readChan clockChan
    printEnvReal $ "[testEnvBenOr]: Events remaining: " ++ show c
    
    --idx <- getNbits 10
    --let i = mod idx c 
    writeChan z2a $ ((SttCruptZ2A_A2F (Left (ClockA2F_Deliver 0))), SendTokens 10)
    readChan pump
  
  --() <- readChan pump
  writeChan outp =<< readIORef transcript


testBenOr :: IO Transcript
testBenOr = runITMinIO 120 $ execUC
  (testEnvBenOr 100)
  --(runAsyncP $ protBenOr)
  (runAsyncP $ protBenOrBreak BenOrOneCorrect BenOrTwoDCorrect BenOrDecideCorrect 0)
  (runAsyncF $ bangFAsync fMulticastToken)
  dummyAdversaryToken

testEnvBreak
  :: (MonadEnvironment m) => Int -> 
  Environment BenOrF2P ((ClockP2F BenOrP2F), CarryTokens Int)
    --(SttCruptA2Z (SID, (MulticastF2P BenOrMsg, TransferTokens Int))
    (SttCruptA2Z (SID, (MulticastF2P BenOrMsg, CarryTokens Int))
                 (Either (ClockF2A (SID, ((BenOrMsg, TransferTokens Int), CarryTokens Int)))
                         (SID, (MulticastF2A BenOrMsg, TransferTokens Int))))
    ((SttCruptZ2A (ClockP2F (SID, ((BenOrMsg, TransferTokens Int), CarryTokens Int)))
                  (Either ClockA2F (SID, (MulticastA2F BenOrMsg, TransferTokens Int)))), CarryTokens Int) Void
    ClockZ2F Transcript m
testEnvBreak numTokens z2exec (p2z, z2p) (a2z, z2a) (f2z, z2f) pump outp = do
  let sid = ("sidTestACast", show (["Alice", "Bob", "Carol", "Dave", "Eve", "Frank"], 1::Integer, ""))

  let sssid = "sidTestACast"
  let parties = ["Alice", "Bob", "Carol", "Dave", "Eve", "Frank"]
  --writeChan z2exec $ SttCrupt_SidCrupt sid $ Map.empty
  writeChan z2exec $ SttCrupt_SidCrupt sid $ Map.fromList [("Alice",())]

  (lastOut, transcript, clockChan) <- envReadOut p2z a2z
  () <- readChan pump
  
  (deliverer, deliverByPairs) <- envMapQueue z2a a2z clockChan lastOut pump

  writeChan z2p $ ("Bob", ((ClockP2F_Through $ BenOrP2F_Input False), SendTokens numTokens))
  () <- readChan pump

  writeChan z2p $ ("Carol", ((ClockP2F_Through $ BenOrP2F_Input False), SendTokens numTokens))
  () <- readChan pump

  writeChan z2p $ ("Dave", ((ClockP2F_Through $ BenOrP2F_Input False), SendTokens numTokens))
  () <- readChan pump

  writeChan z2p $ ("Eve", ((ClockP2F_Through $ BenOrP2F_Input True), SendTokens numTokens))
  () <- readChan pump

  writeChan z2p $ ("Frank", ((ClockP2F_Through $ BenOrP2F_Input True), SendTokens numTokens))
  () <- readChan pump

  forMseq_ [1..30] $ \x -> do
    writeChan z2a $ ((SttCruptZ2A_A2F (Left (ClockA2F_Deliver 0))), SendTokens 0)
    readChan pump
   
  forMseq_ [1..30] $ \x -> do
    writeChan z2a $ ((SttCruptZ2A_A2F (Left (ClockA2F_Deliver 0))), SendTokens 0)
    readChan pump
 

  ---- BB BC BD
  --forMseq_ [1,1,1] $ \x -> do  
  --  writeChan z2a $ ((SttCruptZ2A_A2F (Left (ClockA2F_Deliver 1))), SendTokens 0)
  --  readChan pump

  ---- CB CC CD
  --forMseq_ [4,4,4] $ \x -> do
  --  writeChan z2a $ ((SttCruptZ2A_A2F (Left (ClockA2F_Deliver 4))), SendTokens 0)
  --  readChan pump

  ---- DB DC DD
  --forMseq_ [7,7,7] $ \x -> do
  --  writeChan z2a $ ((SttCruptZ2A_A2F (Left (ClockA2F_Deliver 7))), SendTokens 0)
  --  readChan pump

  ---- EB EC ED
  --forMseq_ [10,10,10] $ \x -> do
  --  writeChan z2a $ ((SttCruptZ2A_A2F (Left (ClockA2F_Deliver 10))), SendTokens 0)
  --  readChan pump

  --let ssid1 = multicastSid sssid "Alice" parties "1"
  --writeChan z2a $ ((SttCruptZ2A_A2F $ Right (ssid1, (MulticastA2F_Deliver "Bob" (One 1 False), DeliverTokensWithMessage 0))), SendTokens 0)
  --() <- readChan pump
  --
  --writeChan z2a $ ((SttCruptZ2A_A2F $ Right (ssid1, (MulticastA2F_Deliver "Carol" (One 1 False), DeliverTokensWithMessage 0))), SendTokens 0)
  --() <- readChan pump
  --
  --writeChan z2a $ ((SttCruptZ2A_A2F $ Right (ssid1, (MulticastA2F_Deliver "Dave" (One 1 False), DeliverTokensWithMessage 0))), SendTokens 0)
  --() <- readChan pump

  --forMseq_ [19,19,19] $ \x -> do
  --  writeChan z2a $ ((SttCruptZ2A_A2F (Left (ClockA2F_Deliver 19))), SendTokens 0)
  --  readChan pump

  --writeChan z2a $ ((SttCruptZ2A_A2F (Left (ClockA2F_Deliver 22))), SendTokens 0)
  --readChan pump
  --
  --writeChan z2a $ ((SttCruptZ2A_A2F (Left (ClockA2F_Deliver 23))), SendTokens 0)
  --readChan pump

  --forMseq_ [26,26] $ \x -> do
  --  writeChan z2a $ ((SttCruptZ2A_A2F (Left (ClockA2F_Deliver 26))), SendTokens 0)
  --  readChan pump

  --forMseq_ [4,4] $ \x -> do
  --  writeChan z2a $ ((SttCruptZ2A_A2F (Left (ClockA2F_Deliver 4))), SendTokens 0)
  --  readChan pump

  --forMseq_ [5,5] $ \x -> do
  --  writeChan z2a $ ((SttCruptZ2A_A2F (Left (ClockA2F_Deliver 5))), SendTokens 0)
  --  readChan pump

  --forMseq_ [6,6] $ \x -> do
  --  writeChan z2a $ ((SttCruptZ2A_A2F (Left (ClockA2F_Deliver 6))), SendTokens 0)
  --  readChan pump

  --forMseq_ [10,10] $ \x -> do
  --  writeChan z2a $ ((SttCruptZ2A_A2F (Left (ClockA2F_Deliver 10))), SendTokens 0)
  --  readChan pump

  --let ssid1 = multicastSid sssid "Alice" parties "1"
  --writeChan z2a $ ((SttCruptZ2A_A2F $ Right (ssid1, (MulticastA2F_Deliver "Eve" (One 1 True), DeliverTokensWithMessage 0))), SendTokens 0)
  --() <- readChan pump
  --
  --writeChan z2a $ ((SttCruptZ2A_A2F $ Right (ssid1, (MulticastA2F_Deliver "Frank" (One 1 True), DeliverTokensWithMessage 0))), SendTokens 0)
  --() <- readChan pump
 
  
 
  writeChan outp =<< readIORef transcript
 
testBreak :: IO Transcript
testBreak = runITMinIO 120 $ execUC
  (testEnvBreak 100)
  --(runAsyncP $ protBenOr)
  (runAsyncP $ protBenOrBreak BenOrOneCorrect BenOrTwoDCorrect BenOrDecideCorrect 0)
  (runAsyncF $ bangFAsync fMulticastToken)
  dummyAdversaryToken



testNumRounds :: IO ()
testNumRounds = do
  let importSchedule = [6, 12, 18, 24, 30, 36, 42, 48, 54, 60, 66, 72, 78, 84, 90]
  let numTests = 50
  results <- newIORef (Map.empty :: Map Int (Int, Int))
  forMseq_ importSchedule $ \numImport -> do
    numSuccess <- newIORef 0
    numFails <- newIORef 0
    forMseq_ [1..numTests] $ \_ -> do
      t <- runITMinIO 120 $ execUC
        (testEnvBenOr numImport)
        (runAsyncP $ protBenOr)
        (runAsyncF $ bangFAsync fMulticastToken)
        dummyAdversaryToken
      numDecides <- newIORef 0
      forMseq_ t $ \x -> do
        case x of 
          Right (pid, BenOrF2P_Deliver m) -> modifyIORef numDecides $ (+) 1
          _ -> return ()
      n <- readIORef numDecides
      if (n == 6) then modifyIORef numSuccess $ (+) 1
      else modifyIORef numFails $ (+) 1
    ns <- readIORef numSuccess
    nf <- readIORef numFails
    modifyIORef results $ Map.insert numImport (ns, nf) 
  
  forMseq_ importSchedule $ \numImport -> do
    (ns, nf) <- readIORef results >>= return . (! numImport)
    liftIO $ putStrLn $ ("\n[ Tests: 50 ; import = " ++ show numImport ++ " ]\n\tterminated = " ++ show ns ++ " ; failed = " ++ show nf) 
  return ()
 
testEnvBenOrCrupt
  :: (MonadEnvironment m) => 
  Environment BenOrF2P ((ClockP2F BenOrP2F), CarryTokens Int)
    -- (SttCruptA2Z (SID, (MulticastF2P BenOrMsg, TransferTokens Int))
    (SttCruptA2Z (SID, (MulticastF2P BenOrMsg, CarryTokens Int))
                 (Either (ClockF2A (SID, ((BenOrMsg, TransferTokens Int), CarryTokens Int)))
                         (SID, (MulticastF2A BenOrMsg, TransferTokens Int))))
    ((SttCruptZ2A (ClockP2F (SID, ((BenOrMsg, TransferTokens Int), CarryTokens Int)))
                  (Either ClockA2F (SID, (MulticastA2F BenOrMsg, TransferTokens Int)))), CarryTokens Int) Void
    ClockZ2F Transcript m
testEnvBenOrCrupt z2exec (p2z, z2p) (a2z, z2a) (f2z, z2f) pump outp = do
  let sid = ("sidTestACast", show (["Alice", "Bob", "Carol", "Dave", "Eve", "Frank"], 1::Integer, ""))

  liftIO $ putStrLn $ "Stuck even before sid crupt"
  writeChan z2exec $ SttCrupt_SidCrupt sid $ Map.fromList [("Frank",())]

  (lastOut, transcript, clockChan) <- envReadOut p2z a2z

  liftIO $ putStrLn $ "Stuck after envReadOut"
  () <- readChan pump
  writeChan z2p $ ("Alice", ((ClockP2F_Through $ BenOrP2F_Input True), SendTokens 32))
 
  () <- readChan pump
  writeChan z2p $ ("Bob", ((ClockP2F_Through $ BenOrP2F_Input True), SendTokens 32))
 
  () <- readChan pump
  writeChan z2p $ ("Carol", ((ClockP2F_Through $ BenOrP2F_Input True), SendTokens 32))

  () <- readChan pump
  writeChan z2p $ ("Dave", ((ClockP2F_Through $ BenOrP2F_Input False), SendTokens 32))
  
  () <- readChan pump
  writeChan z2p $ ("Eve", ((ClockP2F_Through $ BenOrP2F_Input False), SendTokens 32))

  --() <- readChan pump
  --writeChan z2p $ ("Frank", ((ClockP2F_Through $ BenOrP2F_Input False), SendTokens 32))

  --() <- readChan pump
  --writeChan z2a $ ((SttCruptZ2A_A2F (Left ClockA2F_GetCount)), SendTokens 0)
  --c <- readChan clockChan 

  ---- everyone's multicasts of the ONE message
  --forMseq_ [1..36] $ \x -> do
  --  writeChan z2a $ ((SttCruptZ2A_A2F (Left (ClockA2F_Deliver 0))), SendTokens 0)
  --  readChan pump

  ---- everyone's TWO messages
  --forMseq_ [1..36] $ \x -> do
  --  writeChan z2a $ ((SttCruptZ2A_A2F (Left (ClockA2F_Deliver 0))), SendTokens 0)
  --  readChan pump

  ---- everyone's ONE message round 2
  --forMseq_ [1..36] $ \x -> do
  --  writeChan z2a $ ((SttCruptZ2A_A2F (Left (ClockA2F_Deliver 0))), SendTokens 0)
  --  readChan pump
  --
  ---- everyone's TWO messages
  --forMseq_ [1..36] $ \x -> do
  --  writeChan z2a $ ((SttCruptZ2A_A2F (Left (ClockA2F_Deliver 0))), SendTokens 0)
  --  readChan pump

  let checkQueue = do
        writeChan z2a $ ((SttCruptZ2A_A2F (Left ClockA2F_GetCount)), SendTokens 1)
        c <- readChan clockChan
        return (c > 0)

  liftIO $ putStrLn $ "Stuck after honestinputs"

  () <- readChan pump
  whileM_ checkQueue $ do
    writeChan z2a $ ((SttCruptZ2A_A2F (Left ClockA2F_GetCount)), SendTokens 0)
    liftIO $ putStrLn $ "Stuck after first clock count"
    c <- readChan clockChan
    printEnvReal $ "[testEnvBenOr]: Events remaining: " ++ show c
    
    --idx <- getNbits 10
    --let i = mod idx c 
    writeChan z2a $ ((SttCruptZ2A_A2F (Left (ClockA2F_Deliver 0))), SendTokens 10)
    readChan pump
  
  --() <- readChan pump
  writeChan outp =<< readIORef transcript


testBenOrCrupt :: IO Transcript
testBenOrCrupt = runITMinIO 120 $ execUC
  (testEnvBenOr 36)
  --(runAsyncP $ protBenOr)
  (runAsyncP $ protBenOrBreak BenOrOneCorrect BenOrTwoDCorrect BenOrDecideCorrect 0)
  (runAsyncF $ bangFAsync fMulticastToken)
  dummyAdversaryToken
