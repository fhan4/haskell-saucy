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
import Data.Map.Strict (Map)
import Data.List (elemIndex, delete)
import qualified Data.Map.Strict as Map

data BenOrMsg = One Int Bool | Two Int | TwoD Int Bool deriving (Show, Eq, Read)

-- Give (fBang fMulticast) a nicer interface
manyMulticast :: MonadProtocol m =>
     PID -> [PID]
     -> (Chan (SID, (MulticastF2P t, TransferTokens Int)), Chan (SID, ((t, TransferTokens Int), CarryTokens Int)))
     -> m (Chan (PID, (t, TransferTokens Int)), Chan ((t, TransferTokens Int), CarryTokens Int), Chan ())
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
      (MulticastF2P_OK, DeliverTokensWithMessage _) -> do
                     require (pidS == pid) "ok delivered to wrong pid"
                     writeChan cOK ()
      (MulticastF2P_Deliver m, DeliverTokensWithMessage t) -> do
                     writeChan f2p' (pidS, (m, DeliverTokensWithMessage t))
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
                            (SID, (MulticastF2P BenOrMsg, TransferTokens Int))
                            (Either
                               (ClockF2A (SID, ((BenOrMsg, TransferTokens Int), CarryTokens Int)))
                               (SID, (MulticastF2A BenOrMsg, TransferTokens Int))))
                         (PID, BenOrF2P)]


protBenOr :: MonadAsyncP m => Protocol ((ClockP2F BenOrP2F), CarryTokens Int) BenOrF2P
                                             (SID, (MulticastF2P BenOrMsg, TransferTokens Int))
                                             (SID, ((BenOrMsg, TransferTokens Int), CarryTokens Int)) m
protBenOr (z2p, p2z) (f2p, p2f) = do
  let (parties :: [PID], t :: Int, sssid :: String) = readNote "protACast" $ snd ?sid

  tokens <- newIORef 0

  -- Require means print the error then pass
  let require cond msg = 
        if not cond then do
          liftIO $ putStrLn $ "ERROR ERROR ERROR: " ++ msg
          ?pass
          readChan =<< newChan -- block without returning
        else return ()
  
  -- Prepare channels
  (recvC, multicastC, cOK) <- manyMulticast ?pid parties (f2p, p2f)
  
  let multicast (x, DeliverTokensWithMessage st) = do
        tk <- readIORef tokens
        let neededTokens = (length parties) * (st+1)
        writeIORef tokens (max 0 (tk-neededTokens))
        liftIO $ putStrLn $ ">>>>>. Multicasting [" ++ show ?pid ++ "] " ++ show x ++ " with SendTokens " ++ show (min tk neededTokens) ++ " and DeliverTokensWithMessage " ++ show st
        writeChan multicastC ((x, DeliverTokensWithMessage st), SendTokens (min tk neededTokens))
        readChan cOK
  let recv = readChan recvC -- :: m (ACastMsg t)
   
  round <- newIORef (1 :: Int)

  (mf, SendTokens a) <- readChan z2p
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
      liftIO $ putStrLn $ "[BenOr " ++ show ?pid ++ "] Submitting input"
      r <- readIORef round
      multicast (One r m, DeliverTokensWithMessage 0)
      writeIORef decision m
      writeChan p2z BenOrF2P_OK

  let newRoundFrom r = do
            liftIO $ putStrLn $ "\t[ " ++ show ?pid ++ " ] new round " ++ show r ++ " -> " ++ show (r+1)
            b <- ?getBit
            writeIORef decision b
            liftIO $ putStrLn $ "\t[ " ++ show ?pid ++ " ] random choice " ++ show b
            modifyIORef round $ (+) 1
            writeIORef ones Map.empty
            writeIORef twos Map.empty
            writeIORef alreadyOned False
            writeIORef numOne1 0
            writeIORef numOne0 0
            writeIORef numTwo0 0 
            writeIORef numTwo1 0
            writeIORef numTwos 0
            multicast (One (r+1) b, DeliverTokensWithMessage 0)
            return ()

  fork $ forever $ do
    r <- readIORef round
    (pid', (m, DeliverTokensWithMessage a)) <- recv 
    liftIO $ putStrLn $ "[ " ++ show ?pid ++ "] Round " ++ show r
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
          if (r' == r) then do
            os <- readIORef ones
            require (not $ Map.member pid' os) $ "Already sent a round 1 message"
            modifyIORef ones $ Map.insert pid' ()
            if (x == False) then do
              modifyIORef numOne0 $ (+) 1
            else if (x == True) then
              modifyIORef numOne1 $ (+) 1
            else error "not a 0 or 1"

            total <- (readIORef numOne0 >>= \n0 -> readIORef numOne1 >>= (\n1 -> return (n0 + n1)))
            if total == (n - t) then do
              num0 <- readIORef numOne0
              num1 <- readIORef numOne1
              writeIORef alreadyOned True
              -- TODO: maybe we dont' send any import and rely on Z for giving enough to everyone
              if (num0 > ((n+t) `div` 2)) then do
                multicast $ ((TwoD r False ), DeliverTokensWithMessage 0)
                ?pass
              else if (num1 >   ((n+t) `div` 2)) then do
                multicast $ ((TwoD r True ), DeliverTokensWithMessage 0)
                ?pass
              else do
                multicast $ ((Two r), DeliverTokensWithMessage 0)
                ?pass
            else ?pass
          else ?pass
        Two r' -> do
          --require (r' == r) $ "message for wrong round. expected " ++ show r ++ " got " ++ show r'
          if (r' == r) then do 
            readIORef alreadyOned >>= \a -> require a "Two message out of order"
            ts <- readIORef twos
            require (not $ Map.member pid' ts) $ "Already sent a round 2 message"
            modifyIORef twos $ Map.insert pid' ()
            modifyIORef numTwos $ ((+) 1)
            nts <- readIORef numTwos
        
            if (nts == (n-t)) then do
              liftIO $ putStrLn $ "\t[ " ++ show ?pid ++ " ] N-t achieved"
              nt0 <- readIORef numTwo0
              nt1 <- readIORef numTwo1 
              if (nt0 >= t+1) then 
                writeIORef decision False
              else if (nt1 >= t+1) then
                writeIORef decision True
              else return ()
              if (nt0 >= ((n+t) `div` 2)) then do
                writeIORef decided True
                writeIORef decision False
                writeChan p2z (BenOrF2P_Deliver False)
              else if (nt1 >= ((n+t) `div` 2)) then do
                writeIORef decided True
                writeIORef decision True
                writeChan p2z (BenOrF2P_Deliver True)
              else do
                newRoundFrom r
                ?pass
            else ?pass
          else ?pass
        TwoD r' x -> do
          --require (r' == r) $ "message for wrong round. expected " ++ show r ++ " got " ++ show r'
          if (r' == r) then do
            readIORef alreadyOned >>= \a -> require a "Two message out of order"
            ts <- readIORef twos
            require (not $ Map.member pid' ts) $ "Already sent a round 2 message"
            modifyIORef twos $ Map.insert pid' ()
            modifyIORef numTwos $ ((+) 1)
            nts <- readIORef numTwos

            if x then modifyIORef numTwo1 $ (+) 1
            else modifyIORef numTwo0 $ (+) 1      
 
            liftIO $ putStrLn $ "\t\t[" ++ show ?pid ++ "] trying to decide"
            if (nts == (n-t)) then do
              liftIO $ putStrLn $ "\t[ " ++ show ?pid ++ " ] N-t achieved"
              nt0 <- readIORef numTwo0
              nt1 <- readIORef numTwo1 
              liftIO $ putStrLn $ "[" ++ show ?pid ++ "] nt0: " ++ show nt0 ++ " nt1: " ++ show nt1
              if (nt0 >= t+1) then 
                writeIORef decision False
              else if (nt1 >= t+1) then
                writeIORef decision True
              else return ()
              if (nt0 >= ((n+t) `div` 2)) then do
                writeIORef decided True
                writeChan p2z (BenOrF2P_Deliver False)
              else if (nt1 >= ((n+t) `div` 2)) then do
                writeIORef decided True
                writeChan p2z (BenOrF2P_Deliver True)
              else do
                newRoundFrom r
                ?pass
            else ?pass
          else ?pass
          --return ()
    --liftIO $ putStrLn $ "[ " ++ show ?pid ++ " ] Looping back around"
  return ()

--type Transcript = [Either
--                         (SttCruptA2Z
--                          (SID, (MulticastF2P BenOrMsg, TransferTokens Int))
--                          (Either
--                            (ClockF2A (SID, ((BenOrMsg, TransferTokens Int), CarryTokens Int)))
--                            (SID, (MulticastF2A BenOrMsg, TransferTokens Int))))
--                         (PID, BenOrF2P)]

testEnvBenOr
  :: (MonadEnvironment m) => 
  Environment BenOrF2P ((ClockP2F BenOrP2F), CarryTokens Int)
    (SttCruptA2Z (SID, (MulticastF2P BenOrMsg, TransferTokens Int))
                 (Either (ClockF2A (SID, ((BenOrMsg, TransferTokens Int), CarryTokens Int)))
                         (SID, (MulticastF2A BenOrMsg, TransferTokens Int))))
    ((SttCruptZ2A (ClockP2F (SID, ((BenOrMsg, TransferTokens Int), CarryTokens Int)))
                  (Either ClockA2F (SID, (MulticastA2F BenOrMsg, TransferTokens Int)))), CarryTokens Int) Void
    ClockZ2F Transcript m
testEnvBenOr z2exec (p2z, z2p) (a2z, z2a) (f2z, z2f) pump outp = do
  transcript <- newIORef []
  let sid = ("sidTestACast", show (["Alice", "Bob", "Carol", "Dave", "Eve", "Frank"], 1::Integer, ""))

  writeChan z2exec $ SttCrupt_SidCrupt sid $ Map.empty

  fork $ forever $ do
    (pid, m) <- readChan p2z
    modifyIORef transcript (++ [Right (pid, m)])
    printEnvIdeal $ "[testEnvACast]: pid[" ++ pid ++ "] output " ++ show m
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
      _ -> error $ "Help!" ++ show mb

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

  () <- readChan pump
  writeChan z2p $ ("Frank", ((ClockP2F_Through $ BenOrP2F_Input False), SendTokens 32))

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
  testEnvBenOr
  (runAsyncP $ protBenOr)
  (runAsyncF $ bangFAsync fMulticastToken)
  dummyAdversaryToken
 
