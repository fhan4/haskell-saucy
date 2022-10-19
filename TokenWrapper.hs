{-# LANGUAGE ImplicitParams, ScopedTypeVariables, Rank2Types,
             ConstraintKinds
  #-}


module TokenWrapper where

import ProcessIO
import StaticCorruptions
import Multisession
import Async

import Safe
import Control.Concurrent.MonadIO
import Control.Monad (forever)

import Data.IORef.MonadIO
import Data.Map.Strict (member, empty, insert, Map)
import qualified Data.Map.Strict as Map


data Carry_Tokens a = Send_Tokens a deriving Show


type MonadAdversaryToken m = (MonadAdversary m,
                              -- ?sendToken :: m () -> m (),
                              ?getToken :: m Int)

-- sendToken :: MonadAdversaryToken m => m () -> m ()
-- sendToken = ?sendToken

getToken :: MonadAdversaryToken m => m Int
getToken = ?getToken



runTokenA :: MonadAdversary m =>
          (MonadAdversaryToken m => Adversary (b, Carry_Tokens Int) a2z p2a a2p f2a (Either ClockA2F a2f) m)
          -> Adversary (b, Carry_Tokens Int) a2z p2a a2p f2a (Either ClockA2F a2f) m
runTokenA a (z2a, a2z) (p2a, a2p) (f2a, a2f) = do

  tokens <- newIORef 0

  z2a' <- newChan
  a2f' <- newChan

  fork $ forever $ do
    (mf, Send_Tokens a) <- readChan z2a
    if a>=0 then do
      tk <- readIORef tokens
      writeIORef tokens (tk+a)
    else
      error "sending negative tokens"
    writeChan z2a' (mf, Send_Tokens a)

  fork $ forever $ do
    mf <- readChan a2f'
    case mf of
      Left (ClockA2F_Deliver _) -> do
        tk <- readIORef tokens
        if (tk-1) < 0 then
          error "not enough tokens"
        else
          writeIORef tokens (tk-1)
      Left (ClockA2F_Delay rounds) -> do
        if rounds > 0 then do
          tk <- readIORef tokens
          if (tk-rounds) < 0 then
            error "not enough tokens"
          else
            writeIORef tokens (tk-rounds)
        else
          return()
      _ -> return()
    writeChan a2f mf

  let _getToken = do
        tk <- readIORef tokens
        return tk

  let ?getToken = _getToken in
    a (z2a', a2z) (p2a, a2p) (f2a, a2f')
  return ()

dummyAdversaryToken :: MonadAdversaryToken m => Adversary ((SttCruptZ2A b d), Carry_Tokens Int) (SttCruptA2Z a c) a b c d m
dummyAdversaryToken (z2a, a2z) (p2a, a2p) (f2a, a2f) = do
  fork $ forever $ readChan z2a >>= \mf ->
      case mf of
        ((SttCruptZ2A_A2F b), Send_Tokens _)        -> writeChan a2f b
        ((SttCruptZ2A_A2P (pid, m)), Send_Tokens _) -> writeChan a2p (pid, m)
  fork $ forever $ readChan f2a >>= writeChan a2z . SttCruptA2Z_F2A
  fork $ forever $ readChan p2a >>= writeChan a2z . SttCruptA2Z_P2A
  return ()

idealProtocolToken :: MonadProtocol m => Protocol (ClockP2F a, Carry_Tokens Int) b b (ClockP2F (a, Carry_Tokens Int)) m
idealProtocolToken (z2p, p2z) (f2p, p2f) = do
  fork $ forever $ do
    mf <- readChan z2p
    --liftIO $ putStrLn $ "idealProtocol received from z2p " ++ pid
    case mf of
      (ClockP2F_Pass, Send_Tokens _)       -> writeChan p2f ClockP2F_Pass
      (ClockP2F_Through m, Send_Tokens tk) -> writeChan p2f (ClockP2F_Through (m, Send_Tokens tk))
  fork $ forever $ do
    m <- readChan f2p
    --liftIO $ putStrLn $ "idealProtocol received from f2p " ++ pid
    writeChan p2z m
  return ()
