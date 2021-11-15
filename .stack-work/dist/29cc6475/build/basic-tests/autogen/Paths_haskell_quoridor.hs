{-# LANGUAGE CPP #-}
{-# LANGUAGE NoRebindableSyntax #-}
{-# OPTIONS_GHC -fno-warn-missing-import-lists #-}
module Paths_haskell_quoridor (
    version,
    getBinDir, getLibDir, getDynLibDir, getDataDir, getLibexecDir,
    getDataFileName, getSysconfDir
  ) where

import qualified Control.Exception as Exception
import Data.Version (Version(..))
import System.Environment (getEnv)
import Prelude

#if defined(VERSION_base)

#if MIN_VERSION_base(4,0,0)
catchIO :: IO a -> (Exception.IOException -> IO a) -> IO a
#else
catchIO :: IO a -> (Exception.Exception -> IO a) -> IO a
#endif

#else
catchIO :: IO a -> (Exception.IOException -> IO a) -> IO a
#endif
catchIO = Exception.catch

version :: Version
version = Version [1,0] []
bindir, libdir, dynlibdir, datadir, libexecdir, sysconfdir :: FilePath

bindir     = "D:\\Users\\Admin\\Desktop\\RaACW\\haskell-quoridor\\.stack-work\\install\\9c1acc3b\\bin"
libdir     = "D:\\Users\\Admin\\Desktop\\RaACW\\haskell-quoridor\\.stack-work\\install\\9c1acc3b\\lib\\x86_64-windows-ghc-8.8.4\\haskell-quoridor-1.0-KxD18lihma2802Pb9NeQky-basic-tests"
dynlibdir  = "D:\\Users\\Admin\\Desktop\\RaACW\\haskell-quoridor\\.stack-work\\install\\9c1acc3b\\lib\\x86_64-windows-ghc-8.8.4"
datadir    = "D:\\Users\\Admin\\Desktop\\RaACW\\haskell-quoridor\\.stack-work\\install\\9c1acc3b\\share\\x86_64-windows-ghc-8.8.4\\haskell-quoridor-1.0"
libexecdir = "D:\\Users\\Admin\\Desktop\\RaACW\\haskell-quoridor\\.stack-work\\install\\9c1acc3b\\libexec\\x86_64-windows-ghc-8.8.4\\haskell-quoridor-1.0"
sysconfdir = "D:\\Users\\Admin\\Desktop\\RaACW\\haskell-quoridor\\.stack-work\\install\\9c1acc3b\\etc"

getBinDir, getLibDir, getDynLibDir, getDataDir, getLibexecDir, getSysconfDir :: IO FilePath
getBinDir = catchIO (getEnv "haskell_quoridor_bindir") (\_ -> return bindir)
getLibDir = catchIO (getEnv "haskell_quoridor_libdir") (\_ -> return libdir)
getDynLibDir = catchIO (getEnv "haskell_quoridor_dynlibdir") (\_ -> return dynlibdir)
getDataDir = catchIO (getEnv "haskell_quoridor_datadir") (\_ -> return datadir)
getLibexecDir = catchIO (getEnv "haskell_quoridor_libexecdir") (\_ -> return libexecdir)
getSysconfDir = catchIO (getEnv "haskell_quoridor_sysconfdir") (\_ -> return sysconfdir)

getDataFileName :: FilePath -> IO FilePath
getDataFileName name = do
  dir <- getDataDir
  return (dir ++ "\\" ++ name)
