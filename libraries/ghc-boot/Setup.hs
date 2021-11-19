{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE CPP #-}
module Main where

import Distribution.Simple
import Distribution.Simple.BuildPaths
import Distribution.Types.LocalBuildInfo
import Distribution.Verbosity
import Distribution.Simple.Program

import System.IO
import System.Directory
import System.FilePath
import Control.Monad
import Data.Char
import GHC.ResponseFile

main :: IO ()
main = defaultMainWithHooks ghcHooks
  where
    ghcHooks = simpleUserHooks
      { buildHook = \pd lbi uh bf -> do
          ghcAutogen lbi
          buildHook simpleUserHooks pd lbi uh bf
      }

ghcAutogen :: LocalBuildInfo -> IO ()
ghcAutogen lbi@LocalBuildInfo{..} = do
  -- Get compiler/ root directory from the cabal file
  let Just compilerRoot = takeDirectory <$> pkgDescrFile

  -- Require the necessary programs
  (gcc   ,withPrograms) <- requireProgram normal gccProgram withPrograms
  (ghc   ,withPrograms) <- requireProgram normal ghcProgram withPrograms
  (ghcPkg,withPrograms) <- requireProgram normal ghcPkgProgram withPrograms

  -- Get compiler settings
  settings <- read <$> getProgramOutput normal ghc ["--info"]

  -- Write GHC.Platform.Host
  let platformHostPath = autogenPackageModulesDir lbi </> "GHC/Platform/Host.hs"
  createDirectoryIfMissing True (takeDirectory platformHostPath)
  writeFile platformHostPath (generatePlatformHostHs settings)

  -- Write GHC.Version
  let ghcVersionPath = autogenPackageModulesDir lbi </> "GHC/Version.hs"
  createDirectoryIfMissing True (takeDirectory ghcVersionPath)
  writeFile ghcVersionPath (generateVersionHs settings)

generatePlatformHostHs :: [(String,String)] -> String
generatePlatformHostHs settings = either error id $ do
    let getSetting k = case lookup k settings of
          Nothing -> Left (show k ++ " not found in settings")
          Just v -> Right v
    cHostPlatformArch <- getSetting "target arch"
    cHostPlatformOS   <- getSetting "target os"
    return $ unlines
        [ "module GHC.Platform.Host where"
        , ""
        , "import GHC.Platform.ArchOS"
        , ""
        , "hostPlatformArch :: Arch"
        , "hostPlatformArch = " ++ cHostPlatformArch
        , ""
        , "hostPlatformOS   :: OS"
        , "hostPlatformOS   = " ++ cHostPlatformOS
        , ""
        , "hostPlatformArchOS :: ArchOS"
        , "hostPlatformArchOS = ArchOS hostPlatformArch hostPlatformOS"
        ]

generateVersionHs :: [(String,String)] -> String
generateVersionHs settings = either error id $ do
    let getSetting k = case lookup k settings of
          Nothing -> Left (show k ++ " not found in settings")
          Just v -> Right v
    cProjectGitCommitId <- getSetting "Project Git commit id"
    cProjectVersion     <- getSetting "Project version"
    cProjectVersionInt  <- pure $ show $ __GLASGOW_HASKELL__
    cProjectPatchLevel  <- pure $ show $ __GLASGOW_HASKELL_PATCHLEVEL1__
    cProjectPatchLevel1 <- pure $ cProjectPatchLevel
    cProjectPatchLevel2 <- pure ""
    return $ unlines
        [ "module GHC.Version where"
        , ""
        , "import Prelude -- See Note [Why do we import Prelude here?]"
        , ""
        , "cProjectGitCommitId   :: String"
        , "cProjectGitCommitId   = " ++ show cProjectGitCommitId
        , ""
        , "cProjectVersion       :: String"
        , "cProjectVersion       = " ++ show cProjectVersion
        , ""
        , "cProjectVersionInt    :: String"
        , "cProjectVersionInt    = " ++ show cProjectVersionInt
        , ""
        , "cProjectPatchLevel    :: String"
        , "cProjectPatchLevel    = " ++ show cProjectPatchLevel
        , ""
        , "cProjectPatchLevel1   :: String"
        , "cProjectPatchLevel1   = " ++ show cProjectPatchLevel1
        , ""
        , "cProjectPatchLevel2   :: String"
        , "cProjectPatchLevel2   = " ++ show cProjectPatchLevel2
        ]
