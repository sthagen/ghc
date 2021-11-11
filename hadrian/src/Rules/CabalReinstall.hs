module Rules.CabalReinstall where

import Context
import Expression
import Oracles.Flag
import Packages
import Settings
import Target
import Utilities
import qualified System.Directory.Extra as IO
import Data.Either
import Rules.BinaryDist
import Hadrian.Haskell.Cabal (pkgIdentifier)

{-
Note [Testing reinstallable GHC]
~~~~~~~~~~~~~~~~~~~~~~~~~~~
To test the reinstallable GHC configuration, we install a GHC to <build root>/stage-cabal/bin
along with appropriate wrapper scripts.

The libdir of the reinstalled GHC points to the libdir of the stage 2 compiler (in <build root>/stage1)
-}

cabalBuildRules :: Rules ()
cabalBuildRules = do
    root <- buildRootRules
    phony "build-cabal" $ do
        -- We 'need' all binaries and libraries
        all_pkgs <- stagePackages Stage1
        (lib_targets, bin_targets) <- partitionEithers <$> mapM pkgTarget all_pkgs
        cross <- flag CrossCompiling
        iserv_targets <- if cross then pure [] else iservBins
        need (lib_targets ++ (map (\(_, p) -> p) (bin_targets ++ iserv_targets)))

        distDir        <- Context.distDir Stage1
        rtsDir         <- pkgIdentifier rts

        let ghcBuildDir      = root -/- stageString Stage1
            rtsIncludeDir    = ghcBuildDir -/- "lib" -/- distDir -/- rtsDir
                               -/- "include"

        libdir  <- liftIO . IO.makeAbsolute =<< stageLibPath Stage1
        outputDir <- liftIO $ IO.makeAbsolute $ root -/- "stage-cabal" -/- "bin"
        includeDir <- liftIO $ IO.makeAbsolute rtsIncludeDir

        createDirectory outputDir
        forM_ (filter ((/= iserv) . fst) bin_targets) $ \(bin_pkg,_bin_path) -> do
            withVerbosity Diagnostic $
              buildWithCmdOptions [] $
                target (vanillaContext Stage2 bin_pkg) (Cabal Build Stage2) [] []
            [cabal_bin_out] <- words <$> askWithResources [] (target (vanillaContext Stage2 bin_pkg) (Cabal ListBin Stage2) [] [])
            needed_wrappers <- pkgToWrappers bin_pkg
            forM_ needed_wrappers $ \wrapper_name -> do
              let wrapper_prefix = unlines
                    ["#!/bin/env sh"
                    ,"executablename="++show cabal_bin_out
                    ,"libdir="++show libdir
                    ,"bindir="++show outputDir
                    ,"exedir="++show outputDir
                    ,"includedir="++show includeDir
                    ]
                  output_file = outputDir -/- wrapper_name
              wrapper_content <- wrapper wrapper_name
              writeFile' output_file (wrapper_prefix ++ wrapper_content)
              makeExecutable output_file
              pure ()

        -- Just symlink these for now
        -- TODO: build these with cabal as well
        forM_ iserv_targets $ \(_bin_pkg,bin_path') -> do
            bin_path <- liftIO $ IO.makeAbsolute bin_path'
            let orig_filename = takeFileName bin_path
                output_file = outputDir -/- orig_filename
            liftIO $ do
              IO.removeFile output_file <|> pure ()
              IO.createFileLink bin_path output_file
            pure ()
