module CompileSpec where

import qualified Data.Map                      as M
import           Test.Hspec                     ( describe
                                                , it
                                                , Spec
                                                )
import           Test.Hspec.Golden              ( Golden(..) )
import qualified Data.Text.IO                  as T
import           Data.Text                      ( Text
                                                , pack
                                                , replace
                                                , unpack
                                                )
import           Text.Show.Pretty               ( ppShow )
import           Control.Monad.Except           ( runExcept )
import           Control.Monad.State            ( StateT(runStateT) )

import qualified AST.Source                    as Src
import           Infer.Solve
import           Infer.Env
import           Infer.Infer
import           Error.Error
import           Explain.Reason
import           Parse.AST
import           Compile
import           Prelude                 hiding ( readFile )
import           GHC.IO                         ( unsafePerformIO )
import           Utils.PathUtils
import           TestUtils
import           Debug.Trace                    ( trace )


snapshotTest :: String -> String -> Golden Text
snapshotTest name actualOutput = Golden
  { output        = pack actualOutput
  , encodePretty  = unpack
  , writeToFile   = T.writeFile
  , readFromFile  = T.readFile
  , testName      = unpack $ replace (pack " ") (pack "_") (pack name)
  , directory     = ".snapshots"
  , failFirstTime = False
  }


-- TODO: Refactor in order to use the inferAST function instead that supports imports
tester :: String -> String
tester code =
  let inferred = case buildAST "path" code of
        (Right ast) -> runEnv ast >>= (`runInfer` ast)
        _           -> Left $ InferError (UnboundVariable "") NoReason
  in  case inferred of
        Right x -> compile "" "./build" x
        Left  e -> ppShow e
 where
  runEnv x =
    fst <$> runExcept (runStateT (buildInitialEnv x) Unique { count = 0 })

tableTester :: FilePath -> Src.Table -> Src.AST -> String
tableTester rootPath table ast =
  let resolved =
          fst <$> runExcept
            (runStateT (solveTable table ast) Unique { count = 0 })
  in  case resolved of
        Right x -> concat $ compile rootPath "./build" <$> M.elems x
        Left  e -> ppShow e

spec :: Spec
spec = do
  describe "compile" $ do
    it "should compile to JS" $ do
      let code = unlines
            [ "export fn = (b, c) => (b + c)"
            , "inc :: Number -> Number"
            , "inc = (x) => (x + 1)"
            , "dec :: Number -> Number"
            , "dec = (x) => (x - 1)"
            , "double :: Number -> Number"
            , "double = (x) => (x * 2)"
            , "half :: Number -> Number"
            , "half = (x) => (x / 2)"
            , "3 |> half |> double"
            , "3 == 5"
            , "response     = { users: [] }"
            , "users        = response.users"
            , "carResponse  = { cars: [] }"
            , "allResponses = { ...response, ...carResponse }"
            , "where(allResponses) {"
            , "  is { users: List a, cars: cs }: cs"
            , "  is _                          : []"
            , "}"
            , "where(3) {"
            , "  is Number: 3"
            , "}"
            , "where(\"3\") {"
            , "  is String: 3"
            , "}"
            , "where(true) {"
            , "  is Boolean: 3"
            , "}"
            , "where(3) {"
            , "  is 3: 3"
            , "}"
            , "where(\"3\") {"
            , "  is \"3\": 3"
            , "}"
            , "where(true) {"
            , "  is true: 3"
            , "}"
            , "log :: a -> a"
            , "log = (a) => (#- { console.log(a); return a; } -#)"
            , "if (true) { \"OK\" } else { \"NOT OK\" }"
            , "data Maybe a = Just a | Nothing"
            , "mapMaybe :: (a -> b) -> Maybe a -> Maybe b"
            , "mapMaybe = (f, m) => (where(m) {"
            , "  is Just x : Just(f(x))"
            , "  is Nothing: Nothing"
            , "})"
            , "might = Just(3)"
            , "x = where(might) {"
            , "  is Just x : x"
            , "  is Nothing: 1"
            , "}"
            , "true && false"
            , "false || true"
            , "false || true && false"
            , "1 > 3"
            , "1 < 3"
            , "(1 > 3) && (3 < 1) || true"
            , "1 >= 3"
            , "1 <= 3"
            , "(1 >= 3) && (3 <= 1) || true"
            , "!false"
            , "!true"
            , "!false && !true"
            , "!false || !true"
            , "arr = [1, 2, 3]"
            , "all = [ ...arr, 4, 5, 6]"
            , "where([1, 2, 3, 5, 8]) {"
            , "  is [1, 2, 3]: 1"
            , "  is [1, 2, n]: n"
            , "  is [n, 3]   : n"
            , "  is [x, y, z]: x + y + z"
            , "  is []       : 0"
            , "}"
            , "map :: (a -> b) -> List a -> List b"
            , "export map = (f, xs) => (where(xs) {"
            , "  is [a, b, c]: [f(a), ...map(f, [b, c])]"
            , "  is [a, b]   : [f(a), ...map(f, [b])]"
            , "  is [a]      : [f(a)]"
            , "  is []       : []"
            , "})"
            , "true"
            , "  ? \"ok\""
            , "  : \"not ok\""
            , "(1 == 2 ? \"ok\" : \"not ok\")"
            , "  |> (x) => (x)"
            , "  |> (x) => (x == \"ok\" ? 1 : 10)"
            , "  |> (x) => (x)"
            , "1 == 2 ? \"ok\" : \"not ok\""
            , "where(3)"
            , "  is 3: 48"
            , "  is n: 1 |> (x) => (x + 1)"
            , "(where(\"3\")"
            , "  is \"3\": 48"
            , "  is n: 1"
            , ") |> (x) => (x + 1)"
            , "where([1, 2, 3, 4, 5]) {"
            , "  is [2, ...rest]      : rest"
            , "  is [1, 2, 3, ...rest]: rest"
            , "} |> (x) => (x)"
            , "where({ x: 4, name: \"John\" }) {"
            , "  is { name: \"Bob\" }: \"Bob\""
            , "  is { x: x, ...b } : b.name"
            , "}"
            , "addXAndY = (r) => ("
            , "  where(r) {"
            , "    is { x, y }: x + y"
            , "  }"
            , ")"
            , "fnTCHOU = (x) => (x.a.b.c.d.e)"
            , "crazyRecordPattern = (r) => ("
            , "  where(r) {"
            , "    is { x: { y: { y: y }, ...k }, ...c }: y + k.z + c.o + c.i"
            , "  }"
            , ")"
            ]
          actual = tester code
      snapshotTest "should compile to JS" actual


    it "should compile imports and exports" $ do
      let codeA = "export singleton = (a) => ([a])"
          astA  = buildAST "./ModuleA" codeA

          codeB = unlines
            [ "import L from \"./ModuleA\""
            , "import { singleton } from \"./ModuleA\""
            , "L.singleton(3)"
            ]
          astB   = buildAST "./ModuleB" codeB
          actual = case (astA, astB) of
            (Right a, Right b) ->
              let astTable = M.fromList [("./ModuleA", a), ("./ModuleB", b)]
              in  tableTester "" astTable b
      snapshotTest "should compile imports and exports" actual


    it "should compile imports and exports of Namespaced ADTs" $ do
      let
        codeA = "export data Maybe a = Just a | Nothing"
        astA  = buildAST "./ADTs" codeA

        codeB = unlines
          [ "import ADTs from \"./ADTs\""
          , "(ADTs.Just(3) :: ADTs.Maybe Num)"
          , "ADTs.Nothing"
          , "fn :: ADTs.Maybe (ADTs.Maybe Num) -> ADTs.Maybe (ADTs.Maybe Num)"
          , "export fn = (m) => (m)"
          , "fn2 :: ADTs.Maybe (ADTs.Maybe Num) -> Num"
          , "export fn2 = (m) => ("
          , "  where(m) {"
          , "    is ADTs.Just (ADTs.Just n): n"
          , "  }"
          , ")"
          ]
        astB   = buildAST "./Module" codeB
        actual = case (astA, astB) of
          (Right a, Right b) ->
            let astTable = M.fromList [("./Module", b), ("./ADTs", a)]
            in  tableTester "" astTable b

      snapshotTest "should compile imports and exports of Namespaced ADTs"
                   actual


    it "should compile and resolve imported packages" $ do
      let
        madlibDotJSON = unlines ["{", "  \"main\": \"src/Main.mad\"", "}"]

        libMain       = unlines
          [ "import R from \"./Utils/Random\""
          , "export random = (seed) => (R.random(seed))"
          ]

        libRandom = "export random = (seed) => (seed / 2)"

        main      = unlines ["import R from \"random\"", "R.random(3)"]

        files     = M.fromList
          [ ("/madlib_modules/random/madlib.json"         , madlibDotJSON)
          , ("/madlib_modules/random/src/Main.mad"        , libMain)
          , ("/madlib_modules/random/src/Utils/Random.mad", libRandom)
          , ("/src/Main.mad"                              , main)
          ]

        pathUtils = defaultPathUtils
          { readFile = makeReadFile files
          , byteStringReadFile = makeByteStringReadFile files
          , doesFileExist = \f -> if f == "/madlib_modules/random/madlib.json"
                              then return True
                              else return False
          }

      let r = unsafePerformIO
            $ buildASTTable' pathUtils "/src/Main.mad" Nothing "/src/Main.mad"
      let ast = r >>= flip findAST "/src/Main.mad"
      let actual = case (ast, r) of
            (Right a, Right t) -> tableTester "/src" t a

      snapshotTest "should compile and resolve imported packages" actual


    it
        "should compile and resolve imported packages when project is not at root path"
      $ do
          let
            madlibDotJSON = unlines ["{", "  \"main\": \"src/Main.mad\"", "}"]

            libMain       = unlines
              [ "import R from \"./Utils/Random\""
              , "export random = (seed) => (R.random(seed))"
              , "export data Maybe a = Just a | Nothing"
              ]

            libRandom = "export random = (seed) => (seed / 2)"

            main      = unlines ["import R from \"random\"", "R.random(3)"]

            files     = M.fromList
              [ ( "/root/project/madlib_modules/random/madlib.json"
                , madlibDotJSON
                )
              , ("/root/project/madlib_modules/random/src/Main.mad", libMain)
              , ( "/root/project/madlib_modules/random/src/Utils/Random.mad"
                , libRandom
                )
              , ("/root/project/src/Main.mad", main)
              ]

            pathUtils = defaultPathUtils
              { readFile           = makeReadFile files
              , byteStringReadFile = makeByteStringReadFile files
              , doesFileExist      = \f ->
                if f == "/root/project/madlib_modules/random/madlib.json"
                  then return True
                  else return False
              }

          let r = unsafePerformIO $ buildASTTable'
                pathUtils
                "/root/project/src/Main.mad"
                Nothing
                "/root/project/src/Main.mad"
          let ast = r >>= flip findAST "/root/project/src/Main.mad"
          let actual = case (ast, r) of
                (Right a, Right t) -> tableTester "/root/project/src" t a

          snapshotTest
            "should compile and resolve imported packages when project is not at root path"
            actual


    it "should compile and resolve files importing prelude modules" $ do
      let
        listModule = unlines
          [ "map :: (a -> b) -> List a -> List b"
          , "export map = (f, xs) => (#- xs.map(f) -#)"
          ]

        main =
          unlines ["import L from \"List\"", "L.map((x) => (x * 2), [1, 2, 3])"]

        files = M.fromList
          [ ("/root/project/prelude/__internal__/List.mad", listModule)
          , ("/root/project/src/Main.mad"                 , main)
          ]

        pathUtils = defaultPathUtils
          { readFile           = makeReadFile files
          , byteStringReadFile = makeByteStringReadFile files
          , getExecutablePath  = return "/root/project/madlib"
          }

      let r = unsafePerformIO $ buildASTTable' pathUtils
                                               "/root/project/src/Main.mad"
                                               Nothing
                                               "/root/project/src/Main.mad"
      let ast = r >>= flip findAST "/root/project/src/Main.mad"
      let actual = case (ast, r) of
            (Right a, Right t) -> tableTester "/root/project/src" t a
            (Left  e, _      ) -> ppShow e
            (_      , Left e ) -> ppShow e

      snapshotTest
        "should compile and resolve files importing prelude modules"
        actual


    it "should compile and resolve imported packages that also rely on packages"
      $ do
          let
            mathMadlibDotJSON =
              unlines ["{", "  \"main\": \"src/Main.mad\"", "}"]
            mathMain = unlines ["export avg = (a, b) => ((a + b) / 2)"]

            randomMadlibDotJSON =
              unlines ["{", "  \"main\": \"src/Main.mad\"", "}"]

            randomMain = unlines
              [ "import R from \"./Utils/Random\""
              , "import M from \"math\""
              , "export random = (seed) => (R.random(seed) + M.avg(seed, seed))"
              ]

            libRandom = "export random = (seed) => (seed / 2)"

            main      = unlines ["import R from \"random\"", "R.random(3)"]

            files     = M.fromList
              [ ( "/madlib_modules/random/madlib_modules/math/madlib.json"
                , mathMadlibDotJSON
                )
              , ( "/madlib_modules/random/madlib_modules/math/src/Main.mad"
                , mathMain
                )
              , ("/madlib_modules/random/madlib.json", randomMadlibDotJSON)
              , ("/madlib_modules/random/src/Main.mad"        , randomMain)
              , ("/madlib_modules/random/src/Utils/Random.mad", libRandom)
              , ("/src/Main.mad"                              , main)
              ]

            pathUtils = defaultPathUtils
              { readFile           = makeReadFile files
              , byteStringReadFile = makeByteStringReadFile files
              , doesFileExist      = \f ->
                if f
                   == "/madlib_modules/random/madlib.json"
                   || f
                   == "/madlib_modules/random/madlib_modules/math/madlib.json"
                then
                  return True
                else
                  return False
              }

          let r = unsafePerformIO $ buildASTTable' pathUtils
                                                   "/src/Main.mad"
                                                   Nothing
                                                   "/src/Main.mad"
          let ast = r >>= flip findAST "/src/Main.mad"
          let actual = case (ast, r) of
                (Right a, Right t) -> tableTester "/src" t a

          snapshotTest
            "should compile and resolve imported packages that also rely on packages"
            actual

