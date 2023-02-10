import Test.Framework (defaultMain)
import Test.Framework.Providers.HUnit (hUnitTestToTests)
import Test.HUnit

import qualified Unit.TypeChecker as TypeChecker (allTests)

allTests :: Test
allTests = TestList [TypeChecker.allTests]

main :: IO ()
main = defaultMain (hUnitTestToTests allTests)
