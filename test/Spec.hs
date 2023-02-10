import Test.HUnit
import Test.Framework (defaultMain)
import Test.Framework.Providers.HUnit (hUnitTestToTests)

import qualified NbE (allTests)

allTests :: Test
allTests = TestList
  [ NbE.allTests
  ]

main :: IO ()
main = defaultMain (hUnitTestToTests allTests)
