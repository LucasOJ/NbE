import qualified UntypedTests.GensymNbE
import qualified UntypedTests.DeBruijnNbE
import qualified MonotypedTests.ChurchBooleans
import qualified MonotypedTests.ChurchNumerals


main :: IO ()
main = do 
    putStrLn $ "Untyped gensym tests passed:       " ++ show UntypedTests.GensymNbE.allTestsPassed
    putStrLn $ "Untyped de Bruijn tests passed:    " ++ show UntypedTests.DeBruijnNbE.allTestsPassed
    putStrLn $ "Typed church boolean tests passed: " ++ show MonotypedTests.ChurchBooleans.allTestsPassed
    putStrLn $ "Typed church numeral tests passed: " ++ show UntypedTests.GensymNbE.allTestsPassed
