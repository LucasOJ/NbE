import UntypedTests.GensymNbE (gensymBenchmarks)

import Criterion.Main

main :: IO ()
main = defaultMain [
        gensymBenchmarks
    ]
