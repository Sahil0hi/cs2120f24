-- File: /c:/Users/sahil/OneDrive/Desktop/DiscreteGit/cs2120f24/Cs2120f24/MyWork/test_hw#04.lean

import Cs2120f24.MyWork.hw#04

-- Tests for fac function
#eval fac 0   -- expect 1
#eval fac 1   -- expect 1
#eval fac 2   -- expect 2
#eval fac 3   -- expect 6
#eval fac 4   -- expect 24
#eval fac 5   -- expect 120

-- Tests for sum function
#eval sum 0   -- expect 0
#eval sum 1   -- expect 1
#eval sum 2   -- expect 3
#eval sum 3   -- expect 6
#eval sum 4   -- expect 10
#eval sum 5   -- expect 15

-- Tests for sum' function
#eval sum' 0    -- expect 0
#eval sum' 5    -- expect 15
#eval sum' 2    -- expect 3

-- Tests for summ function
#eval summ 0    -- expect 0
#eval summ 5    -- expect 15
#eval summ 100  -- expect 5050

-- Tests for sumSq' function
#eval sumSq' 0  -- expect 0
#eval sumSq' 1  -- expect 1
#eval sumSq' 2  -- expect 5
#eval sumSq' 3  -- expect 14
#eval sumSq' 4  -- expect 30
#eval sumSq' 5  -- expect 55

-- Tests for sumSq function
#eval sumSq 0   -- expect 0
#eval sumSq 1   -- expect 1
#eval sumSq 2   -- expect 5
#eval sumSq 3   -- expect 14
#eval sumSq 4   -- expect 30
#eval sumSq 5   -- expect 55

-- Tests for binaryRep function
#eval binaryRep 0   -- expect "0"
#eval binaryRep 1   -- expect "1"
#eval binaryRep 2   -- expect "10"
#eval binaryRep 3   -- expect "11"
#eval binaryRep 4   -- expect "100"
#eval binaryRep 5   -- expect "101"

-- Tests for fib function
#eval fib 0   -- expect 0
#eval fib 1   -- expect 1
#eval fib 2   -- expect 1
#eval fib 3   -- expect 2
#eval fib 4   -- expect 3
#eval fib 5   -- expect 5
#eval fib 10  -- expect 55