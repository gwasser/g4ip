import Proposition
import Inference
import Decide

-- set some standard atoms for formulas
a = Atom "A"
b = Atom "B"
c = Atom "C"
d = Atom "D"
e = Atom "E"
f = Atom "F"

-- list of test cases
-- each item in list is a pair of a Prop, and whether it is provable or not
test_cases = [ ( a ==> a , True ),
    ( a ==> (b ==> a) , True ),
    ( ((a ==> b) ==> a) ==> a, False ),
    ( n (n (((a ==> b) ==> a) ==> a)) , True ),
    ( a & b ==> b & a , True ),
    ( a \/ b ==> b \/ a , True ),
    -- hw02, implOr:
    ( (a \/ c) & (b ==> c) ==> (a ==> b) ==> c, True ),
    -- some basic propositional (non-)tautologies
    ( (a ==> b ==> c) <=> (a & b ==> c) , True ),
    ( (a ==> b & c) <=> (a ==> b) & (a ==> c) , True ),
    ( (a ==> b \/ c) ==> (a ==> b) \/ (a ==> c) , False ),
    ( (a ==> b \/ c) <== (a ==> b) \/ (a ==> c) , True ),
    ( ((a ==> b) ==> c) ==> ((a \/ b) & (b ==> c)) , False ),
    ( ((a ==> b) ==> c) <== ((a \/ b) & (b ==> c)) , True ),
    ( (a \/ b ==> c) <=> (a ==> c) & (b ==> c) , True ),
    ( (a & (b \/ c)) <=> (a & b) \/ (a & c) , True ),
    ( (a \/ (b & c)) <=> (a \/ b) & (a \/ c) , True ),
    -- some deMorgan-like dualities
    ( n (a & b) ==> n a \/ n b , False ),
    ( n (a & b) <== n a \/ n b , True ),
    ( n (a \/ b) <=> n a & n b , True ),
    ( n (a ==> b) ==> a & n b , False ),
    ( n (a ==> b) <== a & n b , True ),
    ( n (n a) ==> a , False ),
    ( n (n a) <== a , True ),
    ( n TrueP <=> FalseP , True ),
    ( n FalseP <=> TrueP , True ),
    -- triple-negation elimination
    ( n (n (n a)) <=> n a , True ),
    -- three-way transitivity
    ( (a ==> b) ==> (b ==> c) ==> (c ==> d) ==> (a ==> d) , True ),
    -- some test cases for various common mistakes
    ( (a ==> b) ==> (a ==> c) ==> a ==> b , True ),
    ( (a ==> b) ==> (a ==> c) ==> a ==> c , True ),
    ( a ==> (a ==> b) ==> (a ==> c) ==> b , True ),
    ( a ==> (a ==> b) ==> (a ==> c) ==> c , True ),
    ( (a ==> b ==> c) ==> a ==> b ==> c , True ),
    ( (a ==> b ==> c) ==> b ==> a ==> c , True ),
    ( a ==> b ==> (a ==> b ==> c) ==> c , True ),
    ( b ==> a ==> (a ==> b ==> c) ==> c , True ),
    -- it turns out that heavily left-nested instances of the identity theorem make really great stress-tests for correctness!
    ( (a ==> b) ==> a ==> b , True ),
    ( ((a ==> b) ==> c) ==> ((a ==> b) ==> c) , True ),
    ( (((a ==> b) ==> c) ==> d) ==> (((a ==> b) ==> c) ==> d) , True ),
    ( ((((a ==> b) ==> c) ==> d) ==> e) ==> (((a ==> b) ==> c) ==> d) ==> e , True ),
    ( (((((a ==> b) ==> c) ==> d) ==> e) ==> f) ==> ((((a ==> b) ==> c) ==> d) ==> e) ==> f , True ),
    ( (((((a ==> b) ==> c) ==> d) ==> e) ==> f) ==> (((((a ==> b) ==> c) ==> d) ==> e) ==> f) \/ (((((a ==> b) ==> c) ==> d) ==> e) ==> f) , True ),
    ( ((a ==> b) ==> c) ==> d ==> d \/ d, True ),
    -- student suggested test cases from Piazza
    ( ((c ==> d) & ((a ==> f) ==> b)) ==> (c ==> d), True ),
    ( (((a ==> f) ==> b) & (c ==> d)) ==> (c ==> d), True ),
    ( (a \/ (n a)) ==> ((n (n a)) ==> a), True ),
    ( (a \/ (n a)) ==> (((a ==> b) ==> a) ==> a), True )
    ]

-- function to automatically run test cases and report results
run_test :: [(Prop, Bool)] -> Int -> IO Int
run_test [] n = return n
run_test ((p,b):ts) n = do
    if (decide p == b)
       then putStr "[OK]   : "
       else putStr "[FAIL] : "
    putStr (show p)
    if b
       then putStr " provable"
       else putStr " unprovable"
    putStr "\n"
    run_test ts (if (decide p == b) then n + 1 else n)

main :: IO ()
main = do
    putStrLn "******* G4ip Tester Program *******"
    putStrLn "* written by : Garret Wassermann"
    putStrLn "* for CMU 15-317 Constructive Logic"
    putStrLn "* Homework 7, due 2015-10-29"
    putStrLn "***********************************"
    putStrLn "Running Tests..."
    let t = length test_cases
    n <- run_test test_cases 0
    putStrLn "-----------------------------"
    putStrLn ("Results : " ++ (show n) ++ " out of " ++ (show t))
