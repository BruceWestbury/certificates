/-
  PolynomialTests.lean

  Smoke tests for Polynomial and LinearCombination.
  Run with:  lake build Certificates.PolynomialTests
-/

import Certificates.Polynomial

open Polynomial

-- ─── helpers ────────────────────────────────────────────────────────────────

private def check (label : String) (b : Bool) : IO Unit :=
  if b then IO.println s!"  ✓  {label}"
  else do
    IO.println s!"  ✗  {label}"
    IO.Process.exit 1

private def checkEq (label : String) (p q : Poly) : IO Unit :=
  check label (beq p q)

-- ─── Polynomial tests ────────────────────────────────────────────────────────

def testNormalize : IO Unit := do
  IO.println "normalize"
  checkEq "[] is zero"           (normalize [])          []
  checkEq "trailing zeros"       (normalize [1, 0, 0])   [1]
  checkEq "all zeros"            (normalize [0, 0])      []
  checkEq "no trailing zeros"    (normalize [1, 2, 3])   [1, 2, 3]
  checkEq "interior zero kept"   (normalize [0, 1])      [0, 1]

def testAdd : IO Unit := do
  IO.println "add"
  -- (1 + 2n) + (3 + 4n) = 4 + 6n
  checkEq "same degree"   (add [1, 2] [3, 4])        [4, 6]
  -- (1 + 2n) + (3 + 4n + 5n²) = 4 + 6n + 5n²
  checkEq "rhs longer"    (add [1, 2] [3, 4, 5])     [4, 6, 5]
  -- (1 + 2n + 3n²) + (−1 − 2n) = 3n²
  checkEq "lhs longer"    (add [1, 2, 3] [-1, -2])   [0, 0, 3]
  -- add with zero poly
  checkEq "add zero"      (add [1, 2] [])             [1, 2]

def testNeg : IO Unit := do
  IO.println "neg"
  checkEq "neg"    (neg [1, -2, 3])   [-1, 2, -3]
  checkEq "neg []" (neg [])           []

def testSub : IO Unit := do
  IO.println "sub"
  -- (3 + 5n) − (1 + 2n) = 2 + 3n
  checkEq "basic sub"   (sub [3, 5] [1, 2])   [2, 3]
  -- p − p = 0  (after normalize)
  checkEq "p - p = 0"   (normalize (sub [1, 2, 3] [1, 2, 3]))  []

def testMul : IO Unit := do
  IO.println "mul"
  -- (1 + n)(1 + n) = 1 + 2n + n²
  checkEq "(1+n)²"         (normalize (mul [1, 1] [1, 1]))      [1, 2, 1]
  -- (2)(3 + 4n) = 6 + 8n
  checkEq "const × poly"   (normalize (mul [2] [3, 4]))         [6, 8]
  -- (1 + n)(1 − n) = 1 − n²
  checkEq "(1+n)(1-n)"     (normalize (mul [1, 1] [1, -1]))     [1, 0, -1]
  -- zero × anything = 0
  checkEq "zero × poly"    (normalize (mul [] [1, 2, 3]))        []
  -- multiply by var shifts
  checkEq "n × (1+n)"      (normalize (mul var [1, 1]))          [0, 1, 1]

def testEval : IO Unit := do
  IO.println "eval"
  -- 1 + 2n + n² at n=3: 1 + 6 + 9 = 16
  check "eval at 3"  (eval [1, 2, 1] 3 == 16)
  -- zero poly at any point
  check "eval zero"  (eval [] 100 == 0)

def testBeq : IO Unit := do
  IO.println "beq (with normalization)"
  check "[1,0] == [1]"         (beq [1, 0] [1])
  check "[0,0] == []"          (beq [0, 0] [])
  check "[1,2] ≠ [1,3]"        (! beq [1, 2] [1, 3])
  check "[1,2,0] == [1,2]"     (beq [1, 2, 0] [1, 2])

-- ─── LinearCombination tests ─────────────────────────────────────────────────

open LinearCombination in
def testLC : IO Unit := do
  IO.println "LinearCombination"
  -- singleton
  let t1 : LC String := singleton [1, 1] "A"   -- (1+n)·A
  let t2 : LC String := singleton [2]   "A"   --    2·A
  -- smul: 3 · [(1+n)·A] = [(3+3n)·A]
  let scaled := smul [3] t1
  check "smul coeff"  (Polynomial.beq (scaled.head!.coeff) [3, 3])
  -- neg
  let negT1 := neg t1
  check "neg coeff"   (Polynomial.beq (negT1.head!.coeff) [-1, -1])
  -- addAligned success
  match addAligned t1 t2 with
  | none    => IO.println "  ✗  addAligned (should succeed)"; IO.Process.exit 1
  | some lc =>
    check "addAligned coeff"  (Polynomial.beq (lc.head!.coeff) [3, 1])
  -- addAligned label mismatch → none
  let t3 : LC String := singleton [1] "B"
  match addAligned t1 t3 with
  | none    => IO.println "  ✓  addAligned label mismatch → none"
  | some _  => IO.println "  ✗  should have been none"; IO.Process.exit 1
  -- normalize drops zero terms
  let withZero : LC String := [⟨[0, 0], "A"⟩, ⟨[1], "B"⟩]
  let normed := normalize withZero
  check "normalize drops zero"  (normed.length == 1 && normed.head!.label == "B")
  -- beq
  let lc1 : LC String := [⟨[1, 0], "A"⟩]   -- trailing zero
  let lc2 : LC String := [⟨[1],    "A"⟩]
  check "LC beq with norm"  (beq lc1 lc2)

-- ─── entry point ─────────────────────────────────────────────────────────────

def main : IO Unit := do
  IO.println "=== Polynomial smoke tests ==="
  testNormalize
  testAdd
  testNeg
  testSub
  testMul
  testEval
  testBeq
  IO.println "=== LinearCombination smoke tests ==="
  testLC
  IO.println "All tests passed."
