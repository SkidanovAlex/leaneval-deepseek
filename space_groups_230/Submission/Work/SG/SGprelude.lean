import Mathlib
import Submission.Work.SG.Defs

/-!
# `sg_data_facts`: integer-side mirror of the generated tables

This file sets up the machine-readable ("certificate") side of
`Submission/Work/SG/sg_data_facts.lean`.

The tables in `Submission.Work.SG.Defs` (`sgClose`, `sgTable`, `sgTau`) are computed over
`List ℚ` translations.  The Lean kernel cannot evaluate `ℚ` arithmetic (the `Rat` operations
are `irreducible`, so the corresponding `fract`/`+`/`*` terms are stuck), while compiled
`#eval` handles them fine.  Therefore every *computation* in this development is performed on
`List ℤ` data (matrices and integer numerators over a fixed denominator `d`), and the
`ℚ`-side facts are obtained from general bridge lemmas proved once and for all
(`toPair`, `zMul`, ...).

Conventions:
* a *flat matrix* is a `List ℤ` of `9` entries, row major (`m9mul`, `imatOfList`);
* an *integer affine pair* is `(A, u) : List ℤ × List ℤ` meaning the affine map
  `x ↦ A x + u/d` (mod `ℤ³`), where `d` is the denominator of the representative;
* `zMul d` is the corresponding multiplication, using `· % d` in place of `Int.fract`.
-/

namespace Work.SG

/-! ## Integer side -/

/-- Pointwise reduction modulo `d`. -/
def emodList (d : ℕ) (v : List ℤ) : List ℤ := v.map fun x => x % (d : ℤ)

/-- Flat integer matrix times integer vector (row major, `3 × 3` by `3`). -/
def m9vecZ (a v : List ℤ) : List ℤ :=
  (List.range 3).map fun i =>
    ((List.range 3).map fun k => a.getD (3 * i + k) 0 * v.getD k 0).sum

/-- The identity of the integer affine pairs (denominator-free). -/
def zOne : List ℤ × List ℤ := ([1, 0, 0, 0, 1, 0, 0, 0, 1], [0, 0, 0])

/-- Product of integer affine pairs with translations mod `d`:
`(A, u) · (B, v) = (A B, (u + A v) mod d)`.  This is the `ℤ`-mirror of `sgMulPair` at
denominator `d`. -/
def zMul (d : ℕ) (p q : List ℤ × List ℤ) : List ℤ × List ℤ :=
  (m9mul p.1 q.1, emodList d (List.zipWith (· + ·) p.2 (m9vecZ p.1 q.2)))

/-- `n / d` as a rational number.  (Defining this as a named function avoids an unfortunate
elaboration of `fun n => (n : ℚ) / (d : ℚ)` as a composition of two `List.map`s.) -/
def divQ (d : ℕ) (n : ℤ) : ℚ := (n : ℚ) / (d : ℚ)

/-- Scale a list of integer numerators by `1/d`. -/
def toPairL (d : ℕ) (v : List ℤ) : List ℚ := v.map (divQ d)

/-- Interpret an integer affine pair at denominator `d` as a pair of the `Defs` shape. -/
def toPair (d : ℕ) (p : List ℤ × List ℤ) : List ℤ × List ℚ :=
  (p.1, toPairL d p.2)

theorem toPair_fst (d : ℕ) (p : List ℤ × List ℤ) : (toPair d p).1 = p.1 := rfl

theorem toPair_snd (d : ℕ) (p : List ℤ × List ℤ) : (toPair d p).2 = toPairL d p.2 := rfl

/-- The `ℚ`-side identity is the image of the integer one (for `d ≠ 0`). -/
theorem toPair_zOne (d : ℕ) : toPair d zOne = sgOne := by
  simp [toPair, toPairL, divQ, zOne, sgOne]

/-! ## The generated data of the representatives -/

/-- Denominator of the `k`-th representative. -/
def sgDen (k : Fin 230) : ℕ := (sgDataList.getD k.val (0, 1, [], 0)).2.1

/-- Integer numerators of the generator translations of the `k`-th representative. -/
def sgGenTransZ (k : Fin 230) : List (List ℤ) :=
  let e := sgDataList.getD k.val (0, 1, [], 0)
  (List.range (arithGensList.getD e.1 []).length).map fun g =>
    (List.range 3).map fun i => e.2.2.1.getD (3 * g + i) 0

/-- The integer affine generators of the `k`-th representative. -/
def gensZ (k : Fin 230) : List (List ℤ × List ℤ) :=
  List.zip (arithGens (sgArith k)) (sgGenTransZ k)

/-- The (`ℚ`-side) generators of the `k`-th representative, as in `Defs.sgTable`. -/
def gensQ (k : Fin 230) : List (List ℤ × List ℚ) :=
  List.zip (arithGens (sgArith k)) (sgGenTrans k)

theorem gensQ_def (k : Fin 230) :
    gensQ k = List.zip (arithGens (sgArith k)) (sgGenTrans k) := rfl

theorem sgTable_eq (k : Fin 230) : sgTable k = sgClose (gensQ k) 48 [sgOne] := rfl

/-- Generators of the `j`-th arithmetic class as pairs with trivial translation
(`ℚ`-side, matching the definition of `arithRep`). -/
def arithGensQ (j : Fin 73) : List (List ℤ × List ℚ) := (arithGens j).map fun g => (g, [0, 0, 0])

theorem arithRep_eq (j : Fin 73) :
    arithRep j = {A | ∃ p ∈ sgClose (arithGensQ j) 48 [sgOne], A = imatOfList p.1} := rfl

/-- Sarrus rule determinant of a flat matrix. -/
def det9 (l : List ℤ) : ℤ :=
  l.getD 0 0 * (l.getD 4 0 * l.getD 8 0 - l.getD 5 0 * l.getD 7 0)
    - l.getD 1 0 * (l.getD 3 0 * l.getD 8 0 - l.getD 5 0 * l.getD 6 0)
    + l.getD 2 0 * (l.getD 3 0 * l.getD 7 0 - l.getD 4 0 * l.getD 6 0)

/-! ## Elementary matrix facts (proofs by computation on the flat representation) -/

/-- Multiplication of flat matrices corresponds to multiplication of matrices. -/
theorem imatOfList_mul (a b : List ℤ) : imatOfList (m9mul a b) = imatOfList a * imatOfList b := by
  have h3 : (List.range 3) = [0, 1, 2] := rfl
  ext i j
  fin_cases i <;> fin_cases j <;>
    · simp only [imatOfList, m9mul, Matrix.mul_apply, Fin.sum_univ_three, h3,
        List.flatMap_cons, List.flatMap_nil, List.map_cons, List.map_nil, List.sum_cons,
        List.sum_nil, List.cons_append, List.nil_append, List.getD_cons_zero,
        List.getD_cons_succ, Matrix.of_apply, Fin.val_zero, Fin.val_one, Fin.val_two,
        Nat.mul_zero, Nat.add_zero, Nat.zero_mul, Nat.zero_add]
      ring

/-- The flat identity matrix is the identity matrix. -/
theorem imatOfList_one : imatOfList [1, 0, 0, 0, 1, 0, 0, 0, 1] = (1 : IMat) := by
  have h3 : (List.range 3) = [0, 1, 2] := rfl
  ext i j
  fin_cases i <;> fin_cases j <;>
    · simp only [imatOfList, Matrix.one_apply, h3, Matrix.of_apply, List.getD_cons_zero,
        List.getD_cons_succ, Fin.val_zero, Fin.val_one, Fin.val_two, Nat.mul_zero,
        Nat.add_zero, Nat.zero_mul, Nat.zero_add, Fin.ext_iff]
      rfl

/-- The product of two flat matrices has nine entries. -/
theorem length_m9mul (a b : List ℤ) : (m9mul a b).length = 9 := by
  have h3 : (List.range 3) = [0, 1, 2] := rfl
  simp only [m9mul, h3, List.flatMap_cons, List.flatMap_nil, List.map_cons, List.map_nil,
    List.length_cons, List.length_nil, List.length_append]

/-! ## The matrix-level closure attached to a list of flat matrix generators -/

/-- One closure round on flat matrices. -/
def mF (gensM accM : List (List ℤ)) : List (List ℤ) :=
  (accM ++ accM.flatMap fun a => gensM.map fun g => m9mul a g).dedup

/-- The matrix closure obtained by iterating `mF`. -/
def mClose (gensM : List (List ℤ)) : ℕ → List (List ℤ) → List (List ℤ)
  | 0, acc => acc
  | k + 1, acc => mClose gensM k (mF gensM acc)

/-- `l` is a product of generators. -/
def IsWordProd (gensM : List (List ℤ)) (l : List ℤ) : Prop :=
  ∃ w : List (List ℤ),
    (∀ g ∈ w, g ∈ gensM) ∧ w.foldl m9mul [1, 0, 0, 0, 1, 0, 0, 0, 1] = l

/-! ## The integer closure mirroring `sgClose` -/

/-- One closure round on integer affine pairs. -/
def zF (gens : List (List ℤ × List ℤ)) (d : ℕ) (acc : List (List ℤ × List ℤ)) :
    List (List ℤ × List ℤ) :=
  (acc ++ acc.flatMap fun a => gens.map fun g => zMul d a g).dedup

/-- The integer closure of a list of generators (mirror of `sgClose`). -/
def zClose (gens : List (List ℤ × List ℤ)) (d : ℕ) : ℕ → List (List ℤ × List ℤ) →
    List (List ℤ × List ℤ)
  | 0, acc => acc
  | k + 1, acc => zClose gens d k (zF gens d acc)

end Work.SG
