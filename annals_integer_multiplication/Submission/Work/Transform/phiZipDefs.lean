import Mathlib
import Submission.Work.Transform.phiAux

/-!
# Shared vocabulary for `Work.Transform.phiZipWord` (paper Prop 3.5, `T̃`)

`phiZipWord` zips the two block lists `a`, `b` of an `R`-array (`KernelLib.zipWith`), each pair of
blocks being combined coefficient by coefficient (`KernelLib.zipWith` again, with the one-element
product word `Work.Transform.cfxMulWord`).  This module collects what the two halves of that proof
share:

* injectivity of `ofList`, `cvecVal`, `rarrVal`, and the index lemmas `map_getD_nil`,
  `cvecVal_getD`, `cfxVal_getD` for `(l.map f).getD i .nil`;
* the pointwise predicates `PhiZP` (the per-pair precondition: both values are `cvecVal`s of
  `C̃◦`-vectors) and `PhiZQ` (the per-pair postcondition: `z = cvecVal ws` with `ws ∈ C̃◦^r` and
  `2^p ‖w̃ - b̃ * ã‖ < 2`), in the witness order used by the extractions (`ws` first);
* the arithmetic lemma `phiZipCost` turning the outer zip's cost
  `M * (c + K * (L + 1)) + K` (`c = K * (r p²) + K`, `L = 200 (r p² + 1)`) into
  `K' * (M * r * p²) + K'`.
-/

set_option autoImplicit false

namespace Work.Transform

open HvdH

/-! ## Injectivity of the value constructors -/

theorem ofList_injective : Function.Injective (ofList : List Val → Val) := by
  intro l
  induction l with
  | nil =>
    intro m h
    cases m with
    | nil => rfl
    | cons y ys => simp [ofList] at h
  | cons x xs ih =>
    intro m h
    cases m with
    | nil => simp [ofList] at h
    | cons y ys =>
      have h' : x = y ∧ ofList xs = ofList ys := by simpa [ofList, Val.cons.injEq] using h
      rw [h'.1, ih h'.2]

theorem cvecVal_injective : Function.Injective cvecVal := by
  intro u v h
  have h2 : u.map cfxVal = v.map cfxVal := ofList_injective h
  exact List.map_injective_iff.mpr (fun a b hab => cfxVal_injective hab) h2

theorem ofList_map_cvecVal_injective {A B : List (List (ℤ × ℤ))}
    (h : ofList (A.map cvecVal) = ofList (B.map cvecVal)) : A = B :=
  List.map_injective_iff.mpr cvecVal_injective (ofList_injective h)

theorem rarrVal_injective : Function.Injective rarrVal := fun _ _ h =>
  ofList_map_cvecVal_injective h

/-! ## Index lemmas -/

/-- Reading the `i`-th value of `l.map f` below the length. -/
theorem map_getD_nil {α : Type} [Inhabited α] (f : α → Val) (l : List α) {i : ℕ}
    (h : i < l.length) : (l.map f).getD i .nil = f (l.getD i (default : α)) := by
  rw [List.getD_eq_getElem _ _ (by simpa using h), List.getElem_map, List.getD_eq_getElem _ _ h]

theorem cvecVal_getD {l : List (List (ℤ × ℤ))} {i : ℕ} (h : i < l.length) :
    (l.map cvecVal).getD i .nil = cvecVal (l.getD i []) := by
  rw [List.getD_eq_getElem _ _ (by simpa using h), List.getElem_map, List.getD_eq_getElem _ _ h]

theorem cfxVal_getD {l : List (ℤ × ℤ)} {i : ℕ} (h : i < l.length) :
    (l.map cfxVal).getD i .nil = cfxVal (l.getD i (0, 0)) := by
  rw [List.getD_eq_getElem _ _ (by simpa using h), List.getElem_map, List.getD_eq_getElem _ _ h]

/-! ## The pointwise predicates of the two zip levels -/

/-- Per-pair precondition of the outer (`M`-block) zip: both values are `cvecVal`s of
`C̃◦`-vectors of length `r`. -/
def PhiZP (p r : ℕ) (x y : Val) : Prop :=
  ∃ pa pb : List (ℤ × ℤ), x = cvecVal pa ∧ y = cvecVal pb ∧ InDiscVec p r pa ∧ InDiscVec p r pb

/-- Per-pair postcondition of the outer zip: `z = cvecVal ws` with `ws ∈ C̃◦^r` and
`2^p ‖w̃ - b̃ * ã‖ < 2` (`x` carries `a`'s block, `y` carries `b`'s block).  The output vector `ws`
is the *first* witness so that `Classical.choose` of an inhabitant returns it. -/
def PhiZQ (p r : ℕ) (x y z : Val) : Prop :=
  ∃ (ws pa pb : List (ℤ × ℤ)), z = cvecVal ws ∧ x = cvecVal pa ∧ y = cvecVal pb ∧
    InDiscVec p r ws ∧ ∀ c < r, (2 : ℝ) ^ p * ‖fxC p (ws.getD c (0, 0))
      - fxC p (pb.getD c (0, 0)) * fxC p (pa.getD c (0, 0))‖ < 2

/-! ## Cost arithmetic -/

/-- The outer zip's cost `M * (c + K * (L + 1)) + K` with `c = K * (r p²) + K` and
`L = 200 * (r p² + 1)` is bounded by `K' * (M * r * p²) + K'` with `K' = 2 * K + 401 * Kz + 1`. -/
theorem phiZipCost (KB Kz M r p : ℕ) (hp : 100 ≤ p) (hr : 2 ≤ r) :
    M * ((KB * (r * p ^ 2) + KB) + Kz * (200 * (r * p ^ 2 + 1) + 1)) + Kz
      ≤ (2 * KB + 401 * Kz + 1) * ((M * r) * p ^ 2) + (2 * KB + 401 * Kz + 1) := by
  have hrp : 1 ≤ r * p ^ 2 := by nlinarith
  have h2 : (M * r) * p ^ 2 = M * (r * p ^ 2) := by ring
  rw [h2]
  nlinarith [Nat.zero_le KB, Nat.zero_le Kz, Nat.zero_le M,
    Nat.mul_le_mul_right (M * (r * p ^ 2)) (Nat.zero_le KB),
    Nat.mul_le_mul_left Kz hrp, Nat.mul_le_mul_left KB hrp, Nat.mul_le_mul_left M hrp]

end Work.Transform
