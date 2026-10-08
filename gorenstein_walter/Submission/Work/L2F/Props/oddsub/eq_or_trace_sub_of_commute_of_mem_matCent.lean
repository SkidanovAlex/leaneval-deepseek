import Mathlib
import Submission.Work.L2F.Props.oddsub.NoUnipotentDefs
import Submission.Work.L2F.Props.oddsub.eq_or_trace_sub_of_commute

/-!
# `MatCent`-elements with equal trace and determinant are equal or reflections of one another

Let `A ≤ SL(2,F)` and suppose every nonzero element of the commutant `MatCent A` is invertible
(`hinv`).  If `a, b ∈ MatCent A` commute with each other and have the same trace and determinant,
then `b = a` or `b = a.trace • 1 - a`.

The proof is a direct computation that never uses the invertibility of `a` or `b` itself, only the
invertibility of the two "difference" matrices.  Put

* `A := b - a`  (so `A = 0` is the first alternative), and
* `B := b - (a.trace • 1 - a)`  (so `B = 0` is the second alternative).

Both are in `MatCent A` (the commutant is closed under subtraction, and scalar matrices are
central), both have trace `0`, and Cayley–Hamilton for `2 × 2` matrices together with
`b * a = a * b`, `tr a = tr b`, `det a = det b` gives `A * B = 0` and `B * A = 0`.  Hence if both
`A` and `B` were nonzero, the fact that `A` is traceless and `A * B = 0` with `B ≠ 0` forces
`det A = 0`, contradicting `hinv A`; so `A = 0` or `B = 0`, which is the claim.
-/

open scoped MatrixGroups
open Matrix

namespace Work.L2F.Props.oddsub

/-- The commutant `MatCent A` is closed under subtraction. -/
theorem matCent_sub {F : Type*} [Field F]
    (A : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F))
    {M N : Matrix (Fin 2) (Fin 2) F} (hM : MatCent A M) (hN : MatCent A N) :
    MatCent A (M - N) := by
  intro g hg
  have h1 : M * (g : Matrix (Fin 2) (Fin 2) F) = (g : Matrix (Fin 2) (Fin 2) F) * M := hM g hg
  have h2 : N * (g : Matrix (Fin 2) (Fin 2) F) = (g : Matrix (Fin 2) (Fin 2) F) * N := hN g hg
  simp only [Matrix.sub_mul, Matrix.mul_sub, h1, h2]

/-- Every scalar matrix lies in the commutant `MatCent A`. -/
theorem matCent_smul_one {F : Type*} [Field F]
    (A : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F)) (c : F) :
    MatCent A (c • (1 : Matrix (Fin 2) (Fin 2) F)) := by
  intro g hg
  rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]

theorem eq_or_trace_sub_of_commute_of_mem_matCent (F : Type*) [Field F]
    (A : Subgroup (Matrix.SpecialLinearGroup (Fin 2) F))
    {a b : Matrix (Fin 2) (Fin 2) F}
    (ha : Work.L2F.Props.oddsub.MatCent A a) (hb : Work.L2F.Props.oddsub.MatCent A b)
    (hab : b * a = a * b) (htr : a.trace = b.trace) (hdet : a.det = b.det)
    (hinv : ∀ M : Matrix (Fin 2) (Fin 2) F,
      Work.L2F.Props.oddsub.MatCent A M → M ≠ 0 → M.det ≠ 0) :
    b = a ∨ b = a.trace • (1 : Matrix (Fin 2) (Fin 2) F) - a := by
  -- Cayley–Hamilton for `a` and for `b` (the latter rewritten through `htr`, `hdet`).
  have haa : a * a = a.trace • a - a.det • (1 : Matrix (Fin 2) (Fin 2) F) :=
    Work.L2F.Mat2.sq_eq_trace_smul_sub_det F a
  have hbb : b * b = a.trace • b - a.det • (1 : Matrix (Fin 2) (Fin 2) F) := by
    have h := Work.L2F.Mat2.sq_eq_trace_smul_sub_det F b
    rw [← htr, ← hdet] at h
    exact h
  -- The two difference matrices are traceless.
  have htrA : (b - a).trace = 0 := by rw [Matrix.trace_sub, htr, sub_self]
  have htrB : (b - (a.trace • (1 : Matrix (Fin 2) (Fin 2) F) - a)).trace = 0 := by
    simp only [Matrix.trace_sub, Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin, htr]
    ring
  -- ... and they annihilate each other in both orders.
  have hAB : (b - a) * (b - (a.trace • (1 : Matrix (Fin 2) (Fin 2) F) - a)) = 0 := by
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.mul_one, hab, hbb, haa]
    module
  have hBA : (b - (a.trace • (1 : Matrix (Fin 2) (Fin 2) F) - a)) * (b - a) = 0 := by
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.smul_mul, Matrix.one_mul, hab, hbb, haa]
    module
  -- Both differences lie in the commutant.
  have hAmem : MatCent A (b - a) := matCent_sub A hb ha
  have hscal : MatCent A (a.trace • (1 : Matrix (Fin 2) (Fin 2) F)) := matCent_smul_one A a.trace
  have hBmem : MatCent A (b - (a.trace • (1 : Matrix (Fin 2) (Fin 2) F) - a)) :=
    matCent_sub A hb (matCent_sub A hscal ha)
  -- At least one of the two differences vanishes.
  have key : b - a = 0 ∨ b - (a.trace • (1 : Matrix (Fin 2) (Fin 2) F) - a) = 0 := by
    by_contra h
    simp only [not_or] at h
    obtain ⟨hA0, hB0⟩ := h
    have hdetA : (b - a).det = 0 :=
      det_eq_zero_of_traceless_mul_eq_zero htrA hAB hB0
    exact hinv (b - a) hAmem hA0 hdetA
  rcases key with h | h
  · left; exact sub_eq_zero.mp h
  · right; exact sub_eq_zero.mp h

end Work.L2F.Props.oddsub
