import Mathlib
import Submission.Work.Idx.WPenBlk

namespace Work.Idx

open Matrix MeasureTheory intervalIntegral
open scoped Topology Interval

set_option linter.style.haveILetI false

noncomputable section

section Algebra

/-- The totalized inverse of a scalar multiple in a complex algebra: for `z ≠ 0` the scalar
`z • 1` is a unit with inverse `z⁻¹ • 1`, so `Ring.inverse (z • x) = z⁻¹ • Ring.inverse x`;
for `z = 0` both sides vanish. -/
lemma ringInverse_smul {R : Type*} [Ring R] [Algebra ℂ R] (z : ℂ) (x : R) :
    Ring.inverse (z • x) = z⁻¹ • Ring.inverse x := by
  rw [Algebra.smul_def]
  by_cases hz : z = 0
  · subst hz; simp
  · have hu : IsUnit (algebraMap ℂ R z) := (isUnit_iff_ne_zero.mpr hz).map (algebraMap ℂ R)
    have h2 : Ring.inverse (algebraMap ℂ R z) = algebraMap ℂ R z⁻¹ := by
      calc Ring.inverse (algebraMap ℂ R z)
          = Ring.inverse (algebraMap ℂ R z) * 1 := (mul_one _).symm
        _ = Ring.inverse (algebraMap ℂ R z) * (algebraMap ℂ R z * algebraMap ℂ R z⁻¹) := by
              rw [← map_mul, mul_inv_cancel₀ hz, map_one]
        _ = (Ring.inverse (algebraMap ℂ R z) * algebraMap ℂ R z) * algebraMap ℂ R z⁻¹ := by
              rw [mul_assoc]
        _ = 1 * algebraMap ℂ R z⁻¹ := by rw [Ring.inverse_mul_cancel _ hu]
        _ = algebraMap ℂ R z⁻¹ := one_mul _
    rw [Ring.inverse_mul (Or.inl hu), h2, Algebra.smul_def, Algebra.commutes]

end Algebra

section Banach

variable {R : Type*} [NormedRing R] [NormedAlgebra ℂ R]

/-- **The circle-integral form of the shift.**  For any `Q : ℂ → R` with values in a complex
Banach algebra, the integrand `z ↦ z^m • (z • Q z)⁻¹` has the same circle integral as
`z ↦ z^{m-1} • (Q z)⁻¹`: pointwise on the unit circle (`z ≠ 0`) the scalar `z` can be pulled out
of the totalized inverse and cancelled against `z^m`. -/
lemma circleIntegral_shift (Q : ℂ → R) (m : ℤ) :
    (2 * Real.pi * Complex.I)⁻¹ • (∮ z in C(0, 1), (z ^ m) • Ring.inverse (z • Q z)) =
      (2 * Real.pi * Complex.I)⁻¹ • (∮ z in C(0, 1), (z ^ (m - 1)) • Ring.inverse (Q z)) := by
  have h : (∮ z in C(0, 1), (z ^ m) • Ring.inverse (z • Q z))
      = ∮ z in C(0, 1), (z ^ (m - 1)) • Ring.inverse (Q z) := by
    refine circleIntegral.integral_congr zero_le_one fun z hz => ?_
    have hz1 : ‖z‖ = 1 := by simpa [Metric.mem_sphere, dist_eq_norm] using hz
    have hz0 : z ≠ 0 := by intro h0; rw [h0] at hz1; simp at hz1
    rw [ringInverse_smul, smul_smul]
    have hpow : z ^ (m - 1) = z ^ m * z⁻¹ := by
      rw [zpow_sub₀ hz0 m 1, zpow_one, div_eq_mul_inv]
    rw [hpow]
  rw [h]

end Banach

variable (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]

/-- Prepending a zero coefficient multiplies the polynomial matrix by `z`:
`wQ n (d+1) (preSeq X b) z = z • wQ n d b z`. -/
lemma wQ_preSeq (n d : ℕ) (b : Fin (d + 1) → Matrix (Fin n) (Fin n) C(X, ℂ)) (z : ℂ) :
    wQ (A := C(X, ℂ)) n (d + 1) (Work.KT.Idx.preSeq X b) z
      = z • wQ (A := C(X, ℂ)) n d b z := by
  have key : (∑ j : Fin (d + 2), (z : ℂ) ^ (j : ℕ) • Work.KT.Idx.preSeq X b j)
      = z • (∑ i : Fin (d + 1), (z : ℂ) ^ (i : ℕ) • b i) := by
    conv_lhs => rw [Fin.sum_univ_succ]
    rw [show (z : ℂ) ^ ((0 : Fin (d + 2)) : ℕ) • Work.KT.Idx.preSeq X b 0 = 0 from by
          rw [Work.KT.Idx.preSeq_apply, dif_neg (by simp)]; simp]
    rw [zero_add]
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hfin : (⟨((i.succ : Fin (d + 2)) : ℕ) - 1, by omega⟩ : Fin (d + 1)) = i := by
      ext; simp [Fin.val_succ]
    rw [Work.KT.Idx.preSeq_apply, dif_pos (by simp [Fin.val_succ]), hfin]
    show (z : ℂ) ^ ((i.succ : Fin (d + 2)) : ℕ) • b i = z • (z : ℂ) ^ (i : ℕ) • b i
    rw [Fin.val_succ, pow_succ', smul_smul]
  simpa only [wQ] using key

/-- **Prepending a zero coefficient shifts the Fourier data.**  For the coefficient sequence
`Work.KT.Idx.preSeq X b = (0, b₀, …, b_d)` (i.e. the polynomial `z · q_b`), whose Fourier data is
`wPsi X n (d+1) (preSeq X b)`, one has `Ψ^{(preSeq b)}_m = Ψ^{(b)}_{m-1}` for every `m : ℤ`.

Route.  `wQ n (d+1) (preSeq X b) z = z • wQ n d b z` (shift the sum with `Fin.sum_univ_succ`), and
for `z ≠ 0` the totalized inverse of a scalar multiple is
`Ring.inverse (z • x) = z⁻¹ • Ring.inverse x` (if `x` is a unit this is `(z•x)⁻¹ = z⁻¹x⁻¹`; if not
then `z • x` is not a unit either and both sides are `0`).  Hence
`z^m • Ring.inverse (z • wQ n d b z) = z^{m-1} • Ring.inverse (wQ n d b z)` on the unit circle
(`z ≠ 0` there), and `circleIntegral.integral_congr` gives the claim.  The hypothesis `hQ` is
available from the caller; the identity itself needs no invertibility hypothesis. -/
theorem wPsi_preSeq {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X]
    (n d : ℕ) (b : Fin (d + 1) → Matrix (Fin n) (Fin n) C(X, ℂ))
    (hQ : ∀ z : ℂ, ‖z‖ = 1 → IsUnit (wQ (A := C(X, ℂ)) n d b z)) (m : ℤ) :
    wPsi X n (d + 1) (Work.KT.Idx.preSeq X b) m = wPsi X n d b (m - 1) := by
  letI : NormedRing (Matrix (Fin n) (Fin n) C(X, ℂ)) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℂ (Matrix (Fin n) (Fin n) C(X, ℂ)) := Matrix.linftyOpNormedAlgebra
  letI : CompleteSpace (Matrix (Fin n) (Fin n) C(X, ℂ)) := Matrix.instCompleteSpace _ _ _
  have key := @circleIntegral_shift (Matrix (Fin n) (Fin n) C(X, ℂ))
    Matrix.linftyOpNormedRing Matrix.linftyOpNormedAlgebra
    (fun z => wQ (A := C(X, ℂ)) n d b z) m
  simpa only [wPsi, wQ_preSeq] using key

end

end Work.Idx
