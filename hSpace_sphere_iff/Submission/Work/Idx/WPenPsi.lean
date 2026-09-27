import Mathlib
import Submission.Work.Idx.WPenBlk

/-!
# `Work.Idx.WPenPsi` — the Fourier data `Ψ` of the W pencil

For a coefficient sequence `c : Fin (D+1) → Mₙ(C(X, ℂ))` with polynomial matrix
`wQ n D c z = ∑_j z^j • c_j`, the Fourier data is
`wPsi X n D c m = (2πi)⁻¹ ∮_{|z|=1} z^m • (wQ n D c z)⁻¹ dz`.

The basic relation, proved here, is

  `∑_k c_k * wPsi X n D c (k + p) = if p = -1 then 1 else 0`

which is the "Fourier coefficient of `z ↦ Q(z)·Q(z)⁻¹ = 1`" identity: it is what makes the
correction term `wUpdate` an idempotent Murray–von Neumann equivalent to `1`.  We also record the
compatibility with prepending a zero coefficient:
`wPsi X n (d+1) (preSeq X b) m = wPsi X n d b (m - 1)`.

The analytic core is proved in the abstract setting of a complex Banach algebra `R` (where the
structure is a variable and hence unique), and then instantiated at `Mₙ(C(X, ℂ))`.
-/

namespace Work.Idx

open Matrix MeasureTheory intervalIntegral
open scoped Topology Interval BigOperators

noncomputable section

/-- `z ↦ z^m` is continuous on the unit circle. -/
lemma continuousOn_zpow_sphere (m : ℤ) :
    ContinuousOn (fun z : ℂ => z ^ m) (Metric.sphere (0 : ℂ) 1) := by
  refine ContinuousOn.zpow₀ continuousOn_id m fun z hz => Or.inl ?_
  simp only [id_eq]
  intro h0
  rw [h0] at hz
  simp only [Metric.mem_sphere, dist_zero_right, norm_zero] at hz
  norm_num at hz

/-- The circle integral of `z^p`. -/
lemma circleIntegral_zpow (p : ℤ) :
    (∮ z in C(0, 1), (z ^ p : ℂ)) = if p = -1 then 2 * Real.pi * Complex.I else 0 := by
  by_cases hp : p = -1
  · subst hp
    rw [if_pos rfl]
    have h := circleIntegral.integral_sub_inv_of_mem_ball (c := 0) (w := 0) (R := 1)
      (by simp [Metric.mem_ball, zero_lt_one])
    simpa using h
  · rw [if_neg hp]
    have h := circleIntegral.integral_sub_zpow_of_ne hp (0 : ℂ) (0 : ℂ) 1
    simpa using h

section Abstract

variable {R : Type*} [NormedRing R] [NormedAlgebra ℂ R] [CompleteSpace R]

/-- The inverse of a continuous function which is invertible on the unit circle is continuous
there. -/
lemma continuousOn_ringInverse_of (q : ℂ → R)
    (hcont : ContinuousOn q (Metric.sphere (0 : ℂ) 1))
    (hq : ∀ z : ℂ, ‖z‖ = 1 → IsUnit (q z)) :
    ContinuousOn (fun z : ℂ => Ring.inverse (q z)) (Metric.sphere (0 : ℂ) 1) := by
  intro z hz
  have hz1 : ‖z‖ = 1 := by simpa [Metric.mem_sphere, dist_eq_norm] using hz
  have hzu := hq z hz1
  have h2 : ContinuousAt Ring.inverse (q z) := by
    have h := NormedRing.inverse_continuousAt hzu.unit
    rwa [hzu.unit_spec] at h
  exact h2.comp_continuousWithinAt (hcont z hz)

/-- **The pointwise Fourier identity**, in an abstract Banach algebra. -/
lemma wRow_wPsi_pointwise {D : ℕ} (c : Fin (D + 1) → R) (Q : ℂ → R) (p : ℤ) {z : ℂ}
    (hz0 : z ≠ 0) (hQ : Q z * Ring.inverse (Q z) = 1)
    (hQeq : Q z = ∑ j : Fin (D + 1), (z ^ ((j : ℕ))) • c j) :
    (∑ k : Fin (D + 1), c k * ((z ^ ((k : ℤ) + p)) • Ring.inverse (Q z)))
      = (z ^ p) • (1 : R) := by
  have hexp : ∀ k : Fin (D + 1), z ^ ((k : ℤ) + p) = z ^ (p + 1) * z ^ ((k : ℤ) - 1) := by
    intro k
    have h : (p + 1) + ((k : ℤ) - 1) = (k : ℤ) + p := by ring
    rw [← h, zpow_add₀ hz0]
  have hexp2 : ∀ k : Fin (D + 1), z ^ ((k : ℤ) - 1) = z ^ (-1 : ℤ) * z ^ ((k : ℤ)) := by
    intro k
    have h : (-1 : ℤ) + (k : ℤ) = (k : ℤ) - 1 := by ring
    rw [← h, zpow_add₀ hz0]
  calc (∑ k : Fin (D + 1), c k * ((z ^ ((k : ℤ) + p)) • Ring.inverse (Q z)))
      = ∑ k : Fin (D + 1), (z ^ ((k : ℤ) + p)) • (c k * Ring.inverse (Q z)) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [mul_smul_comm]
    _ = (∑ k : Fin (D + 1), ((z ^ ((k : ℤ) + p)) • c k) * Ring.inverse (Q z)) := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [smul_mul_assoc]
    _ = (∑ k : Fin (D + 1), (z ^ ((k : ℤ) + p)) • c k) * Ring.inverse (Q z) := by
        rw [Finset.sum_mul]
    _ = (z ^ (p + 1) • (∑ k : Fin (D + 1), (z ^ ((k : ℤ) - 1)) • c k)) *
          Ring.inverse (Q z) := by
        congr 2
        rw [Finset.smul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [hexp k, smul_smul]
    _ = (z ^ (p + 1) • (z ^ (-1 : ℤ) • (∑ k : Fin (D + 1), (z ^ ((k : ℤ))) • c k))) *
          Ring.inverse (Q z) := by
        congr 2
        rw [Finset.smul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [hexp2 k, smul_smul]
    _ = (z ^ (p + 1) • (z ^ (-1 : ℤ) • Q z)) * Ring.inverse (Q z) := by
        congr 3
        rw [hQeq]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [zpow_natCast]
    _ = (z ^ (p + 1)) • ((z ^ (-1 : ℤ)) • (1 : R)) := by
        rw [smul_mul_assoc, smul_mul_assoc, hQ]
    _ = (z ^ p) • (1 : R) := by
        rw [smul_smul, ← zpow_add₀ hz0]
        congr 2
        ring

/-- **The Fourier relation**, in an abstract Banach algebra: for `Q z = ∑_j z^j • c_j` invertible
on the unit circle, `∑_k c_k * (2πi)⁻¹ ∮ z^p • Q(z)⁻¹ dz = δ_{p,-1}`. -/
theorem wRow_wPsi_gen {D : ℕ} (c : Fin (D + 1) → R) (Q : ℂ → R)
    (hQeq : ∀ z : ℂ, Q z = ∑ j : Fin (D + 1), (z ^ ((j : ℕ))) • c j)
    (hcont : ContinuousOn Q (Metric.sphere (0 : ℂ) 1))
    (hQ : ∀ z : ℂ, ‖z‖ = 1 → IsUnit (Q z)) (p : ℤ) :
    (∑ k : Fin (D + 1), c k * ((2 * Real.pi * Complex.I)⁻¹ •
        ∮ z in C(0, 1), (z ^ ((k : ℤ) + p)) • Ring.inverse (Q z)))
      = if p = -1 then 1 else 0 := by
  have hcontE := continuousOn_ringInverse_of Q hcont hQ
  have hzpow : ContinuousOn (fun z : ℂ => z ^ p) (Metric.sphere (0 : ℂ) 1) :=
    continuousOn_zpow_sphere p
  have hI : ∀ m : ℤ, CircleIntegrable (fun z : ℂ => (z ^ m) • Ring.inverse (Q z)) 0 1 := by
    intro m
    exact ContinuousOn.circleIntegrable zero_le_one
      ((continuousOn_zpow_sphere m).smul hcontE)
  have hstep : ∀ k : Fin (D + 1),
      c k * ((2 * Real.pi * Complex.I)⁻¹ • ∮ z in C(0, 1), (z ^ ((k : ℤ) + p)) • Ring.inverse (Q z))
        = (2 * Real.pi * Complex.I)⁻¹ •
            ∮ z in C(0, 1), c k * ((z ^ ((k : ℤ) + p)) • Ring.inverse (Q z)) := by
    intro k
    rw [mul_smul_comm]
    congr 1
    exact (Work.KT.Fund.circleIntegral_const_mul (c k) _ 0 1 (hI ((k : ℤ) + p))).symm
  have hint : ∀ k ∈ (Finset.univ : Finset (Fin (D + 1))),
      CircleIntegrable (fun z : ℂ => c k * ((z ^ ((k : ℤ) + p)) • Ring.inverse (Q z))) 0 1 := by
    intro k _
    exact ContinuousOn.circleIntegrable zero_le_one
      (continuousOn_const.mul ((continuousOn_zpow_sphere _).smul hcontE))
  rw [Finset.sum_congr rfl fun k _ => hstep k, ← Finset.smul_sum]
  rw [show (∑ k : Fin (D + 1), ∮ z in C(0, 1), c k * ((z ^ ((k : ℤ) + p)) • Ring.inverse (Q z)))
      = ∮ z in C(0, 1), ∑ k : Fin (D + 1), c k * ((z ^ ((k : ℤ) + p)) • Ring.inverse (Q z))
      from (circleIntegral.integral_fun_sum (s := Finset.univ) (c := 0) (R := 1) hint).symm]
  rw [circleIntegral.integral_congr zero_le_one fun z hz => ?_]
  · rw [circleIntegral.integral_smul_const, circleIntegral_zpow]
    by_cases hp : p = -1
    · rw [if_pos hp, if_pos hp, smul_smul, inv_mul_cancel₀ (by
        simp [Complex.I_ne_zero, Real.pi_ne_zero]), one_smul]
    · rw [if_neg hp, if_neg hp]
      simp
  · have hz1 : ‖z‖ = 1 := by simpa [Metric.mem_sphere, dist_eq_norm] using hz
    have hz0 : z ≠ 0 := by
      intro h0
      rw [h0] at hz1
      simp at hz1
    exact wRow_wPsi_pointwise c Q p hz0 (Ring.mul_inverse_cancel _ (hQ z hz1)) (hQeq z)

end Abstract

variable (X : Type) [TopologicalSpace X] [CompactSpace X] [T2Space X]

/-- `z ↦ wQ n D c z` is continuous. -/
lemma continuous_wQ (n D : ℕ) (c : Fin (D + 1) → Matrix (Fin n) (Fin n) C(X, ℂ)) :
    Continuous fun z : ℂ => wQ (A := C(X, ℂ)) n D c z := by
  unfold wQ
  exact continuous_finset_sum _ fun j _ =>
    Continuous.smul (continuous_id.pow ((j : ℕ))) continuous_const

/-- **The Fourier relation.** `∑_k c_k * Ψ_{k+p} = δ_{p,-1}`. -/
theorem wRow_wPsi (n D : ℕ) (c : Fin (D + 1) → Matrix (Fin n) (Fin n) C(X, ℂ))
    (hQ : ∀ z : ℂ, ‖z‖ = 1 → IsUnit (wQ (A := C(X, ℂ)) n D c z)) (p : ℤ) :
    (∑ k : Fin (D + 1), c k * wPsi X n D c ((k : ℤ) + p)) = if p = -1 then 1 else 0 := by
  letI : NormedRing (Matrix (Fin n) (Fin n) C(X, ℂ)) := Matrix.linftyOpNormedRing
  letI : NormedAlgebra ℂ (Matrix (Fin n) (Fin n) C(X, ℂ)) := Matrix.linftyOpNormedAlgebra
  letI : CompleteSpace (Matrix (Fin n) (Fin n) C(X, ℂ)) := Matrix.instCompleteSpace _ _ _
  have hQeq : ∀ z : ℂ, wQ (A := C(X, ℂ)) n D c z
      = ∑ j : Fin (D + 1), (z ^ ((j : ℕ))) • c j := fun z => rfl
  have hcont : ContinuousOn (fun z : ℂ => wQ (A := C(X, ℂ)) n D c z)
      (Metric.sphere (0 : ℂ) 1) := (continuous_wQ X n D c).continuousOn
  have key := @wRow_wPsi_gen (Matrix (Fin n) (Fin n) C(X, ℂ)) Matrix.linftyOpNormedRing
      Matrix.linftyOpNormedAlgebra (Matrix.instCompleteSpace (Fin n) (Fin n) C(X, ℂ)) D c
      (fun z => wQ (A := C(X, ℂ)) n D c z) hQeq hcont hQ p
  simpa only [wPsi] using key

end

end Work.Idx
