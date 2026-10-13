import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EllSol.PkgK5.radialAuxAng

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-!
# Radial profiles vs. their `sin (2θ)`-multiples: the angular integrals

Part 3 of the proof of `Work.FTS.EllSol.PkgK5.radialHkNorm_le_sinMul`: the explicit angular
constants (`Φ`, `A_η`, `A_{2-η}`, `B(α,i)`, `W`), their continuity and the uniform estimates
for the angular coefficients of the mixed slots.
-/

namespace Work.FTS.EllSol.PkgK5

namespace Radial

/-! ## Integrability and positivity of the angular integrals -/

/-- `sin(2·)^p` is integrable on `Iθ` for `-1 < p ≤ 2`. -/
theorem integrable_sin_rpow {p : ℝ} (hp1 : -1 < p) (hp2 : p ≤ 2) :
    Integrable (fun θ : ℝ => Real.sin (2 * θ) ^ p) (volume.restrict Work.Spaces.Iθ) := by
  rcases le_or_gt p 0 with hp | hp
  · exact (Work.Spaces.sin_two_rpow p hp1 hp).1
  · refine MeasureTheory.IntegrableOn.of_bound (C := 1) ?_ ?_ ?_
    · rw [Work.Spaces.Iθ, Real.volume_Icc]; exact ENNReal.ofReal_lt_top
    · exact (measurable_sin2_rpow p).aestronglyMeasurable
    · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => ?_)
      rw [Real.norm_of_nonneg (Real.rpow_nonneg (sin_two_nonneg hθ) p)]
      exact Real.rpow_le_one (sin_two_nonneg hθ) (sin_two_le_one θ) hp.le

/-- `∫_θ sin(2θ)^p ≤ 100` for `p ≥ 0` (the integrand is bounded by `1`). -/
theorem integral_sin_rpow_le {p : ℝ} (hp0 : 0 ≤ p) :
    (∫ θ in Work.Spaces.Iθ, Real.sin (2 * θ) ^ p) ≤ 100 := by
  have hmono : (∫ θ in Work.Spaces.Iθ, Real.sin (2 * θ) ^ p)
      ≤ ∫ θ in Work.Spaces.Iθ, (1 : ℝ) := by
    refine MeasureTheory.integral_mono_of_nonneg ?_ ?_ ?_
    · exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
        (fun θ hθ => Real.rpow_nonneg (sin_two_nonneg hθ) p)
    · refine MeasureTheory.IntegrableOn.of_bound (C := 1) ?_ ?_ ?_
      · rw [Work.Spaces.Iθ, Real.volume_Icc]; exact ENNReal.ofReal_lt_top
      · exact aestronglyMeasurable_const
      · filter_upwards with θ; simp
    · exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
        (fun θ hθ => Real.rpow_le_one (sin_two_nonneg hθ) (sin_two_le_one θ) hp0)
  have hone : (∫ θ in Work.Spaces.Iθ, (1 : ℝ)) = Real.pi / 2 := by
    rw [MeasureTheory.setIntegral_const]
    simp only [smul_eq_mul, mul_one, MeasureTheory.measureReal_def, Work.Spaces.Iθ,
      Real.volume_Icc]
    rw [ENNReal.toReal_ofReal (by linarith [Real.pi_pos])]
    ring
  rw [hone] at hmono
  linarith [Real.pi_lt_four]

/-- `0 < ∫_θ sin(2θ)^p` for `-1 < p ≤ 2`. -/
theorem sin_rpow_pos {p : ℝ} (hp1 : -1 < p) (hp2 : p ≤ 2) :
    0 < ∫ θ in Work.Spaces.Iθ, Real.sin (2 * θ) ^ p := by
  have hint : Integrable (fun θ : ℝ => Real.sin (2 * θ) ^ p)
      (volume.restrict (Set.Icc 0 (Real.pi / 2))) := integrable_sin_rpow hp1 hp2
  rw [show Work.Spaces.Iθ = Set.Icc 0 (Real.pi / 2) from rfl]
  rw [MeasureTheory.setIntegral_pos_iff_support_of_nonneg_ae
    (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
      (fun θ hθ => Real.rpow_nonneg (sin_two_nonneg hθ) p)) hint]
  have hsub : Set.Ioo 0 (Real.pi / 2)
      ⊆ Function.support (fun θ : ℝ => Real.sin (2 * θ) ^ p) ∩ Set.Icc 0 (Real.pi / 2) := by
    intro θ hθ
    exact ⟨(Real.rpow_pos_of_pos (Real.sin_pos_of_mem_Ioo
      ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩) p).ne', hθ.1.le, hθ.2.le⟩
  refine lt_of_lt_of_le ?_ (measure_mono hsub)
  rw [Real.volume_Ioo]
  exact ENNReal.ofReal_pos.mpr (by linarith [Real.pi_pos])

/-! ## The weighted diagonal sum and the angular constants -/

/-- The diagonal weight-sum of the radial derivatives:
`Φ z = ∑_{j ≤ k} (D^jΛ(z) · w(z))²`. -/
def Phi (k : ℕ) (Λ : ℝ → ℝ) (z : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (k + 1), (RIter j Λ z * Work.Spaces.w z) ^ 2

theorem Phi_nonneg (k : ℕ) (Λ : ℝ → ℝ) (z : ℝ) : 0 ≤ Phi k Λ z :=
  Finset.sum_nonneg fun j _ => sq_nonneg _

theorem continuousOn_Phi (k : ℕ) (Λ : ℝ → ℝ)
    (hΛ : ∀ n : ℕ, ContDiffOn ℝ n Λ (Set.Ioi 0)) :
    ContinuousOn (fun z => Phi k Λ z) (Set.Ioi 0) := by
  show ContinuousOn (fun z => ∑ j ∈ Finset.range (k + 1),
    (RIter j Λ z * Work.Spaces.w z) ^ 2) (Set.Ioi 0)
  refine continuousOn_finsetSum _ (fun j hj => ?_)
  exact ((continuousOn_RIter Λ hΛ j).mul continuousOn_w).pow 2

/-- `A₁ = ∫_θ sin(2θ)^{-η}`. -/
def Aeta : ℝ := ∫ θ in Work.Spaces.Iθ, Real.sin (2 * θ) ^ (-Work.Spaces.eta)

/-- `A₂ = ∫_θ sin(2θ)^{2-η}`. -/
def Aeta2 : ℝ := ∫ θ in Work.Spaces.Iθ, Real.sin (2 * θ) ^ (2 - Work.Spaces.eta)

/-- `B(α,i) = ∫_θ (D_θ^i sin 2·)² sin(2θ)^{-γ}`. -/
def Bcoef (α : ℝ) (i : ℕ) : ℝ :=
  ∫ θ in Work.Spaces.Iθ,
    (Work.FTS.EllipticEst.LopIter i (fun θ : ℝ => Real.sin (2 * θ)) θ) ^ 2
      * Real.sin (2 * θ) ^ (-(Work.Spaces.gam α))

/-- The mixed-slot contribution to the `θ`-integral of `HkIntegrand` of `Λ·sin 2·`. -/
def W (α : ℝ) (k : ℕ) (Λ : ℝ → ℝ) (z : ℝ) : ℝ :=
  ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
    if 1 ≤ i ∧ i + j ≤ k then (RIter j Λ z * Work.Spaces.w z) ^ 2 * Bcoef α i else 0

theorem Bcoef_nonneg (α : ℝ) (i : ℕ) : 0 ≤ Bcoef α i := by
  rw [Bcoef]
  refine MeasureTheory.integral_nonneg_of_ae
    (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => ?_))
  exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (sin_two_nonneg hθ) _)

theorem W_nonneg (α : ℝ) (k : ℕ) (Λ : ℝ → ℝ) (z : ℝ) : 0 ≤ W α k Λ z := by
  refine Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => ?_
  split_ifs with h
  · exact mul_nonneg (sq_nonneg _) (Bcoef_nonneg α i)
  · exact le_refl 0

theorem continuousOn_W (α : ℝ) (k : ℕ) (Λ : ℝ → ℝ)
    (hΛ : ∀ n : ℕ, ContDiffOn ℝ n Λ (Set.Ioi 0)) :
    ContinuousOn (fun z => W α k Λ z) (Set.Ioi 0) := by
  show ContinuousOn (fun z => ∑ i ∈ Finset.range (k + 1), ∑ j ∈ Finset.range (k + 1),
    (if 1 ≤ i ∧ i + j ≤ k then (RIter j Λ z * Work.Spaces.w z) ^ 2 * Bcoef α i else 0))
    (Set.Ioi 0)
  refine continuousOn_finsetSum _ (fun i hi => ?_)
  refine continuousOn_finsetSum _ (fun j hj => ?_)
  by_cases h : 1 ≤ i ∧ i + j ≤ k
  · have hfun : (fun z : ℝ => (if 1 ≤ i ∧ i + j ≤ k then
        (RIter j Λ z * Work.Spaces.w z) ^ 2 * Bcoef α i else 0))
        = fun z : ℝ => (RIter j Λ z * Work.Spaces.w z) ^ 2 * Bcoef α i := by
      funext z; rw [if_pos h]
    rw [hfun]
    exact (((continuousOn_RIter Λ hΛ j).mul continuousOn_w).pow 2).mul continuousOn_const
  · have hfun : (fun z : ℝ => (if 1 ≤ i ∧ i + j ≤ k then
        (RIter j Λ z * Work.Spaces.w z) ^ 2 * Bcoef α i else 0))
        = fun _ : ℝ => (0 : ℝ) := by
      funext z; rw [if_neg h]
    rw [hfun]
    exact continuousOn_const

/-- `W z ≤ (∑_i B(α,i)) · Φ z`. -/
theorem W_le_sum_Bcoef_mul_Phi (α : ℝ) (k : ℕ) (Λ : ℝ → ℝ) (z : ℝ) :
    W α k Λ z ≤ (∑ i ∈ Finset.range (k + 1), Bcoef α i) * Phi k Λ z := by
  rw [W, Phi, Finset.sum_mul]
  refine Finset.sum_le_sum (fun i hi => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum (fun j hj => ?_)
  by_cases h : 1 ≤ i ∧ i + j ≤ k
  · rw [if_pos h]; exact le_of_eq (mul_comm _ _)
  · rw [if_neg h]; exact mul_nonneg (Bcoef_nonneg α i) (sq_nonneg _)

/-! ## The angular coefficient of a mixed slot -/

/-- **The angular coefficient of a mixed slot is integrable**, uniformly in `i ≤ k`. -/
theorem integrable_angCoef {α A : ℝ} (hα : 0 < α) (hα1 : α ≤ 1 / 4) (hA0 : 0 ≤ A)
    {i : ℕ} (hA : ∀ θ ∈ Work.Spaces.Iθ,
      |Work.FTS.EllipticEst.LopIter i (fun θ : ℝ => Real.sin (2 * θ)) θ| ≤ A * Real.sin (2 * θ)) :
    Integrable (fun θ : ℝ => (Work.FTS.EllipticEst.LopIter i (fun θ : ℝ => Real.sin (2 * θ)) θ) ^ 2
      * Real.sin (2 * θ) ^ (-(Work.Spaces.gam α))) (volume.restrict Work.Spaces.Iθ) := by
  have h1 : -1 < 2 - Work.Spaces.gam α := by rw [Work.Spaces.gam]; linarith
  have h2 : 2 - Work.Spaces.gam α ≤ 2 := by rw [Work.Spaces.gam]; linarith
  refine MeasureTheory.Integrable.mono'
    (Integrable.const_mul (integrable_sin_rpow h1 h2) (A ^ 2))
    (((continuous_LopIter_sin i).measurable.pow_const 2).mul (measurable_sin2_rpow _)).aestronglyMeasurable
    ?_
  refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => ?_)
  have hS : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg hθ
  have hrpow : 0 ≤ Real.sin (2 * θ) ^ (-(Work.Spaces.gam α)) := Real.rpow_nonneg hS _
  have hsq : (Work.FTS.EllipticEst.LopIter i (fun θ : ℝ => Real.sin (2 * θ)) θ) ^ 2
      ≤ (A * Real.sin (2 * θ)) ^ 2 := by
    have hAS : 0 ≤ A * Real.sin (2 * θ) := mul_nonneg hA0 hS
    rw [← sq_abs (Work.FTS.EllipticEst.LopIter i (fun θ : ℝ => Real.sin (2 * θ)) θ)]
    exact sq_le_sq' (by linarith [abs_nonneg (Work.FTS.EllipticEst.LopIter i
      (fun θ : ℝ => Real.sin (2 * θ)) θ), hAS]) (hA θ hθ)
  have hg2 : Work.Spaces.gam α ≠ 2 := by rw [Work.Spaces.gam]; intro h; linarith
  have hkey : (A * Real.sin (2 * θ)) ^ 2 * Real.sin (2 * θ) ^ (-(Work.Spaces.gam α))
      = A ^ 2 * Real.sin (2 * θ) ^ (2 - Work.Spaces.gam α) := by
    calc (A * Real.sin (2 * θ)) ^ 2 * Real.sin (2 * θ) ^ (-(Work.Spaces.gam α))
        = A ^ 2 * ((Real.sin (2 * θ)) ^ 2 * Real.sin (2 * θ) ^ (-(Work.Spaces.gam α))) := by ring
      _ = A ^ 2 * Real.sin (2 * θ) ^ (2 - Work.Spaces.gam α) := by
          rw [sq_mul_rpow_neg (Work.Spaces.gam α) hg2 hS]
  rw [Real.norm_of_nonneg (mul_nonneg (sq_nonneg _) hrpow)]
  exact (mul_le_mul_of_nonneg_right hsq hrpow).trans hkey.le

/-- **The angular coefficient of a mixed slot is bounded by `A² · 100`.** -/
theorem integral_angCoef_le {α A : ℝ} (hα : 0 < α) (hα1 : α ≤ 1 / 4) (hA0 : 0 ≤ A)
    {i : ℕ} (hA : ∀ θ ∈ Work.Spaces.Iθ,
      |Work.FTS.EllipticEst.LopIter i (fun θ : ℝ => Real.sin (2 * θ)) θ| ≤ A * Real.sin (2 * θ)) :
    (∫ θ in Work.Spaces.Iθ, (Work.FTS.EllipticEst.LopIter i (fun θ : ℝ => Real.sin (2 * θ)) θ) ^ 2
      * Real.sin (2 * θ) ^ (-(Work.Spaces.gam α))) ≤ A ^ 2 * 100 := by
  have h1 : -1 < 2 - Work.Spaces.gam α := by rw [Work.Spaces.gam]; linarith
  have h2 : 2 - Work.Spaces.gam α ≤ 2 := by rw [Work.Spaces.gam]; linarith
  have h2g0 : 0 ≤ 2 - Work.Spaces.gam α := by rw [Work.Spaces.gam]; linarith
  have hle : ∀ θ ∈ Work.Spaces.Iθ,
      (Work.FTS.EllipticEst.LopIter i (fun θ : ℝ => Real.sin (2 * θ)) θ) ^ 2
          * Real.sin (2 * θ) ^ (-(Work.Spaces.gam α))
        ≤ A ^ 2 * Real.sin (2 * θ) ^ (2 - Work.Spaces.gam α) := by
    intro θ hθ
    have hS : 0 ≤ Real.sin (2 * θ) := sin_two_nonneg hθ
    have hrpow : 0 ≤ Real.sin (2 * θ) ^ (-(Work.Spaces.gam α)) := Real.rpow_nonneg hS _
    have hsq : (Work.FTS.EllipticEst.LopIter i (fun θ : ℝ => Real.sin (2 * θ)) θ) ^ 2
        ≤ (A * Real.sin (2 * θ)) ^ 2 := by
      have hAS : 0 ≤ A * Real.sin (2 * θ) := mul_nonneg hA0 hS
      rw [← sq_abs (Work.FTS.EllipticEst.LopIter i (fun θ : ℝ => Real.sin (2 * θ)) θ)]
      exact sq_le_sq' (by linarith [abs_nonneg (Work.FTS.EllipticEst.LopIter i
        (fun θ : ℝ => Real.sin (2 * θ)) θ), hAS]) (hA θ hθ)
    have hg2 : Work.Spaces.gam α ≠ 2 := by rw [Work.Spaces.gam]; intro h; linarith
    calc (Work.FTS.EllipticEst.LopIter i (fun θ : ℝ => Real.sin (2 * θ)) θ) ^ 2
          * Real.sin (2 * θ) ^ (-(Work.Spaces.gam α))
        ≤ (A * Real.sin (2 * θ)) ^ 2 * Real.sin (2 * θ) ^ (-(Work.Spaces.gam α)) :=
          mul_le_mul_of_nonneg_right hsq hrpow
      _ = A ^ 2 * ((Real.sin (2 * θ)) ^ 2 * Real.sin (2 * θ) ^ (-(Work.Spaces.gam α))) := by ring
      _ = A ^ 2 * Real.sin (2 * θ) ^ (2 - Work.Spaces.gam α) := by
          rw [sq_mul_rpow_neg (Work.Spaces.gam α) hg2 hS]
  have hmono := MeasureTheory.integral_mono_of_nonneg
    (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
      (fun θ hθ => mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (sin_two_nonneg hθ) _)))
    (Integrable.const_mul (integrable_sin_rpow h1 h2) (A ^ 2))
    (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc hle)
  calc (∫ θ in Work.Spaces.Iθ, (Work.FTS.EllipticEst.LopIter i (fun θ : ℝ => Real.sin (2 * θ)) θ) ^ 2
        * Real.sin (2 * θ) ^ (-(Work.Spaces.gam α)))
      ≤ ∫ θ in Work.Spaces.Iθ, A ^ 2 * Real.sin (2 * θ) ^ (2 - Work.Spaces.gam α) := hmono
    _ = A ^ 2 * ∫ θ in Work.Spaces.Iθ, Real.sin (2 * θ) ^ (2 - Work.Spaces.gam α) := by
        rw [MeasureTheory.integral_const_mul]
    _ ≤ A ^ 2 * 100 := mul_le_mul_of_nonneg_left (integral_sin_rpow_le h2g0) (sq_nonneg A)

end Radial

end Work.FTS.EllSol.PkgK5
