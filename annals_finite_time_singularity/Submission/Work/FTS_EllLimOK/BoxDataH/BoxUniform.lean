import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.Order.Chebyshev
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.EllipticEst.remov.TopCoreB.far_vBound
import Submission.Work.FTS.EllipticEst.remov.slice_gprime_ident
import Submission.Work.FTS.H2.hard_sq_prod_z
import Submission.Work.FTS.PhiStar.RadGreenSupport.ibp_upper
import Submission.Work.FTS.PhiStar.RadGreenSupport.radGreen_ode_weak
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.H2.T1Q.IbpCutoff
import Submission.Work.H2W.PsiSlices.weakPos2_dilate
import Submission.Work.RPFresh.slice_sq_le
import Submission.Work.Spaces.HProductRule_bad_term
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.Spaces.SmoothCompact_HkMem
import Submission.Work.Spaces.WProductRule
import Submission.Work.Spaces.bt_integral_weight_id
import Submission.Work.Spaces.bt_prod_integrable
import Submission.Work.Spaces.dthU_Gam
import Submission.Work.Spaces.pz_DthIter_mul_eq
import Submission.Work.Spaces.pz_mixed_mul_le_4
import Submission.Work.Spaces.scoef_sum_shift
import Submission.Work.Spaces.sin_two_rpow
-- ===== merged: Submission.Work.FTS.EllSol.PkgK5.radialAuxInt =====
section

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


end Radial

end Work.FTS.EllSol.PkgK5
end
end
-- ===== merged: Submission.Work.FTS.EllipticEst.AngGainFinal.AngGainFinal =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `AngGainFinal`: from the `v = u / cos θ` slots to the top slot of `u`

Given the weighted `v`-bounds (`v = u / cos θ`, weights `q = sin(2θ)^{2k-γ}`)

`∫_Iθ (v^{(m)})² q ≤ C₀ · AngRHS k γ u g`   for every `m ≤ k+1`

we deduce the top-order angular estimate for `u` itself,

`∫_Iθ (u^{(k+2)})² q ≤ C · AngRHS k γ u g`.

The route is pointwise and elementary: `remov.Baux.angV_ident` writes `u^{(k+2)}` as the
Leibniz sum `Σ_j C(k+1,j) sin^{(k+1-j)}(θ) v^{(j)}` minus the two lower order terms `6u^{(k)}`
and `g^{(k)}`; `remov.Baux.angSum_sq_le` bounds the square of that sum by
`(2^{k+1})²(k+2) Σ_j (v^{(j)})²` (using `|sin^{(m)}| ≤ 1`), and the square of a sum of three
terms is at most three times the sum of the squares.  At the endpoints `θ = 0, π/2` the weight
`q` vanishes, so the pointwise inequality holds on all of `Iθ` and a monotone integral
comparison finishes.
-/

namespace Work.FTS.EllipticEst.AngGainFinal

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-- The gain constant (it depends only on `k`). -/
noncomputable def Mk (k : ℕ) : ℝ := 3 * (((2 : ℝ) ^ (k + 1)) ^ 2 * ((k : ℝ) + 2)) + 108

lemma Mk_pos (k : ℕ) : 0 < Mk k := by
  have h1 : 0 ≤ ((2 : ℝ) ^ (k + 1)) ^ 2 * ((k : ℝ) + 2) := by positivity
  rw [Mk]; linarith

lemma Mk_ge_three (k : ℕ) : 3 * (((2 : ℝ) ^ (k + 1)) ^ 2 * ((k : ℝ) + 2)) ≤ Mk k := by
  have h1 : 0 ≤ ((2 : ℝ) ^ (k + 1)) ^ 2 * ((k : ℝ) + 2) := by positivity
  rw [Mk]; linarith

lemma Mk_ge_108 (k : ℕ) : (108 : ℝ) ≤ Mk k := by
  have h1 : 0 ≤ ((2 : ℝ) ^ (k + 1)) ^ 2 * ((k : ℝ) + 2) := by positivity
  rw [Mk]; linarith

lemma Mk_ge_3 (k : ℕ) : (3 : ℝ) ≤ Mk k := le_trans (by norm_num) (Mk_ge_108 k)

/-- The abstract arithmetic of the gain: a Cauchy–Schwarz bound on `Ss²` together with the
nonnegativity of the four quantities gives the pointwise bound for the square of
`Ss - 6·Uk - Gk`. -/
lemma Mk_arith (k : ℕ) {Ss Sg Uk Gk : ℝ}
    (hcs : Ss ^ 2 ≤ ((2 : ℝ) ^ (k + 1)) ^ 2 * ((k : ℝ) + 2) * Sg)
    (hSg : 0 ≤ Sg) (hUk : 0 ≤ Uk ^ 2) (hGk : 0 ≤ Gk ^ 2) :
    (Ss - 6 * Uk - Gk) ^ 2 ≤ Mk k * (Sg + Uk ^ 2 + Gk ^ 2) := by
  have hA0 : 0 ≤ ((2 : ℝ) ^ (k + 1)) ^ 2 * ((k : ℝ) + 2) := by positivity
  have e1 : (Ss - 6 * Uk - Gk) ^ 2 ≤ 3 * (Ss ^ 2 + 36 * Uk ^ 2 + Gk ^ 2) := by
    nlinarith [sq_nonneg (Ss + 6 * Uk), sq_nonneg (Ss + Gk), sq_nonneg (6 * Uk - Gk)]
  have e2 : 3 * Ss ^ 2 ≤ 3 * (((2 : ℝ) ^ (k + 1)) ^ 2 * ((k : ℝ) + 2) * Sg) := by
    nlinarith [hcs]
  have e3 : 3 * (((2 : ℝ) ^ (k + 1)) ^ 2 * ((k : ℝ) + 2) * Sg) ≤ Mk k * Sg := by
    have h := mul_le_mul_of_nonneg_right (Mk_ge_three k) hSg
    linarith [h]
  have e4 : 108 * Uk ^ 2 ≤ Mk k * Uk ^ 2 :=
    mul_le_mul_of_nonneg_right (Mk_ge_108 k) hUk
  have e5 : 3 * Gk ^ 2 ≤ Mk k * Gk ^ 2 :=
    mul_le_mul_of_nonneg_right (Mk_ge_3 k) hGk
  linarith [e1, e2, e3, e4, e5]

/-- **The pointwise gain.**  On `Iθ` the top derivative of `u` is controlled by the `v`-slots
plus the two lower order slots of `u` and `g`, all with the weight `q`. -/
lemma angGain_pointwise (k : ℕ) (hk : 2 ≤ k) {γ : ℝ} (hγ : γ ≤ 5 / 4) {u g : ℝ → ℝ}
    (hu : ContDiffOn ℝ (k + 2) u (Set.Ioo 0 (Real.pi / 2)))
    (hg : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), g θ = Work.FTS.EllipticEst.Lzero1 u θ) :
    ∀ θ ∈ Work.Spaces.Iθ,
      (iteratedDeriv (k + 2) u θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ)
        ≤ Mk k * ((∑ j ∈ Finset.range (k + 2),
              (iteratedDeriv j (fun t => u t / Real.cos t) θ) ^ 2
                * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ))
            + (iteratedDeriv k u θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ)
            + (iteratedDeriv k g θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ)) := by
  have hExp : 2 * (k : ℝ) - γ ≠ 0 := by
    have hk2 : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
    linarith
  intro θ hθ
  rw [Work.Spaces.Iθ, Set.mem_Icc] at hθ
  rcases eq_or_lt_of_le hθ.1 with h0 | h0
  · rw [← h0]
    have hQ0 : Real.rpow (Real.sin (2 * (0 : ℝ))) (2 * (k : ℝ) - γ) = 0 := by
      rw [show Real.sin (2 * (0 : ℝ)) = 0 by norm_num [Real.sin_zero]]
      exact Real.zero_rpow hExp
    rw [hQ0]
    simp
  rcases eq_or_lt_of_le hθ.2 with hpi | hpi
  · rw [hpi]
    have hQ0 : Real.rpow (Real.sin (2 * (Real.pi / 2))) (2 * (k : ℝ) - γ) = 0 := by
      rw [show Real.sin (2 * (Real.pi / 2)) = 0 by
        rw [show 2 * (Real.pi / 2) = Real.pi by ring, Real.sin_pi]]
      exact Real.zero_rpow hExp
    rw [hQ0]
    simp
  · have hIoo : θ ∈ Set.Ioo 0 (Real.pi / 2) := ⟨h0, hpi⟩
    have hQnn : 0 ≤ Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ) :=
      Real.rpow_nonneg (le_of_lt (Real.sin_pos_of_mem_Ioo ⟨by linarith, by linarith [Real.pi_pos]⟩)) _
    have hid := Work.FTS.EllipticEst.remov.Baux.angV_ident k hu hg θ hIoo
    have hsv : Work.FTS.EllipticEst.remov.sv u = (fun t => u t / Real.cos t) := rfl
    rw [hsv] at hid
    set Ss : ℝ := ∑ j ∈ Finset.range (k + 2), ((k + 1).choose j : ℝ)
        * iteratedDeriv (k + 1 - j) Real.sin θ
        * iteratedDeriv j (fun t => u t / Real.cos t) θ with hSs
    have hcs := Work.FTS.EllipticEst.remov.Baux.angSum_sq_le k
      (fun j => iteratedDeriv j (fun t => u t / Real.cos t) θ) θ
    rw [← hSs] at hcs
    have hSgnn : 0 ≤ ∑ j ∈ Finset.range (k + 2),
        (iteratedDeriv j (fun t => u t / Real.cos t) θ) ^ 2 :=
      Finset.sum_nonneg (fun j _ => sq_nonneg _)
    have hmain : (iteratedDeriv (k + 2) u θ) ^ 2 ≤ Mk k *
        ((∑ j ∈ Finset.range (k + 2),
              (iteratedDeriv j (fun t => u t / Real.cos t) θ) ^ 2)
          + (iteratedDeriv k u θ) ^ 2 + (iteratedDeriv k g θ) ^ 2) := by
      rw [hid]
      exact Mk_arith k (Ss := Ss)
        (Sg := ∑ j ∈ Finset.range (k + 2),
          (iteratedDeriv j (fun t => u t / Real.cos t) θ) ^ 2)
        (Uk := iteratedDeriv k u θ) (Gk := iteratedDeriv k g θ)
        hcs hSgnn (sq_nonneg _) (sq_nonneg _)
    have hexp : (∑ j ∈ Finset.range (k + 2),
            (iteratedDeriv j (fun t => u t / Real.cos t) θ) ^ 2)
          * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ)
        = ∑ j ∈ Finset.range (k + 2),
            (iteratedDeriv j (fun t => u t / Real.cos t) θ) ^ 2
              * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ) :=
      Finset.sum_mul _ _ _
    calc (iteratedDeriv (k + 2) u θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ)
        ≤ (Mk k * ((∑ j ∈ Finset.range (k + 2),
              (iteratedDeriv j (fun t => u t / Real.cos t) θ) ^ 2)
            + (iteratedDeriv k u θ) ^ 2 + (iteratedDeriv k g θ) ^ 2))
            * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ) :=
          mul_le_mul_of_nonneg_right hmain hQnn
      _ = Mk k * ((∑ j ∈ Finset.range (k + 2),
              (iteratedDeriv j (fun t => u t / Real.cos t) θ) ^ 2
                * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ))
            + (iteratedDeriv k u θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ)
            + (iteratedDeriv k g θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ)) := by
          rw [mul_assoc, add_mul, add_mul, hexp]

theorem AngGainFinal (k : ℕ) (hk : 2 ≤ k)
    (hV : ∃ C : ℝ, 0 < C ∧ ∀ (γ : ℝ) (u g : ℝ → ℝ), Work.FTS.EllipticEst.remov.SliceHyp k γ u g →
        ∀ m : ℕ, m ≤ k + 1 →
          MeasureTheory.IntegrableOn (fun θ => (iteratedDeriv m (fun t => u t / Real.cos t) θ) ^ 2
              * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ)) Work.Spaces.Iθ
          ∧ (∫ θ in Work.Spaces.Iθ, (iteratedDeriv m (fun t => u t / Real.cos t) θ) ^ 2
                * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ))
              ≤ C * Work.FTS.EllipticEst.remov.AngRHS k γ u g) :
    ∃ C : ℝ, 0 < C ∧ ∀ (γ : ℝ) (u g : ℝ → ℝ), Work.FTS.EllipticEst.remov.SliceHyp k γ u g →
      (∫ θ in Work.Spaces.Iθ, (iteratedDeriv (k + 2) u θ) ^ 2
          * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ))
        ≤ C * Work.FTS.EllipticEst.remov.AngRHS k γ u g := by
  obtain ⟨C₀, hC₀pos, hV'⟩ := hV
  refine ⟨Mk k * (((k : ℝ) + 2) * C₀ + 2), mul_pos (Mk_pos k) ?_, ?_⟩
  · have hk0 : (0 : ℝ) ≤ (k : ℝ) := Nat.cast_nonneg k
    nlinarith [hC₀pos]
  · intro γ u g hH
    have hHmem : Work.FTS.EllipticEst.remov.SliceHyp k γ u g := hH
    obtain ⟨hγ1, hγ2, hu, hcont, hu0, hupi, hg, hInt_k2, hInt_gk, hInt_high, hInt_2, hInt_1,
      hInt_0⟩ := hH
    have hIθmeas : MeasurableSet Work.Spaces.Iθ := by
      rw [Work.Spaces.Iθ]; exact measurableSet_Icc
    have hslotInt : ∀ m : ℕ, m ≤ k + 1 → IntegrableOn (fun θ =>
        (iteratedDeriv m (fun t => u t / Real.cos t) θ) ^ 2
          * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ)) Work.Spaces.Iθ :=
      fun m hm => (hV' γ u g hHmem m hm).1
    have hslotBnd : ∀ m : ℕ, m ≤ k + 1 → (∫ θ in Work.Spaces.Iθ,
        (iteratedDeriv m (fun t => u t / Real.cos t) θ) ^ 2
          * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ))
        ≤ C₀ * Work.FTS.EllipticEst.remov.AngRHS k γ u g :=
      fun m hm => (hV' γ u g hHmem m hm).2
    have huk := Work.FTS.EllipticEst.remov.angSlot_le_AngRHS k hk γ u g hγ1 hγ2 hu hcont
      hInt_gk hInt_high hInt_2 hInt_1 hInt_0 k (by omega)
    have hIntUk : IntegrableOn (fun θ => (iteratedDeriv k u θ) ^ 2
        * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ)) Work.Spaces.Iθ := huk.1
    have hBndUk : (∫ θ in Work.Spaces.Iθ, (iteratedDeriv k u θ) ^ 2
        * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ))
        ≤ Work.FTS.EllipticEst.remov.AngRHS k γ u g := huk.2
    have hBndGk : (∫ θ in Work.Spaces.Iθ, (iteratedDeriv k g θ) ^ 2
        * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ))
        ≤ Work.FTS.EllipticEst.remov.AngRHS k γ u g :=
      Work.FTS.EllipticEst.remov.g_slot_le_angRHS k γ u g
    -- integrability of the sum of the `v`-slots
    have hIntSum : IntegrableOn (fun θ => ∑ j ∈ Finset.range (k + 2),
        (iteratedDeriv j (fun t => u t / Real.cos t) θ) ^ 2
          * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ)) Work.Spaces.Iθ :=
      MeasureTheory.integrable_finsetSum (Finset.range (k + 2))
        (f := fun j θ => (iteratedDeriv j (fun t => u t / Real.cos t) θ) ^ 2
          * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ))
        (fun j hj => hslotInt j (by rw [Finset.mem_range] at hj; omega))
    have hIntR : IntegrableOn (fun θ => Mk k * ((∑ j ∈ Finset.range (k + 2),
            (iteratedDeriv j (fun t => u t / Real.cos t) θ) ^ 2
              * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ))
          + (iteratedDeriv k u θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ)
          + (iteratedDeriv k g θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ)))
        Work.Spaces.Iθ :=
      ((hIntSum.add hIntUk).add hInt_gk).const_mul (Mk k)
    -- the pointwise bound, integrated
    have hmono : (∫ θ in Work.Spaces.Iθ, (iteratedDeriv (k + 2) u θ) ^ 2
        * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ))
        ≤ ∫ θ in Work.Spaces.Iθ, Mk k * ((∑ j ∈ Finset.range (k + 2),
              (iteratedDeriv j (fun t => u t / Real.cos t) θ) ^ 2
                * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ))
            + (iteratedDeriv k u θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ)
            + (iteratedDeriv k g θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ)) :=
      MeasureTheory.setIntegral_mono_on hInt_k2 hIntR hIθmeas
        (angGain_pointwise k hk hγ2 hu hg)
    -- evaluate the right-hand side
    have hIvs : (∫ θ in Work.Spaces.Iθ, ∑ j ∈ Finset.range (k + 2),
            (iteratedDeriv j (fun t => u t / Real.cos t) θ) ^ 2
              * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ))
        = ∑ j ∈ Finset.range (k + 2), ∫ θ in Work.Spaces.Iθ,
            (iteratedDeriv j (fun t => u t / Real.cos t) θ) ^ 2
              * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ) :=
      MeasureTheory.integral_finsetSum (Finset.range (k + 2))
        (fun j hj => hslotInt j (by rw [Finset.mem_range] at hj; omega))
    have hIadd : (∫ θ in Work.Spaces.Iθ, ((∑ j ∈ Finset.range (k + 2),
            (iteratedDeriv j (fun t => u t / Real.cos t) θ) ^ 2
              * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ))
          + (iteratedDeriv k u θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ)
          + (iteratedDeriv k g θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ)))
        = (∫ θ in Work.Spaces.Iθ, ∑ j ∈ Finset.range (k + 2),
              (iteratedDeriv j (fun t => u t / Real.cos t) θ) ^ 2
                * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ))
          + (∫ θ in Work.Spaces.Iθ, (iteratedDeriv k u θ) ^ 2
              * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ))
          + (∫ θ in Work.Spaces.Iθ, (iteratedDeriv k g θ) ^ 2
              * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ)) := by
      have h1 : (∫ θ in Work.Spaces.Iθ, ((∑ j ∈ Finset.range (k + 2),
            (iteratedDeriv j (fun t => u t / Real.cos t) θ) ^ 2
              * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ))
          + (iteratedDeriv k u θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ)
          + (iteratedDeriv k g θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ)))
        = (∫ θ in Work.Spaces.Iθ, ((∑ j ∈ Finset.range (k + 2),
              (iteratedDeriv j (fun t => u t / Real.cos t) θ) ^ 2
                * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ))
            + (iteratedDeriv k u θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ)))
          + (∫ θ in Work.Spaces.Iθ, (iteratedDeriv k g θ) ^ 2
              * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ)) :=
        MeasureTheory.integral_add (hIntSum.add hIntUk) hInt_gk
      have h2 : (∫ θ in Work.Spaces.Iθ, ((∑ j ∈ Finset.range (k + 2),
              (iteratedDeriv j (fun t => u t / Real.cos t) θ) ^ 2
                * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ))
            + (iteratedDeriv k u θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ)))
          = (∫ θ in Work.Spaces.Iθ, ∑ j ∈ Finset.range (k + 2),
                (iteratedDeriv j (fun t => u t / Real.cos t) θ) ^ 2
                  * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ))
            + (∫ θ in Work.Spaces.Iθ, (iteratedDeriv k u θ) ^ 2
                * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ)) :=
        MeasureTheory.integral_add hIntSum hIntUk
      rw [h1, h2]
    have hval : (∫ θ in Work.Spaces.Iθ, Mk k * ((∑ j ∈ Finset.range (k + 2),
            (iteratedDeriv j (fun t => u t / Real.cos t) θ) ^ 2
              * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ))
          + (iteratedDeriv k u θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ)
          + (iteratedDeriv k g θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ)))
        = Mk k * ((∑ j ∈ Finset.range (k + 2), ∫ θ in Work.Spaces.Iθ,
              (iteratedDeriv j (fun t => u t / Real.cos t) θ) ^ 2
                * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ))
          + (∫ θ in Work.Spaces.Iθ, (iteratedDeriv k u θ) ^ 2
              * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ))
          + (∫ θ in Work.Spaces.Iθ, (iteratedDeriv k g θ) ^ 2
              * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ))) := by
      have h1 : (∫ θ in Work.Spaces.Iθ, Mk k * ((∑ j ∈ Finset.range (k + 2),
              (iteratedDeriv j (fun t => u t / Real.cos t) θ) ^ 2
                * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ))
            + (iteratedDeriv k u θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ)
            + (iteratedDeriv k g θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ)))
          = Mk k * (∫ θ in Work.Spaces.Iθ, ((∑ j ∈ Finset.range (k + 2),
                (iteratedDeriv j (fun t => u t / Real.cos t) θ) ^ 2
                  * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ))
              + (iteratedDeriv k u θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ)
              + (iteratedDeriv k g θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ))) :=
        MeasureTheory.integral_const_mul (Mk k)
          (fun θ => ((∑ j ∈ Finset.range (k + 2),
                (iteratedDeriv j (fun t => u t / Real.cos t) θ) ^ 2
                  * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ))
              + (iteratedDeriv k u θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ)
              + (iteratedDeriv k g θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ)))
      rw [h1, hIadd, hIvs]
    -- bound the sum of the `v`-slots
    have hbndA : (∑ j ∈ Finset.range (k + 2), ∫ θ in Work.Spaces.Iθ,
            (iteratedDeriv j (fun t => u t / Real.cos t) θ) ^ 2
              * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ))
        ≤ ((k + 2 : ℕ) : ℝ) * (C₀ * Work.FTS.EllipticEst.remov.AngRHS k γ u g) := by
      have h := Finset.sum_le_card_nsmul (Finset.range (k + 2))
        (fun j => ∫ θ in Work.Spaces.Iθ, (iteratedDeriv j (fun t => u t / Real.cos t) θ) ^ 2
          * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ))
        (C₀ * Work.FTS.EllipticEst.remov.AngRHS k γ u g)
        (fun j hj => hslotBnd j (by rw [Finset.mem_range] at hj; omega))
      simpa only [Finset.card_range, nsmul_eq_mul] using h
    calc (∫ θ in Work.Spaces.Iθ, (iteratedDeriv (k + 2) u θ) ^ 2
            * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ))
        ≤ ∫ θ in Work.Spaces.Iθ, Mk k * ((∑ j ∈ Finset.range (k + 2),
              (iteratedDeriv j (fun t => u t / Real.cos t) θ) ^ 2
                * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ))
            + (iteratedDeriv k u θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ)
            + (iteratedDeriv k g θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ)) :=
          hmono
      _ = Mk k * ((∑ j ∈ Finset.range (k + 2), ∫ θ in Work.Spaces.Iθ,
              (iteratedDeriv j (fun t => u t / Real.cos t) θ) ^ 2
                * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ))
            + (∫ θ in Work.Spaces.Iθ, (iteratedDeriv k u θ) ^ 2
                * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ))
            + (∫ θ in Work.Spaces.Iθ, (iteratedDeriv k g θ) ^ 2
                * Real.rpow (Real.sin (2 * θ)) (2 * (k : ℝ) - γ))) := hval
      _ ≤ Mk k * ((((k + 2 : ℕ) : ℝ) * (C₀ * Work.FTS.EllipticEst.remov.AngRHS k γ u g))
            + Work.FTS.EllipticEst.remov.AngRHS k γ u g
            + Work.FTS.EllipticEst.remov.AngRHS k γ u g) := by
          refine mul_le_mul_of_nonneg_left ?_ (le_of_lt (Mk_pos k))
          linarith [hbndA, hBndUk, hBndGk]
      _ = Mk k * (((k : ℝ) + 2) * C₀ + 2) * Work.FTS.EllipticEst.remov.AngRHS k γ u g := by
          push_cast
          ring

end Work.FTS.EllipticEst.AngGainFinal
end
-- ===== merged: Submission.Work.FTS.EllipticEst.remov.TopCoreB.far_E_leibniz =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ContDiff
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.remov.TopCoreB

set_option autoImplicit false
set_option maxHeartbeats 2000000

/-! ## The auxiliary sums and the master algebraic identity for `A_b - T_b`

Writing `v = vF u = u / cos θ`, `Q = u^{(k+2)}` and
`Z`, `Y`, `W` for the three Leibniz remainders introduced below, the integrand of the lemma's
left-hand side satisfies the *exact* pointwise identity

`∂^{k+1}(tan θ·u)·u^{(k+2)} - tripleT k γ u
   = - X·Y + Q·(Z - Y) - (k+1)·(u^{(k)} + W)·((k+3)Q + (k+2)X + Y)`,
`X := 6u^{(k)} + g^{(k)} - Z`,

which is the form in which every term is controlled by the `u`-slots (orders `≤ k+1`), the
source slot `g^{(k)}` and the hypothesis' `v`-slots (orders `≤ k`) — in particular the
`(u^{(k+2)})²` terms cancel identically, so that only a `Young` budget of `1/32 < 1/16` on
`(u^{(k+2)})²` is needed.  All the pieces of the right-hand side carry coefficients bounded by
`C(k)` uniformly in `γ`, `u`, `g` and `b`. -/

/-- `iteratedDeriv (n+2) sin = - iteratedDeriv n sin`. -/
theorem iteratedDeriv_sin_add_two (n : ℕ) :
    iteratedDeriv (n + 2) Real.sin = -iteratedDeriv n Real.sin := by
  have h1 : iteratedDeriv (n + 2) Real.sin = iteratedDeriv (n + 1) Real.cos := by
    have h := iteratedDeriv_succ' (n := n + 1) (f := Real.sin)
    rwa [Real.deriv_sin] at h
  have h2 : iteratedDeriv (n + 1) Real.cos = -iteratedDeriv n Real.sin := by
    have h := iteratedDeriv_succ' (n := n) (f := Real.cos)
    have hcos : deriv Real.cos = fun x : ℝ => -Real.sin x := by
      funext x; exact Real.deriv_cos
    rw [hcos] at h
    have h3 : iteratedDeriv n (fun x : ℝ => -Real.sin x) = -iteratedDeriv n Real.sin := by
      funext x; exact iteratedDeriv_neg n Real.sin x
    rw [h3] at h
    exact h
  rw [h1, h2]

/-- `iteratedDeriv (n+2) cos = - iteratedDeriv n cos`. -/
theorem iteratedDeriv_cos_add_two (n : ℕ) :
    iteratedDeriv (n + 2) Real.cos = -iteratedDeriv n Real.cos := by
  have h1 : iteratedDeriv (n + 2) Real.cos = -iteratedDeriv (n + 1) Real.sin := by
    have h := iteratedDeriv_succ' (n := n + 1) (f := Real.cos)
    have hcos : deriv Real.cos = fun x : ℝ => -Real.sin x := by
      funext x; exact Real.deriv_cos
    rw [hcos] at h
    have h3 : iteratedDeriv (n + 1) (fun x : ℝ => -Real.sin x)
        = -iteratedDeriv (n + 1) Real.sin := by
      funext x; exact iteratedDeriv_neg (n + 1) Real.sin x
    rw [h3] at h
    exact h
  have h2 : iteratedDeriv (n + 1) Real.sin = iteratedDeriv n Real.cos := by
    have h := iteratedDeriv_succ' (n := n) (f := Real.sin)
    rwa [Real.deriv_sin] at h
  rw [h1, h2]

/-- All iterated derivatives of `sin` are bounded by `1`. -/
theorem abs_iteratedDeriv_sin_le_one (n : ℕ) (θ : ℝ) :
    |iteratedDeriv n Real.sin θ| ≤ 1 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => simpa using Real.abs_sin_le_one θ
    | 1 => simpa using Real.abs_cos_le_one θ
    | (m + 2) =>
      rw [iteratedDeriv_sin_add_two m]
      simp only [Pi.neg_apply, abs_neg]
      exact ih m (by omega)

/-- All iterated derivatives of `cos` are bounded by `1`. -/
theorem abs_iteratedDeriv_cos_le_one (n : ℕ) (θ : ℝ) :
    |iteratedDeriv n Real.cos θ| ≤ 1 := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n with
    | 0 => simpa using Real.abs_cos_le_one θ
    | 1 =>
      have h : iteratedDeriv 1 Real.cos θ = -Real.sin θ := by
        rw [iteratedDeriv_one]; exact Real.deriv_cos
      rw [h, abs_neg]; exact Real.abs_sin_le_one θ
    | (m + 2) =>
      show |iteratedDeriv (m + 2) Real.cos θ| ≤ 1
      rw [iteratedDeriv_cos_add_two m]
      simp only [Pi.neg_apply, abs_neg]
      exact ih m (by omega)




/-! ## The three Leibniz remainders `Z`, `Y`, `W`, and `X = 6u^{(k)} + g^{(k)} - Z` -/

/-- The Leibniz remainder of `∂^{k+1}(sin θ · v)`: the sum of the terms with at least one
derivative falling on `sin` (`v = vF u = u / cos θ`). -/
def Zsum (k : ℕ) (u : ℝ → ℝ) : ℝ → ℝ := fun θ =>
  ∑ r ∈ Finset.Icc 1 (k + 1), ((k + 1).choose r : ℝ) * iteratedDeriv r Real.sin θ
    * iteratedDeriv (k + 1 - r) (vF u) θ













/-! ## The constants and the pointwise estimate -/

/-- The product `(k+1)(k+3)`, the natural coefficient of the `W`-block. -/
def KW (k : ℕ) : ℝ := ((k : ℝ) + 1) * ((k : ℝ) + 3)

/-- The product `(k+1)(k+2)²`, the natural coefficient of the `u^{(k)}`-block. -/
def KUv (k : ℕ) : ℝ := ((k : ℝ) + 1) * ((k : ℝ) + 2) ^ 2




/-- Coefficient of `(u^{(k)})²` in the pointwise estimate. -/
def CU (k : ℕ) : ℝ := 54 + 64 * KW k ^ 2 + ((k : ℝ) + 1) + 108 * KUv k

/-- Coefficient of `(g^{(k)})²` in the pointwise estimate. -/
def CG (k : ℕ) : ℝ := 3 / 2 + 3 * KUv k





















theorem choose_le_two_pow (n i : ℕ) : n.choose i ≤ 2 ^ n := by
  by_cases hi : i ≤ n
  · calc n.choose i ≤ ∑ j ∈ Finset.range (n + 1), n.choose j :=
        Finset.single_le_sum (fun j _ => Nat.zero_le _)
          (by simp only [Finset.mem_range]; omega)
      _ = 2 ^ n := Nat.sum_range_choose n
  · rw [Nat.choose_eq_zero_of_lt (by omega)]; exact Nat.zero_le _







/-! ## Continuity and the interval estimate -/

/-- `iteratedDeriv m f` is continuous wherever `f` is `C^n`. -/
theorem continuousOn_iteratedDeriv_of_contDiffOn {n m : ℕ} {f : ℝ → ℝ} {s : Set ℝ}
    (hs : IsOpen s) (hf : ContDiffOn ℝ n f s) (hm : m ≤ n) :
    ContinuousOn (iteratedDeriv m f) s := by
  have h1 : ContinuousOn (iteratedDerivWithin m f s) s :=
    hf.continuousOn_iteratedDerivWithin (by exact_mod_cast hm) hs.uniqueDiffOn
  refine h1.congr fun x hx => ?_
  exact (iteratedDerivWithin_eq_iteratedDeriv hs.uniqueDiffOn
    ((hf.contDiffAt (hs.mem_nhds hx)).of_le (by exact_mod_cast hm)) hx).symm

/-- `vF u = u / cos` is `C^n` on the open strip as soon as `u` is. -/
theorem contDiffOn_vF {n : ℕ} {u : ℝ → ℝ} (hu : ContDiffOn ℝ n u (Set.Ioo 0 (Real.pi / 2))) :
    ContDiffOn ℝ n (vF u) (Set.Ioo 0 (Real.pi / 2)) := by
  have hcos : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), Real.cos θ ≠ 0 := fun θ hθ =>
    (Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩).ne'
  have h := hu.div Real.contDiff_cos.contDiffOn hcos
  rwa [show (u / Real.cos) = vF u from rfl] at h











end Work.FTS.EllipticEst.remov.TopCoreB
end
end
-- ===== merged: Submission.Work.FTS.H2.STHardSlot =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! ## The two exponent identities -/



/-! ## The pointwise bound on the coefficient produced by the integration by parts -/


/-! ## The boundary vanishing -/


end Work.FTS.H2
end
end
-- ===== merged: Submission.Work.FTS.H2.Transport3Aux.Z3Defs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.H2.Transport3Aux
namespace Z3

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## The Leibniz summands of the `D_z`-pairing -/

/-- The `(i,k)`-th `D_z`-slot Leibniz summand of `H4PairInt α (f · D_z g) g`:
`binom(i,k) · D_z^k f · D_z^{i+1-k} g · D_z^i g · Whz²`, in exactly the bracketing in which
the Leibniz expansion of `(D_z^i (f D_z g) · Whz) · (D_z^i g · Whz)` produces it. -/
def TZ (α : ℝ) (f g : ℝ → ℝ → ℝ) (i k : ℕ) (z θ : ℝ) : ℝ :=
  (((i.choose k : ℝ) * (Work.Spaces.DzIter k f z θ * Work.Spaces.DzIter (i + 1 - k) g z θ))
      * Whz z θ) * (Work.Spaces.DzIter i g z θ * Whz z θ)

/-- The `(i,j,a,b)`-th mixed-slot Leibniz summand of `H4PairInt α (f · D_z g) g`:
`binom(i,a) binom(j,b) · D_z^bD_θ^a f · D_z^{j-b+1}D_θ^{i-a} g · D_z^jD_θ^i g · Wm²`. -/
def TM (α : ℝ) (f g : ℝ → ℝ → ℝ) (i j a b : ℕ) (z θ : ℝ) : ℝ :=
  ((((i.choose a : ℝ) * (j.choose b : ℝ))
      * (Work.Spaces.mixed b a f z θ * Work.Spaces.mixed (j - b + 1) (i - a) g z θ))
      * Wm α z θ) * (Work.Spaces.mixed j i g z θ * Wm α z θ)





/-! ## The Leibniz rules for the factor `D_z g` -/

/-- `D_z^n (D_z g) = D_z^{n+1} g`. -/
theorem DzIter_Dz (n : ℕ) (g : ℝ → ℝ → ℝ) :
    Work.Spaces.DzIter n (Work.Spaces.Dz g) = Work.Spaces.DzIter (n + 1) g := by
  induction n with
  | zero => rfl
  | succ k ih =>
      rw [Work.Spaces.DzIter_succ k (Work.Spaces.Dz g), ih, Work.Spaces.DzIter_succ (k + 1) g]




/-! ## The identification of the removed summands with `Badz` and `Mismatchz` -/





end Z3
end Work.FTS.H2.Transport3Aux
end
end
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.DiffGreen.sum_sqrt_eNorm_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty.DiffGreen


/-- Telescoping: `∑_{m<n} 1/((m+1)(m+2)) = 1 - 1/(n+1)`. -/
private lemma sum_range_inv_mul_succ (n : ℕ) :
    ∑ m ∈ Finset.range n, (((m : ℝ) + 1) * ((m : ℝ) + 2))⁻¹ = 1 - ((n : ℝ) + 1)⁻¹ := by
  induction n with
  | zero => simp
  | succ k ih =>
      rw [Finset.sum_range_succ, ih]
      have hstep : (((k : ℝ) + 1) * ((k : ℝ) + 2))⁻¹
          = ((k : ℝ) + 1)⁻¹ - ((k : ℝ) + 2)⁻¹ := by
        rw [eq_sub_iff_add_eq]
        field_simp
        ring
      rw [hstep]
      push_cast
      ring

/-- The Cauchy–Schwarz weight sum: `m + 1 ≤ eNorm m` gives
`∑_{m≤N} 1/(eNorm m · (m+1)) ≤ 1 + ∑_{m<N} 1/((m+1)(m+2)) ≤ 2`. -/
private lemma sum_inv_eNorm_mul_le_two (N : ℕ) :
    ∑ m ∈ Finset.range (N + 1),
      (Work.EllipticEst.ModalSolution.eNorm m * ((m : ℝ) + 1))⁻¹ ≤ 2 := by
  rw [Finset.sum_range_succ']
  have key : ∀ m : ℕ,
      (Work.EllipticEst.ModalSolution.eNorm (m + 1) * (((m + 1 : ℕ) : ℝ) + 1))⁻¹
        ≤ (((m : ℝ) + 1) * ((m : ℝ) + 2))⁻¹ := by
    intro m
    have h := (Work.FTS.ClassCHon.CmpSupp.eNorm_bounds (m + 1)).2
    push_cast at h ⊢
    rw [inv_le_inv₀ (mul_pos (Work.EllipticEst.ModalSolution.eNorm_pos (m + 1)) (by positivity))
      (by positivity)]
    nlinarith [h]
  have hsum : ∑ m ∈ Finset.range N,
      (Work.EllipticEst.ModalSolution.eNorm (m + 1) * (((m + 1 : ℕ) : ℝ) + 1))⁻¹ ≤ 1 := by
    calc _ ≤ ∑ m ∈ Finset.range N, (((m : ℝ) + 1) * ((m : ℝ) + 2))⁻¹ :=
          Finset.sum_le_sum fun m _ => key m
      _ = 1 - ((N : ℝ) + 1)⁻¹ := sum_range_inv_mul_succ N
      _ ≤ 1 := by
          have hpos : (0 : ℝ) < (N : ℝ) + 1 := by positivity
          have := inv_pos.2 hpos
          linarith
  have h0 : (Work.EllipticEst.ModalSolution.eNorm 0 * ((0 : ℝ) + 1))⁻¹ ≤ 1 := by
    rw [inv_le_one₀ (mul_pos (Work.EllipticEst.ModalSolution.eNorm_pos 0) (by norm_num))]
    have h := (Work.FTS.ClassCHon.CmpSupp.eNorm_bounds 0).1
    linarith
  linarith

/-- **The Cauchy–Schwarz sum step for the modal series.**  If `U ≥ 0` has Bessel-bounded
`eNorm`-weighted energy, `∑_{m≤N} eNorm m · U m² ≤ H` for every `N`, then

  `∑_{m≤N} U m / √(m+1) ≤ 2 √H`  for every `N`,

because `U m/√(m+1) = (√(eNorm m)·U m)·(1/(√(eNorm m)·√(m+1)))`, Cauchy–Schwarz over the
finite range gives `√(∑ eNorm m U m²)·√(∑ 1/(eNorm m (m+1)))`, and `m + 1 ≤ eNorm m`
(so `∑_{m≤N} 1/(eNorm m (m+1)) ≤ 1 + ∑_{m=1}^{N} 1/(m(m+1)) ≤ 2`); hence the constant `2`. -/
theorem sum_sqrt_eNorm_le {U : ℕ → ℝ} (hU : ∀ m : ℕ, 0 ≤ U m) {H : ℝ} (hH : 0 ≤ H)
    (hB : ∀ N : ℕ, ∑ m ∈ Finset.range (N + 1),
      Work.EllipticEst.ModalSolution.eNorm m * (U m) ^ 2 ≤ H) :
    ∀ N : ℕ, ∑ m ∈ Finset.range (N + 1), U m / Real.sqrt ((m : ℝ) + 1)
      ≤ 2 * Real.sqrt H := by
  intro N
  -- The two Cauchy–Schwarz factors `√(f m)` and `√(g m)` multiply to `U m / √(m+1)`.
  have hf : ∀ m : ℕ, 0 ≤ Work.EllipticEst.ModalSolution.eNorm m * (U m) ^ 2 :=
    fun m => mul_nonneg (le_of_lt (Work.EllipticEst.ModalSolution.eNorm_pos m)) (sq_nonneg _)
  have hg : ∀ m : ℕ, 0 ≤ (Work.EllipticEst.ModalSolution.eNorm m * ((m : ℝ) + 1))⁻¹ :=
    fun m => inv_nonneg.2 (mul_nonneg (le_of_lt (Work.EllipticEst.ModalSolution.eNorm_pos m))
      (by positivity))
  have hterm : ∀ m ∈ Finset.range (N + 1),
      Real.sqrt (Work.EllipticEst.ModalSolution.eNorm m * (U m) ^ 2)
        * Real.sqrt ((Work.EllipticEst.ModalSolution.eNorm m * ((m : ℝ) + 1))⁻¹)
      = U m / Real.sqrt ((m : ℝ) + 1) := by
    intro m _
    have hE := Work.EllipticEst.ModalSolution.eNorm_pos m
    have h1 : Real.sqrt (Work.EllipticEst.ModalSolution.eNorm m * (U m) ^ 2)
        = Real.sqrt (Work.EllipticEst.ModalSolution.eNorm m) * U m := by
      rw [Real.sqrt_mul (le_of_lt hE), Real.sqrt_sq (hU m)]
    have h2 : Real.sqrt ((Work.EllipticEst.ModalSolution.eNorm m * ((m : ℝ) + 1))⁻¹)
        = (Real.sqrt (Work.EllipticEst.ModalSolution.eNorm m)
            * Real.sqrt ((m : ℝ) + 1))⁻¹ := by
      rw [Real.sqrt_inv, Real.sqrt_mul (le_of_lt hE)]
    rw [h1, h2]
    have hne : Real.sqrt (Work.EllipticEst.ModalSolution.eNorm m) ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.2 hE)
    have hne2 : Real.sqrt ((m : ℝ) + 1) ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.2 (by positivity))
    field_simp
  calc ∑ m ∈ Finset.range (N + 1), U m / Real.sqrt ((m : ℝ) + 1)
      = ∑ m ∈ Finset.range (N + 1),
          Real.sqrt (Work.EllipticEst.ModalSolution.eNorm m * (U m) ^ 2)
            * Real.sqrt ((Work.EllipticEst.ModalSolution.eNorm m * ((m : ℝ) + 1))⁻¹) :=
        (Finset.sum_congr rfl fun m hm => (hterm m hm).symm)
    _ ≤ Real.sqrt (∑ m ∈ Finset.range (N + 1),
            Work.EllipticEst.ModalSolution.eNorm m * (U m) ^ 2)
          * Real.sqrt (∑ m ∈ Finset.range (N + 1),
            (Work.EllipticEst.ModalSolution.eNorm m * ((m : ℝ) + 1))⁻¹) :=
        Real.sum_sqrt_mul_sqrt_le _ hf hg
    _ ≤ Real.sqrt H * Real.sqrt 2 := by
        refine mul_le_mul (Real.sqrt_le_sqrt (hB N)) (Real.sqrt_le_sqrt (sum_inv_eNorm_mul_le_two N))
          (Real.sqrt_nonneg _) (Real.sqrt_nonneg H)
    _ ≤ 2 * Real.sqrt H := by
        have h2 : Real.sqrt 2 ≤ 2 := by
          have := Real.sqrt_two_lt_three_halves
          linarith
        have h3 : Real.sqrt H * Real.sqrt 2 ≤ Real.sqrt H * 2 :=
          mul_le_mul_of_nonneg_left h2 (Real.sqrt_nonneg H)
        linarith

end Work.FTS.PhiStar.Honesty.DiffGreen
end
-- ===== merged: Submission.Work.FTS.StrongEps.ClassCRHS.DzBoundR0 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.ClassCRHS

open Work.FTS.NonlinRows.AkRhoJetBasic (akRho akRho_abs_le akJet_mul_w)

/-- `z ↦ 2z²/(1+z)³` and its `z∂_z`-iterates vanish at `0`: for `i ≥ 1` this is because `z∂_z`
carries a factor `z`, and `SR0 0 = 0`. -/
lemma DzdIter_SR0_zero (i : ℕ) : Work.Elliptic.DzdIter i SR0 0 = 0 := by
  cases i with
  | zero => simp [Work.Elliptic.DzdIter_zero, SR0]
  | succ k => rw [Work.Elliptic.DzdIter_succ]; simp [Work.Elliptic.Dzd]

/-- The radial profile `SR0 z = 2z²/(1+z)³` has `z∂_z`-iterates of order `≤ 4` bounded by
`720·z²/(1+z)³`.

The `i`-th iterate is `z²·q_i(z)/(1+z)^(3+i)` with `Σ|coeff q_i| ≤ 720` (the coefficients `q_i`
are exactly `Work.FTS.NonlinRows.AkRhoJetBasic.akNum i`, whose jets are computed there).
Equivalently, with the Hardy weight `w z = (1+z)²/z²`, the product
`DzIter i (2z²/(1+z)³)·w` is the `akRho i` of `AkRhoJetBasic`, bounded by `720/(1+z)` there;
multiplying back by `z²/(1+z)²` gives the claim, with one constant `720` for all `i ≤ 4`. -/
theorem DzBoundR0 : ∃ C : ℝ, 0 < C ∧ ∀ i : ℕ, i ≤ 4 → ∀ z : ℝ, 0 ≤ z →
    |Work.Elliptic.DzdIter i Work.FTS.StrongEps.ClassCRHS.SR0 z|
      ≤ C * z ^ 2 / (1 + z) ^ 3 := by
  refine ⟨720, by norm_num, fun i hi z hz => ?_⟩
  rcases eq_or_lt_of_le hz with hz0 | hzpos
  · subst hz0
    rw [DzdIter_SR0_zero, abs_zero]
    norm_num
  · have hzm : z ≠ 0 := ne_of_gt hzpos
    have hzn : z ≠ -1 := by intro h; linarith
    have hwpos : 0 < Work.Spaces.w z := by rw [Work.Spaces.w]; positivity
    have hwne : Work.Spaces.w z ≠ 0 := ne_of_gt hwpos
    have hA : Work.Spaces.DzIter i (fun z _ => 2 * z ^ 2 / (1 + z) ^ 3) z 0
        = akRho i z / Work.Spaces.w z :=
      (eq_div_iff hwne).mpr (akJet_mul_w i hi hzm hzn 0)
    rw [← Work.Elliptic.DzIter_rad SR0 i z 0]
    change |Work.Spaces.DzIter i (fun z _ => 2 * z ^ 2 / (1 + z) ^ 3) z 0|
        ≤ 720 * z ^ 2 / (1 + z) ^ 3
    rw [hA, abs_div, abs_of_pos hwpos]
    calc |akRho i z| / Work.Spaces.w z
        ≤ (720 / (1 + z)) / Work.Spaces.w z :=
          div_le_div_of_nonneg_right (akRho_abs_le i hi hzpos.le) hwpos.le
      _ = 720 * z ^ 2 / (1 + z) ^ 3 := by
          rw [Work.Spaces.w]
          field_simp

end Work.FTS.StrongEps.ClassCRHS
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Aux.DzdIter_mul_of_diff =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Aux

open Set Filter

/-- The one-`Dzd` step of the Leibniz rule for a summand `c * (X * Y)`
(`Dzd u = z u'`). -/
private theorem Dzd_const_mul_mul (c : ℝ) {X Y : ℝ → ℝ} {z : ℝ}
    (hX : DifferentiableAt ℝ X z) (hY : DifferentiableAt ℝ Y z) :
    Work.Elliptic.Dzd (fun w => c * (X w * Y w)) z
      = c * (Work.Elliptic.Dzd X z * Y z + X z * Work.Elliptic.Dzd Y z) := by
  have hXY : DifferentiableAt ℝ (fun w : ℝ => X w * Y w) z := hX.mul hY
  have h1 : deriv (fun w : ℝ => c * (X w * Y w)) z
      = c * deriv (fun w : ℝ => X w * Y w) z := deriv_const_mul c hXY
  have h2 : deriv (fun w : ℝ => X w * Y w) z = deriv X z * Y z + X z * deriv Y z :=
    deriv_mul hX hY
  simp only [Work.Elliptic.Dzd]
  rw [h1, h2]
  ring

/-- `Dzd` is linear over finite sums of differentiable functions. -/
private theorem Dzd_sum_range (K : ℕ) (A : ℕ → ℝ → ℝ) {z : ℝ}
    (hA : ∀ b ≤ K, DifferentiableAt ℝ (A b) z) :
    Work.Elliptic.Dzd (fun w => ∑ b ∈ Finset.range (K + 1), A b w) z
      = ∑ b ∈ Finset.range (K + 1), Work.Elliptic.Dzd (A b) z := by
  have hd : ∀ b ∈ Finset.range (K + 1), DifferentiableAt ℝ (A b) z :=
    fun b hb => hA b (Nat.lt_succ_iff.mp (Finset.mem_range.mp hb))
  simp only [Work.Elliptic.Dzd]
  rw [deriv_fun_sum hd, Finset.mul_sum]

theorem DzdIter_mul_of_diff (N : ℕ) (u v : ℝ → ℝ)
    (hu : ∀ b, b + 1 ≤ N → DifferentiableOn ℝ (Work.Elliptic.DzdIter b u) (Set.Ioi (0 : ℝ)))
    (hv : ∀ b, b + 1 ≤ N → DifferentiableOn ℝ (Work.Elliptic.DzdIter b v) (Set.Ioi (0 : ℝ))) :
    ∀ z ∈ Set.Ioi (0 : ℝ),
      Work.Elliptic.DzdIter N (fun z => u z * v z) z
        = ∑ b ∈ Finset.range (N + 1),
            (N.choose b : ℝ) * (Work.Elliptic.DzdIter b u z * Work.Elliptic.DzdIter (N - b) v z) := by
  revert hu hv
  induction N with
  | zero =>
      intro hu hv z hz
      simp
  | succ N ih =>
      intro hu hv z hz
      -- the differentiability hypotheses at the (one lower) level `N`
      have hu' : ∀ b, b + 1 ≤ N → DifferentiableOn ℝ (Work.Elliptic.DzdIter b u) (Set.Ioi 0) :=
        fun b hb => hu b (by omega)
      have hv' : ∀ b, b + 1 ≤ N → DifferentiableOn ℝ (Work.Elliptic.DzdIter b v) (Set.Ioi 0) :=
        fun b hb => hv b (by omega)
      -- the inductive hypothesis, as an `EqOn` on the open set `Ioi 0`
      have hIH : Set.EqOn (Work.Elliptic.DzdIter N (fun z => u z * v z))
          (fun w => ∑ b ∈ Finset.range (N + 1),
            (N.choose b : ℝ) * (Work.Elliptic.DzdIter b u w * Work.Elliptic.DzdIter (N - b) v w))
          (Set.Ioi 0) := fun w hw => ih hu' hv' w hw
      have hder : deriv (Work.Elliptic.DzdIter N (fun z => u z * v z)) z
          = deriv (fun w => ∑ b ∈ Finset.range (N + 1),
              (N.choose b : ℝ) * (Work.Elliptic.DzdIter b u w * Work.Elliptic.DzdIter (N - b) v w)) z :=
        hIH.deriv isOpen_Ioi hz
      -- differentiability of the summands at `z ∈ Ioi 0`
      have hd_X : ∀ b ≤ N, DifferentiableAt ℝ (Work.Elliptic.DzdIter b u) z :=
        fun b hb => (hu b (by omega)).differentiableAt (isOpen_Ioi.mem_nhds hz)
      have hd_Y : ∀ b ≤ N, DifferentiableAt ℝ (Work.Elliptic.DzdIter (N - b) v) z :=
        fun b hb => (hv (N - b) (by omega)).differentiableAt (isOpen_Ioi.mem_nhds hz)
      calc Work.Elliptic.DzdIter (N + 1) (fun z => u z * v z) z
          = Work.Elliptic.Dzd (Work.Elliptic.DzdIter N (fun z => u z * v z)) z := rfl
        _ = z * deriv (Work.Elliptic.DzdIter N (fun z => u z * v z)) z := rfl
        _ = z * deriv (fun w => ∑ b ∈ Finset.range (N + 1),
              (N.choose b : ℝ) * (Work.Elliptic.DzdIter b u w * Work.Elliptic.DzdIter (N - b) v w)) z := by
              rw [hder]
        _ = Work.Elliptic.Dzd (fun w => ∑ b ∈ Finset.range (N + 1),
              (N.choose b : ℝ) * (Work.Elliptic.DzdIter b u w * Work.Elliptic.DzdIter (N - b) v w)) z := rfl
        _ = ∑ b ∈ Finset.range (N + 1), Work.Elliptic.Dzd
              (fun w => (N.choose b : ℝ)
                * (Work.Elliptic.DzdIter b u w * Work.Elliptic.DzdIter (N - b) v w)) z := by
              apply Dzd_sum_range
              intro b hb
              exact ((hd_X b hb).mul (hd_Y b hb)).const_mul _
        _ = ∑ b ∈ Finset.range (N + 1), (N.choose b : ℝ)
              * (Work.Elliptic.DzdIter (b + 1) u z * Work.Elliptic.DzdIter (N - b) v z
                + Work.Elliptic.DzdIter b u z * Work.Elliptic.DzdIter (N - b + 1) v z) := by
              apply Finset.sum_congr rfl
              intro b hb
              have hbN : b ≤ N := Nat.lt_succ_iff.mp (Finset.mem_range.mp hb)
              rw [Dzd_const_mul_mul (N.choose b : ℝ) (hd_X b hbN) (hd_Y b hbN)]
              simp only [Work.Elliptic.DzdIter_succ]
        _ = ∑ j ∈ Finset.range (N + 1 + 1), ((N + 1).choose j : ℝ)
              * (Work.Elliptic.DzdIter j u z * Work.Elliptic.DzdIter (N + 1 - j) v z) :=
              Work.Spaces.leibniz_step N (fun i => Work.Elliptic.DzdIter i u z)
                (fun i => Work.Elliptic.DzdIter i v z)

end Work.FTS.StrongPersist.H6Aux
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Pair6Aux.boundarySeqs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Pair6Aux

/-- Boundary-vanishing sequences at `0` and at `∞`: for a nonnegative integrable `H` on
`(0,∞)` which is continuous on each dyadic annulus around `0` and on each `[k+1, 2k+2]`,
there are `ε k → 0⁺` and `M k → ∞` with `ε k ≤ M k` along which the boundary term `H · id`
vanishes.  Immediate from `Work.FTS.EllipticEst.zHardy_seq_bot` (dyadic minimisers) and
`Work.FTS.EllipticEst.zHardy_seq_top` (minimisers on `[k+1, 2k+2]`), both in
`Submission.Work.FTS.EllipticEst.zHardyAux`: the minimiser `ε k ∈ [2^{-(k+1)}, 2^{-k}]`
satisfies `H (ε k) * ε k ≤ 2 * ∫_{(0, 2^{-k}]} H → 0`, similarly at `∞`. -/
theorem boundarySeqs (H : ℝ → ℝ) (hH : MeasureTheory.IntegrableOn H (Set.Ioi 0))
    (hHnn : ∀ z, 0 ≤ H z)
    (hc1 : ∀ k : ℕ, ContinuousOn H (Set.Icc ((1 / 2 : ℝ) ^ (k + 1)) ((1 / 2 : ℝ) ^ k)))
    (hc2 : ∀ k : ℕ, ContinuousOn H (Set.Icc ((k : ℝ) + 1) (2 * ((k : ℝ) + 1)))) :
    ∃ ε M : ℕ → ℝ, (∀ k, 0 < ε k) ∧ (∀ k, ε k ≤ M k) ∧
      Filter.Tendsto ε Filter.atTop (nhds 0) ∧
      Filter.Tendsto M Filter.atTop Filter.atTop ∧
      Filter.Tendsto (fun k => H (ε k) * ε k) Filter.atTop (nhds 0) ∧
      Filter.Tendsto (fun k => H (M k) * M k) Filter.atTop (nhds 0) := by
  -- Integrability on the two halves of `(0,∞)`.
  have hbot : MeasureTheory.IntegrableOn H (Set.Ioc (0:ℝ) 1) :=
    hH.mono_set (fun z hz => hz.1)
  have htop : MeasureTheory.IntegrableOn H (Set.Ioi (1:ℝ)) :=
    hH.mono_set (Set.Ioi_subset_Ioi (by norm_num : (0:ℝ) ≤ 1))
  obtain ⟨ε, hεmem, hεtend, hεbd⟩ :=
    Work.FTS.EllipticEst.zHardy_seq_bot H hbot hHnn hc1
  obtain ⟨M, hMmem, hMtend, hMbd⟩ :=
    Work.FTS.EllipticEst.zHardy_seq_top H htop hHnn hc2
  refine ⟨ε, M, ?_, ?_, hεtend, hMtend, hεbd, hMbd⟩
  · -- `0 < 2^{-(k+1)} ≤ ε k`
    intro k
    have h := (Set.mem_Icc.mp (hεmem k)).1
    have hpos : (0:ℝ) < (1/2:ℝ) ^ (k + 1) := by positivity
    linarith
  · -- `ε k ≤ 2^{-k} ≤ 1 ≤ k+1 ≤ M k`
    intro k
    have hε := (Set.mem_Icc.mp (hεmem k)).2
    have hM := (Set.mem_Icc.mp (hMmem k)).1
    have hpow : (1/2:ℝ) ^ k ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    have hk : (0:ℝ) ≤ (k:ℝ) := Nat.cast_nonneg k
    linarith

end Work.FTS.StrongPersist.H6Pair6Aux
end
-- ===== merged: Submission.Work.FTS_EllLimOK.BoxDataH.BoxUniform =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_EllLimOK.BoxDataH

set_option autoImplicit false

/-- **The uniform `C^{2,β}` data of a family on a box** — the abstract form of `PkgBoxH` along a
sequence. -/
def BoxUniform2 (a b : ℝ) (H : ℕ → ℝ → ℝ → ℝ) : Prop :=
  ∃ K β : ℝ, 0 < β ∧
    (∀ n, ContDiffOn ℝ 2 (Function.uncurry (H n)) (cbox a b)) ∧
    (∀ n k : ℕ, k ≤ 2 → ∀ p ∈ cbox a b,
      ‖iteratedFDerivWithin ℝ k (Function.uncurry (H n)) (cbox a b) p‖ ≤ K) ∧
    (∀ n, ∀ p ∈ cbox a b, ∀ q ∈ cbox a b,
      ‖iteratedFDerivWithin ℝ 2 (Function.uncurry (H n)) (cbox a b) p
        - iteratedFDerivWithin ℝ 2 (Function.uncurry (H n)) (cbox a b) q‖
        ≤ K * ‖p - q‖ ^ β)

/-- **The slice data** of a function `F` on the box: the six one-variable within-derivatives of
`F`, `wPz F` and `wPth F` on the two intervals of the box.  (The two mixed components are the
`z`-derivative of the `wPth`-slice and the `θ`-derivative of the `wPz`-slice, in this order.) -/
def SliceData (a b : ℝ) (F : ℝ × ℝ → ℝ) : Prop :=
  (∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc 0 (π / 2),
    HasDerivWithinAt (fun z' => F (z', θ)) (wPz (cbox a b) F (z, θ)) (Set.Icc a b) z) ∧
  (∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc 0 (π / 2),
    HasDerivWithinAt (fun θ' => F (z, θ')) (wPth (cbox a b) F (z, θ)) (Set.Icc 0 (π / 2)) θ) ∧
  (∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc 0 (π / 2),
    HasDerivWithinAt (fun z' => wPz (cbox a b) F (z', θ)) (wPzz (cbox a b) F (z, θ))
      (Set.Icc a b) z) ∧
  (∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc 0 (π / 2),
    HasDerivWithinAt (fun θ' => wPz (cbox a b) F (z, θ')) (wPtz (cbox a b) F (z, θ))
      (Set.Icc 0 (π / 2)) θ) ∧
  (∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc 0 (π / 2),
    HasDerivWithinAt (fun z' => wPth (cbox a b) F (z', θ)) (wPzt (cbox a b) F (z, θ))
      (Set.Icc a b) z) ∧
  (∀ z ∈ Set.Icc a b, ∀ θ ∈ Set.Icc 0 (π / 2),
    HasDerivWithinAt (fun θ' => wPth (cbox a b) F (z, θ')) (wPtt (cbox a b) F (z, θ))
      (Set.Icc 0 (π / 2)) θ)

end Work.FTS_EllLimOK.BoxDataH
end
end
