import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.ThetaPoincareDefs
import Submission.Work.Spaces.Defs
import Submission.Work.EllipticEst.Core.sliceBoundaryLimit

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.EllipticEst.Core

set_option autoImplicit false

/-- `|a| ≤ √B` follows from `a² ≤ B` and `0 ≤ B`. -/
private lemma tie_abs_le_sqrt {a B : ℝ} (_hB : 0 ≤ B) (h : a ^ 2 ≤ B) : |a| ≤ Real.sqrt B := by
  rw [← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt h

/-- Monotonicity of the set integral in the domain, for a nonnegative integrand on the
open angular interval `(0, π/2)`. -/
private lemma tie_setIntegral_mono {F : ℝ → ℝ}
    (hint : IntegrableOn F (Set.Ioo 0 (Real.pi / 2)))
    (hnn : ∀ t ∈ Set.Ioo 0 (Real.pi / 2), 0 ≤ F t)
    {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    (∫ t in Set.Ioo 0 θ, F t) ≤ ∫ t in Set.Ioo 0 (Real.pi / 2), F t := by
  refine MeasureTheory.setIntegral_mono_set hint ?_ ?_
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with t ht
    exact hnn t ht
  · filter_upwards with t ht
    exact ⟨ht.1, lt_trans ht.2 hθ.2⟩

/-- If `g` satisfies the endpoint bound `(g θ - c)² ≤ K θ^{1+η} ∫_{(0,θ)} G` coming from
`sliceBoundaryLimit`, with `G ≥ 0` and `K ≥ 0`, then `g` is uniformly bounded on the open
angular interval, with the explicit bound displayed below. -/
private lemma tie_bound_of_limit_bound {g : ℝ → ℝ} {G : ℝ → ℝ} {c K : ℝ} (hK : 0 ≤ K)
    (hint : IntegrableOn G (Set.Ioo 0 (Real.pi / 2)))
    (hnn : ∀ t ∈ Set.Ioo 0 (Real.pi / 2), 0 ≤ G t)
    (hb : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      (g θ - c) ^ 2 ≤ K * θ ^ (1 + Work.Spaces.eta) * (∫ t in Set.Ioo 0 θ, G t)) :
    ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), |g θ| ≤ |c| +
      Real.sqrt (K * (Real.pi / 2) ^ (1 + Work.Spaces.eta)
        * (∫ t in Set.Ioo 0 (Real.pi / 2), G t)) := by
  have hpi : (0 : ℝ) < Real.pi / 2 := by linarith [Real.pi_pos]
  have hexp : 0 ≤ 1 + Work.Spaces.eta := by linarith [Work.Spaces.eta_pos]
  have hEfull : 0 ≤ ∫ t in Set.Ioo 0 (Real.pi / 2), G t :=
    MeasureTheory.setIntegral_nonneg measurableSet_Ioo hnn
  have hconst : 0 ≤ K * (Real.pi / 2) ^ (1 + Work.Spaces.eta)
      * (∫ t in Set.Ioo 0 (Real.pi / 2), G t) :=
    mul_nonneg (mul_nonneg hK (Real.rpow_nonneg hpi.le _)) hEfull
  intro θ hθ
  have hrpow : θ ^ (1 + Work.Spaces.eta) ≤ (Real.pi / 2) ^ (1 + Work.Spaces.eta) :=
    Real.rpow_le_rpow hθ.1.le hθ.2.le hexp
  have hmono := tie_setIntegral_mono hint hnn hθ
  have hEθ : 0 ≤ ∫ t in Set.Ioo 0 θ, G t :=
    MeasureTheory.setIntegral_nonneg measurableSet_Ioo
      (fun t ht => hnn t ⟨ht.1, lt_trans ht.2 hθ.2⟩)
  have hsq : (g θ - c) ^ 2 ≤ K * (Real.pi / 2) ^ (1 + Work.Spaces.eta)
      * (∫ t in Set.Ioo 0 (Real.pi / 2), G t) := by
    refine le_trans (hb θ hθ) ?_
    calc K * θ ^ (1 + Work.Spaces.eta) * (∫ t in Set.Ioo 0 θ, G t)
        ≤ K * (Real.pi / 2) ^ (1 + Work.Spaces.eta) * (∫ t in Set.Ioo 0 θ, G t) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hrpow hK) hEθ
      _ ≤ K * (Real.pi / 2) ^ (1 + Work.Spaces.eta)
            * (∫ t in Set.Ioo 0 (Real.pi / 2), G t) :=
          mul_le_mul_of_nonneg_left hmono (mul_nonneg hK (Real.rpow_nonneg hpi.le _))
  calc |g θ| = |(g θ - c) + c| := by ring_nf
    _ ≤ |g θ - c| + |c| := abs_add_le _ _
    _ ≤ Real.sqrt (K * (Real.pi / 2) ^ (1 + Work.Spaces.eta)
          * (∫ t in Set.Ioo 0 (Real.pi / 2), G t)) + |c| :=
        add_le_add_left (tie_abs_le_sqrt hconst hsq) |c|
    _ = |c| + Real.sqrt (K * (Real.pi / 2) ^ (1 + Work.Spaces.eta)
          * (∫ t in Set.Ioo 0 (Real.pi / 2), G t)) := by ring

/-- **Endpoint limits and uniform bounds for angular slices of class `C²` with finite
weighted energy.**

If `f` is `C²` on `(0, π/2)` and the weighted energies `∫ (f)² sin(2θ)^{-η}`,
`∫ (f')² sin(2θ)^{-η}`, `∫ (f'')² sin(2θ)^{-η}` over the closed angular interval `Iθ` are
finite, then `f` and `f'` have limits at both endpoints `0⁺` and `(π/2)⁻`, and both are
bounded on `(0, π/2)`.

The two endpoint limits (and the explicit decay bounds) come from
`Work.EllipticEst.Core.sliceBoundaryLimit` applied to `f` and to `deriv f`; the uniform
bounds are read off from those decay bounds together with the monotonicity of the energy in
the angular variable. -/
theorem thetaInterpEndpoints : ∀ (f : ℝ → ℝ),
    ContDiffOn ℝ 2 f (Set.Ioo 0 (Real.pi / 2)) →
    MeasureTheory.IntegrableOn (fun θ : ℝ => (f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ →
    MeasureTheory.IntegrableOn (fun θ : ℝ => (deriv f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ →
    MeasureTheory.IntegrableOn (fun θ : ℝ => (deriv (deriv f) θ) ^ 2 * Work.FTS.EllipticEst.thEta θ) Work.Spaces.Iθ →
    ∃ F₀ F₁ L₀ L₁ M M' : ℝ,
      Filter.Tendsto f (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds F₀) ∧
      Filter.Tendsto f (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds F₁) ∧
      Filter.Tendsto (deriv f) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds L₀) ∧
      Filter.Tendsto (deriv f) (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds L₁) ∧
      (∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), |f θ| ≤ M) ∧
      (∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), |deriv f θ| ≤ M') := by
  intro f hf _h0 h1 h2
  -- the open interval sits inside `Iθ`
  have hsub : Set.Ioo (0 : ℝ) (Real.pi / 2) ⊆ Work.Spaces.Iθ :=
    fun θ hθ => ⟨hθ.1.le, hθ.2.le⟩
  have h1' : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (deriv f θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
      (Set.Ioo 0 (Real.pi / 2)) := h1.mono_set hsub
  have h2' : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (deriv (deriv f) θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
      (Set.Ioo 0 (Real.pi / 2)) := h2.mono_set hsub
  -- regularity of `f` and of `deriv f` on the open interval
  have hcf : ContDiffOn ℝ 1 f (Set.Ioo 0 (Real.pi / 2)) := hf.of_le (by norm_num)
  have hcd : ContDiffOn ℝ 1 (deriv f) (Set.Ioo 0 (Real.pi / 2)) :=
    hf.deriv_of_isOpen isOpen_Ioo (by norm_num)
  obtain ⟨K, hKpos, hK⟩ := sliceBoundaryLimit
  obtain ⟨⟨F₀, hF₀, hbF₀⟩, ⟨F₁, hF₁, hbF₁⟩⟩ := hK f hcf h1'
  obtain ⟨⟨L₀, hL₀, hbL₀⟩, ⟨L₁, hL₁, hbL₁⟩⟩ := hK (deriv f) hcd h2'
  -- nonnegativity of the two energies, for the monotonicity step
  have hnn1 : ∀ t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      0 ≤ (deriv f t) ^ 2 * Work.FTS.EllipticEst.thEta t := fun t ht =>
    mul_nonneg (sq_nonneg _)
      (Work.FTS.EllipticEst.thEta_nonneg ⟨ht.1.le, ht.2.le⟩)
  have hnn2 : ∀ t ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      0 ≤ (deriv (deriv f) t) ^ 2 * Work.FTS.EllipticEst.thEta t := fun t ht =>
    mul_nonneg (sq_nonneg _)
      (Work.FTS.EllipticEst.thEta_nonneg ⟨ht.1.le, ht.2.le⟩)
  exact ⟨F₀, F₁, L₀, L₁,
    |F₀| + Real.sqrt (K * (Real.pi / 2) ^ (1 + Work.Spaces.eta)
      * (∫ t in Set.Ioo 0 (Real.pi / 2), (deriv f t) ^ 2 * Work.FTS.EllipticEst.thEta t)),
    |L₀| + Real.sqrt (K * (Real.pi / 2) ^ (1 + Work.Spaces.eta)
      * (∫ t in Set.Ioo 0 (Real.pi / 2),
          (deriv (deriv f) t) ^ 2 * Work.FTS.EllipticEst.thEta t)),
    hF₀, hF₁, hL₀, hL₁,
    tie_bound_of_limit_bound hKpos.le h1' hnn1 hbF₀,
    tie_bound_of_limit_bound hKpos.le h2' hnn2 hbL₀⟩

end Work.EllipticEst.Core
