import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Spaces.HkSq_terms

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsE4Thr.FstarJepsSmoothAux

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

/-! ## The `z`-slice estimate of the marginal `H^1`-integrand

For `W ∈ C^∞` on the open quadrant `(0,∞) × (0,π/2)` and in the weighted space
`ℋ¹`, the `z`-slice of `W` and of its radial derivative `∂_z W` on a positive interval
`[c,d]` is dominated by the `z`-slice of the marginal `H^1`-integrand `HkIntegrand α 1 W`,
with the constant `1 / min 1 (c²)`.

The proof is elementary: writing
`A z θ = w z / sin(2θ)^{η/2}`, the definition of `HkIntegrand` at `k = 1` unfolds to
`(W · A)² + (D_z W · A)² + (D_θ W · W_t)²`, and on `z ≥ c > 0`, `θ ∈ (0,π/2)` one has
`A ≥ 1` (since `w z ≥ 1` and `sin(2θ)^{η/2} ≤ 1`) and `z · A ≥ 1` (since
`z · w z = (1+z)²/z ≥ 1`), so that

`W² + (∂_z W)² ≤ (1/min 1 (c²)) · ((W·A)² + (z ∂_z W · A)²) ≤ (1/min 1 (c²)) · HkIntegrand`.

Integrating over `[c,d]` (all the slices are continuous, hence integrable, on the compact
interval) gives the claim. -/

/-- `sin (2θ) > 0` for `θ` in the open angular interval. -/
private lemma sin_two_pos_of_mem {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    0 < Real.sin (2 * θ) :=
  Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])

/-- The `H^1`-integrand written out: at `k = 1` the two sums of `HkIntegrand` collapse to
the three terms `(W · A)²`, `(D_z W · A)²` and `(D_θ W · W_t)²`. -/
theorem HkIntegrand_one (α : ℝ) (W : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.HkIntegrand α 1 W z θ
      = (W z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
        + ((z * Work.Spaces.pz W z θ)
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
        + (Work.Spaces.Dth W z θ * Work.Spaces.Wt α z θ) ^ 2 := by
  rw [Work.Spaces.HkIntegrand]
  simp only [Finset.sum_range_succ, Finset.sum_range_zero,
    Work.Spaces.DzIter_zero, Work.Spaces.DzIter_succ, Work.Spaces.Dz, Work.Spaces.mixed,
    Work.Spaces.DthIter_succ, Work.Spaces.DthIter_zero]
  norm_num

theorem zSlice_sq_le_marginal {α : ℝ} {W : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen W) (hmem : Work.Spaces.HkMem α 1 W)
    {c d : ℝ} (hc : 0 < c) (hcd : c ≤ d) {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    (∫ z in Set.Icc c d, (W z θ) ^ 2) + (∫ z in Set.Icc c d, (Work.Spaces.pz W z θ) ^ 2)
      ≤ 1 / (min 1 (c ^ 2)) * ∫ z in Set.Icc c d, Work.Spaces.HkIntegrand α 1 W z θ := by
  -- this elementary slice estimate uses only the open-quadrant smoothness of `W`
  have _hmem := hmem
  have _hcd := hcd
  have hs_pos : 0 < Real.sin (2 * θ) := sin_two_pos_of_mem hθ
  have hp_pos : 0 < (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) :=
    Real.rpow_pos_of_pos hs_pos _
  have hp_le_one : (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) ≤ 1 := by
    refine Real.rpow_le_one hs_pos.le (Real.sin_le_one _) ?_
    norm_num [Work.Spaces.eta]
  have hm_pos : 0 < min 1 (c ^ 2) := lt_min one_pos (by positivity)
  have hm_le_one : min 1 (c ^ 2) ≤ 1 := min_le_left _ _
  have hinv_pos : 0 < 1 / (min 1 (c ^ 2)) := div_pos one_pos hm_pos
  -- the slice `z ↦ w z` is continuous on `[c,d]` (where `z ≥ c > 0`)
  have hw_cont : ContinuousOn (fun z : ℝ => Work.Spaces.w z) (Set.Icc c d) := by
    show ContinuousOn (fun z : ℝ => (1 + z) ^ 2 / z ^ 2) (Set.Icc c d)
    refine ContinuousOn.div ((ContinuousOn.const_add continuousOn_id 1).pow 2)
      (continuousOn_id.pow 2) (fun z hz => ?_)
    exact pow_ne_zero 2 (ne_of_gt (lt_of_lt_of_le hc hz.1))
  -- continuity of the `z`-slices of the ingredients of `HkIntegrand`
  have hcontW : ContinuousOn (fun z => W z θ) (Set.Icc c d) :=
    (hsm.curry_z hθ).continuousOn.mono (fun z hz => lt_of_lt_of_le hc hz.1)
  have hcontPz : ContinuousOn (fun z => Work.Spaces.pz W z θ) (Set.Icc c d) :=
    (hsm.pz.curry_z hθ).continuousOn.mono (fun z hz => lt_of_lt_of_le hc hz.1)
  have hcontDth : ContinuousOn (fun z => Work.Spaces.Dth W z θ) (Set.Icc c d) :=
    (hsm.Dth.curry_z hθ).continuousOn.mono (fun z hz => lt_of_lt_of_le hc hz.1)
  have hcontWt : ContinuousOn (fun z => Work.Spaces.Wt α z θ) (Set.Icc c d) :=
    (hw_cont.mul (continuousOn_const : ContinuousOn (fun _ : ℝ => Work.Spaces.wTheta α θ)
      (Set.Icc c d))).congr (fun z _ => rfl)
  have hcontA : ContinuousOn
      (fun z => Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))
      (Set.Icc c d) :=
    hw_cont.div continuousOn_const (fun z _ => ne_of_gt hp_pos)
  have hcontHk : ContinuousOn (fun z => Work.Spaces.HkIntegrand α 1 W z θ) (Set.Icc c d) := by
    have h1 : ContinuousOn
        (fun z => W z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)))
        (Set.Icc c d) := hcontW.mul hcontA
    have h2 : ContinuousOn
        (fun z => (z * Work.Spaces.pz W z θ)
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)))
        (Set.Icc c d) := (continuousOn_id.mul hcontPz).mul hcontA
    have h3 : ContinuousOn (fun z => Work.Spaces.Dth W z θ * Work.Spaces.Wt α z θ)
        (Set.Icc c d) := hcontDth.mul hcontWt
    have hsum := (h1.pow 2).add ((h2.pow 2).add (h3.pow 2))
    refine hsum.congr ?_
    intro z _
    simp only [Pi.pow_apply, Pi.add_apply]
    rw [HkIntegrand_one]
    ring
  -- integrability of the three slices
  have hintHk : IntegrableOn (fun z => Work.Spaces.HkIntegrand α 1 W z θ) (Set.Icc c d) :=
    hcontHk.integrableOn_compact isCompact_Icc
  have hintW2 : IntegrableOn (fun z => (W z θ) ^ 2) (Set.Icc c d) :=
    (hcontW.pow 2).integrableOn_compact isCompact_Icc
  have hintPz2 : IntegrableOn (fun z => (Work.Spaces.pz W z θ) ^ 2) (Set.Icc c d) :=
    (hcontPz.pow 2).integrableOn_compact isCompact_Icc
  -- the pointwise bound on `[c,d]`
  have hpt : ∀ z ∈ Set.Icc c d,
      (W z θ) ^ 2 + (Work.Spaces.pz W z θ) ^ 2
        ≤ 1 / (min 1 (c ^ 2)) * Work.Spaces.HkIntegrand α 1 W z θ := by
    intro z hz
    have hz_pos : 0 < z := lt_of_lt_of_le hc hz.1
    have hw_ge_one : 1 ≤ Work.Spaces.w z := by
      rw [Work.Spaces.w, le_div_iff₀ (by positivity : 0 < z ^ 2)]
      nlinarith
    have hA_ge_one : 1 ≤ Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) := by
      rw [le_div_iff₀ hp_pos]
      simpa using le_trans hp_le_one hw_ge_one
    have hdiv_id : z * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))
        = (1 + z) ^ 2 / (z * (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) := by
      rw [Work.Spaces.w]
      field_simp
    have hzA_ge_one : 1 ≤ z * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) := by
      rw [hdiv_id, le_div_iff₀ (by positivity : 0 < z * (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))]
      nlinarith [hp_le_one, hz_pos]
    have hm_le_sq : min 1 (c ^ 2)
        ≤ (z * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
      have h1 : (1 : ℝ)
          ≤ (z * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
        nlinarith [hzA_ge_one]
      exact le_trans (min_le_left 1 (c ^ 2)) h1
    have hW_sq : (W z θ) ^ 2
        ≤ 1 / (min 1 (c ^ 2))
          * (W z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
      have hconv : 1 / (min 1 (c ^ 2))
            * (W z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
          = (W z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
              / (min 1 (c ^ 2)) := by ring
      rw [hconv, le_div_iff₀ hm_pos]
      have hA_sq : (1 : ℝ)
          ≤ (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2 := by
        nlinarith [hA_ge_one, sq_nonneg
          (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2) - 1)]
      have h1 := mul_le_mul_of_nonneg_left (le_trans hm_le_one hA_sq) (sq_nonneg (W z θ))
      have h2 : (W z θ) ^ 2
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2
          = (W z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
        ring
      linarith [h1, h2]
    have hpz_sq : (Work.Spaces.pz W z θ) ^ 2
        ≤ 1 / (min 1 (c ^ 2))
          * (z * Work.Spaces.pz W z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
      have hconv : 1 / (min 1 (c ^ 2))
            * (z * Work.Spaces.pz W z θ
                * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
          = (z * Work.Spaces.pz W z θ
                * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
              / (min 1 (c ^ 2)) := by ring
      rw [hconv, le_div_iff₀ hm_pos]
      have h1 := mul_le_mul_of_nonneg_left hm_le_sq (sq_nonneg (Work.Spaces.pz W z θ))
      have h2 : (Work.Spaces.pz W z θ) ^ 2
            * (z * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
          = (z * Work.Spaces.pz W z θ
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
        ring
      linarith [h1, h2]
    have hinner : (W z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
        + (z * Work.Spaces.pz W z θ
            * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
        ≤ Work.Spaces.HkIntegrand α 1 W z θ := by
      rw [HkIntegrand_one]
      nlinarith [sq_nonneg (Work.Spaces.Dth W z θ * Work.Spaces.Wt α z θ)]
    have hsum2 : (W z θ) ^ 2 + (Work.Spaces.pz W z θ) ^ 2
        ≤ 1 / (min 1 (c ^ 2))
          * ((W z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
            + (z * Work.Spaces.pz W z θ
                * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2) := by
      rw [mul_add]
      linarith [hW_sq, hpz_sq]
    calc (W z θ) ^ 2 + (Work.Spaces.pz W z θ) ^ 2
        ≤ 1 / (min 1 (c ^ 2))
          * ((W z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
            + (z * Work.Spaces.pz W z θ
                * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2) := hsum2
      _ ≤ 1 / (min 1 (c ^ 2)) * Work.Spaces.HkIntegrand α 1 W z θ :=
          mul_le_mul_of_nonneg_left hinner (le_of_lt hinv_pos)
  -- integrate the pointwise bound
  have hsum_int : (∫ z in Set.Icc c d,
        ((W z θ) ^ 2 + (Work.Spaces.pz W z θ) ^ 2))
      = (∫ z in Set.Icc c d, (W z θ) ^ 2)
        + ∫ z in Set.Icc c d, (Work.Spaces.pz W z θ) ^ 2 :=
    integral_add hintW2 hintPz2
  have hmono : (∫ z in Set.Icc c d, ((W z θ) ^ 2 + (Work.Spaces.pz W z θ) ^ 2))
      ≤ ∫ z in Set.Icc c d, 1 / (min 1 (c ^ 2)) * Work.Spaces.HkIntegrand α 1 W z θ := by
    refine integral_mono_of_nonneg (Eventually.of_forall (fun z => by positivity)) ?_
      (ae_restrict_of_forall_mem measurableSet_Icc hpt)
    exact hintHk.const_mul _
  calc (∫ z in Set.Icc c d, (W z θ) ^ 2) + (∫ z in Set.Icc c d, (Work.Spaces.pz W z θ) ^ 2)
      = (∫ z in Set.Icc c d, ((W z θ) ^ 2 + (Work.Spaces.pz W z θ) ^ 2)) := hsum_int.symm
    _ ≤ ∫ z in Set.Icc c d, 1 / (min 1 (c ^ 2)) * Work.Spaces.HkIntegrand α 1 W z θ := hmono
    _ = 1 / (min 1 (c ^ 2)) * ∫ z in Set.Icc c d, Work.Spaces.HkIntegrand α 1 W z θ :=
        integral_const_mul _ _

end Work.FTS.StrongEps.EpsE4Thr.FstarJepsSmoothAux
