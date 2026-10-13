import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.StrongPersist.N6Trans.Hon.TraceOsc

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.N6Trans.Hon

set_option autoImplicit false
/-! ## The traces from the two weighted `L²`-bounds -/

/-- **The boundary traces from the weighted `L²`-bounds.**  For `v` differentiable on
`(0,∞)` with `∫ w² v² < ∞` and `∫ w² (D_z v)² < ∞` on both `(0,1)` and `(1,∞)`
(`w² = (1+z)⁴/z⁴`), the trace `z w(z)² v(z)²` vanishes at `0⁺` and at `+∞`. -/
theorem trace_of_weights {v : ℝ → ℝ}
    (hv : ∀ z ∈ Set.Ioi (0 : ℝ), DifferentiableAt ℝ v z)
    (h1 : IntegrableOn (fun z => (Work.Spaces.w z) ^ 2 * v z ^ 2) (Set.Ioo (0 : ℝ) 1))
    (h2 : IntegrableOn (fun z => (Work.Spaces.w z) ^ 2 * (z * deriv v z) ^ 2) (Set.Ioo (0 : ℝ) 1))
    (h3 : IntegrableOn (fun z => (Work.Spaces.w z) ^ 2 * v z ^ 2) (Set.Ioi (1 : ℝ)))
    (h4 : IntegrableOn (fun z => (Work.Spaces.w z) ^ 2 * (z * deriv v z) ^ 2) (Set.Ioi (1 : ℝ))) :
    Tendsto (fun z => z * (v z * Work.Spaces.w z) ^ 2) (𝓝[>] (0 : ℝ)) (𝓝 0) ∧
      Tendsto (fun z => z * (v z * Work.Spaces.w z) ^ 2) atTop (𝓝 0) := by
  set ψ : ℝ → ℝ := fun z => v z ^ 2 / z ^ 3 with hψ
  set χ : ℝ → ℝ := fun z => z * v z ^ 2 with hχ
  -- `ψ` and its derivative bound on `(0,1)`
  have hψderiv : ∀ z ∈ Set.Ioo (0 : ℝ) 1,
      HasDerivAt ψ ((2 * v z * (z * deriv v z) - 3 * v z ^ 2) / z ^ 4) z := by
    intro z hz
    have hz0 : 0 < z := hz.1
    have hnum : HasDerivAt (fun z : ℝ => v z ^ 2) (2 * v z ^ (2 - 1) * deriv v z) z :=
      (hv z hz0).hasDerivAt.pow 2
    have hden : HasDerivAt (fun z : ℝ => z ^ 3) (3 * z ^ (3 - 1)) z := hasDerivAt_pow 3 z
    have h4 := hnum.div hden (by positivity)
    rw [hψ]
    convert h4 using 1
    field_simp
    ring
  have hψbound : ∀ z ∈ Set.Ioo (0 : ℝ) 1,
      ‖deriv ψ z‖ ≤ 4 * ((Work.Spaces.w z) ^ 2 * v z ^ 2)
        + (Work.Spaces.w z) ^ 2 * (z * deriv v z) ^ 2 := by
    intro z hz
    have hz0 : 0 < z := hz.1
    have hd : deriv ψ z = (2 * v z * (z * deriv v z) - 3 * v z ^ 2) / z ^ 4 :=
      (hψderiv z hz).deriv
    have hw : 1 / z ^ 4 ≤ (Work.Spaces.w z) ^ 2 := one_div_zpow_four_le_w_sq hz0
    have hb : |2 * v z * (z * deriv v z) - 3 * v z ^ 2| ≤ 4 * v z ^ 2 + (z * deriv v z) ^ 2 := by
      have h1 : |2 * v z * (z * deriv v z)| ≤ v z ^ 2 + (z * deriv v z) ^ 2 := by
        rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
        have := two_mul_le_add_sq (|v z|) (|z * deriv v z|)
        rw [sq_abs (v z), sq_abs (z * deriv v z)] at this
        linarith [this]
      have h2 : |3 * v z ^ 2| = 3 * v z ^ 2 := by
        rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3), abs_of_nonneg (sq_nonneg _)]
      have h3 : |2 * v z * (z * deriv v z) - 3 * v z ^ 2|
          ≤ |2 * v z * (z * deriv v z)| + |3 * v z ^ 2| := by
        have h := abs_sub_le (2 * v z * (z * deriv v z)) 0 (3 * v z ^ 2)
        simpa only [sub_zero, zero_sub, abs_neg] using h
      linarith [h3, h1, h2.le, h2.ge]
    rw [Real.norm_eq_abs, hd, abs_div, abs_of_pos (by positivity : (0 : ℝ) < z ^ 4)]
    have hw4 : v z ^ 2 / z ^ 4 ≤ (Work.Spaces.w z) ^ 2 * v z ^ 2 := by
      calc v z ^ 2 / z ^ 4 = (1 / z ^ 4) * v z ^ 2 := by ring
        _ ≤ (Work.Spaces.w z) ^ 2 * v z ^ 2 := mul_le_mul_of_nonneg_right hw (sq_nonneg _)
    have hw5 : (z * deriv v z) ^ 2 / z ^ 4
        ≤ (Work.Spaces.w z) ^ 2 * (z * deriv v z) ^ 2 := by
      calc (z * deriv v z) ^ 2 / z ^ 4 = (1 / z ^ 4) * (z * deriv v z) ^ 2 := by ring
        _ ≤ (Work.Spaces.w z) ^ 2 * (z * deriv v z) ^ 2 :=
            mul_le_mul_of_nonneg_right hw (sq_nonneg _)
    calc |2 * v z * (z * deriv v z) - 3 * v z ^ 2| / z ^ 4
        ≤ (4 * v z ^ 2 + (z * deriv v z) ^ 2) / z ^ 4 := by
          rw [div_le_div_iff_of_pos_right (by positivity)]
          exact hb
      _ = 4 * (v z ^ 2 / z ^ 4) + (z * deriv v z) ^ 2 / z ^ 4 := by ring
      _ ≤ 4 * ((Work.Spaces.w z) ^ 2 * v z ^ 2)
            + (Work.Spaces.w z) ^ 2 * (z * deriv v z) ^ 2 := by linarith [hw4, hw5]
  have hψcont : ContinuousOn (fun z : ℝ => v z ^ 2 / z ^ 3 / z) (Set.Ioo (0 : ℝ) 1) := by
    refine ContinuousOn.div ?_ continuousOn_id (fun z hz => ne_of_gt hz.1)
    refine ContinuousOn.div ?_ (continuousOn_id.pow 3) (fun z hz => ne_of_gt (pow_pos hz.1 3))
    have hvcont : ContinuousOn (fun z : ℝ => v z) (Set.Ioo (0 : ℝ) 1) := by
      intro z hz
      exact (hv z hz.1).continuousAt.continuousWithinAt
    exact hvcont.pow 2
  have hψdiv : IntegrableOn (fun z => ψ z / z) (Set.Ioo (0 : ℝ) 1) := by
    have hpt : ∀ᵐ z ∂(volume.restrict (Set.Ioo (0 : ℝ) 1)),
        ‖ψ z / z‖ ≤ (Work.Spaces.w z) ^ 2 * v z ^ 2 := by
      rw [ae_restrict_iff' measurableSet_Ioo]
      refine Filter.Eventually.of_forall fun z hz => ?_
      have hz0 : 0 < z := hz.1
      have hw : 1 / z ^ 4 ≤ (Work.Spaces.w z) ^ 2 := one_div_zpow_four_le_w_sq hz0
      have h : ψ z / z = (1 / z ^ 4) * v z ^ 2 := by
        rw [hψ]; field_simp
      rw [Real.norm_eq_abs, h, abs_of_nonneg (mul_nonneg (by positivity) (sq_nonneg _))]
      exact mul_le_mul_of_nonneg_right hw (sq_nonneg _)
    refine Integrable.mono' h1 ?_ hpt
    refine (hψcont.aestronglyMeasurable measurableSet_Ioo).congr ?_
    filter_upwards with z
    rw [hψ]
  have hψder : IntegrableOn (deriv ψ) (Set.Ioo (0 : ℝ) 1) := by
    have hint : IntegrableOn
        (fun z => 4 * ((Work.Spaces.w z) ^ 2 * v z ^ 2)
          + (Work.Spaces.w z) ^ 2 * (z * deriv v z) ^ 2) (Set.Ioo (0 : ℝ) 1) :=
      Integrable.add (Integrable.const_mul h1 4) h2
    refine Integrable.mono' hint (measurable_deriv ψ).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with z hz
    exact hψbound z hz
  have hψdiff : ∀ z ∈ Set.Ioo (0 : ℝ) 1, DifferentiableAt ℝ ψ z :=
    fun z hz => (hψderiv z hz).differentiableAt
  have hψnn : ∀ z ∈ Set.Ioo (0 : ℝ) 1, 0 ≤ ψ z := by
    intro z hz
    rw [hψ]
    exact div_nonneg (sq_nonneg _) (pow_nonneg (le_of_lt hz.1) 3)
  have hψ0 : Tendsto ψ (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    tendsto_zero_of_integrableOn_deriv_left hψdiff hψnn hψdiv hψder
  -- `χ` and its derivative bound on `(1,∞)`
  have hχderiv : ∀ z ∈ Set.Ioi (1 : ℝ),
      HasDerivAt χ (v z ^ 2 + 2 * v z * (z * deriv v z)) z := by
    intro z hz
    have hz0 : 0 < z := lt_trans zero_lt_one hz
    have hvz : HasDerivAt v (deriv v z) z := (hv z hz0).hasDerivAt
    have hmul := (hasDerivAt_id z).mul (hvz.pow 2)
    have hfun : (id * v ^ 2 : ℝ → ℝ) = χ := by
      rw [hχ]; funext y; rfl
    rw [hfun] at hmul
    convert hmul using 1
    have h21 : (2 : ℕ) - 1 = 1 := by norm_num
    simp only [Pi.pow_apply, id_eq, one_mul, h21, pow_one]
    ring
  have hχbound : ∀ z ∈ Set.Ioi (1 : ℝ),
      ‖deriv χ z‖ ≤ 2 * ((Work.Spaces.w z) ^ 2 * v z ^ 2)
        + (Work.Spaces.w z) ^ 2 * (z * deriv v z) ^ 2 := by
    intro z hz
    have hz0 : 0 < z := lt_trans zero_lt_one hz
    have hd : deriv χ z = v z ^ 2 + 2 * v z * (z * deriv v z) := (hχderiv z hz).deriv
    have hw : 1 ≤ (Work.Spaces.w z) ^ 2 := one_le_w_sq hz0
    have hb : |v z ^ 2 + 2 * v z * (z * deriv v z)| ≤ 2 * v z ^ 2 + (z * deriv v z) ^ 2 := by
      have h1 : |2 * v z * (z * deriv v z)| ≤ v z ^ 2 + (z * deriv v z) ^ 2 := by
        rw [abs_mul, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
        have := two_mul_le_add_sq (|v z|) (|z * deriv v z|)
        rw [sq_abs (v z), sq_abs (z * deriv v z)] at this
        linarith [this]
      have h2 : |v z ^ 2| = v z ^ 2 := abs_of_nonneg (sq_nonneg _)
      have h3 : |v z ^ 2 + 2 * v z * (z * deriv v z)|
          ≤ |v z ^ 2| + |2 * v z * (z * deriv v z)| := abs_add_le _ _
      linarith [h3, h1, h2.le, h2.ge]
    rw [Real.norm_eq_abs, hd]
    have h6 : v z ^ 2 ≤ (Work.Spaces.w z) ^ 2 * v z ^ 2 := by
      nlinarith [hw, sq_nonneg (v z)]
    have h7 : (z * deriv v z) ^ 2 ≤ (Work.Spaces.w z) ^ 2 * (z * deriv v z) ^ 2 := by
      nlinarith [hw, sq_nonneg (z * deriv v z)]
    linarith [hb, h6, h7]
  have hχcont : ContinuousOn (fun z : ℝ => z * v z ^ 2 / z) (Set.Ioi (1 : ℝ)) := by
    refine ContinuousOn.div ?_ continuousOn_id (fun z hz => ne_of_gt (lt_trans zero_lt_one hz))
    have hvcont : ContinuousOn (fun z : ℝ => v z) (Set.Ioi (1 : ℝ)) := by
      intro z hz
      exact (hv z (lt_trans (zero_lt_one : (0 : ℝ) < 1) hz)).continuousAt.continuousWithinAt
    exact continuousOn_id.mul (hvcont.pow 2)
  have hχdiv : IntegrableOn (fun z => χ z / z) (Set.Ioi (1 : ℝ)) := by
    have hpt : ∀ᵐ z ∂(volume.restrict (Set.Ioi (1 : ℝ))),
        ‖χ z / z‖ ≤ (Work.Spaces.w z) ^ 2 * v z ^ 2 := by
      rw [ae_restrict_iff' measurableSet_Ioi]
      refine Filter.Eventually.of_forall fun z hz => ?_
      have hw : 1 ≤ (Work.Spaces.w z) ^ 2 := one_le_w_sq (lt_trans zero_lt_one hz)
      have hz0 : z ≠ 0 := ne_of_gt (lt_trans (zero_lt_one : (0 : ℝ) < 1) hz)
      have h : χ z / z = v z ^ 2 := by
        change z * v z ^ 2 / z = v z ^ 2
        field_simp
      rw [Real.norm_eq_abs, h, abs_of_nonneg (sq_nonneg _)]
      nlinarith [hw, sq_nonneg (v z)]
    refine Integrable.mono' h3 ?_ hpt
    refine (hχcont.aestronglyMeasurable measurableSet_Ioi).congr ?_
    filter_upwards with z
    rw [hχ]
  have hχder : IntegrableOn (deriv χ) (Set.Ioi (1 : ℝ)) := by
    have hint : IntegrableOn
        (fun z => 2 * ((Work.Spaces.w z) ^ 2 * v z ^ 2)
          + (Work.Spaces.w z) ^ 2 * (z * deriv v z) ^ 2) (Set.Ioi (1 : ℝ)) :=
      Integrable.add (Integrable.const_mul h3 2) h4
    refine Integrable.mono' hint (measurable_deriv χ).aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with z hz
    exact hχbound z hz
  have hχdiff : ∀ z ∈ Set.Ioi (1 : ℝ), DifferentiableAt ℝ χ z :=
    fun z hz => (hχderiv z hz).differentiableAt
  have hχnn : ∀ z ∈ Set.Ioi (1 : ℝ), 0 ≤ χ z := by
    intro z hz
    rw [hχ]
    exact mul_nonneg (le_of_lt (lt_trans zero_lt_one hz)) (sq_nonneg _)
  have hχ0 : Tendsto χ atTop (𝓝 0) :=
    tendsto_zero_of_integrableOn_deriv_atTop hχdiff hχnn hχdiv hχder
  constructor
  · -- left end: `z (v w)² = (1+z)⁴ ψ`
    have hlim1 : Tendsto (fun z : ℝ => (1 + z) ^ 4) (𝓝[>] (0 : ℝ)) (𝓝 1) := by
      have h : ContinuousAt (fun z : ℝ => (1 + z) ^ 4) 0 := by fun_prop
      simpa using h.tendsto.mono_left nhdsWithin_le_nhds
    have h := hlim1.mul hψ0
    simp only [one_mul] at h
    refine h.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with z hz
    exact (z_mul_w_sq_mul z (v z) (ne_of_gt hz)).symm
  · -- right end: `z (v w)² = w² χ`
    have hlim1 : Tendsto (fun z : ℝ => (Work.Spaces.w z) ^ 2) atTop (𝓝 1) := by
      have h1 : Tendsto (fun z : ℝ => (1 + z) / z) atTop (𝓝 1) := by
        have heq : ∀ᶠ z : ℝ in atTop, 1 / z + 1 = (1 + z) / z := by
          filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with z hz
          field_simp
        have hinv : Tendsto (fun z : ℝ => z⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
        have h2 : Tendsto (fun z : ℝ => 1 / z + 1) atTop (𝓝 1) := by
          simpa [one_div, add_comm] using hinv.const_add 1
        exact h2.congr' heq
      have h2 : Tendsto (fun z : ℝ => (((1 + z) / z) ^ 2) ^ 2) atTop (𝓝 1) := by
        simpa using (h1.pow 2).pow 2
      refine h2.congr' (Filter.Eventually.of_forall (fun z => ?_))
      have hq : (((1 + z) / z) ^ 2) ^ 2 = (1 + z) ^ 4 / z ^ 4 := by
        rw [← pow_mul, div_pow, show (2 : ℕ) * 2 = 4 from by norm_num]
      rw [hq]
      exact (w_sq_eq z).symm
    have h := hlim1.mul hχ0
    simp only [one_mul] at h
    refine h.congr' ?_
    filter_upwards with z
    exact (z_mul_w_sq_mul' z (v z)).symm

end Work.FTS.StrongPersist.N6Trans.Hon
