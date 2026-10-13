import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Submission.Work.Spaces.Defs
import Submission.Work.Construction.Defs
import Submission.Work.Construction.L12_Fstar_eq
import Submission.Work.Elliptic.L12Aux
import Submission.Work.FTS.Nonlinear.FstarPkg.L12_Fstar_eq_of_gt_neg_one
import Submission.Work.FTS_RegExport.RXB.l12_aux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_StreamBdry.Inputs

set_option maxHeartbeats 1000000

noncomputable section

open MeasureTheory Set Filter

open scoped Topology

/-! ## Self-contained proofs of the two remaining scalar inputs

These are the two independent scalar facts the `theta_part_jets` assembly needs; they are proved
here (self-contained, no `sorry`) so that the assembly does not depend on scratch material. -/

/-- **Tail majorant of `√s/(1+s)²`.** -/
theorem majorant_sqrt_tail' : ∃ C : ℝ, 0 < C ∧ ∀ z : ℝ, 0 < z →
    IntegrableOn (fun s : ℝ => s ^ ((1 : ℝ) / 2) / (1 + s) ^ 2) (Set.Ioi z) ∧
    ∫ s in Set.Ioi z, s ^ ((1 : ℝ) / 2) / (1 + s) ^ 2 ≤ C := by
  refine ⟨4, by norm_num, ?_⟩
  intro z hz
  -- continuity of the two integrands on the open half-line
  have hc_f : ContinuousOn (fun s : ℝ => s ^ ((1 : ℝ) / 2) / (1 + s) ^ 2) (Set.Ioi z) := by
    refine ContinuousOn.div ?_ ?_ ?_
    · exact continuousOn_id.rpow_const (fun s hs => Or.inl (ne_of_gt (lt_trans hz hs)))
    · exact (continuousOn_const.add continuousOn_id).pow 2
    · intro s hs
      have : (0 : ℝ) < 1 + s := by linarith [lt_trans hz hs]
      positivity
  have hc_g' : ContinuousOn (fun s : ℝ => (1 + s) ^ (-(3 : ℝ) / 2)) (Set.Ioi z) := by
    refine ContinuousOn.rpow_const (continuousOn_const.add continuousOn_id) (fun s hs => Or.inl (by
      have : (0 : ℝ) < 1 + s := by linarith [lt_trans hz hs]
      positivity))
  have hc_g : ContinuousOn (fun s : ℝ => 2 * (1 + s) ^ (-(3 : ℝ) / 2)) (Set.Ioi z) :=
    hc_g'.const_mul 2
  -- integrability of the majorant `2(1+s)^{-3/2}` (dominated by `s^{-3/2}`)
  have hint_g' : IntegrableOn (fun s : ℝ => (1 + s) ^ (-(3 : ℝ) / 2)) (Set.Ioi z) := by
    refine Integrable.mono'
      (integrableOn_Ioi_rpow_of_lt (by norm_num : (-(3 : ℝ) / 2) < -1) hz)
      (hc_g'.aestronglyMeasurable measurableSet_Ioi) ?_
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with s hs
    have hs0 : (0 : ℝ) < s := lt_trans hz hs
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (by linarith) _)]
    exact Real.rpow_le_rpow_of_nonpos hs0 (by linarith) (by norm_num)
  have hint_g : IntegrableOn (fun s : ℝ => 2 * (1 + s) ^ (-(3 : ℝ) / 2)) (Set.Ioi z) :=
    hint_g'.const_mul 2
  -- the value of the majorant integral, by the fundamental theorem of calculus
  have hderiv : ∀ x ∈ Set.Ioi z,
      HasDerivAt (fun s : ℝ => -2 * (1 + s) ^ (-(1 : ℝ) / 2)) ((1 + x) ^ (-(3 : ℝ) / 2)) x := by
    intro x hx
    have hx0 : (0 : ℝ) < 1 + x := by linarith [lt_trans hz hx]
    have hlin : HasDerivAt (fun s : ℝ => 1 + s) 1 x := (hasDerivAt_id x).const_add 1
    have hinner := (Real.hasDerivAt_rpow_const (x := 1 + x) (p := -(1 : ℝ) / 2)
      (Or.inl (ne_of_gt hx0))).comp x hlin
    have h1 := hinner.const_mul (-2)
    convert h1 using 1
    · ext s; simp [Function.comp_apply]
    · rw [show (-(1 : ℝ) / 2) - 1 = -(3 : ℝ) / 2 from by norm_num]; ring
  have hFTC : ∫ s in Set.Ioi z, (1 + s) ^ (-(3 : ℝ) / 2) = 2 * (1 + z) ^ (-(1 : ℝ) / 2) := by
    have hcont : ContinuousWithinAt (fun s : ℝ => -2 * (1 + s) ^ (-(1 : ℝ) / 2))
        (Set.Ici z) z := by
      refine ContinuousAt.continuousWithinAt ?_
      have hz0 : (0 : ℝ) < 1 + z := by linarith
      have h2 : ContinuousAt (fun s : ℝ => (1 + s) ^ (-(1 : ℝ) / 2)) z :=
        (Real.continuousAt_rpow_const (x := 1 + z) (-(1 : ℝ) / 2)
          (Or.inl (ne_of_gt hz0))).comp (continuousAt_const.add continuousAt_id)
      exact h2.const_mul (-2)
    have htend : Tendsto (fun s : ℝ => -2 * (1 + s) ^ (-(1 : ℝ) / 2)) atTop (𝓝 0) := by
      have hlin_t : Tendsto (fun s : ℝ => 1 + s) atTop atTop :=
        tendsto_atTop_mono' atTop (Filter.Eventually.of_forall
          (fun s => le_add_of_nonneg_left zero_le_one)) tendsto_id
      have h1 : Tendsto (fun s : ℝ => (1 + s) ^ (-(1 : ℝ) / 2)) atTop (𝓝 0) := by
        have h := (tendsto_rpow_neg_atTop (y := (1 : ℝ) / 2)
          (by norm_num : (0 : ℝ) < 1 / 2)).comp hlin_t
        convert h using 1
        ext s
        simp only [Function.comp_apply]
        congr 1
        norm_num
      simpa using h1.const_mul (-2)
    have h := integral_Ioi_of_hasDerivAt_of_tendsto (a := z) (f := fun s : ℝ =>
      -2 * (1 + s) ^ (-(1 : ℝ) / 2)) (f' := fun s : ℝ => (1 + s) ^ (-(3 : ℝ) / 2))
      (m := 0) hcont hderiv hint_g' htend
    rw [h]
    ring
  -- integrability of the target
  have hint_f : IntegrableOn (fun s : ℝ => s ^ ((1 : ℝ) / 2) / (1 + s) ^ 2) (Set.Ioi z) := by
    have h0 : IntegrableOn (fun s : ℝ => Real.sqrt s / (1 + s) ^ 2) (Set.Ioi z) :=
      (Work.FTS_RegExport.RXB.integrableOn_sqrt_div_sq).mono_set (Set.Ioi_subset_Ioi hz.le)
    refine h0.congr ?_
    filter_upwards with s
    rw [Real.sqrt_eq_rpow]
  -- the pointwise domination
  have hpt : ∀ᵐ s ∂(volume.restrict (Set.Ioi z)),
      s ^ ((1 : ℝ) / 2) / (1 + s) ^ 2 ≤ 2 * (1 + s) ^ (-(3 : ℝ) / 2) := by
    filter_upwards [self_mem_ae_restrict measurableSet_Ioi] with s hs
    have hs0 : (0 : ℝ) < s := lt_trans hz hs
    have h1s : (0 : ℝ) < 1 + s := by linarith
    have hroot : s ^ ((1 : ℝ) / 2) ≤ 2 * (1 + s) ^ ((1 : ℝ) / 2) := by
      have h1 : s ^ ((1 : ℝ) / 2) ≤ (4 * (1 + s)) ^ ((1 : ℝ) / 2) :=
        Real.rpow_le_rpow hs0.le (by linarith) (by norm_num)
      have h2 : (4 * (1 + s)) ^ ((1 : ℝ) / 2)
          = 4 ^ ((1 : ℝ) / 2) * (1 + s) ^ ((1 : ℝ) / 2) :=
        Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) (by linarith : (0 : ℝ) ≤ 1 + s)
      have h3 : (4 : ℝ) ^ ((1 : ℝ) / 2) = 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 from by norm_num, ← Real.rpow_natCast (2 : ℝ) 2,
          ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2)]
        norm_num
      calc s ^ ((1 : ℝ) / 2) ≤ (4 * (1 + s)) ^ ((1 : ℝ) / 2) := h1
        _ = 4 ^ ((1 : ℝ) / 2) * (1 + s) ^ ((1 : ℝ) / 2) := h2
        _ = 2 * (1 + s) ^ ((1 : ℝ) / 2) := by rw [h3]
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < (1 + s) ^ 2)]
    have hfac : 2 * (1 + s) ^ (-(3 : ℝ) / 2) * (1 + s) ^ 2 = 2 * (1 + s) ^ ((1 : ℝ) / 2) := by
      rw [show 2 * (1 + s) ^ (-(3 : ℝ) / 2) * (1 + s) ^ 2
          = 2 * ((1 + s) ^ (-(3 : ℝ) / 2) * (1 + s) ^ 2) from by ring]
      rw [← Real.rpow_natCast (1 + s) 2, ← Real.rpow_add h1s]
      congr 1
      norm_num
    rw [hfac]
    exact hroot
  refine ⟨hint_f, ?_⟩
  calc ∫ s in Set.Ioi z, s ^ ((1 : ℝ) / 2) / (1 + s) ^ 2
      ≤ ∫ s in Set.Ioi z, 2 * (1 + s) ^ (-(3 : ℝ) / 2) :=
        integral_mono_ae hint_f hint_g hpt
    _ = 2 * ∫ s in Set.Ioi z, (1 + s) ^ (-(3 : ℝ) / 2) := integral_const_mul 2 _
    _ = 2 * (2 * (1 + z) ^ (-(1 : ℝ) / 2)) := by rw [hFTC]
    _ = 4 * (1 + z) ^ (-(1 : ℝ) / 2) := by ring
    _ ≤ 4 * 1 := by
        refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
        exact Real.rpow_le_one_of_one_le_of_nonpos (by linarith) (by norm_num)
    _ = 4 := by norm_num

end

end Work.FTS_StreamBdry.Inputs
