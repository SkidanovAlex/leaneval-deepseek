import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EllipticEst.OpenFTC.absFtcLeIntegralAbsDeriv
import Submission.Work.FTS.LocData6.zfarR_jet_le6_of_jets
import Submission.Work.FTS.PhiStar.Honesty.radGreen_near_limits_of_le_rpow
import Submission.Work.FTS.PhiStar.Honesty.rgG2_sq_div_z4_Ioo
import Submission.Work.FTS.PhiStar.Honesty.zDeriv_radGreen_sq_w_sq_integrableOn
import Submission.Work.FTS.PhiStar.RadGreenSupport.radGreen_ode_weak
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS.RegPkgGal.St1Class
import Submission.Work.FTS.StrongEps.JepsHkMem.continuousOn_Jeps
import Submission.Work.FTS.StrongPersist.H6Rows.H6Pair_of_rows_C6
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkDzdIterSqLe
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.KsAux
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.DzIter_FK_eq_ae
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.StarSlotPcs.DzdIterBound
import Submission.Work.FTS.StrongPersist.H6Rows.NstarRow
import Submission.Work.FTS.StrongPersist.L3Rhs.Defs
import Submission.Work.FTS.StrongPersist.L3Rhs.VfsRadAux.aestronglyMeasurable_slotSum
import Submission.Work.FTS.StrongPersist.N6Trans.SixAux.MainBoundE
import Submission.Work.FTS.StrongPersist.SP6.EH6
import Submission.Work.FTS_EllLimOK.IsBslSolPos_add
import Submission.Work.FTS_EllLimOK.LimTower_identify3
import Submission.Work.FTS_EllLimOK.PkgJets.cosWeightTail_le
import Submission.Work.FTS_RegExport.RXT.jc3_aux
import Submission.Work.PhiStar.Honesty.sqrt_weight_mul_eq_of_mem_Ioo
import Submission.Work.Spaces.ThetaAgmon.agmon_interval
import Submission.Work.Spaces.pz_DthIter_mul_eq
import Submission.Work.Spaces.sq_mul_div_rpow
-- ===== merged: Submission.Work.FTS.PhiStar.Honesty.radGreen_modeEnergy_of_o =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
set_option linter.unusedVariables false
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Honesty

/-! ## The measure-theoretic core of the limiting argument

The target statement has `AEMeasurable c` (not `ContinuousOn c (Set.Ioi 0)`), so the pointwise
ODE/per-mode-energy identity is *not* available: `radGreen α m c` is only a.e.-differentiable.
The way around is to approximate `c` in the two weighted `L²` norms by sources `cₙ` which are
continuous and supported away from `0` (for those the sharp per-mode bound
`radGreen_modeEnergy_of_compactSource` holds), and to let `n → ∞` by Fatou's lemma, using that
`c ↦ radGreen α m c z` is continuous in those norms at each fixed `z > 0`.

This file first isolates the measure-theoretic part of that argument. -/

/-- `w²` is continuous on `(0,∞)`. -/
private lemma continuousOn_w_sq :
    ContinuousOn (fun z : ℝ => (Work.Spaces.w z) ^ 2) (Set.Ioi 0) := by
  have h : (fun z : ℝ => (Work.Spaces.w z) ^ 2)
      = fun z : ℝ => ((1 + z) ^ 2 / z ^ 2) ^ 2 := by
    funext z; rw [Work.Spaces.w]
  rw [h]
  refine ContinuousOn.pow ?_ 2
  exact ContinuousOn.div (by fun_prop) (by fun_prop)
    (fun z hz => pow_ne_zero 2 (ne_of_gt hz))

/-- `w²` is nonnegative. -/
private lemma w_sq_nonneg (z : ℝ) : 0 ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _

/-- **Fatou step.**  If `aₙ → a₀` pointwise on `(0,∞)`, `(aₙ)²w²` is integrable for every `n`,
each `aₙ` satisfies the per-mode inequality with source `cₙ`, and `∫cₙ²w² → ∫c²w²`, then the
inequality passes to the limit. -/
theorem modeEnergy_of_approx {μ : ℝ} (hμ : 0 < μ) {a : ℕ → ℝ → ℝ} {a₀ : ℝ → ℝ} {c : ℝ → ℝ}
    {c_ : ℕ → ℝ → ℝ}
    (ha : ∀ n, ContinuousOn (a n) (Set.Ioi 0))
    (ha₀ : ContinuousOn a₀ (Set.Ioi 0))
    (hAint : ∀ n, MeasureTheory.IntegrableOn
      (fun z => (a n z) ^ 2 * (Work.Spaces.w z) ^ 2) (Set.Ioi 0))
    (hsharp : ∀ n, μ ^ 2 * (∫ z in Set.Ioi 0, (a n z) ^ 2 * (Work.Spaces.w z) ^ 2)
      ≤ ∫ z in Set.Ioi 0, (c_ n z) ^ 2 * (Work.Spaces.w z) ^ 2)
    (hpt : ∀ z, 0 < z → Tendsto (fun n => a n z) atTop (nhds (a₀ z)))
    (hJ : Tendsto (fun n => ∫ z in Set.Ioi 0, (c_ n z) ^ 2 * (Work.Spaces.w z) ^ 2) atTop
      (nhds (∫ z in Set.Ioi 0, (c z) ^ 2 * (Work.Spaces.w z) ^ 2))) :
    μ ^ 2 * (∫ z in Set.Ioi 0, (a₀ z) ^ 2 * (Work.Spaces.w z) ^ 2)
      ≤ ∫ z in Set.Ioi 0, (c z) ^ 2 * (Work.Spaces.w z) ^ 2 := by
  have hμ2 : (0 : ℝ) < μ ^ 2 := by positivity
  -- the sequence of lintegrals of the approximants
  have hlint : ∀ n, (∫⁻ z in Set.Ioi 0,
        ENNReal.ofReal ((a n z) ^ 2 * (Work.Spaces.w z) ^ 2))
      = ENNReal.ofReal (∫ z in Set.Ioi 0, (a n z) ^ 2 * (Work.Spaces.w z) ^ 2) := by
    intro n
    exact (MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hAint n)
      (Filter.Eventually.of_forall fun z =>
        mul_nonneg (sq_nonneg (a n z)) (w_sq_nonneg z))).symm
  -- Fatou's lemma
  have hFatou : (∫⁻ z in Set.Ioi 0,
        ENNReal.ofReal ((a₀ z) ^ 2 * (Work.Spaces.w z) ^ 2))
      ≤ Filter.liminf (fun n => ∫⁻ z in Set.Ioi 0,
          ENNReal.ofReal ((a n z) ^ 2 * (Work.Spaces.w z) ^ 2)) atTop := by
    have hcongr : (∫⁻ z in Set.Ioi 0, Filter.liminf
        (fun n => ENNReal.ofReal ((a n z) ^ 2 * (Work.Spaces.w z) ^ 2)) atTop)
        = ∫⁻ z in Set.Ioi 0, ENNReal.ofReal ((a₀ z) ^ 2 * (Work.Spaces.w z) ^ 2) := by
      refine MeasureTheory.lintegral_congr_ae ?_
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz
      have hlim : Tendsto (fun n => (a n z) ^ 2 * (Work.Spaces.w z) ^ 2) atTop
          (nhds ((a₀ z) ^ 2 * (Work.Spaces.w z) ^ 2)) :=
        ((hpt z hz).pow 2).mul_const _
      exact (ENNReal.tendsto_ofReal hlim).liminf_eq
    rw [← hcongr]
    refine MeasureTheory.lintegral_liminf_le' (μ := volume.restrict (Set.Ioi 0))
      (u := atTop) ?_
    intro n
    have hasm : AEStronglyMeasurable
        (fun z : ℝ => (a n z) ^ 2 * (Work.Spaces.w z) ^ 2)
        (volume.restrict (Set.Ioi 0)) :=
      ((ha n).aestronglyMeasurable measurableSet_Ioi).pow 2 |>.mul
        (continuousOn_w_sq.aestronglyMeasurable measurableSet_Ioi)
    exact hasm.aemeasurable.ennreal_ofReal
  -- each term of the sequence is dominated by the corresponding source term
  have hstep : ∀ n, (∫⁻ z in Set.Ioi 0,
        ENNReal.ofReal ((a n z) ^ 2 * (Work.Spaces.w z) ^ 2))
      ≤ ENNReal.ofReal ((∫ z in Set.Ioi 0, (c_ n z) ^ 2 * (Work.Spaces.w z) ^ 2) / μ ^ 2) := by
    intro n
    rw [hlint n]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [le_div_iff₀ hμ2]
    linarith [hsharp n]
  have hliminf_le : Filter.liminf (fun n => ∫⁻ z in Set.Ioi 0,
        ENNReal.ofReal ((a n z) ^ 2 * (Work.Spaces.w z) ^ 2)) atTop
      ≤ ENNReal.ofReal ((∫ z in Set.Ioi 0, (c z) ^ 2 * (Work.Spaces.w z) ^ 2) / μ ^ 2) := by
    have hdiv : Tendsto (fun n => (∫ z in Set.Ioi 0, (c_ n z) ^ 2 * (Work.Spaces.w z) ^ 2)
        / μ ^ 2) atTop
        (nhds ((∫ z in Set.Ioi 0, (c z) ^ 2 * (Work.Spaces.w z) ^ 2) / μ ^ 2)) :=
      hJ.div_const _
    have hconv := ENNReal.tendsto_ofReal hdiv
    rw [← hconv.liminf_eq]
    exact Filter.liminf_le_liminf (Filter.Eventually.of_forall hstep)
  -- combine, then take `toReal`
  have hmain := le_trans hFatou hliminf_le
  have hmono := ENNReal.toReal_mono (by simp) hmain
  rw [ENNReal.toReal_ofReal (div_nonneg (MeasureTheory.integral_nonneg
    (fun z => mul_nonneg (sq_nonneg (c z)) (w_sq_nonneg z))) hμ2.le)] at hmono
  have hdet : (∫⁻ z in Set.Ioi 0,
        ENNReal.ofReal ((a₀ z) ^ 2 * (Work.Spaces.w z) ^ 2)).toReal
      = ∫ z in Set.Ioi 0, (a₀ z) ^ 2 * (Work.Spaces.w z) ^ 2 :=
    (MeasureTheory.integral_eq_lintegral_of_nonneg_ae
      (Filter.Eventually.of_forall fun z =>
        mul_nonneg (sq_nonneg (a₀ z)) (w_sq_nonneg z))
      (ha₀.aestronglyMeasurable measurableSet_Ioi |>.pow 2 |>.mul
        (continuousOn_w_sq.aestronglyMeasurable measurableSet_Ioi))).symm
  rw [hdet] at hmono
  rw [le_div_iff₀ hμ2] at hmono
  linarith [hmono]

/-! ## Elementary integrability and arithmetic facts used in the assembly -/

/-- `∫_0^∞ c² < ∞` from the two weighted halves. -/
private lemma integrableOn_sq_Ioi_of_halves {c : ℝ → ℝ}
    (hnear : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2 / t ^ 4) (Set.Ioo 0 1))
    (hfar : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2) (Set.Ioi 1)) :
    MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2) (Set.Ioi 0) := by
  have h1 : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2) (Set.Ioo (0:ℝ) 1) := by
    refine MeasureTheory.Integrable.mono' hnear ?_ ?_
    · have hmul : AEStronglyMeasurable (fun t : ℝ => ((c t) ^ 2 / t ^ 4) * t ^ 4)
          (volume.restrict (Set.Ioo (0:ℝ) 1)) :=
        hnear.aestronglyMeasurable.mul
          ((continuousOn_id.pow 4).aestronglyMeasurable measurableSet_Ioo)
      refine hmul.congr ?_
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with t ht
      have ht0 : t ≠ 0 := ne_of_gt ht.1
      field_simp
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with t ht
      have ht4le : t ^ 4 ≤ 1 := by
        have h' : t ^ 4 ≤ 1 ^ 4 := pow_le_pow_left₀ ht.1.le ht.2.le 4
        simpa using h'
      have ht4pos : (0:ℝ) < t ^ 4 := pow_pos ht.1 4
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (c t))]
      rw [le_div_iff₀ ht4pos]
      nlinarith [sq_nonneg (c t)]
  have h2 : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2) (Set.Ioi (1:ℝ)) := hfar
  have hA := h1.congr_set_ae (MeasureTheory.Ioo_ae_eq_Icc).symm
  have hB := h2.congr_set_ae (MeasureTheory.Ioi_ae_eq_Ici).symm
  have hU := hA.union hB
  have hset : Set.Icc (0:ℝ) 1 ∪ Set.Ici (1:ℝ) = Set.Ici (0:ℝ) := by
    ext x
    simp only [Set.mem_union, Set.mem_Icc, Set.mem_Ici]
    constructor
    · rintro (⟨h1', _⟩ | h3) <;> linarith
    · intro h
      rcases le_or_gt x 1 with h' | h'
      · exact Or.inl ⟨h, h'⟩
      · exact Or.inr h'.le
  rw [hset] at hU
  exact hU.mono_set Set.Ioi_subset_Ici_self

/-- `(a+b)² ≤ 2a² + 2b²`. -/
private lemma sq_add_le_two (a b : ℝ) : (a + b) ^ 2 ≤ 2 * a ^ 2 + 2 * b ^ 2 := by
  nlinarith [sq_nonneg (a - b)]

/-- If `(f-g)²/t⁴` and `g²/t⁴` are integrable on `(0,1)` and `f` is continuous on `(0,∞)`, then
so is `f²/t⁴`. -/
private lemma integrableOn_sq_div_of_diff {f g : ℝ → ℝ}
    (hcont : ContinuousOn f (Set.Ioi 0))
    (hdiff : MeasureTheory.IntegrableOn (fun t : ℝ => (f t - g t) ^ 2 / t ^ 4) (Set.Ioo 0 1))
    (hg : MeasureTheory.IntegrableOn (fun t : ℝ => (g t) ^ 2 / t ^ 4) (Set.Ioo 0 1)) :
    MeasureTheory.IntegrableOn (fun t : ℝ => (f t) ^ 2 / t ^ 4) (Set.Ioo 0 1) := by
  have hmaj : MeasureTheory.IntegrableOn
      (fun t : ℝ => 2 * ((f t - g t) ^ 2 / t ^ 4) + 2 * ((g t) ^ 2 / t ^ 4))
      (Set.Ioo 0 1) := (hdiff.const_mul 2).add (hg.const_mul 2)
  refine MeasureTheory.Integrable.mono' hmaj ?_ ?_
  · have hcont' : ContinuousOn (fun t : ℝ => (f t) ^ 2 / t ^ 4) (Set.Ioo (0:ℝ) 1) :=
      ContinuousOn.div ((hcont.mono (fun t ht => ht.1)).pow 2) (continuousOn_id.pow 4)
        (fun t ht => pow_ne_zero 4 (ne_of_gt ht.1))
    exact hcont'.aestronglyMeasurable measurableSet_Ioo
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioo] with t ht
    have ht4 : (0:ℝ) < t ^ 4 := pow_pos ht.1 4
    have hb : (f t) ^ 2 ≤ 2 * (f t - g t) ^ 2 + 2 * (g t) ^ 2 := by
      have h := sq_add_le_two (f t - g t) (g t)
      nlinarith [h]
    rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (sq_nonneg (f t)) ht4.le)]
    calc (f t) ^ 2 / t ^ 4 ≤ (2 * (f t - g t) ^ 2 + 2 * (g t) ^ 2) / t ^ 4 :=
          div_le_div_of_nonneg_right hb ht4.le
      _ = 2 * ((f t - g t) ^ 2 / t ^ 4) + 2 * ((g t) ^ 2 / t ^ 4) := by ring

/-- If `(f-g)²` and `g²` are integrable on `(1,∞)` and `f` is continuous on `(0,∞)`, then so is
`f²`. -/
private lemma integrableOn_sq_of_diff {f g : ℝ → ℝ}
    (hcont : ContinuousOn f (Set.Ioi 0))
    (hdiff : MeasureTheory.IntegrableOn (fun t : ℝ => (f t - g t) ^ 2) (Set.Ioi 1))
    (hg : MeasureTheory.IntegrableOn (fun t : ℝ => (g t) ^ 2) (Set.Ioi 1)) :
    MeasureTheory.IntegrableOn (fun t : ℝ => (f t) ^ 2) (Set.Ioi 1) := by
  have hmaj : MeasureTheory.IntegrableOn
      (fun t : ℝ => 2 * ((f t - g t) ^ 2) + 2 * ((g t) ^ 2)) (Set.Ioi 1) :=
    (hdiff.const_mul 2).add (hg.const_mul 2)
  refine MeasureTheory.Integrable.mono' hmaj ?_ ?_
  · have hcont' : ContinuousOn (fun t : ℝ => (f t) ^ 2) (Set.Ioi (1:ℝ)) :=
      (hcont.mono (fun t ht => by simp only [Set.mem_Ioi] at ht ⊢; linarith)).pow 2
    exact hcont'.aestronglyMeasurable measurableSet_Ioi
  · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
    have hb : (f t) ^ 2 ≤ 2 * (f t - g t) ^ 2 + 2 * (g t) ^ 2 := by
      have h := sq_add_le_two (f t - g t) (g t)
      nlinarith [h]
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg (f t))]
    exact hb

/-- The constant `μ_m = λ_m − 3α² − 3α(5+α)/2` is positive for `m ≥ 1`, `0 < α ≤ 1/4`. -/
private lemma lamR_sub_pos {α : ℝ} {m : ℕ} (hα : 0 < α) (hα4 : α ≤ 1 / 4) (hm : 1 ≤ m) :
    0 < Work.FTS.PhiStar.Radial.lamR m - 3 * α ^ 2 - 3 * α * (5 + α) / 2 := by
  have hm1 : (1 : ℝ) ≤ (m : ℝ) := by exact_mod_cast hm
  rw [Work.FTS.PhiStar.Radial.lamR]
  nlinarith [sq_nonneg α, hα.le, hα4, hm1]

theorem radGreen_modeEnergy_of_o {α : ℝ} {m : ℕ} {c : ℝ → ℝ}
    (hα : 0 < α) (hα4 : α ≤ 1 / 4) (hm : 1 ≤ m) (hc : AEMeasurable c)
    (hnear : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2 / t ^ 4) (Set.Ioo 0 1))
    (hfar : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2) (Set.Ioi 1))
    (hvy : ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, 0 < t → t ≤ δ →
      |c t| ≤ ε * t ^ ((3 : ℝ) / 2)) :
    (Work.FTS.PhiStar.Radial.lamR m - 3 * α ^ 2 - 3 * α * (5 + α) / 2) ^ 2
        * (∫ z in Set.Ioi 0, (Work.FTS.PhiStar.Radial.radGreen α m c z) ^ 2
            * (Work.Spaces.w z) ^ 2)
      ≤ ∫ z in Set.Ioi 0, (c z) ^ 2 * (Work.Spaces.w z) ^ 2 := by
  obtain ⟨c_, hcont_, hsupp_, hint1_, hint2_, hconv1, hconv2, hconv3⟩ :=
    exists_cont_approx_weightedL2 (c := c) hc hnear hfar
  -- the modification `C n = 1_{(0,∞)} · c_ n`, which is measurable on all of `ℝ`
  set C : ℕ → ℝ → ℝ := fun n => (Set.Ioi (0:ℝ)).indicator (c_ n) with hCdef
  have hCeq : ∀ n t, 0 < t → C n t = c_ n t := by
    intro n t ht
    rw [hCdef]
    exact Set.indicator_of_mem ht (c_ n)
  -- the two measurability/continuity requirements
  have hCAe : ∀ n, AEMeasurable (C n) volume := by
    intro n
    rw [hCdef]
    exact (aemeasurable_indicator_iff measurableSet_Ioi).mpr
      (((hcont_ n).aestronglyMeasurable measurableSet_Ioi).aemeasurable)
  have hCcont : ∀ n, ContinuousOn (C n) (Set.Ioi 0) := by
    intro n
    rw [hCdef]
    exact (hcont_ n).congr (fun t ht => Set.indicator_of_mem ht (c_ n))
  have hCsupp : ∀ n, ∃ a b : ℝ, 0 < a ∧ ∀ t : ℝ, t ∉ Set.Icc a b → C n t = 0 := by
    intro n
    obtain ⟨a, b, ha, hab⟩ := hsupp_ n
    refine ⟨a, b, ha, fun t ht => ?_⟩
    by_cases hpos : 0 < t
    · rw [hCeq n t hpos]; exact hab t ht
    · rw [hCdef]; exact Set.indicator_of_notMem (fun h => hpos h) (c_ n)
  -- integrability of the squares of `C n`
  have hCnear : ∀ n, MeasureTheory.IntegrableOn (fun t : ℝ => (C n t) ^ 2 / t ^ 4)
      (Set.Ioo 0 1) := by
    intro n
    exact integrableOn_sq_div_of_diff (f := C n) (g := c) (hCcont n)
      ((hint1_ n).congr_fun (fun t ht => by rw [hCeq n t ht.1]) measurableSet_Ioo) hnear
  have hCfar : ∀ n, MeasureTheory.IntegrableOn (fun t : ℝ => (C n t) ^ 2) (Set.Ioi 1) := by
    intro n
    exact integrableOn_sq_of_diff (f := C n) (g := c) (hCcont n)
      ((hint2_ n).congr_fun
        (fun t ht => by rw [hCeq n t (lt_of_lt_of_le one_pos ht.le)]) measurableSet_Ioi)
      hfar
  -- the sharp inequality for each approximant
  have hsharp : ∀ n,
      (Work.FTS.PhiStar.Radial.lamR m - 3 * α ^ 2 - 3 * α * (5 + α) / 2) ^ 2
          * (∫ z in Set.Ioi 0, (Work.FTS.PhiStar.Radial.radGreen α m (C n) z) ^ 2
              * (Work.Spaces.w z) ^ 2)
        ≤ ∫ z in Set.Ioi 0, (C n z) ^ 2 * (Work.Spaces.w z) ^ 2 :=
    fun n => radGreen_modeEnergy_of_compactSource hα hα4 hm (hCcont n) (hCsupp n)
  -- pointwise convergence at each `z > 0`
  have hpt : ∀ z : ℝ, 0 < z →
      Tendsto (fun n => Work.FTS.PhiStar.Radial.radGreen α m (C n) z) atTop
        (nhds (Work.FTS.PhiStar.Radial.radGreen α m c z)) :=
    radGreen_tendsto_of_weightedL2 hα hα4 hm hc hCAe
      (fun n => (hint1_ n).congr_fun (fun t ht => by rw [hCeq n t ht.1]) measurableSet_Ioo)
      (fun n => (hint2_ n).congr_fun
        (fun t ht => by rw [hCeq n t (lt_of_lt_of_le one_pos ht.le)]) measurableSet_Ioi)
      (hconv1.congr' (Filter.Eventually.of_forall (fun n =>
        MeasureTheory.setIntegral_congr_fun measurableSet_Ioo
          (fun t ht => by rw [hCeq n t ht.1]))))
      (hconv2.congr' (Filter.Eventually.of_forall (fun n =>
        MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
          (fun t ht => by rw [hCeq n t (lt_of_lt_of_le one_pos ht.le)]))))
  -- the source norms converge
  have hJ : Tendsto (fun n => ∫ z in Set.Ioi 0, (C n z) ^ 2 * (Work.Spaces.w z) ^ 2) atTop
      (nhds (∫ z in Set.Ioi 0, (c z) ^ 2 * (Work.Spaces.w z) ^ 2)) :=
    hconv3.congr' (Filter.Eventually.of_forall (fun n =>
      MeasureTheory.setIntegral_congr_fun measurableSet_Ioi
        (fun t ht => by rw [hCeq n t ht])))
  -- integrability of the solution slot, and continuity
  have hAint : ∀ n, MeasureTheory.IntegrableOn
      (fun z : ℝ => (Work.FTS.PhiStar.Radial.radGreen α m (C n) z) ^ 2
        * (Work.Spaces.w z) ^ 2) (Set.Ioi 0) :=
    fun n => radGreen_sq_w_sq_integrableOn (α := α) (m := m) (c := C n) hα hα4 hm
      (hCcont n) (hCnear n) (hCfar n)
  have hcontN : ∀ n, ContinuousOn
      (fun z : ℝ => Work.FTS.PhiStar.Radial.radGreen α m (C n) z) (Set.Ioi 0) :=
    fun n => Work.FTS.H2.ModalSolR.radGreenContinuousOn hα (by linarith) m
      (integrableOn_sq_Ioi_of_halves (hCnear n) (hCfar n))
      ((hCcont n).aestronglyMeasurable measurableSet_Ioi)
  have hcont0 : ContinuousOn (fun z : ℝ => Work.FTS.PhiStar.Radial.radGreen α m c z)
      (Set.Ioi 0) :=
    Work.FTS.H2.ModalSolR.radGreenContinuousOn hα (by linarith) m
      (integrableOn_sq_Ioi_of_halves hnear hfar)
      ((hc.mono_measure Measure.restrict_le_self).aestronglyMeasurable)
  exact modeEnergy_of_approx (μ := Work.FTS.PhiStar.Radial.lamR m - 3 * α ^ 2
      - 3 * α * (5 + α) / 2) (lamR_sub_pos hα hα4 hm) hcontN hcont0 hAint hsharp hpt hJ

end Work.FTS.PhiStar.Honesty
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N0Aux.N04aN05a_HkSq6 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N0Aux

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unusedVariables false

/-! ## Elementary facts about the constant `Cc α = 3α/(2c(α))` -/

lemma Cc_pos {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) : 0 < Cc α := by
  have hc := (Work.Spaces.c_bounds α hα hα1).1
  rw [Cc]
  positivity

lemma Cc_le (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) : Cc α ≤ 15 * α := by
  have hc := (Work.Spaces.c_bounds α hα hα1).1
  rw [Cc, div_le_iff₀ (by linarith : (0 : ℝ) < 2 * Work.Spaces.c α)]
  nlinarith

lemma abs_Cc_le_twenty (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) : |Cc α| ≤ 20 := by
  rw [abs_of_pos (Cc_pos hα hα1)]
  have h := Cc_le α hα hα1
  linarith

lemma sq_Cc_le (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) : (Cc α) ^ 2 ≤ 225 * α ^ 2 := by
  have h := Cc_le α hα hα1
  have h0 : 0 ≤ Cc α := le_of_lt (Cc_pos hα hα1)
  calc (Cc α) ^ 2 ≤ (15 * α) ^ 2 := pow_le_pow_left₀ h0 h 2
    _ = 225 * α ^ 2 := by ring

/-! ## The two separated forms -/

/-- **The separated form of `NP4a`.**  On the open quadrant the piece `NP4a α w` is the product
of the angular profile `CC α` and the radial profile `BB4 w`. -/
lemma NP4a_eq_sep {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (w : ℝ → ℝ → ℝ) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.FTS.StrongPersist.H6Pair6Aux.NP4a α w z θ = CC α θ * BB4 w z := by
  intro z θ hz hθ hθ2
  have h1 : Work.FTS.StrongPersist.H6Pair6Aux.NP4a α w z θ
      = Work.Construction.N04a α (fun z θ => Work.Construction.Fstar α z θ + w z θ) w z θ := by
    simp only [Work.FTS.StrongPersist.H6Pair6Aux.NP4a,
      Work.FTS.StrongPersist.H6Pair6Aux.NA4, Work.Construction.N04a,
      Work.Construction.s2, Work.Spaces.Dth, Work.Spaces.pth,
      Work.Construction.Fstar]
    ring
  rw [h1, Work.FTS.StrongPersist.H6Pair6Aux.H6N0Aux.nzN04a_sep hα hα1 z θ hz ⟨hθ, hθ2⟩]
  simp only [CC, BB4]
  ring

/-- **The separated form of `NP5a`.** -/
lemma NP5a_eq_sep {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (w : ℝ → ℝ → ℝ) :
    ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.FTS.StrongPersist.H6Pair6Aux.NP5a α w z θ = CC5 α θ * BB5 w z := by
  intro z θ hz hθ hθ2
  have h1 : Work.FTS.StrongPersist.H6Pair6Aux.NP5a α w z θ
      = Work.Construction.N05a α (fun z θ => Work.Construction.Fstar α z θ + w z θ) w z θ := by
    simp only [Work.FTS.StrongPersist.H6Pair6Aux.NP5a,
      Work.FTS.StrongPersist.H6Pair6Aux.NA5, Work.Construction.N05a]
    ring
  rw [h1, Work.FTS.StrongPersist.H6Pair6Aux.H6N0Aux.nzN05a_sep hα hα1 z θ hz ⟨hθ, hθ2⟩]
  simp only [CC5, BB5]
  ring

/-! ## The `ℋ⁶`-square of the two pieces equals that of their separated forms -/

lemma HkSq_NP4a_eq {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (w : ℝ → ℝ → ℝ) :
    Work.Spaces.HkSq α 6 (Work.FTS.StrongPersist.H6Pair6Aux.NP4a α w)
      = Work.Spaces.HkSq α 6 (fun z θ => CC α θ * BB4 w z) :=
  Work.FTS.EllipticEst.HkSq_congr_open α 6 (NP4a_eq_sep hα hα1 w)

lemma HkSq_NP5a_eq {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (w : ℝ → ℝ → ℝ) :
    Work.Spaces.HkSq α 6 (Work.FTS.StrongPersist.H6Pair6Aux.NP5a α w)
      = Work.Spaces.HkSq α 6 (fun z θ => CC5 α θ * BB5 w z) :=
  Work.FTS.EllipticEst.HkSq_congr_open α 6 (NP5a_eq_sep hα hα1 w)

/-! ## The angular block of the separated forms -/

lemma AngBlk_CC_eq (α : ℝ) :
    AngBlk α (CC α) = Work.FTS.StrongPersist.H6Pair6Aux.H6N0Aux.angBlk α (Cc α) := by
  funext θ
  simp only [AngBlk, CC, Cc, Work.FTS.StrongPersist.H6Pair6Aux.H6N0Aux.angBlk]

lemma AngBlk_CC5_eq (α : ℝ) :
    AngBlk α (CC5 α) = Work.FTS.StrongPersist.H6Pair6Aux.H6N0Aux.angBlk α (-(Cc α)) := by
  funext θ
  simp only [AngBlk, CC5, Cc, Work.FTS.StrongPersist.H6Pair6Aux.H6N0Aux.angBlk]

/-! ## The main theorem -/

/-
Route hint (the `X · f` engine `radialMaj6_split` does NOT apply here: its `f`-side would be the
non-decaying factor `NA4`/`NA5`, whose `HkSq α 6` is the junk value `0`).  Instead use the
**separation** identities `H6Pair6Aux.nzN04a_sep` / `nzN05a_sep`, which write (for `z > 0`,
`θ ∈ Ioo 0 (π/2)`)

  `N04a α (F_*+w) w = (3α/(2c α)) · (Gam α θ · qfun θ) · (L₁₂ w z · FM.Fstar z)`,
  `N05a α (F_*+w) w = (-(3α/(2c α))) · (Gam α θ · qfun θ) · (L₁₂ w z · Hz z)`,

i.e. both pieces are `ρ(z) · γ(θ)` with a *radial* `ρ` and an *angular* `γ` (up to the
constants `3α/(2c α)`), so their `ℋ⁶`-slots are `(D_z^j ρ)(z)·(D_θ^i γ)(θ)` and the double
integral **factors**:

  `∫∫ (D_z^jρ · D_θ^iγ)² slotW_i = (∫_z (D_z^jρ)² w²) · (∫_θ (D_θ^iγ)² σ_i²)`

(with `σ_i² = sin(2θ)^{-η}` for `i = 0` and `sin(2θ)^{-γ}` for `i ≥ 1`).  The two one-variable
inputs are: `radBlk_le7` (`Cr`, giving `∑_{q≤6} ∫_z (D_z^q(ρ·L₁₂ w))² w² ≤ Cr(1+Kρ)² HkSq α 6 w`
for a radial `ρ` with `|Zop^[b]ρ| ≤ Kρ`, `b ≤ 6`; use `ρ := FM.Fstar` resp. `ρ := Hz`, whose
jet bounds are `H6Pair6Aux.H6N0Aux.nzradZop_bound6`), and the angular bounds
`∫_θ (D_θ^iγ)² σ_i² ≤ C_i·max(1, 1/α)` from `|D_θ^i(Gam·qfun)| ≤ C_i·Gam`
(`LocData6.DthIter_Gam_abs_le6` plus the bounded jets of `qfun θ = cos 2θ - 1/3`) together with
`α·∫_θ Gam α θ² sin(2θ)^{-γ}dθ ≤ C` (spell it as
`∫ (sin 2θ)^{2α/3-γ} ≤ 3000/(17α)`, exactly as in `H6Rows.FstarI12H6.integral_gammaAngMaj6_le`).
-/
theorem N04aN05a_HkSq6 : ∀ C₀ : ℝ, ∃ K : ℝ, 0 < K ∧ ∀ α ∈ Set.Ioc (0 : ℝ) 1,
    ∀ w : Work.FTS.Galerkin.Fn,
    Work.FTS.ClassC.ClassC α w → Work.FTS.Nonlin.Xn α w ≤ C₀ * α ^ 2 →
    Work.Spaces.HkSq α 6 (Work.FTS.StrongPersist.H6Pair6Aux.NP4a α w)
        ≤ K * (1 + Work.Spaces.HkSq α 6 w) ∧
    Work.Spaces.HkSq α 6 (Work.FTS.StrongPersist.H6Pair6Aux.NP5a α w)
        ≤ K * (1 + Work.Spaces.HkSq α 6 w) := by
  intro C₀
  obtain ⟨Aang, hAangpos, hAang⟩ := Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N0Aux.N04aN05aParts.angBlk_bound
  obtain ⟨Cr, hCrpos, hCr⟩ := Work.FTS.StrongPersist.H6Pair6Aux.H6N0Aux.radBlk_le7
  obtain ⟨Kr, hKrpos, hKrF, hKrH⟩ := Work.FTS.StrongPersist.H6Pair6Aux.H6N0Aux.nzradZop_bound6
  refine ⟨225 * Aang * Cr * (1 + Kr) ^ 2 + 1, by positivity, ?_⟩
  intro α hαIoc w hC hXn
  have hαIoc' : α ∈ Set.Ioc (0 : ℝ) 1 := hαIoc
  obtain ⟨hα, hα1⟩ := hαIoc
  -- the class hypotheses
  have hsm : Work.FTS.EllipticEst.SmoothOpen w := hC.reg
  have hmem7 : Work.Spaces.HkMem α 7 w := hC.mem
  have hmem6 : Work.Spaces.HkMem α 6 w :=
    Work.FTS.StrongPersist.HkMem_of_le_of_smoothOpen α (k := 6) (k' := 7) (by norm_num) hsm hmem7
  have hl12 : Work.Construction.L12 w 0 = 0 := hC.l12
  -- the smoothness of the two radial profiles
  have hFs6 : ContDiffOn ℝ 6 Work.FM.Fstar (Set.Ioi 0) :=
    (Work.FTS.StrongPersist.H6Pair6Aux.H6N0Aux.nzsmoothOn_FMFstar).of_le (by norm_num)
  have hHz6 : ContDiffOn ℝ 6 Work.FTS.Nonlinear.FstarPkg.Hz (Set.Ioi 0) :=
    (Work.FTS.StrongPersist.H6Pair6Aux.H6N0Aux.nzsmoothOn_Hz).of_le (by norm_num)
  -- the radial block bounds
  have hrad4 : MeasureTheory.IntegrableOn (Work.FTS.StrongPersist.SlotSum (BB4 w))
        Work.Spaces.Iz ∧
      (∫ z in Work.Spaces.Iz, Work.FTS.StrongPersist.SlotSum (BB4 w) z)
        ≤ Cr * (1 + Kr) ^ 2 * Work.Spaces.HkSq α 6 w := by
    have h := hCr α hαIoc' Work.FM.Fstar w Kr (le_of_lt hKrpos) hFs6
      (fun b hb z hz => hKrF b hb z hz) hsm hmem6 hmem7 hl12
    have hfun : Work.FTS.StrongPersist.SlotSum (BB4 w)
        = fun z => ∑ q ∈ Finset.range 7,
            (Work.Spaces.DzIter q (fun z' _ => Work.FM.Fstar z'
              * Work.Construction.L12 w z') z 0) ^ 2 * (Work.Spaces.w z) ^ 2 := rfl
    rw [hfun]
    exact h
  have hrad5 : MeasureTheory.IntegrableOn (Work.FTS.StrongPersist.SlotSum (BB5 w))
        Work.Spaces.Iz ∧
      (∫ z in Work.Spaces.Iz, Work.FTS.StrongPersist.SlotSum (BB5 w) z)
        ≤ Cr * (1 + Kr) ^ 2 * Work.Spaces.HkSq α 6 w := by
    have h := hCr α hαIoc' Work.FTS.Nonlinear.FstarPkg.Hz w Kr (le_of_lt hKrpos) hHz6
      (fun b hb z hz => hKrH b hb z hz) hsm hmem6 hmem7 hl12
    have hfun : Work.FTS.StrongPersist.SlotSum (BB5 w)
        = fun z => ∑ q ∈ Finset.range 7,
            (Work.Spaces.DzIter q (fun z' _ => Work.FTS.Nonlinear.FstarPkg.Hz z'
              * Work.Construction.L12 w z') z 0) ^ 2 * (Work.Spaces.w z) ^ 2 := rfl
    rw [hfun]
    exact h
  -- the angular block bounds
  have hIntAng4 : MeasureTheory.IntegrableOn (AngBlk α (CC α)) Work.Spaces.Iθ := by
    rw [AngBlk_CC_eq]
    exact (hAang α hαIoc' (Cc α) (abs_Cc_le_twenty α hα hα1)).1
  have hIntAng5 : MeasureTheory.IntegrableOn (AngBlk α (CC5 α)) Work.Spaces.Iθ := by
    rw [AngBlk_CC5_eq]
    exact (hAang α hαIoc' (-(Cc α)) (by
      rw [abs_neg]; exact abs_Cc_le_twenty α hα hα1)).1
  have hAngBd4 : (∫ θ in Work.Spaces.Iθ, AngBlk α (CC α) θ) ≤ 225 * Aang := by
    rw [AngBlk_CC_eq]
    have hb := (hAang α hαIoc' (Cc α) (abs_Cc_le_twenty α hα hα1)).2
    have h2 : Aang * (Cc α) ^ 2 ≤ Aang * (225 * α ^ 2) :=
      mul_le_mul_of_nonneg_left (sq_Cc_le α hα hα1) (le_of_lt hAangpos)
    have h3 : α ^ 2 * (∫ θ in Work.Spaces.Iθ,
        Work.FTS.StrongPersist.H6Pair6Aux.H6N0Aux.angBlk α (Cc α) θ)
        ≤ α ^ 2 * (225 * Aang) := by
      calc α ^ 2 * (∫ θ in Work.Spaces.Iθ,
            Work.FTS.StrongPersist.H6Pair6Aux.H6N0Aux.angBlk α (Cc α) θ)
          ≤ Aang * (Cc α) ^ 2 := hb
        _ ≤ Aang * (225 * α ^ 2) := h2
        _ = α ^ 2 * (225 * Aang) := by ring
    exact le_of_mul_le_mul_left h3 (pow_pos hα 2)
  have hAngBd5 : (∫ θ in Work.Spaces.Iθ, AngBlk α (CC5 α) θ) ≤ 225 * Aang := by
    rw [AngBlk_CC5_eq]
    have hb := (hAang α hαIoc' (-(Cc α)) (by
      rw [abs_neg]; exact abs_Cc_le_twenty α hα hα1)).2
    have h2 : Aang * (-(Cc α)) ^ 2 ≤ Aang * (225 * α ^ 2) := by
      rw [neg_sq]
      exact mul_le_mul_of_nonneg_left (sq_Cc_le α hα hα1) (le_of_lt hAangpos)
    have h3 : α ^ 2 * (∫ θ in Work.Spaces.Iθ,
        Work.FTS.StrongPersist.H6Pair6Aux.H6N0Aux.angBlk α (-(Cc α)) θ)
        ≤ α ^ 2 * (225 * Aang) := by
      calc α ^ 2 * (∫ θ in Work.Spaces.Iθ,
            Work.FTS.StrongPersist.H6Pair6Aux.H6N0Aux.angBlk α (-(Cc α)) θ)
          ≤ Aang * (-(Cc α)) ^ 2 := hb
        _ ≤ Aang * (225 * α ^ 2) := h2
        _ = α ^ 2 * (225 * Aang) := by ring
    exact le_of_mul_le_mul_left h3 (pow_pos hα 2)
  -- the two separation bounds
  have hsep4 := Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N0Aux.N04aN05aParts.sep_HkSq_le (α := α) (C := CC α) (B := BB4 w) hIntAng4 hrad4.1
  have hsep5 := Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N0Aux.N04aN05aParts.sep_HkSq_le (α := α) (C := CC5 α) (B := BB5 w) hIntAng5 hrad5.1
  -- the two block integrals are nonnegative
  have hSlot4nn : 0 ≤ (∫ z in Work.Spaces.Iz, Work.FTS.StrongPersist.SlotSum (BB4 w) z) :=
    integral_nonneg fun z =>
      Finset.sum_nonneg fun q _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have hSlot5nn : 0 ≤ (∫ z in Work.Spaces.Iz, Work.FTS.StrongPersist.SlotSum (BB5 w) z) :=
    integral_nonneg fun z =>
      Finset.sum_nonneg fun q _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)
  have h225 : 0 ≤ 225 * Aang := by linarith [hAangpos]
  have hKnn : 0 ≤ 225 * Aang * Cr * (1 + Kr) ^ 2 := by positivity
  constructor
  · rw [HkSq_NP4a_eq hα hα1 w]
    refine hsep4.trans ?_
    have h1 : (∫ θ in Work.Spaces.Iθ, AngBlk α (CC α) θ)
        * (∫ z in Work.Spaces.Iz, Work.FTS.StrongPersist.SlotSum (BB4 w) z)
        ≤ (225 * Aang) * (Cr * (1 + Kr) ^ 2 * Work.Spaces.HkSq α 6 w) :=
      mul_le_mul hAngBd4 hrad4.2 hSlot4nn h225
    refine h1.trans ?_
    have h2 : (225 * Aang) * (Cr * (1 + Kr) ^ 2 * Work.Spaces.HkSq α 6 w)
        = (225 * Aang * Cr * (1 + Kr) ^ 2) * Work.Spaces.HkSq α 6 w := by ring
    rw [h2]
    have hS := Work.Spaces.HkSq_nonneg α 6 w
    nlinarith [hS, hKnn]
  · rw [HkSq_NP5a_eq hα hα1 w]
    refine hsep5.trans ?_
    have h1 : (∫ θ in Work.Spaces.Iθ, AngBlk α (CC5 α) θ)
        * (∫ z in Work.Spaces.Iz, Work.FTS.StrongPersist.SlotSum (BB5 w) z)
        ≤ (225 * Aang) * (Cr * (1 + Kr) ^ 2 * Work.Spaces.HkSq α 6 w) :=
      mul_le_mul hAngBd5 hrad5.2 hSlot5nn h225
    refine h1.trans ?_
    have h2 : (225 * Aang) * (Cr * (1 + Kr) ^ 2 * Work.Spaces.HkSq α 6 w)
        = (225 * Aang * Cr * (1 + Kr) ^ 2) * Work.Spaces.HkSq α 6 w := by ring
    rw [h2]
    have hS := Work.Spaces.HkSq_nonneg α 6 w
    nlinarith [hS, hKnn]

end Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N0Aux
end
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N0Aux.sep_HkSq4_le =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N0Aux

-- Level-four factorisation of the `ℋ⁴`-energy of the separated product `(z,θ) ↦ C θ · B z`.
-- `AngBlk4 α C θ = (C θ)² sin(2θ)^{-η} + Σ_{1 ≤ i ≤ 4} (dthU^i C θ)² sin(2θ)^{-γ(α)}` and
-- `SlotSum4 B z = Σ_{q ≤ 4} (D_z^q (fun z' _ => B z') z 0)² w(z)²`
-- are defined in `...blocks/N0Aux/B4SepDefs.lean`.  This is the level-four analogue of
-- `L3Aux.HkIntegrand_sep_le` (order three) and of `...blocks/N0Aux/N04aN05aParts/sep_HkSq_le`
-- (order six), which is the proof to copy: `L6Aux.HkIntegrandSepLeGen` at `k := 4` gives the
-- pointwise bound on `Iθ` (the two sides are equal up to unfolding the two definitions), then
-- `integral_mono_of_nonneg` + `integral_mul_const` in `θ` (the `z`-factor is a constant there)
-- and `integral_mono_of_nonneg` + `integral_const_mul` in `z`; use `HkIntegrand_nonneg`.
theorem sep_HkSq4_le {α : ℝ} {C : ℝ → ℝ} {B : ℝ → ℝ}
    (hAng : MeasureTheory.IntegrableOn
      (Work.FTS.StrongEps.E4R3.Apriori4Proofs.N0Aux.AngBlk4 α C) Work.Spaces.Iθ)
    (hRad : MeasureTheory.IntegrableOn
      (Work.FTS.StrongEps.E4R3.Apriori4Proofs.N0Aux.SlotSum4 B) Work.Spaces.Iz) :
    Work.Spaces.HkSq α 4 (fun z θ => C θ * B z)
      ≤ (∫ θ in Work.Spaces.Iθ,
            Work.FTS.StrongEps.E4R3.Apriori4Proofs.N0Aux.AngBlk4 α C θ)
        * (∫ z in Work.Spaces.Iz,
            Work.FTS.StrongEps.E4R3.Apriori4Proofs.N0Aux.SlotSum4 B z) := by
  -- The pointwise separation bound: on `Iθ` the `ℋ⁴`-integrand of `C·B` is dominated by the
  -- product of the angular block `AngBlk4 α C θ` and the radial slot sum `SlotSum4 B z`.
  have hpt : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 4 (fun z' θ' => C θ' * B z') z θ
        ≤ Work.FTS.StrongEps.E4R3.Apriori4Proofs.N0Aux.AngBlk4 α C θ
          * Work.FTS.StrongEps.E4R3.Apriori4Proofs.N0Aux.SlotSum4 B z := by
    intro z hz θ hθ
    have h1 := Work.FTS.StrongPersist.L6Aux.HkIntegrandSepLeGen (α := α) (k := 4)
      (C := C) (B := B) (z := z) (θ := θ) hθ
    simpa only [Work.FTS.StrongEps.E4R3.Apriori4Proofs.N0Aux.AngBlk4,
      Work.FTS.StrongEps.E4R3.Apriori4Proofs.N0Aux.SlotSum4] using h1
  -- Integrate the bound in `θ` (the radial factor is a constant there).
  have hinner : ∀ z ∈ Work.Spaces.Iz,
      (∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α 4 (fun z' θ' => C θ' * B z') z θ)
        ≤ (∫ θ in Work.Spaces.Iθ,
              Work.FTS.StrongEps.E4R3.Apriori4Proofs.N0Aux.AngBlk4 α C θ)
          * Work.FTS.StrongEps.E4R3.Apriori4Proofs.N0Aux.SlotSum4 B z := by
    intro z hz
    have hmaj : MeasureTheory.Integrable
        (fun θ => Work.FTS.StrongEps.E4R3.Apriori4Proofs.N0Aux.AngBlk4 α C θ
          * Work.FTS.StrongEps.E4R3.Apriori4Proofs.N0Aux.SlotSum4 B z)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
      hAng.mul_const _
    have hae : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
        Work.Spaces.HkIntegrand α 4 (fun z' θ' => C θ' * B z') z θ
          ≤ Work.FTS.StrongEps.E4R3.Apriori4Proofs.N0Aux.AngBlk4 α C θ
            * Work.FTS.StrongEps.E4R3.Apriori4Proofs.N0Aux.SlotSum4 B z :=
      MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => hpt z hz θ hθ)
    refine (MeasureTheory.integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α 4 _ z θ) hmaj
      hae).trans (le_of_eq ?_)
    rw [MeasureTheory.integral_mul_const]
  -- Integrate in `z` (now the angular factor is the constant `∫_θ AngBlk4`).
  have houter := MeasureTheory.integral_mono_of_nonneg
    (Filter.Eventually.of_forall fun z => MeasureTheory.integral_nonneg fun θ =>
      Work.Spaces.HkIntegrand_nonneg α 4 _ z θ)
    (hRad.const_mul (∫ θ in Work.Spaces.Iθ,
      Work.FTS.StrongEps.E4R3.Apriori4Proofs.N0Aux.AngBlk4 α C θ))
    (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici hinner)
  rw [MeasureTheory.integral_const_mul] at houter
  rw [Work.Spaces.HkSq]
  exact houter

end Work.FTS.StrongEps.E4R3.Apriori4Proofs.blocks.N0Aux
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsLocalPStar.TraceToEpsMemAe =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsLocalPStar

open scoped Real Topology
open MeasureTheory Set Filter

/-- **Tracing the weighted `ℋ¹`-bound down to the `ε`-space — almost-everywhere version.**

Same as `TraceToEpsMem`, but the two vanishing-trace hypotheses are only required for
almost every `z > 0` (w.r.t. Lebesgue measure), rather than for every `z > 0`.  This is
exactly the form in which the traces are available along the flow of the `ε`-scheme (they
are produced by the angular trace theorems `SliceTraceO`/`SliceTracePiO` a.e. in `z`).

The proof is the proof of `TraceToEpsMem`: the pointwise traces were consumed only inside
the a.e.-in-`z` step `hpoint`, so the two a.e. trace hypotheses simply join the
`filter_upwards` there.  The only bookkeeping is that the a.e. statement is phrased for
`volume.restrict (Ioi 0)` while the slices are indexed by `z ∈ Iz = Ici 0`; the two
measures agree since `Ici 0 = Ioi 0 ∪ {0}` and `{0}` is null. -/
theorem TraceToEpsMemAe :
    ∃ C : ℝ, 0 < C ∧ ∀ α : ℝ, α ∈ Set.Ioc 0 1 → ∀ f : Work.FTS.Galerkin.Fn,
      Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 1 f →
      (∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi (0:ℝ))),
          Filter.Tendsto (fun θ => f z θ) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0)) →
      (∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi (0:ℝ))),
          Filter.Tendsto (fun θ => f z θ) (nhdsWithin (Real.pi/2) (Set.Iio (Real.pi/2))) (nhds 0)) →
      Work.FTS.StrongEps.EpsMem α f ∧
        Work.FTS.StrongEps.EpsSq α f
          ≤ C / (Work.Spaces.gam α - 1) ^ 2 * Work.Spaces.HkSq α 1 f := by
  obtain ⟨CS, hCSpos, hCS⟩ := EpsSliceLe
  refine ⟨CS, hCSpos, fun α hα f hso hm ht1 ht2 => ?_⟩
  obtain ⟨hα0, hα1⟩ := hα
  -- the `(0,1)`-slot of `ℋ¹`
  obtain ⟨hslotInt, hslotLe⟩ := Slot01LeHkSq1 hso hm
  have hprod := Work.FTS.EllipticEst.AeSlotOneAe.Interp.integrable_uncurry_slot_mixed
    (α := α) (k := 1) (F := f) hso hm 0 1 (by norm_num) (by norm_num)
  have hslot_ae := hprod.prod_right_ae
  have hae_pos := Work.FTS.StrongEps.EpsSqTools.ae_pos_Iz
  -- the a.e. trace hypotheses are stated for `volume.restrict (Ioi 0)`, the slices are
  -- indexed by `z ∈ Iz = Ici 0`; the two restricted measures agree (`{0}` is null)
  have hIz : MeasureTheory.volume.restrict (Set.Ioi (0:ℝ))
      = MeasureTheory.volume.restrict Work.Spaces.Iz := by
    rw [Work.Spaces.Iz]
    exact MeasureTheory.Measure.restrict_congr_set MeasureTheory.Ioi_ae_eq_Ici
  have ht1' : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      Filter.Tendsto (fun θ => f z θ) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    rw [← hIz]; exact ht1
  have ht2' : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      Filter.Tendsto (fun θ => f z θ)
        (nhdsWithin (Real.pi/2) (Set.Iio (Real.pi/2))) (nhds 0) := by
    rw [← hIz]; exact ht2
  -- the slicewise Hardy bound, for almost every `z`
  have hpoint : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      MeasureTheory.Integrable (fun θ => (f z θ * Work.FTS.StrongEps.epsW α z θ) ^ 2)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) ∧
      (∫ θ in Work.Spaces.Iθ, (f z θ * Work.FTS.StrongEps.epsW α z θ) ^ 2)
          ≤ CS / (Work.Spaces.gam α - 1) ^ 2 *
            (∫ θ in Work.Spaces.Iθ, (Work.Spaces.mixed 0 1 f z θ * Work.Spaces.Wt α z θ) ^ 2) := by
    filter_upwards [hslot_ae, hae_pos, ht1', ht2'] with z hslot hz htz1 htz2
    have hcd : ContDiffOn ℝ 1 (fun θ => f z θ) (Set.Ioo 0 (Real.pi / 2)) :=
      (hso.curry_θ hz).of_le (show (1 : WithTop ℕ∞) ≤ Work.Stability.smoothOrder from by
        simp [Work.Stability.smoothOrder])
    exact hCS α (show α ∈ Set.Ioc 0 1 from ⟨hα0, hα1⟩) f z hz hcd htz1 htz2 hslot
  have hEint' : MeasureTheory.Integrable
      (fun z : ℝ => CS / (Work.Spaces.gam α - 1) ^ 2 *
        (∫ θ in Work.Spaces.Iθ, (Work.Spaces.mixed 0 1 f z θ * Work.Spaces.Wt α z θ) ^ 2))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) := hslotInt.const_mul _
  -- the outer `z`-integral
  have hmain : (∫ z in Work.Spaces.Iz,
        ∫ θ in Work.Spaces.Iθ, (f z θ * Work.FTS.StrongEps.epsW α z θ) ^ 2)
      ≤ CS / (Work.Spaces.gam α - 1) ^ 2 * Work.Spaces.HkSq α 1 f := by
    refine le_trans ?_ (mul_le_mul_of_nonneg_left hslotLe (div_nonneg hCSpos.le (sq_nonneg _)))
    rw [← MeasureTheory.integral_const_mul]
    refine MeasureTheory.integral_mono_of_nonneg
      (Eventually.of_forall fun z => MeasureTheory.integral_nonneg fun θ => sq_nonneg _) hEint' ?_
    filter_upwards [hpoint] with z hz using hz.2
  refine ⟨?_, ?_⟩
  · -- `EpsMem α f`
    have hAESM : MeasureTheory.AEStronglyMeasurable
        (fun p : ℝ × ℝ => (f p.1 p.2 * Work.FTS.StrongEps.epsW α p.1 p.2) ^ 2)
        ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
      Work.Spaces.aesm_of_continuousOn_Qd _
        (ContinuousOn.pow (ContinuousOn.mul (hso.forall 0).continuousOn
          (Work.FTS.StrongEps.EpsSqTools.continuousOn_epsW α)) 2)
    have hslice : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
        MeasureTheory.HasFiniteIntegral
          (fun θ => (f z θ * Work.FTS.StrongEps.epsW α z θ) ^ 2)
          (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
      filter_upwards [hpoint] with z hz using hz.1.2
    have hzInt : MeasureTheory.HasFiniteIntegral
        (fun z : ℝ => ∫ θ, ‖(f z θ * Work.FTS.StrongEps.epsW α z θ) ^ 2‖
          ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
        (MeasureTheory.volume.restrict Work.Spaces.Iz) := by
      have haesm : MeasureTheory.AEStronglyMeasurable
          (fun z : ℝ => ∫ θ, ‖(f z θ * Work.FTS.StrongEps.epsW α z θ) ^ 2‖
            ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ))
          (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
        hAESM.norm.integral_prod_right'
      have hbdd : (fun z : ℝ => ‖∫ θ, ‖(f z θ * Work.FTS.StrongEps.epsW α z θ) ^ 2‖
            ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ)‖)
          ≤ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iz]
          (fun z : ℝ => CS / (Work.Spaces.gam α - 1) ^ 2 *
            (∫ θ in Work.Spaces.Iθ,
              (Work.Spaces.mixed 0 1 f z θ * Work.Spaces.Wt α z θ) ^ 2)) := by
        filter_upwards [hpoint] with z hz
        rw [Real.norm_of_nonneg (MeasureTheory.integral_nonneg fun θ => norm_nonneg _)]
        refine le_trans (le_of_eq ?_) hz.2
        exact MeasureTheory.integral_congr_ae
          (Filter.Eventually.of_forall fun θ => Real.norm_of_nonneg (sq_nonneg _))
      exact (MeasureTheory.Integrable.mono' hEint' haesm hbdd).2
    have hmeas : (MeasureTheory.volume : Measure (ℝ × ℝ)).restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)
        = (MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
      rw [MeasureTheory.Measure.volume_eq_prod, Measure.prod_restrict]
    rw [Work.FTS.StrongEps.EpsMem, MeasureTheory.IntegrableOn, hmeas]
    exact ⟨hAESM, (MeasureTheory.hasFiniteIntegral_prod_iff' hAESM).mpr ⟨hslice, hzInt⟩⟩
  · calc Work.FTS.StrongEps.EpsSq α f
        = ∫ z in Work.Spaces.Iz,
            ∫ θ in Work.Spaces.Iθ, (f z θ * Work.FTS.StrongEps.epsW α z θ) ^ 2 := rfl
      _ ≤ CS / (Work.Spaces.gam α - 1) ^ 2 * Work.Spaces.HkSq α 1 f := hmain

end Work.FTS.StrongEps.EpsLocalPStar
end
-- ===== merged: Submission.Work.FTS.StrongEps.EpsSqTools.EpsSqIter_mixed_Jeps_le6 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsSqTools

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

/-! ## The order-six mass bound for the routed kernels -/

/-- **The mass of a routed kernel is at most the order-six mass** `Ksm ρ 1 6`.  This is the
order-six analogue of the order-three bound contained in `KdKFacts` (`Ksm` is the double sum of
the masses of all routed kernels of order `≤ M`, so every slot of order `≤ 6` is dominated by
`Ksm ρ 1 6`). -/
theorem integral_abs_KdK_one_le_Ksm6 (ρ : ℝ × ℝ → ℝ) {a b : ℕ} (ha : a ≤ 6) (hb : b ≤ 6) :
    ∫ p : ℝ × ℝ, |Work.FTS.StrongEps.EpsE4Thr.KdK ρ 1 a b p|
      ≤ Work.FTS.StrongEps.EpsE4Thr.Ksm ρ 1 6 := by
  simp only [Work.FTS.StrongEps.EpsE4Thr.Ksm]
  calc ∫ p : ℝ × ℝ, |Work.FTS.StrongEps.EpsE4Thr.KdK ρ 1 a b p|
      ≤ ∑ a' ∈ Finset.range (6 + 1),
          ∫ p : ℝ × ℝ, |Work.FTS.StrongEps.EpsE4Thr.KdK ρ 1 a' b p| :=
        Finset.single_le_sum (f := fun a' => ∫ p : ℝ × ℝ,
            |Work.FTS.StrongEps.EpsE4Thr.KdK ρ 1 a' b p|)
          (fun _ _ => integral_nonneg fun p => abs_nonneg _)
          (Finset.mem_range.mpr (by omega))
    _ ≤ ∑ a' ∈ Finset.range (6 + 1), ∑ b' ∈ Finset.range (6 + 1),
          ∫ p : ℝ × ℝ, |Work.FTS.StrongEps.EpsE4Thr.KdK ρ 1 a' b' p| :=
        Finset.sum_le_sum fun a' _ => Finset.single_le_sum
          (f := fun b' => ∫ p : ℝ × ℝ, |Work.FTS.StrongEps.EpsE4Thr.KdK ρ 1 a' b' p|)
          (fun _ _ => integral_nonneg fun p => abs_nonneg _)
          (Finset.mem_range.mpr (by omega))

/-! ## The main theorem -/

theorem EpsSqIter_mixed_Jeps_le6 (ρ : ℝ × ℝ → ℝ) (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) :
    ∃ C : ℝ, 0 < C ∧ ∀ α : ℝ, α ∈ Set.Ioc 0 1 → ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∀ f : Work.FTS.Galerkin.Fn,
        (∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Work.FTS.StrongEps.Quad) →
        Work.FTS.StrongEps.EpsMem α f →
          Work.FTS.StrongEps.EpsMem α (Work.FTS.StrongEps.Jeps ρ ε f) ∧
          ∀ j i : ℕ, j + i ≤ 6 →
            (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
                ENNReal.ofReal ((Work.Spaces.mixed j i (Work.FTS.StrongEps.Jeps ρ ε f) z θ
                  * Work.FTS.StrongEps.epsW α z θ) ^ 2))
              ≤ ENNReal.ofReal (C * (C / ε) ^ (2 * (j + i)) * Work.FTS.StrongEps.EpsSq α f) := by
  obtain ⟨c, hcpos, hWc⟩ := Work.FTS.StrongEps.HkSqAux.Wt_shift_le
  obtain ⟨δ, hδpos, hJac0⟩ := Work.FTS.StrongEps.HkSqAux.logJac_shift_le
  have hc0 : 0 ≤ c := hcpos.le
  have hδ0 : 0 ≤ δ := hδpos.le
  obtain ⟨kscale, ksm_le, kint, ksupp, kmom⟩ := KdKFacts ρ hρ
  set Cv : ℝ := max 1 (4096 * (Work.FTS.StrongEps.EpsE4Thr.Ksm ρ 1 6) ^ 2
    * Real.exp (2 * (2 * c + δ))) with hCv
  have hCv1 : 1 ≤ Cv := le_max_left _ _
  have hCvpos : 0 < Cv := lt_of_lt_of_le zero_lt_one hCv1
  have hCvbig : 4096 * (Work.FTS.StrongEps.EpsE4Thr.Ksm ρ 1 6) ^ 2
      * Real.exp (2 * (2 * c + δ)) ≤ Cv := le_max_right _ _
  refine ⟨Cv, hCvpos, ?_⟩
  intro α hα ε hε0 hε1 f hf hfmem
  have hα0 : 0 < α := hα.1
  have hfcont : ContinuousOn (fun q : ℝ × ℝ => f q.1 q.2) Work.FTS.StrongEps.Quad :=
    (hf 0).continuousOn
  have hFcont : ContinuousOn (fun q : ℝ × ℝ => f q.1 q.2
      * Work.FTS.StrongEps.epsW α q.1 q.2) Work.FTS.StrongEps.Quad :=
    hfcont.mul (continuousOn_epsW_quad α)
  have hFmeas : AEMeasurable (fun q : ℝ × ℝ => ENNReal.ofReal
      ((f q.1 q.2 * Work.FTS.StrongEps.epsW α q.1 q.2) ^ 2))
      (MeasureTheory.volume.restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) :=
    ENNReal.measurable_ofReal.comp_aemeasurable hfmem.aestronglyMeasurable.aemeasurable
  -- the generic chain, for every slot `(j,i)`
  have hgen : ∀ j i : ℕ,
      (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal ((Work.Spaces.mixed j i (Work.FTS.StrongEps.Jeps ρ ε f) z θ
            * Work.FTS.StrongEps.epsW α z θ) ^ 2))
        ≤ ENNReal.ofReal ((((4 : ℝ) ^ i
              * ∫ p : ℝ × ℝ, |Work.FTS.StrongEps.EpsE4Thr.KdK ρ ε j i p|)
            * (Real.exp (2 * (2 * c + δ))
              * ∫ p : ℝ × ℝ, |Work.FTS.StrongEps.EpsE4Thr.KdK ρ ε j i p|))
            * Work.FTS.StrongEps.EpsSq α f) := by
    intro j i
    set A : ℝ := ∫ p : ℝ × ℝ, |Work.FTS.StrongEps.EpsE4Thr.KdK ρ ε j i p| with hAdef
    set Λ : ℝ × ℝ → ℝ := fun p =>
      |Work.FTS.StrongEps.EpsE4Thr.KdK ρ ε j i p| * Real.exp (2 * c * (|p.1| + |p.2|))
      with hΛdef
    have hA0 : 0 ≤ A := by
      rw [hAdef]
      exact integral_nonneg fun p => abs_nonneg _
    have hΛ0 : ∀ p : ℝ × ℝ, 0 ≤ Λ p := by
      intro p
      rw [hΛdef]
      exact mul_nonneg (abs_nonneg _) (Real.exp_pos _).le
    have hpt : ∀ {z θ : ℝ}, 0 < z → θ ∈ Set.Ioo 0 (π / 2) →
        ENNReal.ofReal ((Work.Spaces.mixed j i (Work.FTS.StrongEps.Jeps ρ ε f) z θ
              * Work.FTS.StrongEps.epsW α z θ) ^ 2)
          ≤ ENNReal.ofReal (4 ^ i * A) * ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Λ p)
              * ENNReal.ofReal ((f (Work.FTS.StrongEps.zShift z p.1)
                    (Work.FTS.StrongEps.thShift θ p.2)
                  * Work.FTS.StrongEps.epsW α (Work.FTS.StrongEps.zShift z p.1)
                      (Work.FTS.StrongEps.thShift θ p.2)) ^ 2) := by
      intro z θ hz hθ
      exact MixedJepsEpsWpt ρ hρ (ε := ε) (α := α) (c := c) hε0 (f := f) hf hz hθ
        (fun p => hWc α hα z θ p.1 p.2 hz hθ) j i
    have hP : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
        ENNReal.ofReal ((Work.Spaces.mixed j i (Work.FTS.StrongEps.Jeps ρ ε f) z θ
              * Work.FTS.StrongEps.epsW α z θ) ^ 2)
          ≤ ENNReal.ofReal (4 ^ i * A) * ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Λ p)
              * ENNReal.ofReal ((f (Work.FTS.StrongEps.zShift z p.1)
                    (Work.FTS.StrongEps.thShift θ p.2)
                  * Work.FTS.StrongEps.epsW α (Work.FTS.StrongEps.zShift z p.1)
                      (Work.FTS.StrongEps.thShift θ p.2)) ^ 2) := by
      intro z hz θ hθ
      by_cases hc' : 0 < z ∧ θ ∈ Set.Ioo 0 (π / 2)
      · exact hpt hc'.1 hc'.2
      · rw [epsW_eq_zero_of_not_mem_quad hα0 hz hθ hc', mul_zero,
          zero_pow (by norm_num : (2 : ℕ) ≠ 0), ENNReal.ofReal_zero]
        exact zero_le
    have hΛexp : ∀ p : ℝ × ℝ, Λ p * Real.exp (δ * (|p.1| + |p.2|))
        = |Work.FTS.StrongEps.EpsE4Thr.KdK ρ ε j i p|
            * Real.exp ((2 * c + δ) * (|p.1| + |p.2|)) := by
      intro p
      rw [hΛdef, mul_assoc, ← Real.exp_add]
      congr 1
      ring_nf
    have hΛfin : ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Λ p * Real.exp (δ * (|p.1| + |p.2|)))
        ≤ ENNReal.ofReal (Real.exp (2 * (2 * c + δ)) * A) := by
      refine le_trans (le_of_eq (lintegral_congr (fun p => by rw [hΛexp p]))) ?_
      simpa only [hAdef] using kmom hε0 hε1 hc0 hδ0 j i
    have hΛcont : Continuous Λ := by
      rw [hΛdef]
      refine (Work.FTS.StrongEps.EpsE4Thr.KdK_continuous hρ ε j i).abs.mul ?_
      refine Real.continuous_exp.comp ?_
      exact continuous_const.mul
        ((continuous_abs.comp continuous_fst).add (continuous_abs.comp continuous_snd))
    have hAe : AEMeasurable (fun z : (ℝ × ℝ) × (ℝ × ℝ) => ENNReal.ofReal (Λ z.2)
        * ENNReal.ofReal ((f (Work.FTS.StrongEps.zShift z.1.1 z.2.1)
              (Work.FTS.StrongEps.thShift z.1.2 z.2.2)
            * Work.FTS.StrongEps.epsW α (Work.FTS.StrongEps.zShift z.1.1 z.2.1)
                (Work.FTS.StrongEps.thShift z.1.2 z.2.2)) ^ 2))
        (((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)).prod MeasureTheory.volume) := by
      have h2 := aemeasurable_shift_comp'
        (F := fun q : ℝ × ℝ => ENNReal.ofReal
          ((f q.1 q.2 * Work.FTS.StrongEps.epsW α q.1 q.2) ^ 2)) hFmeas
      have h1 : AEMeasurable (fun z : (ℝ × ℝ) × (ℝ × ℝ) => ENNReal.ofReal (Λ z.2))
          (((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ)).prod MeasureTheory.volume) :=
        (ENNReal.measurable_ofReal.comp hΛcont.measurable).comp_aemeasurable
          measurable_snd.aemeasurable
      exact h1.mul h2
    have hC₀ : 0 ≤ (4 : ℝ) ^ i * A := mul_nonneg (by positivity) hA0
    have hKmass : 0 ≤ Real.exp (2 * (2 * c + δ)) * A :=
      mul_nonneg (Real.exp_pos _).le hA0
    exact iter_le_of_pointwise (α := α) (c := c) (δ := δ) (Λ := Λ)
      (C₀ := (4 : ℝ) ^ i * A) (Kmass := Real.exp (2 * (2 * c + δ)) * A)
      (f := f) (g := Work.Spaces.mixed j i (Work.FTS.StrongEps.Jeps ρ ε f))
      hC₀ hKmass hΛ0 hΛfin hfmem hJac0 hFcont hAe hP
  -- finiteness of the `(0,0)` slot, hence `EpsMem α (J_ε f)`
  have hlin0 : (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
      ENNReal.ofReal (((Work.FTS.StrongEps.Jeps ρ ε f) z θ
        * Work.FTS.StrongEps.epsW α z θ) ^ 2)) < ⊤ := by
    have h := hgen 0 0
    simp only [Work.Spaces.mixed_zero_left, Work.Spaces.DthIter_zero] at h
    exact lt_of_le_of_lt h ENNReal.ofReal_lt_top
  have hEmem : Work.FTS.StrongEps.EpsMem α (Work.FTS.StrongEps.Jeps ρ ε f) := by
    have hJcont : ContinuousOn (fun q : ℝ × ℝ => Work.FTS.StrongEps.Jeps ρ ε f q.1 q.2)
        Work.FTS.StrongEps.Quad :=
      Work.FTS.StrongEps.JepsHkMem.continuousOn_Jeps hρ.moll hε0 hfcont
    have hcont2 : ContinuousOn (fun q : ℝ × ℝ =>
        ((Work.FTS.StrongEps.Jeps ρ ε f) q.1 q.2 * Work.FTS.StrongEps.epsW α q.1 q.2) ^ 2)
        Work.FTS.StrongEps.Quad :=
      (hJcont.mul (continuousOn_epsW_quad α)).pow 2
    have hAESM : AEStronglyMeasurable (fun q : ℝ × ℝ =>
        ((Work.FTS.StrongEps.Jeps ρ ε f) q.1 q.2 * Work.FTS.StrongEps.epsW α q.1 q.2) ^ 2)
        ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
      Work.Spaces.aesm_of_continuousOn_Qd _
        (by simpa only [Work.FTS.StrongEps.Quad] using hcont2)
    have hfin : MeasureTheory.HasFiniteIntegral (fun q : ℝ × ℝ =>
        ((Work.FTS.StrongEps.Jeps ρ ε f) q.1 q.2 * Work.FTS.StrongEps.epsW α q.1 q.2) ^ 2)
        ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
      rw [MeasureTheory.hasFiniteIntegral_iff_ofReal
        (Filter.Eventually.of_forall fun q => sq_nonneg _)]
      rw [← MeasureTheory.lintegral_lintegral (f := fun z θ => ENNReal.ofReal
          (((Work.FTS.StrongEps.Jeps ρ ε f) z θ * Work.FTS.StrongEps.epsW α z θ) ^ 2))
        (hAESM.aemeasurable.ennreal_ofReal)]
      exact hlin0
    have hmeas : (MeasureTheory.volume : MeasureTheory.Measure (ℝ × ℝ)).restrict
          (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)
        = (MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
      rw [MeasureTheory.Measure.volume_eq_prod, MeasureTheory.Measure.prod_restrict]
    rw [Work.FTS.StrongEps.EpsMem, MeasureTheory.IntegrableOn, hmeas]
    exact ⟨hAESM, hfin⟩
  refine ⟨hEmem, ?_⟩
  intro j i hji
  have hj6 : j ≤ 6 := by omega
  have hi6 : i ≤ 6 := by omega
  have hZ := hgen j i
  -- the constants
  have hKsm0 : 0 ≤ Work.FTS.StrongEps.EpsE4Thr.Ksm ρ 1 6 :=
    Work.FTS.StrongEps.EpsE4Thr.Ksm_nonneg hρ 1 6
  set A : ℝ := ∫ p : ℝ × ℝ, |Work.FTS.StrongEps.EpsE4Thr.KdK ρ ε j i p| with hAdef
  have hA0 : 0 ≤ A := by
    rw [hAdef]
    exact integral_nonneg fun p => abs_nonneg _
  have hA_bound : A ≤ ε⁻¹ ^ (j + i) * Work.FTS.StrongEps.EpsE4Thr.Ksm ρ 1 6 := by
    rw [hAdef, kscale hε0 j i]
    exact mul_le_mul_of_nonneg_left (integral_abs_KdK_one_le_Ksm6 ρ hj6 hi6) (by positivity)
  have hAA : A ^ 2 ≤ (ε⁻¹ ^ (j + i) * Work.FTS.StrongEps.EpsE4Thr.Ksm ρ 1 6) ^ 2 :=
    pow_le_pow_left₀ hA0 hA_bound 2
  have h4i : (4 : ℝ) ^ i ≤ 4096 := by
    have h1 : (4 : ℝ) ^ i ≤ 4 ^ 6 := pow_le_pow_right₀ (by norm_num) hi6
    norm_num at h1
    exact h1
  have hexp2 : (ε⁻¹ ^ (j + i) * Work.FTS.StrongEps.EpsE4Thr.Ksm ρ 1 6) ^ 2
      = ε⁻¹ ^ (2 * (j + i)) * (Work.FTS.StrongEps.EpsE4Thr.Ksm ρ 1 6) ^ 2 := by
    rw [mul_pow, ← pow_mul, Nat.mul_comm]
  have hconst : (4 ^ i * A) * (Real.exp (2 * (2 * c + δ)) * A)
      ≤ Cv * ε⁻¹ ^ (2 * (j + i)) := by
    have h2 : A ^ 2 ≤ ε⁻¹ ^ (2 * (j + i))
        * (Work.FTS.StrongEps.EpsE4Thr.Ksm ρ 1 6) ^ 2 := by
      rw [← hexp2]
      exact hAA
    calc (4 ^ i * A) * (Real.exp (2 * (2 * c + δ)) * A)
        = (4 ^ i * Real.exp (2 * (2 * c + δ))) * A ^ 2 := by ring
      _ ≤ (4 ^ i * Real.exp (2 * (2 * c + δ)))
            * (ε⁻¹ ^ (2 * (j + i))
              * (Work.FTS.StrongEps.EpsE4Thr.Ksm ρ 1 6) ^ 2) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = (4 ^ i * (Work.FTS.StrongEps.EpsE4Thr.Ksm ρ 1 6) ^ 2
              * Real.exp (2 * (2 * c + δ))) * ε⁻¹ ^ (2 * (j + i)) := by ring
      _ ≤ (4096 * (Work.FTS.StrongEps.EpsE4Thr.Ksm ρ 1 6) ^ 2
              * Real.exp (2 * (2 * c + δ))) * ε⁻¹ ^ (2 * (j + i)) := by
          have hfe : (4 : ℝ) ^ i * (Work.FTS.StrongEps.EpsE4Thr.Ksm ρ 1 6) ^ 2
                * Real.exp (2 * (2 * c + δ))
              = (4 : ℝ) ^ i * ((Work.FTS.StrongEps.EpsE4Thr.Ksm ρ 1 6) ^ 2
                  * Real.exp (2 * (2 * c + δ))) := by ring
          have hfe2 : 4096 * (Work.FTS.StrongEps.EpsE4Thr.Ksm ρ 1 6) ^ 2
                * Real.exp (2 * (2 * c + δ))
              = 4096 * ((Work.FTS.StrongEps.EpsE4Thr.Ksm ρ 1 6) ^ 2
                  * Real.exp (2 * (2 * c + δ))) := by ring
          rw [hfe, hfe2]
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          exact mul_le_mul_of_nonneg_right h4i
            (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)
      _ ≤ Cv * ε⁻¹ ^ (2 * (j + i)) := mul_le_mul_of_nonneg_right hCvbig (by positivity)
  have hCeps : Cv * ε⁻¹ ^ (2 * (j + i)) ≤ Cv * (Cv / ε) ^ (2 * (j + i)) := by
    refine mul_le_mul_of_nonneg_left ?_ hCvpos.le
    rw [div_eq_mul_inv]
    refine pow_le_pow_left₀ (by positivity) ?_ _
    simpa using mul_le_mul_of_nonneg_right hCv1 (by positivity : (0 : ℝ) ≤ ε⁻¹)
  refine hZ.trans ?_
  refine ENNReal.ofReal_le_ofReal ?_
  calc ((4 : ℝ) ^ i * A) * (Real.exp (2 * (2 * c + δ)) * A)
        * Work.FTS.StrongEps.EpsSq α f
      ≤ (Cv * ε⁻¹ ^ (2 * (j + i))) * Work.FTS.StrongEps.EpsSq α f :=
        mul_le_mul_of_nonneg_right hconst (Work.FTS.StrongEps.EpsSq_nonneg α f)
    _ ≤ (Cv * (Cv / ε) ^ (2 * (j + i))) * Work.FTS.StrongEps.EpsSq α f :=
        mul_le_mul_of_nonneg_right hCeps (Work.FTS.StrongEps.EpsSq_nonneg α f)

end

end Work.FTS.StrongEps.EpsSqTools
end
-- ===== merged: Submission.Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.FkTileAux.fkDzdIterSharp =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The sharp a.e. pointwise bound on the `D_z`-iterates of the angular moment `FK f`

`FK f z = ∫_θ K(θ)·f(z,θ) dθ` is the zeroth angular moment of `f`; it is a function of `z`
alone.  The claim of this file is that for `f` in the honest open quadrant class
(`Work.FTS.EllipticEst.SmoothOpen`) with weighted energy `ℋ⁶` *and* `ℋ⁷`
(`Work.Spaces.HkMem`), and for `b ≤ 5`, the `b`-th radial iterate
`DzdIter b (FK f) = (z∂_z)^b (FK f)` is bounded almost everywhere in `z` by
`C·√(HkSq α (b+1) f)`, with a universal constant `C`.

This is obtained from the *squared* a.e. statement of the sibling
`Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkDzdIterSqLe` — which reads, for `b ≤ 6`,

`(D_z^b (FK f))² ≤ C₁·HkSq α (b+1) f` a.e. on `Iz`

— by two elementary steps:

* `D_z`-iterates of the *radial* function `(z,θ) ↦ FK f z` are the one-dimensional iterates
  `DzdIter` (`Work.Elliptic.DzIter_rad`, at `θ = 0`), so the sibling's `DzIter`-statement is
  literally about `DzdIter b (FK f)`;
* `|x| = √(x²)` and `√(ab) = √a·√b` turn the squared bound into the linear one, with the
  constant `√C₁` and the factor `√(HkSq α (b+1) f)`.

The statement here is *weaker* than the sibling's (`b ≤ 5`, `α ∈ (0,1]`, same data), so
nothing new is needed beyond the square root bookkeeping.
-/

namespace Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.FkTileAux

theorem fkDzdIterSharp : ∃ C : ℝ, 0 < C ∧ ∀ α ∈ Set.Ioc 0 1, ∀ (f : Work.FTS.Galerkin.Fn),
    Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 6 f → Work.Spaces.HkMem α 7 f →
    ∀ b : ℕ, b ≤ 5 → ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      |Work.Elliptic.DzdIter b (fun z => Work.Construction.FK f z) z|
        ≤ C * Real.sqrt (Work.Spaces.HkSq α (b + 1) f) := by
  obtain ⟨C₁, hC₁pos, hC₁⟩ := Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkDzdIterSqLe
  refine ⟨Real.sqrt C₁, Real.sqrt_pos.mpr hC₁pos, ?_⟩
  intro α hα f hsm hm6 hm7 b hb
  have hb6 : b ≤ 6 := by omega
  filter_upwards [hC₁ hα.1 hsm hm6 hm7 b hb6] with z hz
  -- the two-dimensional `D_z`-iterates of a radial function are the one-dimensional ones
  rw [Work.Elliptic.DzIter_rad (fun w => Work.Construction.FK f w) b z 0] at hz
  calc |Work.Elliptic.DzdIter b (fun w => Work.Construction.FK f w) z|
      = Real.sqrt ((Work.Elliptic.DzdIter b (fun w => Work.Construction.FK f w) z) ^ 2) :=
        (Real.sqrt_sq_eq_abs _).symm
    _ ≤ Real.sqrt (C₁ * Work.Spaces.HkSq α (b + 1) f) := Real.sqrt_le_sqrt hz
    _ = Real.sqrt C₁ * Real.sqrt (Work.Spaces.HkSq α (b + 1) f) :=
        Real.sqrt_mul hC₁pos.le _

end Work.FTS.StrongPersist.H6Pair6Aux.T6Coef.FkTileAux
end
