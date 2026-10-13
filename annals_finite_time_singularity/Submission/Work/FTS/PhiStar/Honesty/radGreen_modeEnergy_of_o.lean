import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.PhiStar.Radial.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.ClassC.ModeEnergyCS
import Submission.Work.FTS.ClassC.flux_radGreen_zero
import Submission.Work.FTS.ClassC.flux_radGreen_atTop
import Submission.Work.FTS.PhiStar.Honesty.radGreen_near_limits_of_le_rpow
import Submission.Work.FTS.PhiStar.Honesty.radGreen_mul_deriv_atTop_zero_meas
import Submission.Work.FTS.PhiStar.Honesty.radGreen_sq_w_sq_integrableOn
import Submission.Work.FTS.PhiStar.Honesty.zDeriv_radGreen_sq_w_sq_integrableOn
import Submission.Work.FTS.H2.ModalSolR.radGreenContinuousOn
import Submission.Work.FTS.PhiStar.Honesty.radGreen_modeEnergy_of_compactSource
import Submission.Work.FTS.PhiStar.Honesty.exists_cont_approx_weightedL2
import Submission.Work.FTS.PhiStar.Honesty.radGreen_tendsto_of_weightedL2

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
