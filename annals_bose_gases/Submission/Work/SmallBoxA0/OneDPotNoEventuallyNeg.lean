import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.Interval.Basic
import Mathlib.Topology.Separation.CompletelyRegular
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Submission.Work.SmallBoxA0.OneDPotDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open MeasureTheory
open scoped Topology Interval

set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

namespace Work.SmallBoxA0

namespace OneDPotAux

/-- An `L¹(a,b)` function vanishing past `b` is `L¹(a,∞)`. -/
lemma integrableOn_Ioi_of_integrableOn_Ioo_of_vanishes {F : ℝ → ℝ} {a b : ℝ}
    (hF : IntegrableOn F (Set.Ioo a b)) (hzero : ∀ x : ℝ, b ≤ x → F x = 0) :
    IntegrableOn F (Set.Ioi a) := by
  rcases lt_or_ge a b with hab | hba
  · have hset : Set.Ioi a = Set.Ioo a b ∪ Set.Ici b := by
      ext x
      simp only [Set.mem_Ioi, Set.mem_union, Set.mem_Ioo, Set.mem_Ici]
      constructor
      · intro hx
        rcases lt_or_ge x b with h | h
        · exact Or.inl ⟨hx, h⟩
        · exact Or.inr h
      · rintro (⟨h1, _⟩ | h2)
        · exact h1
        · exact lt_of_lt_of_le hab h2
    rw [hset]
    refine IntegrableOn.union hF ?_
    refine (integrableOn_zero (s := Set.Ici b)).congr_fun ?_ measurableSet_Ici
    intro x hx
    exact (hzero x hx).symm
  · refine (integrableOn_zero (s := Set.Ioi a)).congr_fun ?_ measurableSet_Ioi
    intro x hx
    exact (hzero x (le_trans hba (le_of_lt hx))).symm

/-- `norm`-integrability transfers to subsets of the domain of integrability. -/
lemma integrableOn_norm_of_subset {f : ℝ → ℝ} {s t : Set ℝ}
    (h : IntegrableOn f t) (hst : s ⊆ t) : IntegrableOn (fun x : ℝ => ‖f x‖) s :=
  Integrable.mono_measure (Integrable.norm h) (Measure.restrict_mono hst le_rfl)

/-- The tail integrand `s ↦ (s^2 * p s)/s` is `L¹` on `(δ,R)` for `δ > 0`. -/
lemma integrableOn_tail_integrand {R δ : ℝ} (hδ : 0 < δ) (p : ℝ → ℝ)
    (hp : IntegrableOn (fun r : ℝ => r ^ 2 * p r) (Set.Ioo (0 : ℝ) R)) :
    IntegrableOn (fun s : ℝ => (s ^ 2 * p s) / s) (Set.Ioo δ R) := by
  have hsub : Set.Ioo δ R ⊆ Set.Ioo (0 : ℝ) R := fun s hs => ⟨lt_trans hδ hs.1, hs.2⟩
  have hAESM : AEStronglyMeasurable (fun s : ℝ => (s ^ 2 * p s) / s)
      (volume.restrict (Set.Ioo δ R)) :=
    (hp.aestronglyMeasurable.mono_set hsub).div₀
      (aestronglyMeasurable_id.mono_measure Measure.restrict_le_self)
  refine Integrable.mono' (g := fun s : ℝ => ‖s ^ 2 * p s‖ / δ) ?_ hAESM ?_
  · have hbase : IntegrableOn (fun s : ℝ => ‖s ^ 2 * p s‖) (Set.Ioo δ R) :=
      integrableOn_norm_of_subset hp hsub
    have h2 : IntegrableOn (fun s : ℝ => (1 / δ) * ‖s ^ 2 * p s‖) (Set.Ioo δ R) :=
      Integrable.const_mul hbase (1 / δ)
    refine IntegrableOn.congr_fun h2 ?_ measurableSet_Ioo
    intro s hs
    rw [div_eq_mul_inv]
    ring
  · rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioo]
    filter_upwards with s hs
    have hs0 : (0 : ℝ) < s := lt_trans hδ hs.1
    have hle : δ ≤ s := le_of_lt hs.1
    rw [norm_div, Real.norm_eq_abs, Real.norm_eq_abs s, abs_of_pos hs0]
    exact div_le_div_of_nonneg_left (abs_nonneg _) hδ hle

/-- The tail integrand is `L¹` on `(δ,R')` for any `R' ≥ R`, `δ > 0`. -/
lemma integrableOn_tail_integrand_of_le {R R' δ : ℝ} (hδ : 0 < δ) (hRR' : R ≤ R')
    (p : ℝ → ℝ) (hp : IntegrableOn (fun r : ℝ => r ^ 2 * p r) (Set.Ioo (0 : ℝ) R))
    (hp0 : ∀ r : ℝ, R ≤ r → p r = 0) :
    IntegrableOn (fun s : ℝ => (s ^ 2 * p s) / s) (Set.Ioo δ R') := by
  have h1 : IntegrableOn (fun s : ℝ => (s ^ 2 * p s) / s) (Set.Ioo δ R) :=
    integrableOn_tail_integrand hδ p hp
  have h2 : IntegrableOn (fun s : ℝ => (s ^ 2 * p s) / s) (Set.Ici R) := by
    refine (integrableOn_zero (s := Set.Ici R)).congr_fun ?_ measurableSet_Ici
    intro s hs
    show (0 : ℝ) = s ^ 2 * p s / s
    rw [hp0 s hs, mul_zero, zero_div]
  have hunion : IntegrableOn (fun s : ℝ => (s ^ 2 * p s) / s)
      (Set.Ioo δ R ∪ (Set.Ioo δ R' ∩ Set.Ici R)) :=
    IntegrableOn.union h1 (h2.mono_set Set.inter_subset_right)
  refine IntegrableOn.mono_set hunion ?_
  intro s hs
  by_cases h : s < R
  · exact Or.inl ⟨hs.1, h⟩
  · exact Or.inr ⟨⟨hs.1, hs.2⟩, le_of_not_gt h⟩

/-- `qfun p r = ∫_r^R s p s ds` for `0 ≤ r ≤ R`. -/
lemma qfun_eq_intervalIntegral {R r : ℝ} (p : ℝ → ℝ)
    (hp0 : ∀ x : ℝ, R ≤ x → p x = 0) (hr : 0 ≤ r) (hrR : r ≤ R) :
    qfun p r = ∫ s in r..R, (s ^ 2 * p s) / s := by
  rw [qfun, intervalIntegral.integral_of_le hrR]
  have hpt : ∀ s ∈ Set.Ioi r,
      (s ^ 2 * p s) / s = (Set.Ioc r R).indicator (fun s : ℝ => (s ^ 2 * p s) / s) s := by
    intro s hs
    by_cases hsR : s ≤ R
    · rw [Set.indicator_of_mem (Set.mem_Ioc.mpr ⟨hs, hsR⟩)]
    · rw [Set.indicator_of_notMem (show s ∉ Set.Ioc r R from fun h => hsR h.2), hp0 s
          (le_of_not_ge hsR), mul_zero, zero_div]
  rw [setIntegral_congr_fun measurableSet_Ioi hpt]
  have hfun : (Set.Ioi r).indicator ((Set.Ioc r R).indicator (fun s : ℝ => (s ^ 2 * p s) / s))
      = (Set.Ioc r R).indicator (fun s : ℝ => (s ^ 2 * p s) / s) := by
    rw [Set.indicator_indicator,
      show Set.Ioi r ∩ Set.Ioc r R = Set.Ioc r R from by
        ext s
        simp only [Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Ioc]
        exact ⟨fun h => h.2, fun h => ⟨h.1, h⟩⟩]
  rw [← integral_indicator measurableSet_Ioi, hfun, integral_indicator measurableSet_Ioc]

/-- `qfun p` vanishes on `[R,∞)`. -/
lemma qfun_eq_zero_of_R_le {R r : ℝ} (p : ℝ → ℝ) (hp0 : ∀ x : ℝ, R ≤ x → p x = 0)
    (hr : R ≤ r) : qfun p r = 0 := by
  rw [qfun]
  refine MeasureTheory.setIntegral_eq_zero_of_ae_eq_zero ?_
  filter_upwards with s hs
  rw [hp0 s (le_trans hr (le_of_lt hs)), mul_zero, zero_div]

/-- `qfun p r = ∫_r^{R'} s p s ds` for any `R' ≥ R` and `0 ≤ r`. -/
lemma qfun_eq_intervalIntegral_of_le {R R' r : ℝ} (p : ℝ → ℝ)
    (hp0 : ∀ x : ℝ, R ≤ x → p x = 0) (hRR' : R ≤ R') (hr : 0 ≤ r) :
    qfun p r = ∫ s in r..R', (s ^ 2 * p s) / s := by
  rcases lt_or_ge r R' with h | h
  · rw [qfun, intervalIntegral.integral_of_le h.le]
    have hpt : ∀ s ∈ Set.Ioi r,
        (s ^ 2 * p s) / s = (Set.Ioc r R').indicator (fun s : ℝ => (s ^ 2 * p s) / s) s := by
      intro s hs
      by_cases hsR : s ≤ R'
      · rw [Set.indicator_of_mem (Set.mem_Ioc.mpr ⟨hs, hsR⟩)]
      · rw [Set.indicator_of_notMem (show s ∉ Set.Ioc r R' from fun hh => hsR hh.2),
          hp0 s (le_trans hRR' (le_of_not_ge hsR)), mul_zero, zero_div]
    rw [setIntegral_congr_fun measurableSet_Ioi hpt]
    have hfun : (Set.Ioi r).indicator ((Set.Ioc r R').indicator
        (fun s : ℝ => (s ^ 2 * p s) / s))
        = (Set.Ioc r R').indicator (fun s : ℝ => (s ^ 2 * p s) / s) := by
      rw [Set.indicator_indicator,
        show Set.Ioi r ∩ Set.Ioc r R' = Set.Ioc r R' from by
          ext s
          simp only [Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Ioc]
          exact ⟨fun h => h.2, fun h => ⟨h.1, h⟩⟩]
    rw [← integral_indicator measurableSet_Ioi, hfun, integral_indicator measurableSet_Ioc]
  · rw [qfun_eq_zero_of_R_le p hp0 (le_trans hRR' h)]
    rw [intervalIntegral.integral_symm]
    rw [intervalIntegral.integral_congr (g := fun _ => (0 : ℝ)) ?_]
    · simp
    · intro s hs
      rw [Set.uIcc_of_le h] at hs
      show s ^ 2 * p s / s = (0 : ℝ)
      rw [hp0 s (le_trans hRR' hs.1), mul_zero, zero_div]

/-- `qfun p` is continuous on `(0,∞)`. -/
lemma continuousAt_qfun {R : ℝ} (p : ℝ → ℝ)
    (hp : IntegrableOn (fun r : ℝ => r ^ 2 * p r) (Set.Ioo (0 : ℝ) R))
    (hp0 : ∀ r : ℝ, R ≤ r → p r = 0) {x : ℝ} (hx : 0 < x) :
    ContinuousAt (qfun p) x := by
  set R' : ℝ := max R (x + 1) with hR'def
  have hRR' : R ≤ R' := le_max_left _ _
  have hx_lt : x < x + 1 := by linarith
  have hxR' : x < R' := lt_of_lt_of_le hx_lt (le_max_right _ _)
  have hδ : (0 : ℝ) < x / 2 := by linarith
  have hx2x : x / 2 < x := by linarith
  have hx2R' : x / 2 ≤ R' := le_of_lt (lt_of_lt_of_le hx2x hxR'.le)
  have huIcc : Set.uIcc (x / 2) R' = Set.Icc (x / 2) R' := Set.uIcc_of_le hx2R'
  have hIntI : IntegrableOn (fun s : ℝ => (s ^ 2 * p s) / s) (Set.Icc (x / 2) R') := by
    rw [integrableOn_Icc_iff_integrableOn_Ioo]
    exact integrableOn_tail_integrand_of_le hδ hRR' p hp hp0
  have hIntU : IntegrableOn (fun s : ℝ => (s ^ 2 * p s) / s) (Set.uIcc (x / 2) R') := by
    rw [huIcc]
    exact hIntI
  have hcont : ContinuousOn (fun r : ℝ => ∫ s in r..R', (s ^ 2 * p s) / s)
      (Set.Icc (x / 2) R') := by
    have h := intervalIntegral.continuousOn_primitive_interval_left hIntU
    rwa [huIcc] at h
  have hmem : Set.Icc (x / 2) R' ∈ 𝓝 x := Icc_mem_nhds hx2x hxR'
  have hxmem : x ∈ Set.Icc (x / 2) R' := ⟨hx2x.le, hxR'.le⟩
  have hcwa : ContinuousAt (fun r : ℝ => ∫ s in r..R', (s ^ 2 * p s) / s) x :=
    (hcont.continuousWithinAt hxmem).continuousAt hmem
  refine hcwa.congr ?_
  filter_upwards [isOpen_Ioi.mem_nhds hx] with r hr
  exact (qfun_eq_intervalIntegral_of_le p hp0 hRR' hr.le).symm

lemma continuousOn_qfun {R : ℝ} (p : ℝ → ℝ)
    (hp : IntegrableOn (fun r : ℝ => r ^ 2 * p r) (Set.Ioo (0 : ℝ) R))
    (hp0 : ∀ r : ℝ, R ≤ r → p r = 0) :
    ContinuousOn (qfun p) (Set.Ioi 0) :=
  fun _ hx => (continuousAt_qfun p hp hp0 hx).continuousWithinAt

/-- `∫_{\mathrm{Ioo}\ a\ b} f = ∫_a^b f` for `a ≤ b`. -/
lemma integral_Ioo_eq_intervalIntegral {a b : ℝ} (hab : a ≤ b) (f : ℝ → ℝ) :
    ∫ x in Set.Ioo a b, f x = ∫ x in a..b, f x := by
  rw [intervalIntegral.integral_of_le hab, MeasureTheory.integral_Ioc_eq_integral_Ioo]

/-- `Ufun p` is the primitive of `qfun p`. -/
lemma Ufun_hasDerivAt (p : ℝ → ℝ) {t : ℝ} (ht : 0 < t)
    (hint : IntegrableOn (qfun p) (Set.Ioo 0 t))
    (hcont : ContinuousOn (qfun p) (Set.Ioi 0)) :
    HasDerivAt (Ufun p) (qfun p t) t := by
  have h_ii : IntervalIntegrable (qfun p) volume 0 t := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le ht.le]
    exact (integrableOn_Ioc_iff_integrableOn_Ioo (f := qfun p)).mpr hint
  have hcontAt : ContinuousAt (qfun p) t := hcont.continuousAt (isOpen_Ioi.mem_nhds ht)
  have hmeas : StronglyMeasurableAtFilter (qfun p) (𝓝 t) volume :=
    ⟨Set.Ioi 0, isOpen_Ioi.mem_nhds ht, hcont.aestronglyMeasurable isOpen_Ioi.measurableSet⟩
  have hderiv : HasDerivAt (fun u => ∫ x in (0 : ℝ)..u, qfun p x) (qfun p t) t :=
    intervalIntegral.integral_hasDerivAt_right h_ii hmeas hcontAt
  refine hderiv.congr_of_eventuallyEq ?_
  filter_upwards [isOpen_Ioi.mem_nhds ht] with s hs
  rw [Ufun]
  exact integral_Ioo_eq_intervalIntegral hs.le (qfun p)

/-- The primitive of an `L¹(0,∞)` function tends to `0` at `0⁺`. -/
lemma tendsto_primitive_zero {G : ℝ → ℝ} (hint : IntegrableOn G (Set.Ioi 0)) :
    Filter.Tendsto (fun ε => ∫ x in Set.Ioo 0 ε, G x)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
  have hcw := hint.continuousWithinAt_Ici_primitive_Ioi
  have hsub : Set.Ioi (0 : ℝ) ⊆ Set.Ici 0 := Set.Ioi_subset_Ici_self
  have hright : Filter.Tendsto (fun b => ∫ x in Set.Ioi b, G x)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (𝓝 (∫ x in Set.Ioi (0 : ℝ), G x)) :=
    hcw.mono_left (nhdsWithin_mono 0 hsub)
  have hmain : Filter.Tendsto
      (fun ε => (∫ x in Set.Ioi (0 : ℝ), G x) - (∫ x in Set.Ioi ε, G x))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (𝓝 0) := by
    have h : Filter.Tendsto
        (fun ε => (∫ x in Set.Ioi (0 : ℝ), G x) - (∫ x in Set.Ioi ε, G x))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0))
        (𝓝 ((∫ x in Set.Ioi (0 : ℝ), G x) - (∫ x in Set.Ioi (0 : ℝ), G x))) :=
      tendsto_const_nhds.sub hright
    rw [sub_self] at h
    simpa using h
  refine hmain.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hdisj : Disjoint (Set.Ioc (0 : ℝ) ε) (Set.Ioi ε) := by
    rw [Set.disjoint_left]
    intro x hx hx'
    exact absurd (Set.mem_Ioi.mp hx') (not_lt.mpr (Set.mem_Ioc.mp hx).2)
  have h1 : IntegrableOn G (Set.Ioc (0 : ℝ) ε) :=
    hint.mono_set (fun x hx => Set.mem_Ioi.mpr (Set.mem_Ioc.mp hx).1)
  have h2 : IntegrableOn G (Set.Ioi ε) :=
    hint.mono_set (fun x hx => Set.mem_Ioi.mpr (lt_trans hε (Set.mem_Ioi.mp hx)))
  have h3 := MeasureTheory.setIntegral_union hdisj measurableSet_Ioi h1 h2
  rw [Set.Ioc_union_Ioi_eq_Ioi hε.le] at h3
  rw [h3, MeasureTheory.integral_Ioc_eq_integral_Ioo]
  ring

/-- Interval integrability of `t ↦ qfun p t * Ufun p t`. -/
lemma intervalIntegrable_qU_mul {p : ℝ → ℝ} {ε ε₁ : ℝ} (hε : 0 < ε) (hεε₁ : ε ≤ ε₁)
    (hderiv : ∀ t : ℝ, 0 < t → t ≤ ε₁ → HasDerivAt (Ufun p) (qfun p t) t)
    (hcont : ContinuousOn (qfun p) (Set.Ioi 0)) :
    IntervalIntegrable (fun t => qfun p t * Ufun p t) volume ε ε₁ := by
  have huIcc : Set.uIcc ε ε₁ = Set.Icc ε ε₁ := Set.uIcc_of_le hεε₁
  have hUcont : ContinuousOn (Ufun p) (Set.Icc ε ε₁) := by
    intro x hx
    exact ((hderiv x (lt_of_lt_of_le hε hx.1) hx.2).continuousAt).continuousWithinAt
  have hqcont : ContinuousOn (qfun p) (Set.Icc ε ε₁) :=
    hcont.mono (fun x hx => lt_of_lt_of_le hε hx.1)
  have hc : ContinuousOn (fun t => qfun p t * Ufun p t) (Set.uIcc ε ε₁) := by
    rw [huIcc]
    exact hqcont.mul hUcont
  exact hc.intervalIntegrable

/-- Fundamental-theorem identity: `∫_ε^{ε₁} qfun p * Ufun p = (Ufun p ε₁)^2/2 - (Ufun p ε)^2/2`. -/
lemma integral_qU_mul {p : ℝ → ℝ} {ε ε₁ : ℝ} (hε : 0 < ε) (hεε₁ : ε ≤ ε₁)
    (hderiv : ∀ t : ℝ, 0 < t → t ≤ ε₁ → HasDerivAt (Ufun p) (qfun p t) t)
    (hcont : ContinuousOn (qfun p) (Set.Ioi 0)) :
    ∫ t in ε..ε₁, qfun p t * Ufun p t = (Ufun p ε₁) ^ 2 / 2 - (Ufun p ε) ^ 2 / 2 := by
  have huIcc : Set.uIcc ε ε₁ = Set.Icc ε ε₁ := Set.uIcc_of_le hεε₁
  have hInt := intervalIntegrable_qU_mul hε hεε₁ hderiv hcont
  have hmain : ∫ t in ε..ε₁, qfun p t * Ufun p t
      = Ufun p ε₁ * Ufun p ε₁ / 2 - Ufun p ε * Ufun p ε / 2 := by
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := fun t => Ufun p t * Ufun p t / 2) (f' := fun t => qfun p t * Ufun p t) ?_ hInt
    intro x hx
    rw [huIcc] at hx
    have hx0 : 0 < x := lt_of_lt_of_le hε hx.1
    have hxd := hderiv x hx0 hx.2
    have h1 : HasDerivAt (fun t => Ufun p t * Ufun p t)
        (qfun p x * Ufun p x + Ufun p x * qfun p x) x := hxd.mul hxd
    have h2 := h1.div_const 2
    have hgoal : (qfun p x * Ufun p x + Ufun p x * qfun p x) / 2
        = qfun p x * Ufun p x := by ring
    rw [hgoal] at h2
    exact h2
  rw [hmain]
  ring

end OneDPotAux

open OneDPotAux

theorem OneDPotNoEventuallyNeg {R : ℝ} (hR : 0 < R) (p : ℝ → ℝ)
    (hp : MeasureTheory.IntegrableOn (fun r : ℝ => r ^ 2 * p r) (Set.Ioo (0 : ℝ) R))
    (hp0 : ∀ r : ℝ, R ≤ r → p r = 0) :
    ¬ ∃ c : ℝ, 0 < c ∧ ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ →
      qfun p ε * Ufun p ε ≤ -c := by
  rintro ⟨c, hc, ε₀, hε₀, hbad⟩
  by_cases hcase : ∃ ε : ℝ, 0 < ε ∧ ε < ε₀ ∧ ¬ IntegrableOn (qfun p) (Set.Ioo 0 ε)
  · obtain ⟨ε, hεpos, hεlt, hni⟩ := hcase
    have hU0 : Ufun p ε = 0 := by
      rw [Ufun]
      exact MeasureTheory.integral_undef hni
    have h := hbad ε hεpos hεlt
    rw [hU0, mul_zero] at h
    linarith
  · push_neg at hcase
    have hcont : ContinuousOn (qfun p) (Set.Ioi 0) := continuousOn_qfun p hp hp0
    set ε₁ : ℝ := ε₀ / 4 with hε₁
    have hε₁pos : 0 < ε₁ := by positivity
    have hε₁lt : ε₁ < ε₀ := by linarith
    have hε₀2pos : (0 : ℝ) < ε₀ / 2 := by linarith
    -- the truncation of `qfun p` to `(0, ε₀/2)` is `L¹`
    set G : ℝ → ℝ := (Set.Ioo (0 : ℝ) (ε₀ / 2)).indicator (qfun p) with hG
    have hGint : IntegrableOn G (Set.Ioi 0) := by
      have h1 : IntegrableOn (qfun p) (Set.Ioo (0 : ℝ) (ε₀ / 2)) :=
        hcase (ε₀ / 2) hε₀2pos (by linarith)
      have h2 : Integrable ((Set.Ioo (0 : ℝ) (ε₀ / 2)).indicator (qfun p)) volume :=
        h1.integrable_indicator measurableSet_Ioo
      exact Integrable.mono_measure h2 Measure.restrict_le_self
    have hlimG : Filter.Tendsto (fun ε => ∫ x in Set.Ioo 0 ε, G x)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (𝓝 0) := tendsto_primitive_zero hGint
    have hUeq : (fun ε => Ufun p ε)
        =ᶠ[nhdsWithin (0 : ℝ) (Set.Ioi 0)] (fun ε => ∫ x in Set.Ioo 0 ε, G x) := by
      filter_upwards [self_mem_nhdsWithin,
        Filter.Eventually.filter_mono nhdsWithin_le_nhds (Iio_mem_nhds hε₀2pos)] with ε hε hlt
      rw [Ufun, hG]
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioo ?_
      intro x hx
      rw [Set.indicator_of_mem (Set.mem_Ioo.mpr ⟨hx.1, lt_trans hx.2 hlt⟩)]
    have hlimU : Filter.Tendsto (Ufun p) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (𝓝 0) :=
      hlimG.congr' hUeq.symm
    have hderiv : ∀ t : ℝ, 0 < t → t ≤ ε₁ → HasDerivAt (Ufun p) (qfun p t) t := by
      intro t ht htle
      exact Ufun_hasDerivAt p ht (hcase t ht (lt_of_le_of_lt htle hε₁lt)) hcont
    have hkey : ∀ ε : ℝ, 0 < ε → ε < ε₁ →
        (Ufun p ε₁) ^ 2 / 2 - (Ufun p ε) ^ 2 / 2 ≤ -c * (ε₁ - ε) := by
      intro ε hε hεlt
      have hid := integral_qU_mul hε hεlt.le hderiv hcont
      have hInt := intervalIntegrable_qU_mul hε hεlt.le hderiv hcont
      have hmono : ∫ t in ε..ε₁, qfun p t * Ufun p t ≤ ∫ t in ε..ε₁, (-c) := by
        refine intervalIntegral.integral_mono_on hεlt.le hInt intervalIntegrable_const ?_
        intro x hx
        exact hbad x (lt_of_lt_of_le hε hx.1) (lt_of_le_of_lt hx.2 hε₁lt)
      have hmono' : ∫ t in ε..ε₁, qfun p t * Ufun p t ≤ -c * (ε₁ - ε) := by
        simpa [intervalIntegral.integral_const, smul_eq_mul, mul_comm] using hmono
      rw [← hid]
      exact hmono'
    have hlim1 : Filter.Tendsto (fun ε => (Ufun p ε₁) ^ 2 / 2 - (Ufun p ε) ^ 2 / 2)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (𝓝 ((Ufun p ε₁) ^ 2 / 2)) := by
      have h2 : Filter.Tendsto (fun ε => (Ufun p ε) ^ 2 / 2)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (𝓝 0) := by
        have h := (hlimU.pow 2).div_const 2
        simpa using h
      have h3 : Filter.Tendsto
          (fun ε => (Ufun p ε₁) ^ 2 / 2 - (Ufun p ε) ^ 2 / 2)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (𝓝 ((Ufun p ε₁) ^ 2 / 2 - 0)) :=
        tendsto_const_nhds.sub h2
      simpa using h3
    have hlim2 : Filter.Tendsto (fun ε => -c * (ε₁ - ε))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (𝓝 (-c * ε₁)) := by
      have hid : Filter.Tendsto (fun ε : ℝ => ε) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (𝓝 0) :=
        tendsto_nhdsWithin_of_tendsto_nhds Filter.tendsto_id
      have h3 : Filter.Tendsto (fun ε : ℝ => -c * (ε₁ - ε))
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (𝓝 (-c * (ε₁ - 0))) :=
        (tendsto_const_nhds.sub hid).const_mul (-c)
      simpa using h3
    have hev : ∀ᶠ ε in nhdsWithin (0 : ℝ) (Set.Ioi 0),
        (Ufun p ε₁) ^ 2 / 2 - (Ufun p ε) ^ 2 / 2 ≤ -c * (ε₁ - ε) := by
      filter_upwards [self_mem_nhdsWithin,
        Filter.Eventually.filter_mono nhdsWithin_le_nhds (Iio_mem_nhds hε₁pos)] with ε hε hlt
      exact hkey ε hε hlt
    have hle : (Ufun p ε₁) ^ 2 / 2 ≤ -c * ε₁ := le_of_tendsto_of_tendsto hlim1 hlim2 hev
    nlinarith [sq_nonneg (Ufun p ε₁), hc, hε₁pos, hle]

end Work.SmallBoxA0
