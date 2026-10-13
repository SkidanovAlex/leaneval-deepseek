import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Elliptic.lintegral_Ici_ofReal_rpow

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace Work.Elliptic

set_option autoImplicit false

/-- The `Ioi 0`-truncated weight `s ↦ s ^ a * f s ^ 2` as an `ℝ≥0∞`-valued function. -/
noncomputable def hardyXi (a : ℝ) (f : ℝ → ℝ) : ℝ → ℝ≥0∞ :=
  (Set.Ioi 0).indicator (fun s => ENNReal.ofReal (s ^ a * f s ^ 2))

/-- The `Ioi 0`-truncated Hardy weight `z ↦ z ^ (-c)`. -/
noncomputable def hardyA (c : ℝ) : ℝ → ℝ≥0∞ :=
  (Set.Ioi 0).indicator (fun z => ENNReal.ofReal (z ^ (-c)))

/-- The region `{(z,s) | 0 < s ≤ z}` of the double integral. -/
def hardyR : Set (ℝ × ℝ) := {p : ℝ × ℝ | 0 < p.2 ∧ p.2 ≤ p.1}

theorem measurableSet_hardyR : MeasurableSet hardyR := by
  have h1 : MeasurableSet {p : ℝ × ℝ | 0 < p.2} :=
    measurableSet_lt measurable_const measurable_snd
  have h2 : MeasurableSet {p : ℝ × ℝ | p.2 ≤ p.1} :=
    measurableSet_le measurable_snd measurable_fst
  exact h1.inter h2

theorem hardyXi_ne_top (a : ℝ) (f : ℝ → ℝ) (s : ℝ) : hardyXi a f s ≠ ⊤ := by
  unfold hardyXi
  by_cases h : s ∈ Set.Ioi (0 : ℝ)
  · rw [Set.indicator_of_mem h]; exact ENNReal.ofReal_ne_top
  · rw [Set.indicator_of_notMem h]; exact ENNReal.zero_ne_top

/-- If `g` is a.e. measurable for the measure restricted to `s`, then the `s`-indicator of `g`
is a.e. measurable for the ambient measure. -/
theorem aemeasurable_indicator_restrict {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [Zero β] {μ : Measure α} {s : Set α} (hs : MeasurableSet s) {g : α → β}
    (hg : AEMeasurable g (μ.restrict s)) : AEMeasurable (s.indicator g) μ := by
  obtain ⟨g', hg'm, hg'eq⟩ := hg
  refine ⟨s.indicator g', hg'm.indicator hs, ?_⟩
  have hg'eq' : ∀ᵐ x ∂(μ.restrict s), g x = g' x := hg'eq
  rw [MeasureTheory.ae_restrict_iff' hs] at hg'eq'
  filter_upwards [hg'eq'] with x hx
  by_cases hxs : x ∈ s
  · simp only [Set.indicator_of_mem hxs]; exact hx hxs
  · simp only [Set.indicator_of_notMem hxs]

theorem aemeasurable_hardyA (c : ℝ) : AEMeasurable (hardyA c) volume := by
  unfold hardyA
  refine aemeasurable_indicator_restrict measurableSet_Ioi ?_
  exact (ENNReal.continuous_ofReal.comp_continuousOn
    (ContinuousOn.rpow_const continuousOn_id (fun x hx => Or.inl (ne_of_gt hx)))).aemeasurable
      measurableSet_Ioi

theorem aemeasurable_hardyXi {a : ℝ} {f : ℝ → ℝ}
    (hf : IntegrableOn (fun z : ℝ => f z ^ 2) (Set.Ioi 0)) :
    AEMeasurable (hardyXi a f) volume := by
  unfold hardyXi
  refine aemeasurable_indicator_restrict measurableSet_Ioi ?_
  have h1 : AEMeasurable (fun s : ℝ => f s ^ 2) (volume.restrict (Set.Ioi 0)) :=
    hf.aestronglyMeasurable.aemeasurable
  have h2 : AEMeasurable (fun s : ℝ => s ^ a) (volume.restrict (Set.Ioi 0)) :=
    (ContinuousOn.rpow_const continuousOn_id (fun x hx => Or.inl (ne_of_gt hx))).aemeasurable
      measurableSet_Ioi
  exact ENNReal.measurable_ofReal.comp_aemeasurable (h2.mul h1)

theorem ofReal_hardy_algebra {a c s y : ℝ} (hc : 1 < c) (ha : a = c - 1) (hs : 0 < s) :
    ENNReal.ofReal (s ^ a * y ^ 2) * ENNReal.ofReal (s ^ (1 - c) / (c - 1))
      = ENNReal.ofReal (1 / (c - 1)) * ENNReal.ofReal (y ^ 2) := by
  subst ha
  have hc1 : (0 : ℝ) < c - 1 := by linarith
  have hp1 : (0 : ℝ) ≤ s ^ (c - 1) * y ^ 2 :=
    mul_nonneg (Real.rpow_nonneg hs.le _) (sq_nonneg y)
  have hp2 : (0 : ℝ) ≤ 1 / (c - 1) := (one_div_pos.mpr hc1).le
  have hrpow : s ^ (c - 1) * s ^ (1 - c) = 1 := by
    rw [← Real.rpow_add hs]
    have h : c - 1 + (1 - c) = 0 := by ring
    rw [h, Real.rpow_zero]
  rw [← ENNReal.ofReal_mul hp1, ← ENNReal.ofReal_mul hp2]
  congr 1
  rw [show s ^ (c - 1) * y ^ 2 * (s ^ (1 - c) / (c - 1))
        = (s ^ (c - 1) * s ^ (1 - c)) * y ^ 2 / (c - 1) by ring, hrpow, one_mul]
  ring

/-- The Tonelli (double integral) computation in general form. -/
theorem hardy_tonelli_swap (c a : ℝ) (hc : 1 < c) (ha : a = c - 1) (f : ℝ → ℝ)
    (hf : IntegrableOn (fun z : ℝ => f z ^ 2) (Set.Ioi 0)) :
    (∫⁻ z in Set.Ioi 0, ENNReal.ofReal (z ^ (-c)) *
        (∫⁻ s in Set.Ioc 0 z, ENNReal.ofReal (s ^ a * f s ^ 2)))
      = ENNReal.ofReal (1 / (c - 1) * ∫ z in Set.Ioi 0, f z ^ 2) := by
  have hc1 : (0 : ℝ) < c - 1 := by linarith
  have hΞ : AEMeasurable (hardyXi a f) volume := aemeasurable_hardyXi hf
  have hA : AEMeasurable (hardyA c) volume := aemeasurable_hardyA c
  have huncurry : AEMeasurable
      (fun p : ℝ × ℝ => ENNReal.ofReal (p.1 ^ (-c)) *
        (Set.Ioc 0 p.1).indicator (hardyXi a f) p.2) (volume.prod volume) := by
    have hpt : (fun p : ℝ × ℝ => ENNReal.ofReal (p.1 ^ (-c)) *
          (Set.Ioc 0 p.1).indicator (hardyXi a f) p.2)
        = fun p : ℝ × ℝ => hardyA c p.1 * hardyXi a f p.2 * hardyR.indicator (fun _ => 1) p := by
      funext p
      obtain ⟨z, s⟩ := p
      dsimp only
      by_cases h : s ∈ Set.Ioc 0 z
      · have hz : z ∈ Set.Ioi (0 : ℝ) := lt_of_lt_of_le h.1 h.2
        have hmem : (z, s) ∈ hardyR := h
        unfold hardyA
        rw [Set.indicator_of_mem hz, Set.indicator_of_mem h, Set.indicator_of_mem hmem, mul_one]
      · have hmem : (z, s) ∉ hardyR := h
        unfold hardyA hardyXi
        rw [Set.indicator_of_notMem h, Set.indicator_of_notMem hmem]
        simp
    rw [hpt]
    exact ((hA.comp_fst).mul (hΞ.comp_snd)).mul
      (measurable_const.indicator measurableSet_hardyR).aemeasurable
  have hinner : ∀ z : ℝ, (∫⁻ s in Set.Ioc 0 z, ENNReal.ofReal (s ^ a * f s ^ 2))
      = ∫⁻ s in Set.Ioc 0 z, hardyXi a f s := by
    intro z
    refine setLIntegral_congr_fun measurableSet_Ioc (fun s hs => ?_)
    unfold hardyXi
    exact (Set.indicator_of_mem (show s ∈ Set.Ioi (0 : ℝ) from hs.1)
      (fun s => ENNReal.ofReal (s ^ a * f s ^ 2))).symm
  have h1 : (∫⁻ z in Set.Ioi 0, ENNReal.ofReal (z ^ (-c)) *
        (∫⁻ s in Set.Ioc 0 z, ENNReal.ofReal (s ^ a * f s ^ 2)))
      = ∫⁻ z, ∫⁻ s, ENNReal.ofReal (z ^ (-c)) *
          (Set.Ioc 0 z).indicator (hardyXi a f) s := by
    have h1a : (∫⁻ z in Set.Ioi 0, ENNReal.ofReal (z ^ (-c)) *
          (∫⁻ s in Set.Ioc 0 z, ENNReal.ofReal (s ^ a * f s ^ 2)))
        = ∫⁻ z in Set.Ioi 0, ENNReal.ofReal (z ^ (-c)) *
          (∫⁻ s in Set.Ioc 0 z, hardyXi a f s) := by
      refine setLIntegral_congr_fun measurableSet_Ioi (fun z hz => ?_)
      rw [hinner z]
    have h1b : (∫⁻ z in Set.Ioi 0, ENNReal.ofReal (z ^ (-c)) *
          (∫⁻ s in Set.Ioc 0 z, hardyXi a f s))
        = ∫⁻ z, ∫⁻ s, ENNReal.ofReal (z ^ (-c)) *
            (Set.Ioc 0 z).indicator (hardyXi a f) s := by
      rw [← lintegral_indicator measurableSet_Ioi]
      apply lintegral_congr
      intro z
      by_cases hz : z ∈ Set.Ioi (0 : ℝ)
      · rw [Set.indicator_of_mem hz, lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
          lintegral_indicator measurableSet_Ioc]
      · rw [Set.indicator_of_notMem hz]
        have hz0 : Set.Ioc 0 z = ∅ := Set.Ioc_eq_empty hz
        rw [hz0]
        simp
    exact h1a.trans h1b
  have h2 : (∫⁻ z, ∫⁻ s, ENNReal.ofReal (z ^ (-c)) *
        (Set.Ioc 0 z).indicator (hardyXi a f) s)
      = ∫⁻ s, ∫⁻ z, ENNReal.ofReal (z ^ (-c)) *
        (Set.Ioc 0 z).indicator (hardyXi a f) s :=
    lintegral_lintegral_swap huncurry
  have h3 : (∫⁻ s, ∫⁻ z, ENNReal.ofReal (z ^ (-c)) *
        (Set.Ioc 0 z).indicator (hardyXi a f) s)
      = ∫⁻ s in Set.Ioi 0,
          hardyXi a f s * ∫⁻ z in Set.Ici s, ENNReal.ofReal (z ^ (-c)) := by
    rw [← lintegral_indicator measurableSet_Ioi]
    apply lintegral_congr
    intro s
    by_cases hs : s ∈ Set.Ioi (0 : ℝ)
    · rw [Set.indicator_of_mem hs]
      have hFeq : (fun z => ENNReal.ofReal (z ^ (-c)) *
            (Set.Ioc 0 z).indicator (hardyXi a f) s)
          = (Set.Ici s).indicator (fun z => ENNReal.ofReal (z ^ (-c)) *
              hardyXi a f s) := by
        funext z
        by_cases hzs : s ≤ z
        · rw [Set.indicator_of_mem (show s ∈ Set.Ioc 0 z from ⟨hs, hzs⟩),
              Set.indicator_of_mem (show z ∈ Set.Ici s from hzs)]
        · rw [Set.indicator_of_notMem (show s ∉ Set.Ioc 0 z from fun h => hzs h.2),
              Set.indicator_of_notMem (show z ∉ Set.Ici s from hzs)]
          simp
      rw [hFeq, lintegral_indicator measurableSet_Ici]
      rw [show (∫⁻ z in Set.Ici s, ENNReal.ofReal (z ^ (-c)) * hardyXi a f s)
            = ∫⁻ z in Set.Ici s, hardyXi a f s * ENNReal.ofReal (z ^ (-c)) from
          setLIntegral_congr_fun measurableSet_Ici (fun z _ => mul_comm _ _)]
      rw [lintegral_const_mul' (hardyXi a f s) (fun z => ENNReal.ofReal (z ^ (-c)))
        (hardyXi_ne_top a f s)]
    · rw [Set.indicator_of_notMem hs]
      have hzero : (fun z => ENNReal.ofReal (z ^ (-c)) *
            (Set.Ioc 0 z).indicator (hardyXi a f) s) = fun _ => (0 : ℝ≥0∞) := by
        funext z
        rw [Set.indicator_of_notMem (show s ∉ Set.Ioc 0 z from fun h => hs h.1)]
        simp
      rw [hzero]
      simp
  have h4 : (∫⁻ s in Set.Ioi 0,
          hardyXi a f s * ∫⁻ z in Set.Ici s, ENNReal.ofReal (z ^ (-c)))
      = ∫⁻ s in Set.Ioi 0, ENNReal.ofReal (s ^ a * f s ^ 2) *
          ENNReal.ofReal (s ^ (1 - c) / (c - 1)) := by
    refine setLIntegral_congr_fun measurableSet_Ioi (fun s hs => ?_)
    unfold hardyXi
    rw [lintegral_Ici_ofReal_rpow hc hs, Set.indicator_of_mem hs]
  have h5 : (∫⁻ s in Set.Ioi 0, ENNReal.ofReal (s ^ a * f s ^ 2) *
        ENNReal.ofReal (s ^ (1 - c) / (c - 1)))
      = ENNReal.ofReal (1 / (c - 1) * ∫ z in Set.Ioi 0, f z ^ 2) := by
    have h5a : (∫⁻ s in Set.Ioi 0, ENNReal.ofReal (s ^ a * f s ^ 2) *
          ENNReal.ofReal (s ^ (1 - c) / (c - 1)))
        = ∫⁻ s in Set.Ioi 0, ENNReal.ofReal (1 / (c - 1)) * ENNReal.ofReal (f s ^ 2) := by
      refine setLIntegral_congr_fun measurableSet_Ioi (fun s hs => ?_)
      exact ofReal_hardy_algebra hc ha hs
    rw [h5a, lintegral_const_mul' (ENNReal.ofReal (1 / (c - 1))) _ ENNReal.ofReal_ne_top]
    rw [show (∫⁻ s in Set.Ioi 0, ENNReal.ofReal (f s ^ 2))
          = ENNReal.ofReal (∫ s in Set.Ioi 0, f s ^ 2) from
        (ofReal_integral_eq_lintegral_ofReal hf
          (Filter.Eventually.of_forall (fun z => sq_nonneg (f z)))).symm]
    rw [← ENNReal.ofReal_mul (one_div_pos.mpr hc1).le]
  exact h1.trans (h2.trans (h3.trans (h4.trans h5)))

theorem hardy_op_L2_tonelli (β : ℝ) (hβ : 1 < β) (f : ℝ → ℝ)
    (hf : MeasureTheory.IntegrableOn (fun z : ℝ => f z ^ 2) (Set.Ioi 0)) :
    (∫⁻ z in Set.Ioi 0, ENNReal.ofReal (z ^ (-(3 * β / 2))) *
        (∫⁻ s in Set.Ioc 0 z, ENNReal.ofReal (s ^ ((3 * β - 2) / 2) * f s ^ 2)))
      = ENNReal.ofReal (2 / (3 * β - 2) * ∫ z in Set.Ioi 0, f z ^ 2) := by
  have h := hardy_tonelli_swap (3 * β / 2) ((3 * β - 2) / 2) (by linarith) (by ring) f hf
  have hcoef : 1 / (3 * β / 2 - 1) = 2 / (3 * β - 2) := by
    rw [div_eq_div_iff (by linarith : (3 * β / 2 - 1) ≠ 0) (by linarith : (3 * β - 2) ≠ 0)]
    ring
  rw [h, hcoef]

end Work.Elliptic
