import Submission.Work.KMTAreas.A7.LargeInterface
import Submission.Port.Aesm

namespace Work.KMTAreas.A7

open MeasureTheory
open scoped ENNReal

/-- Joint measurability of a countably indexed family of measurable `ℝ≥0∞`-valued functions:
if the measurable space on the index type `ι` is discrete (e.g. `ι = ℤ`), then the uncurried
function `(t, x) ↦ G x t` is measurable for the product `σ`-algebra. -/
lemma measurable_uncurry_count {ι : Type*} [MeasurableSpace ι] [Countable ι]
    [MeasurableSingletonClass ι] {β : Type*} [MeasurableSpace β] {G : ι → β → ℝ≥0∞}
    (hG : ∀ x, Measurable (G x)) :
    Measurable (fun p : β × ι => G p.2 p.1) := by
  classical
  have hfun : (fun p : β × ι => G p.2 p.1)
      = fun p => ∑' x : ι, (if p.2 = x then G x p.1 else 0) := by
    ext p
    rw [tsum_eq_single p.2]
    · simp
    · intro b hb
      simp only [hb.symm, ↓reduceIte]
  rw [hfun]
  exact Measurable.tsum fun x =>
    Measurable.ite ((measurableSet_singleton x).preimage measurable_snd)
      ((hG x).comp measurable_fst) measurable_const

/-- The measure of `Set.Ioc (1/2) 1` is at most `1`. -/
lemma volume_restrict_Ioc_half_le_one :
    (volume.restrict (Set.Ioc (1/2 : ℝ) 1)) Set.univ ≤ (1 : ENNReal) := by
  rw [Measure.restrict_apply_univ, Real.volume_Ioc]
  norm_num

/-- The Lebesgue integral over `Set.Ioc (1/2) 1` of a function which is everywhere bounded by a
constant `C` on this interval is at most `C` (because the interval has measure `1/2 ≤ 1`). -/
lemma setLIntegral_Ioc_le (f : ℝ → ℝ≥0∞) (C : ENNReal)
    (h : ∀ t ∈ Set.Ioc (1/2 : ℝ) 1, f t ≤ C) :
    ∫⁻ t in Set.Ioc (1/2 : ℝ) 1, f t ≤ C := by
  calc ∫⁻ t in Set.Ioc (1/2 : ℝ) 1, f t ≤ ∫⁻ t in Set.Ioc (1/2 : ℝ) 1, C :=
        setLIntegral_mono measurable_const h
    _ = C * (volume.restrict (Set.Ioc (1/2 : ℝ) 1)) Set.univ := by rw [lintegral_const]
    _ ≤ C := by
        calc C * (volume.restrict (Set.Ioc (1/2 : ℝ) 1)) Set.univ ≤ C * 1 := by
              gcongr
              exact volume_restrict_Ioc_half_le_one
          _ = C := mul_one C

theorem eLpNorm_lintegral_le (q : ENNReal) (hq : 1 ≤ q) (Z : ℝ → ℤ → ENNReal) (C : ENNReal)
    (h : ∀ t ∈ Set.Ioc (1/2 : ℝ) 1,
      MeasureTheory.eLpNorm (fun x : ℤ => Z t x) q MeasureTheory.Measure.count ≤ C) :
    MeasureTheory.eLpNorm (fun x : ℤ => ∫⁻ t in Set.Ioc (1/2 : ℝ) 1, Z t x) q
      MeasureTheory.Measure.count ≤ C := by
  classical
  set ν : Measure ℝ := volume.restrict (Set.Ioc (1/2 : ℝ) 1) with hν
  rcases eq_or_ne q ⊤ with rfl | hqtop
  · -- `q = ⊤`: every section is pointwise bounded by `C`, and the integral respects that.
    have hsec : ∀ t ∈ Set.Ioc (1/2 : ℝ) 1, ∀ x : ℤ, Z t x ≤ C := by
      intro t ht x
      have h1 : MeasureTheory.eLpNorm (fun x : ℤ => Z t x) ⊤ MeasureTheory.Measure.count
          = ⨆ x : ℤ, Z t x := by
        rw [MeasureTheory.eLpNorm_exponent_top (hf := by pw_aesm), MeasureTheory.eLpNormEssSup_count]
        simp only [enorm_eq_self]
      calc Z t x ≤ ⨆ x : ℤ, Z t x := le_iSup (fun x : ℤ => Z t x) x
        _ = MeasureTheory.eLpNorm (fun x : ℤ => Z t x) ⊤ MeasureTheory.Measure.count := h1.symm
        _ ≤ C := h t ht
    have hL : MeasureTheory.eLpNorm (fun x : ℤ => ∫⁻ t, Z t x ∂ν) ⊤
          MeasureTheory.Measure.count = ⨆ x : ℤ, ∫⁻ t, Z t x ∂ν := by
      rw [MeasureTheory.eLpNorm_exponent_top (hf := by pw_aesm), MeasureTheory.eLpNormEssSup_count]
      simp only [enorm_eq_self]
    rw [hL]
    refine iSup_le fun x => ?_
    calc ∫⁻ t, Z t x ∂ν
        = ∫⁻ t in Set.Ioc (1/2 : ℝ) 1, Z t x := by rw [hν]
      _ ≤ C := setLIntegral_Ioc_le (fun t => Z t x) C (fun t ht => hsec t ht x)
  · -- `1 ≤ q < ∞`: replace every section by a measurable minorant with the same integral.
    have hex : ∀ x : ℤ, ∃ g : ℝ → ℝ≥0∞, Measurable g ∧ g ≤ (fun t : ℝ => Z t x) ∧
        ∫⁻ t, Z t x ∂ν = ∫⁻ t, g t ∂ν :=
      fun x => MeasureTheory.exists_measurable_le_lintegral_eq ν (fun t : ℝ => Z t x)
    choose G hGmeas hGle hGint using hex
    have hZ'meas : Measurable (fun p : ℝ × ℤ => G p.2 p.1) := measurable_uncurry_count hGmeas
    have hZ'ae : AEMeasurable (Function.uncurry (fun t : ℝ => fun x : ℤ => G x t))
        (ν.prod MeasureTheory.Measure.count) := hZ'meas.aemeasurable
    have hMink := Commons.Analysis.Integral.lintegral_lintegral_le_lintegral_lintegral
      (μ := MeasureTheory.Measure.count) (ν := ν) (p := q)
      (g := fun t : ℝ => fun x : ℤ => G x t) hq hZ'ae
    have hgoal : (fun x : ℤ => ∫⁻ t, Z t x ∂ν) = fun x : ℤ => ∫⁻ t, G x t ∂ν := by
      funext x
      exact hGint x
    rw [hgoal]
    refine hMink.trans ?_
    calc ∫⁻ t, MeasureTheory.eLpNorm (fun x : ℤ => G x t) q MeasureTheory.Measure.count ∂ν
        ≤ ∫⁻ t, MeasureTheory.eLpNorm (fun x : ℤ => Z t x) q MeasureTheory.Measure.count ∂ν := by
          refine lintegral_mono fun t => ?_
          refine eLpNorm_mono_enorm (hf := by pw_aesm) fun x => ?_
          simp only [enorm_eq_self]
          exact hGle x t
      _ = ∫⁻ t in Set.Ioc (1/2 : ℝ) 1,
            MeasureTheory.eLpNorm (fun x : ℤ => Z t x) q MeasureTheory.Measure.count := by
          rw [hν]
      _ ≤ C := setLIntegral_Ioc_le
          (fun t => MeasureTheory.eLpNorm (fun x : ℤ => Z t x) q MeasureTheory.Measure.count) C h

end Work.KMTAreas.A7
