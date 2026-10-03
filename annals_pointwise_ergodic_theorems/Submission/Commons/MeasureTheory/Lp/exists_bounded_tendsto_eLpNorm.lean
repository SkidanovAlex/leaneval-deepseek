import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity
import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Sub
import Submission.Port.Aesm

open MeasureTheory Filter
open scoped ENNReal Topology

namespace Commons.MeasureTheory.Lp

/-- Auxiliary: the family `k ↦ (if c ≤ k then 0 else a)^p` (with `p ≥ 0`) is antitone in `k`. -/
private lemma antitone_trunc {c : ℝ} {a : ℝ≥0∞} {p : ℝ} (hp : 0 ≤ p) :
    Antitone (fun k : ℕ => (if c ≤ (k : ℝ) then (0 : ℝ≥0∞) else a) ^ p) := by
  intro m n hmn
  have hmn' : (m : ℝ) ≤ (n : ℝ) := by exact_mod_cast hmn
  by_cases hcm : c ≤ (m : ℝ)
  · have hcn : c ≤ (n : ℝ) := le_trans hcm hmn'
    simp only [hcm, hcn, ↓reduceIte]; exact le_rfl
  · by_cases hcn : c ≤ (n : ℝ)
    · simp only [hcm, hcn, ↓reduceIte]
      exact ENNReal.rpow_le_rpow (by simp) hp
    · simp only [hcm, hcn, ↓reduceIte]; exact le_rfl

theorem exists_bounded_tendsto_eLpNorm {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    {p : ENNReal} (hp : p ≠ ⊤) {f : α → ℂ} (hf : MeasureTheory.MemLp f p μ) :
    ∃ g : ℕ → α → ℂ, (∀ n, Measurable (g n)) ∧ (∀ n, ∃ C : ℝ, ∀ x, ‖g n x‖ ≤ C) ∧
      (∀ n, MeasureTheory.MemLp (g n) p μ) ∧
      (∀ n, MeasureTheory.eLpNorm (g n) p μ ≤ MeasureTheory.eLpNorm f p μ) ∧
      Filter.Tendsto (fun n => MeasureTheory.eLpNorm (f - g n) p μ) Filter.atTop (nhds 0) := by
  -- A genuinely measurable representative of `f`.
  obtain ⟨f', hf'_meas, hf'_eq⟩ : ∃ f' : α → ℂ, Measurable f' ∧ f =ᵐ[μ] f' :=
    ⟨hf.aemeasurable.mk f, hf.aemeasurable.measurable_mk, hf.aemeasurable.ae_eq_mk⟩
  have hf'_eLpNorm_lt_top : eLpNorm f' p μ < ∞ := by
    rw [← eLpNorm_congr_ae hf'_eq]; exact hf.eLpNorm_lt_top
  let g : ℕ → α → ℂ := fun n x => if ‖f' x‖ ≤ (n : ℝ) then f' x else 0
  have hg_meas : ∀ n, Measurable (g n) := by
    intro n
    dsimp only [g]
    exact Measurable.ite (measurableSet_le hf'_meas.norm measurable_const) hf'_meas measurable_const
  -- pointwise description of the difference
  have h_pt : ∀ n x, ‖f' x - g n x‖ₑ = if ‖f' x‖ ≤ (n : ℝ) then (0 : ℝ≥0∞) else ‖f' x‖ₑ := by
    intro n x
    dsimp only [g]
    by_cases hx : ‖f' x‖ ≤ (n : ℝ)
    · rw [if_pos hx, if_pos hx]; simp
    · rw [if_neg hx, if_neg hx]; simp
  refine ⟨g, hg_meas, ?_, ?_, ?_, ?_⟩
  · intro n
    exact ⟨(n : ℝ), fun x => by
      dsimp only [g]
      by_cases hx : ‖f' x‖ ≤ (n : ℝ)
      · rw [if_pos hx]; exact hx
      · rw [if_neg hx]; simp⟩
  · intro n
    rw [MeasureTheory.memLp_iff]
    refine lt_of_le_of_lt (eLpNorm_mono (hf := by pw_aesm) (fun x => ?_)) hf'_eLpNorm_lt_top
    dsimp only [g]
    by_cases hx : ‖f' x‖ ≤ (n : ℝ)
    · rw [if_pos hx]
    · rw [if_neg hx]; simp
  · intro n
    calc eLpNorm (g n) p μ ≤ eLpNorm f' p μ := eLpNorm_mono (hf := by pw_aesm) (fun x => by
          dsimp only [g]
          by_cases hx : ‖f' x‖ ≤ (n : ℝ)
          · rw [if_pos hx]
          · rw [if_neg hx]; simp)
      _ = eLpNorm f p μ := (eLpNorm_congr_ae hf'_eq).symm
  · by_cases hp0 : p = 0
    · have h0 : ∀ n, eLpNorm (f - g n) p μ = 0 := fun n => by
        rw [hp0]
        exact eLpNorm_exponent_zero (hf.aestronglyMeasurable.sub (hg_meas n).aestronglyMeasurable)
      simp_rw [h0]
      exact tendsto_const_nhds
    · have hp0lt : 0 < p.toReal := ENNReal.toReal_pos hp0 hp
      let h : ℕ → α → ℝ≥0∞ := fun n x => ‖f' x - g n x‖ₑ ^ p.toReal
      have h_meas : ∀ n, AEMeasurable (h n) μ := by
        intro n
        show AEMeasurable (fun x => ‖f' x - g n x‖ₑ ^ p.toReal) μ
        have hm : Measurable (fun x => ‖f' x - g n x‖ₑ) := (hf'_meas.sub (hg_meas n)).enorm
        exact ((ENNReal.continuous_rpow_const (y := p.toReal)).measurable.comp hm).aemeasurable
      have h_anti : ∀ᵐ x ∂μ, Antitone fun n => h n x := by
        apply Filter.Eventually.of_forall
        intro x
        have hfun : (fun n => h n x) = fun (n : ℕ) =>
            (if ‖f' x‖ ≤ (n : ℝ) then (0 : ℝ≥0∞) else ‖f' x‖ₑ) ^ p.toReal := by
          funext n
          dsimp only [h]
          rw [h_pt n x]
        rw [hfun]
        exact antitone_trunc hp0lt.le
      have h_tendsto : ∀ᵐ x ∂μ, Tendsto (fun n => h n x) atTop (𝓝 0) := by
        apply Filter.Eventually.of_forall
        intro x
        have hev : ∀ᶠ n : ℕ in atTop, ‖f' x‖ ≤ (n : ℝ) :=
          tendsto_natCast_atTop_atTop.eventually (eventually_ge_atTop ‖f' x‖)
        refine Tendsto.congr' ?_ tendsto_const_nhds
        filter_upwards [hev] with n hn
        dsimp only [h]
        rw [h_pt n x, if_pos hn, ENNReal.zero_rpow_of_pos hp0lt]
      have h0 : ∫⁻ x, h 0 x ∂μ ≠ ∞ := by
        apply ne_of_lt
        refine lt_of_le_of_lt (lintegral_mono (fun x => ?_))
          (lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top hp0 hp hf'_eLpNorm_lt_top)
        dsimp only [h]
        rw [h_pt 0 x]
        exact ENNReal.rpow_le_rpow (by by_cases hx : ‖f' x‖ ≤ (0 : ℝ) <;> simp [hx]) hp0lt.le
      have h_int_tendsto : Tendsto (fun n => ∫⁻ x, h n x ∂μ) atTop (𝓝 0) := by
        simpa using lintegral_tendsto_of_tendsto_of_antitone h_meas h_anti h0 h_tendsto
      have h_conv : Tendsto (fun n => eLpNorm (f' - g n) p μ) atTop (𝓝 0) := by
        have heq : ∀ n, eLpNorm (f' - g n) p μ = (∫⁻ x, h n x ∂μ) ^ (1 / p.toReal) := by
          intro n
          rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (hf := by pw_aesm) hp0 hp]
          rfl
        simp only [heq]
        have hc := (ENNReal.continuous_rpow_const (y := 1 / p.toReal)).tendsto 0
        have := hc.comp h_int_tendsto
        rwa [ENNReal.zero_rpow_of_pos (one_div_pos.mpr hp0lt)] at this
      have hcongr : (fun n => eLpNorm (f' - g n) p μ) =ᶠ[atTop]
          (fun n => eLpNorm (f - g n) p μ) :=
        Filter.Eventually.of_forall (fun n =>
          (eLpNorm_congr_ae (hf'_eq.sub (Filter.EventuallyEq.refl (ae μ) (g n)))).symm)
      exact Tendsto.congr' hcongr h_conv

end Commons.MeasureTheory.Lp