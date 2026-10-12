import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open MeasureTheory Filter
open scoped ENNReal Topology

namespace Work.BoseSym.Abs

theorem tendsto_toLp_of_dominated {α : Type*} [MeasurableSpace α] {μ : MeasureTheory.Measure α}
    {f : ℕ → α → ℝ} {g B : α → ℝ}
    (hf : ∀ n, MeasureTheory.MemLp (f n) 2 μ) (hg : MeasureTheory.MemLp g 2 μ)
    (hB : MeasureTheory.MemLp B 2 μ)
    (hb : ∀ n, ∀ᵐ x ∂μ, ‖f n x - g x‖ ≤ ‖B x‖)
    (hlim : ∀ᵐ x ∂μ, Filter.Tendsto (fun n => f n x) Filter.atTop (nhds (g x))) :
    Filter.Tendsto (fun n => (hf n).toLp (f n)) Filter.atTop (nhds (hg.toLp g)) := by
  -- It suffices to prove convergence in `eLpNorm`.
  rw [MeasureTheory.Lp.tendsto_Lp_iff_tendsto_eLpNorm'' f hf g hg]
  -- Integrand of the (extended) `L²` norm.
  have hmeas : ∀ n, AEMeasurable (fun x => ‖f n x - g x‖ₑ ^ (2:ℝ)) μ := by
    intro n
    have h1 : AEMeasurable (fun x => f n x - g x) μ :=
      ((hf n).sub hg).aestronglyMeasurable.aemeasurable
    have h3 := h1.enorm.pow_const 2
    simpa only [ENNReal.rpow_two] using h3
  have hbound : ∀ n, (fun x => ‖f n x - g x‖ₑ ^ (2:ℝ)) ≤ᵐ[μ]
      (fun x => ‖B x‖ₑ ^ (2:ℝ)) := by
    intro n
    filter_upwards [hb n] with x hx
    rw [← ofReal_norm (f n x - g x), ← ofReal_norm (B x)]
    exact ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal hx) (by norm_num)
  have hfin : ∫⁻ x, ‖B x‖ₑ ^ (2:ℝ) ∂μ ≠ ∞ := by
    have h := (MeasureTheory.eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
      (p := 2) (μ := μ) (f := B) (by norm_num) (by norm_num) hB.aestronglyMeasurable).mp hB.eLpNorm_lt_top
    simpa using h.ne
  have hlimF : ∀ᵐ x ∂μ, Tendsto (fun n => ‖f n x - g x‖ₑ ^ (2:ℝ)) atTop (nhds 0) := by
    filter_upwards [hlim] with x hx
    have h1 : Tendsto (fun n => f n x - g x) atTop (nhds 0) := by
      simpa using hx.sub_const (g x)
    have h2 : Tendsto (fun n => ‖f n x - g x‖ₑ) atTop (nhds 0) := by
      simpa using h1.enorm
    have h3 : Tendsto (fun n => ‖f n x - g x‖ₑ ^ (2:ℝ)) atTop (nhds ((0:ℝ≥0∞) ^ (2:ℝ))) :=
      ((ENNReal.continuous_rpow_const (y := (2:ℝ))).tendsto (0:ℝ≥0∞)).comp h2
    rwa [ENNReal.zero_rpow_of_pos (by norm_num)] at h3
  have heq : ∀ n, eLpNorm (f n - g) 2 μ = (∫⁻ x, ‖f n x - g x‖ₑ ^ (2:ℝ) ∂μ) ^ (1/2:ℝ) := by
    intro n
    rw [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal (p := 2) (by norm_num)
      (by norm_num) ((hf n).sub hg).aestronglyMeasurable]
    simp only [Pi.sub_apply, ENNReal.toReal_ofNat]
  -- Dominated convergence for the Lebesgue integral of the squared norms.
  have hA : Tendsto (fun n => ∫⁻ x, ‖f n x - g x‖ₑ ^ (2:ℝ) ∂μ) atTop (nhds 0) := by
    have hmain := MeasureTheory.tendsto_lintegral_of_dominated_convergence'
      (μ := μ) (F := fun n (x : α) => ‖f n x - g x‖ₑ ^ (2:ℝ))
      (f := fun _ : α => (0:ℝ≥0∞)) (fun x => ‖B x‖ₑ ^ (2:ℝ)) hmeas hbound hfin hlimF
    simpa using hmain
  have hcont : Tendsto (fun y : ℝ≥0∞ => y ^ (1/2:ℝ)) (nhds 0) (nhds 0) := by
    have h := (ENNReal.continuous_rpow_const (y := (1/2:ℝ))).tendsto (0:ℝ≥0∞)
    rwa [ENNReal.zero_rpow_of_pos (by norm_num)] at h
  exact Filter.Tendsto.congr (fun n => (heq n).symm) (hcont.comp hA)

end Work.BoseSym.Abs
