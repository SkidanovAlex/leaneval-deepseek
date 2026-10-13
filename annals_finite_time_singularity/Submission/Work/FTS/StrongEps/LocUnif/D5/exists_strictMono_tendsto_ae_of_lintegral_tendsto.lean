import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Markov

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory Filter

namespace Work.FTS.StrongEps.LocUnif.D5

/-- **Extraction step.**  If `∫⁻ x, L k x ∂μ → 0`, then there is a strictly increasing
`ψ : ℕ → ℕ` along which the integrals are summable, indeed bounded by the summable
geometric sequence `(1/2)^{k+1}`.

This is the "diagonal" selection: at stage `k` the hypothesis gives a threshold `N k`
beyond which `∫⁻ x, L m x ∂μ ≤ (1/2)^{k+1}`; the subsequence
`ψ k = (sup_{j ≤ k} N j) + k` is strictly increasing and stays beyond every threshold. -/
theorem exists_strictMono_lintegral_le_geometric {α : Type*} [MeasurableSpace α]
    {μ : MeasureTheory.Measure α}
    {L : ℕ → α → ENNReal}
    (h : Filter.Tendsto (fun k => ∫⁻ x, L k x ∂μ) Filter.atTop (nhds 0)) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      ∀ k, ∫⁻ x, L (ψ k) x ∂μ ≤ ENNReal.ofReal ((1/2 : ℝ) ^ (k + 1)) := by
  have hδpos : ∀ k, 0 < ENNReal.ofReal ((1/2 : ℝ) ^ (k + 1)) :=
    fun k => ENNReal.ofReal_pos.mpr (by positivity)
  have hex : ∀ k, ∃ N, ∀ m ≥ N, ∫⁻ x, L m x ∂μ ≤ ENNReal.ofReal ((1/2 : ℝ) ^ (k + 1)) :=
    fun k => (ENNReal.tendsto_atTop_zero.1 h) _ (hδpos k)
  choose N hN using hex
  refine ⟨fun k => (Finset.range (k + 1)).sup N + k, ?_, ?_⟩
  · intro a b hab
    have hsup : (Finset.range (a + 1)).sup N ≤ (Finset.range (b + 1)).sup N := by
      refine Finset.sup_le fun c hc => Finset.le_sup ?_
      simp only [Finset.mem_range] at hc ⊢
      omega
    simp only
    omega
  · intro k
    have hle : N k ≤ (Finset.range (k + 1)).sup N :=
      Finset.le_sup (Finset.mem_range.mpr (Nat.lt_succ_self k))
    exact hN k _ (le_trans hle (Nat.le_add_right _ _))

/-- **Limit step.**  If the series of integrals `∑' k, ∫⁻ x, L (ψ k) x ∂μ` is finite, then
`L (ψ k) x → 0` for almost every `x`: Tonelli's theorem turns the series of integrals into
the integral of the series, which is therefore finite a.e., and a finite `ℝ≥0∞`-series has
terms tending to `0`. -/
theorem ae_tendsto_of_tsum_lintegral_ne_top {α : Type*} [MeasurableSpace α]
    {μ : MeasureTheory.Measure α}
    {L : ℕ → α → ENNReal} (hm : ∀ k, AEMeasurable (L k) μ) {ψ : ℕ → ℕ}
    (h : (∑' k, ∫⁻ x, L (ψ k) x ∂μ) ≠ ⊤) :
    ∀ᵐ x ∂μ, Filter.Tendsto (fun k => L (ψ k) x) Filter.atTop (nhds 0) := by
  have hInt : ∫⁻ x, (∑' k, L (ψ k) x) ∂μ = ∑' k, ∫⁻ x, L (ψ k) x ∂μ :=
    MeasureTheory.lintegral_tsum (fun k => hm (ψ k))
  have haefin : ∀ᵐ x ∂μ, (∑' k, L (ψ k) x) < ⊤ := by
    refine MeasureTheory.ae_lt_top' ?_ ?_
    · exact AEMeasurable.tsum (fun k => hm (ψ k))
    · rw [hInt]; exact h
  filter_upwards [haefin] with x hx
  exact ENNReal.tendsto_atTop_zero_of_tsum_ne_top hx.ne

theorem exists_strictMono_tendsto_ae_of_lintegral_tendsto {α : Type*} [MeasurableSpace α]
    {μ : MeasureTheory.Measure α} [MeasureTheory.IsFiniteMeasure μ]
    {L : ℕ → α → ENNReal}
    (hm : ∀ k, AEMeasurable (L k) μ)
    (h : Filter.Tendsto (fun k => ∫⁻ x, L k x ∂μ) Filter.atTop (nhds 0)) :
    ∃ ψ : ℕ → ℕ, StrictMono ψ ∧
      ∀ᵐ x ∂μ, Filter.Tendsto (fun k => L (ψ k) x) Filter.atTop (nhds 0) := by
  obtain ⟨ψ, hψ, hbound⟩ := exists_strictMono_lintegral_le_geometric h
  refine ⟨ψ, hψ, ae_tendsto_of_tsum_lintegral_ne_top hm ?_⟩
  have hS : Summable (fun k : ℕ => (1/2 : ℝ) ^ (k + 1)) := by
    simpa [pow_succ, mul_comm] using
      (summable_geometric_of_norm_lt_one (by norm_num : ‖(1/2 : ℝ)‖ < 1)).mul_left (1/2 : ℝ)
  exact ne_top_of_le_ne_top hS.tsum_ofReal_ne_top (ENNReal.tsum_le_tsum hbound)

end Work.FTS.StrongEps.LocUnif.D5
