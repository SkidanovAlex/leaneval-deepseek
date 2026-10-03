import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.PertCrux.exists_uniform_level_small

namespace Work.Analysis.PertCrux

open Set Filter
open scoped Topology

/-- For a §4.1 datum `d` for a parabolic germ `f₀`, a compact `K ⊆ d.DE` and `ε > 0` there is a
single time `N` such that for every `w ∈ K` the whole orbit of `φ₀(w)` stays in `D₀` and drops
below `ε` at time `N` and stays below it:
`∃ N, ∀ w ∈ K, (∀ n, f₀^[n] (d.φ w) ∈ D₀) ∧ ∀ n ≥ N, ‖f₀^[n] (d.φ w)‖ < ε`.
This is `ParabolicBasin` made uniform: finitely many basin neighbourhoods cover the compact
`d.φ '' K`. -/
theorem exists_uniform_eventually_small {f₀ : ℂ → ℂ} {D₀ : Set ℂ}
    (d : MandelDim.ParabData f₀ D₀) (hd : MandelDim.IsParabolicGerm f₀ D₀)
    {K : Set ℂ} (hKc : IsCompact K) (hK : K ⊆ d.DE) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ w ∈ K, (∀ n : ℕ, f₀^[n] (d.φ w) ∈ D₀) ∧
      ∀ n : ℕ, N ≤ n → ‖f₀^[n] (d.φ w)‖ < ε := by
  classical
  -- Every point of `K` maps into the parabolic basin, so it has a basin neighbourhood on which
  -- all iterates land in `D₀` and converge to `0` *uniformly* (in the point and in the time).
  have hpt : ∀ x : K, ∃ U : Set ℂ, U ∈ 𝓝 (d.φ x) ∧ (∀ n : ℕ, MapsTo (f₀^[n]) U D₀) ∧
      TendstoUniformlyOn (fun n : ℕ => f₀^[n]) (fun _ => (0 : ℂ)) atTop U :=
    fun x => (hK x.2).2
  choose U hUnhds hUmap hUtend using hpt
  -- Restate the uniform convergence as a time beyond which `U x` stays below `ε`.
  have hex : ∀ x : K, ∃ M : ℕ, ∀ n : ℕ, M ≤ n → ∀ z ∈ U x, ‖f₀^[n] z‖ < ε := by
    intro x
    have h1 : ∀ᶠ n : ℕ in atTop, ∀ z ∈ U x, ‖f₀^[n] z‖ < ε := by
      have h2 := (Metric.tendstoUniformlyOn_iff.mp (hUtend x)) ε hε
      filter_upwards [h2] with n hn z hz
      simpa using hn z hz
    obtain ⟨M, hM⟩ := Filter.eventually_atTop.mp h1
    exact ⟨M, fun n hn z hz => hM n hn z hz⟩
  choose M hMconv using hex
  -- The open sets `d.Dφ ∩ φ₀⁻¹ (interior (U x))` cover the compact `K`.
  have hopen : ∀ x : K, IsOpen (d.Dφ ∩ d.φ ⁻¹' interior (U x)) :=
    fun x => d.φ_holo.continuousOn.isOpen_inter_preimage d.Dφ_open isOpen_interior
  have hcov : K ⊆ ⋃ x : K, (d.Dφ ∩ d.φ ⁻¹' interior (U x)) := by
    intro w hw
    refine Set.mem_iUnion.mpr ⟨⟨w, hw⟩, ?_, ?_⟩
    · exact (hK hw).1
    · exact mem_interior_iff_mem_nhds.mpr (hUnhds ⟨w, hw⟩)
  obtain ⟨t, ht⟩ :=
    hKc.elim_finite_subcover (fun x : K => d.Dφ ∩ d.φ ⁻¹' interior (U x)) hopen hcov
  refine ⟨t.sup (fun x : K => M x), ?_⟩
  intro w hw
  obtain ⟨x, hxt, hxw⟩ := by simpa only [Set.mem_iUnion] using ht hw
  have hmem : d.φ w ∈ U x := interior_subset hxw.2
  constructor
  · -- the whole orbit of `φ₀ w` stays in `D₀`, because `φ₀ w` lies in the basin neighbourhood
    -- `U x` and all iterates map `U x` into `D₀`.
    intro n
    exact hUmap x n hmem
  · -- and beyond the finite maximum of the times `M x` it is below `ε`.
    intro n hn
    exact hMconv x n (le_trans (Finset.le_sup hxt) hn) (d.φ w) hmem

end Work.Analysis.PertCrux
