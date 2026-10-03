import Mathlib
import Submission.Work.Pert.Basic
import Submission.Work.Pert.Setup
import Submission.Work.Pert.tools
import Submission.Work.Interfaces.Fatou
import Submission.Work.Interfaces.Parabolic

/-!
# Uniform level: every compact piece of the gate drops below `ε` at a common time

`Work.PertCrux.exists_uniform_level_small`.  For a parabolic germ `f₀` with §4.1 data `d`, a
compact `K ⊆ d.DE` and `ε > 0` there is a single time `m` such that *for every* `w ∈ K` the
orbit of `φ₀(w)` stays in `D₀` up to time `m` and `‖f₀^[m] (φ₀ w)‖ < ε`.

Mathematically this is just the definition of the parabolic basin made uniform: by definition of
`ParabolicBasin`, every `z = φ₀ w` has a neighbourhood `U_z` on which all iterates land in `D₀`
and on which `f₀^[n] → 0` *uniformly*.  The family `{φ₀⁻¹ (interior U_{φ₀ w})}` is an open cover
of the compact `K` (here `φ₀` is holomorphic, hence continuous, on the open set `d.Dφ ⊇ d.DE`),
so finitely many `w`'s suffice, and the maximum of their times works for all of `K`.
-/

namespace Work.PertCrux

open Set Filter
open scoped Topology

theorem exists_uniform_level_small {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (d : MandelDim.ParabData f₀ D₀)
    (hd : MandelDim.IsParabolicGerm f₀ D₀)
    {K : Set ℂ} (hKc : IsCompact K) (hK : K ⊆ d.DE) {ε : ℝ} (hε : 0 < ε) :
    ∃ m : ℕ, ∀ w ∈ K,
      (∀ j : ℕ, j ≤ m → f₀^[j] (d.φ w) ∈ D₀) ∧ ‖f₀^[m] (d.φ w)‖ < ε := by
  classical
  -- Each point of `K` is in the parabolic basin; record the basin neighbourhood.
  have hpt : ∀ x : K, ∃ U : Set ℂ, U ∈ 𝓝 (d.φ x) ∧ (∀ n : ℕ, MapsTo (f₀^[n]) U D₀) ∧
      TendstoUniformlyOn (fun n : ℕ => f₀^[n]) (fun _ => (0 : ℂ)) atTop U :=
    fun x => (hK x.2).2
  choose U hUnhds hUmap hUtend using hpt
  -- Convert uniform convergence on `U x` into a time bound.
  have hex : ∀ x : K, ∃ M : ℕ, ∀ n : ℕ, M ≤ n → ∀ z ∈ U x, ‖f₀^[n] z‖ < ε := by
    intro x
    have h1 : ∀ᶠ n : ℕ in atTop, ∀ z ∈ U x, ‖f₀^[n] z‖ < ε := by
      have h2 := (Metric.tendstoUniformlyOn_iff.mp (hUtend x)) ε hε
      filter_upwards [h2] with n hn z hz
      simpa using hn z hz
    obtain ⟨M, hM⟩ := Filter.eventually_atTop.mp h1
    exact ⟨M, fun n hn z hz => hM n hn z hz⟩
  choose M hMconv using hex
  -- The family of open sets `d.Dφ ∩ φ₀⁻¹ (interior (U x))` covers the compact `K`.
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
  · intro j hj
    exact hUmap x j hmem
  · have hle : M x ≤ t.sup (fun x : K => M x) := Finset.le_sup hxt
    exact hMconv x _ hle _ hmem

end Work.PertCrux
