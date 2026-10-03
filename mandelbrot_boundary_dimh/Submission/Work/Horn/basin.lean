import Mathlib
import Submission.Work.Interfaces.Parabolic

/-!
# The parabolic basin as defined by the interface: openness and invariance

`ParabolicBasin f D = {z | ∃ U ∈ 𝓝 z, (∀ n, f^[n] '' U ⊆ D) ∧ f^[n] → 0 uniformly on U}`.

This file proves (from the definition alone, plus the local openness of `f`):

* `basin_open_map` : a non-constant holomorphic map on a domain is locally open
  (Mathlib's open mapping theorem `AnalyticOnNhd.is_constant_or_isOpen`).
* `basin_basic` : the basin is open, forward invariant, and backward invariant.
-/

namespace Work.Horn

noncomputable section

open MandelDim Filter Topology Metric
open scoped Topology

namespace MandelDim

/-- A non-constant holomorphic function on a domain is locally open. -/
theorem basin_open_map {D : Set ℂ} (hD : IsOpen D) (hconn : IsPreconnected D) {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f D) {z₀ : ℂ} (hz₀ : z₀ ∈ D) (hne : deriv f z₀ ≠ 0) :
    ∀ z ∈ D, ∀ U ∈ nhds z, f '' U ∈ nhds (f z) := by
  rcases (hf.analyticOnNhd hD).is_constant_or_isOpen hconn with ⟨w, hw⟩ | hopen
  · exfalso
    have h1 : f =ᶠ[nhds z₀] fun _ => w := by
      filter_upwards [hD.mem_nhds hz₀] with z hz using hw z hz
    have h2 : deriv f z₀ = deriv (fun _ : ℂ => w) z₀ := h1.deriv_eq
    rw [h2] at hne
    simp at hne
  · intro z hz U hU
    obtain ⟨V, hVU, hVopen, hzV⟩ := _root_.mem_nhds_iff.mp hU
    have h1 : f '' (V ∩ D) ∈ nhds (f z) :=
      (hopen (V ∩ D) (fun x hx => hx.2) (hVopen.inter hD)).mem_nhds ⟨z, ⟨hzV, hz⟩, rfl⟩
    refine Filter.mem_of_superset h1 ?_
    rintro y ⟨x, ⟨hxV, _⟩, rfl⟩
    exact ⟨x, hVU hxV, rfl⟩

/-- The parabolic basin is open, forward invariant, and backward invariant (inside `D`). -/
theorem basin_basic {f : ℂ → ℂ} {D : Set ℂ} (hD : IsOpen D) (hf : DifferentiableOn ℂ f D)
    (hopen : ∀ z ∈ D, ∀ U ∈ nhds z, f '' U ∈ nhds (f z)) :
    IsOpen (ParabolicBasin f D) ∧
      (∀ z ∈ ParabolicBasin f D, f z ∈ ParabolicBasin f D) ∧
      (∀ z ∈ D, f z ∈ ParabolicBasin f D → z ∈ ParabolicBasin f D) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [isOpen_iff_mem_nhds]
    intro z hz
    obtain ⟨U, hU, hiter, hconv⟩ := hz
    obtain ⟨V, hVU, hVopen, hzV⟩ := _root_.mem_nhds_iff.mp hU
    refine Filter.mem_of_superset (hVopen.mem_nhds hzV) ?_
    intro w hw
    exact ⟨U, Filter.mem_of_superset (hVopen.mem_nhds hw) hVU, hiter, hconv⟩
  · intro z hz
    obtain ⟨U, hU, hiter, hconv⟩ := hz
    obtain ⟨V, hVU, hVopen, hzV⟩ := _root_.mem_nhds_iff.mp hU
    have hzD : z ∈ D := by simpa using hiter 0 (hVU hzV)
    refine ⟨f '' V, hopen z hzD V (hVopen.mem_nhds hzV), ?_, ?_⟩
    · intro n y hy
      obtain ⟨x, hx, rfl⟩ := hy
      simpa [Function.iterate_succ_apply] using hiter (n + 1) (hVU hx)
    · rw [Metric.tendstoUniformlyOn_iff] at hconv ⊢
      intro ε hε
      obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (hconv ε hε)
      refine Filter.eventually_atTop.mpr ⟨N, fun n hn y hy => ?_⟩
      obtain ⟨x, hx, rfl⟩ := hy
      have h4 : f^[n] (f x) = f^[n + 1] x := (Function.iterate_succ_apply f n x).symm
      rw [h4]
      exact hN (n + 1) (by omega) x (hVU hx)
  · intro z hzD hz
    obtain ⟨U, hU, hiter, hconv⟩ := hz
    have hcont : ContinuousAt f z := hf.continuousOn.continuousAt (hD.mem_nhds hzD)
    refine ⟨f ⁻¹' U ∩ D, Filter.inter_mem (hcont.preimage_mem_nhds hU) (hD.mem_nhds hzD), ?_, ?_⟩
    · intro n y hy
      cases n with
      | zero => exact hy.2
      | succ k =>
          simpa [Function.iterate_succ_apply] using hiter k hy.1
    · rw [Metric.tendstoUniformlyOn_iff] at hconv ⊢
      intro ε hε
      obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp (hconv ε hε)
      refine Filter.eventually_atTop.mpr ⟨N + 1, fun n hn y hy => ?_⟩
      obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
      have h4 : f^[k + 1] y = f^[k] (f y) := Function.iterate_succ_apply f k y
      rw [h4]
      exact hN k (by omega) (f y) hy.1

end MandelDim

end

end Work.Horn
