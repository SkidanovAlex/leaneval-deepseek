import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.L62.branch_unique

/-!
# L62 — uniqueness of a holomorphic section of `ĥ = Ẽ - β` over an arbitrary connected base

`Work.L62.branch_unique` proves that two holomorphic sections of `ĥ = d.E - β` over the whole
upper component `hd.Bu` of the horn domain, agreeing at one point, coincide.  The §6 construction
(Lemma 6.2) needs the same statement on an *arbitrary* open preconnected base `W ⊆ hd.Bu` (the
chain of discs marches into the domain, and each disc is such a base).

The proof is the same local argument, run on `W`:

* `d.E = Φ ∘ φ` is holomorphic on `hd.Bu ⊇ W` (`hd.sub : Bu ∪ Bl ⊆ d.DE`), hence analytic at the
  point `q = H w₀`;
* differentiating `ĥ ∘ H = id` near `w₀` (chain rule) shows `deriv ĥ (H w₀) ≠ 0`, so `ĥ` is
  injective on a neighbourhood `U` of `q`
  (`injOn_nhds_of_analyticAt_deriv_ne_zero`, proved in `branch_unique.lean`);
* by continuity, both `H` and `H'` land in `U` near `w₀` and both are pushed by `ĥ` to `w`, so
  they agree on a neighbourhood of `w₀`;
* the identity theorem (`AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq`) on the open
  preconnected `W` finishes.
-/

namespace Work.L62

open MandelDim Set Filter
open scoped Topology

set_option linter.unusedVariables false

theorem section_unique_on {g₀ : ℂ → ℂ} {D : Set ℂ} (d : MandelDim.ParabData g₀ D)
    (hd : MandelDim.HornData d) {β : ℂ} {W : Set ℂ} (hWo : IsOpen W)
    (hWpc : IsPreconnected W) (hWsub : W ⊆ hd.Bu)
    {H H' : ℂ → ℂ} (hHd : DifferentiableOn ℂ H W) (hH'd : DifferentiableOn ℂ H' W)
    (hH : ∀ w ∈ W, (fun u => d.E u - β) (H w) = w ∧ H w ∈ hd.Bu)
    (hH' : ∀ w ∈ W, (fun u => d.E u - β) (H' w) = w ∧ H' w ∈ hd.Bu)
    {w₀ : ℂ} (hw₀ : w₀ ∈ W) (heq : H w₀ = H' w₀) :
    ∀ w ∈ W, H w = H' w := by
  -- `d.E = Φ ∘ φ` is holomorphic on `hd.Bu`
  have hφ_Bu : DifferentiableOn ℂ d.φ hd.Bu :=
    d.φ_holo.mono fun w hw => (hd.sub (Or.inl hw)).1
  have hE_diff : DifferentiableOn ℂ d.E hd.Bu :=
    d.Φ_holo.comp hφ_Bu fun w hw => (hd.sub (Or.inl hw)).2
  have hE_ana : AnalyticOnNhd ℂ d.E hd.Bu := hE_diff.analyticOnNhd hd.Bu_open
  have hq : H w₀ ∈ hd.Bu := (hH w₀ hw₀).2
  -- the derivative of `ĥ = d.E - β` at `q = H w₀` is nonzero: differentiate `ĥ ∘ H = id`
  have hq_ne : deriv (fun u => d.E u - β) (H w₀) ≠ 0 := by
    have hH_at : DifferentiableAt ℂ H w₀ := hHd.differentiableAt (hWo.mem_nhds hw₀)
    have hqE_at : DifferentiableAt ℂ d.E (H w₀) :=
      hE_diff.differentiableAt (hd.Bu_open.mem_nhds hq)
    have hψ_at : DifferentiableAt ℂ (fun u => d.E u - β) (H w₀) := hqE_at.sub_const β
    have hev : (fun w => (fun u => d.E u - β) (H w)) =ᶠ[𝓝 w₀] id :=
      Filter.eventually_of_mem (hWo.mem_nhds hw₀) fun w hw => (hH w hw).1
    have h1 : HasDerivAt (fun w => (fun u => d.E u - β) (H w)) 1 w₀ :=
      HasDerivAt.congr_of_eventuallyEq (hasDerivAt_id w₀) hev
    have h2 : HasDerivAt (fun w => (fun u => d.E u - β) (H w))
        (deriv (fun u => d.E u - β) (H w₀) * deriv H w₀) w₀ := by
      have h := (hψ_at.hasDerivAt).comp w₀ (hH_at.hasDerivAt)
      simpa [Function.comp_def] using h
    have huniq := h1.unique h2
    intro hzero
    rw [hzero, zero_mul] at huniq
    exact one_ne_zero huniq
  -- `ĥ` is injective on a neighbourhood `U` of `q`
  obtain ⟨U, hU, hUinj⟩ := injOn_nhds_of_analyticAt_deriv_ne_zero
    ((hE_ana (H w₀) hq).sub (analyticAt_const (v := β) (x := H w₀))) hq_ne
  -- both `H` and `H'` land in `U` near `w₀`, so they agree near `w₀`
  have hHc : ContinuousAt H w₀ := (hHd.differentiableAt (hWo.mem_nhds hw₀)).continuousAt
  have hH'c : ContinuousAt H' w₀ := (hH'd.differentiableAt (hWo.mem_nhds hw₀)).continuousAt
  have hpre : H ⁻¹' U ∈ 𝓝 w₀ := hHc.preimage_mem_nhds hU
  have hpre' : H' ⁻¹' U ∈ 𝓝 w₀ := hH'c.preimage_mem_nhds (heq ▸ hU)
  have hev2 : (fun w => H w - H' w) =ᶠ[𝓝 w₀] (fun _ : ℂ => (0 : ℂ)) := by
    filter_upwards [hpre, hpre', hWo.mem_nhds hw₀] with w hwU hwU' hwW
    have h1 : (fun u => d.E u - β) (H w) = w := (hH w hwW).1
    have h2 : (fun u => d.E u - β) (H' w) = w := (hH' w hwW).1
    have hEqw : H w = H' w := hUinj hwU hwU' (h1.trans h2.symm)
    simp [hEqw]
  -- identity theorem on the open preconnected set `W`
  have hF_ana : AnalyticOnNhd ℂ (fun w => H w - H' w) W := (hHd.sub hH'd).analyticOnNhd hWo
  have hEq : Set.EqOn (fun w => H w - H' w) (fun _ : ℂ => (0 : ℂ)) W :=
    hF_ana.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const hWpc hw₀ hev2
  intro w hw
  exact sub_eq_zero.mp (hEq hw)

end Work.L62
