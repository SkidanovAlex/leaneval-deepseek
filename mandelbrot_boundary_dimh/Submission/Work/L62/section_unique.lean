import Mathlib
import Submission.Work.L62.branch_unique

open Filter
open scoped Topology

namespace Work.L62

/-- **Uniqueness of a holomorphic section of a map over a connected base.**  If `X` is open, `p` is
holomorphic on `X`, `Y ⊆ X` is open and preconnected, and `s`, `t` are holomorphic sections of `p`
over `Y` (i.e. `s y ∈ X` and `p (s y) = y` for `y ∈ Y`, likewise `t`) which agree at one point
`y₀ ∈ Y`, then `s = t` on `Y`.

Intended proof (the standard one for sections of a locally biholomorphic map, exactly as in
`Work.L62.branch_unique`, which proves the same statement for the special base `hd.Bu` of the horn
map): differentiating `p ∘ s = id` near `y₀` shows `deriv p (s y₀) ≠ 0`, so `p` is injective on a
neighbourhood of `s y₀` (the local-injectivity lemma `injOn_nhds_of_analyticAt_deriv_ne_zero` of
`Work.L62.branch_unique.lean`), and since both `s` and `t` are continuous at `y₀` and both land in
that neighbourhood, they agree on a neighbourhood of `y₀`; the identity theorem
(`AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq`) finishes. -/
theorem section_unique {X Y : Set ℂ} (hXo : IsOpen X) (hYo : IsOpen Y)
    (hYc : IsPreconnected Y)
    (hYX : Y ⊆ X) {p : ℂ → ℂ} (hp : DifferentiableOn ℂ p X)
    {s t : ℂ → ℂ} (hs : DifferentiableOn ℂ s Y) (ht : DifferentiableOn ℂ t Y)
    (hsv : ∀ y ∈ Y, s y ∈ X ∧ p (s y) = y) (htv : ∀ y ∈ Y, t y ∈ X ∧ p (t y) = y)
    {y₀ : ℂ} (hy₀ : y₀ ∈ Y) (heq : s y₀ = t y₀) :
    ∀ y ∈ Y, s y = t y := by
  have hY_nhds : Y ∈ 𝓝 y₀ := hYo.mem_nhds hy₀
  have hsX : s y₀ ∈ X := (hsv y₀ hy₀).1
  have hp_at : AnalyticAt ℂ p (s y₀) := (hp.analyticOnNhd hXo) (s y₀) hsX
  -- differentiate `p ∘ s = id` near `y₀` to see `deriv p (s y₀) ≠ 0`
  have hs_at : DifferentiableAt ℂ s y₀ := hs.differentiableAt hY_nhds
  have hp_at_diff : DifferentiableAt ℂ p (s y₀) := hp.differentiableAt (hXo.mem_nhds hsX)
  have hq_ne : deriv p (s y₀) ≠ 0 := by
    have hev : (fun y => p (s y)) =ᶠ[𝓝 y₀] id :=
      Filter.eventually_of_mem hY_nhds fun y hy => (hsv y hy).2
    have h1 : HasDerivAt (fun y => p (s y)) 1 y₀ :=
      HasDerivAt.congr_of_eventuallyEq (hasDerivAt_id y₀) hev
    have h2 : HasDerivAt (fun y => p (s y)) (deriv p (s y₀) * deriv s y₀) y₀ := by
      have h := (hp_at_diff.hasDerivAt).comp y₀ (hs_at.hasDerivAt)
      simpa [Function.comp_def] using h
    have huniq := h1.unique h2
    intro hzero
    rw [hzero, zero_mul] at huniq
    exact one_ne_zero huniq
  -- `p` is injective on a neighbourhood `U` of `s y₀`
  obtain ⟨U, hU, hUinj⟩ := injOn_nhds_of_analyticAt_deriv_ne_zero hp_at hq_ne
  -- both `s` and `t` land in `U` near `y₀`
  have hsc : ContinuousAt s y₀ := hs_at.continuousAt
  have htc : ContinuousAt t y₀ := (ht.differentiableAt hY_nhds).continuousAt
  have hpre : s ⁻¹' U ∈ 𝓝 y₀ := hsc.preimage_mem_nhds hU
  have hpre' : t ⁻¹' U ∈ 𝓝 y₀ := htc.preimage_mem_nhds (heq ▸ hU)
  have hev2 : (fun y => s y - t y) =ᶠ[𝓝 y₀] (fun _ : ℂ => (0 : ℂ)) := by
    filter_upwards [hpre, hpre', hY_nhds] with y hyU hyU' hyY
    have hp1 : p (s y) = y := (hsv y hyY).2
    have hp2 : p (t y) = y := (htv y hyY).2
    have hEqw : s y = t y := hUinj hyU hyU' (by rw [hp1, hp2])
    simp [hEqw]
  -- identity theorem on the preconnected open set `Y`
  have hF_ana : AnalyticOnNhd ℂ (fun y => s y - t y) Y := (hs.sub ht).analyticOnNhd hYo
  have hEq : Set.EqOn (fun y => s y - t y) (fun _ : ℂ => (0 : ℂ)) Y :=
    hF_ana.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const hYc hy₀ hev2
  intro y hy
  exact sub_eq_zero.mp (hEq hy)

end Work.L62
