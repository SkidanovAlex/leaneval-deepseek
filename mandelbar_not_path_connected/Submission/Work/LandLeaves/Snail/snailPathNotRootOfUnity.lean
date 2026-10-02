import Mathlib
import Submission.Work.LandLeaves.Snail.snailPathCases
import Submission.Work.LandLeaves.Snail.noSnailOfNotRootOfUnityClean

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The irrationally indifferent case of the Snail lemma in path form

`no_snail_of_not_rootOfUnity_path`: a germ `g` at a fixed point `z₀` with `‖deriv g z₀‖ = 1` and
`(deriv g z₀) ^ q ≠ 1` for every `q ≥ 1` admits **no** continuous forward path
`p : [0,∞) → ℂ ∖ {z₀}` with `g (p t) = p (t + 1)` and `p t → z₀`.

This is the case that the landing chain needs for an irrationally indifferent multiplier.  It is
obtained by translating `z₀` to the origin, which reduces it to the germ form at `0`,
`Work.LandLeaves.Snail.noSnailOfNotRootOfUnityClean` (the path form of Milnor's Lemma 13.2, proved
in this directory from the log-lift, the drift, the invariant region cut off by the snail path and
the Cauchy/dominated-convergence endgame).

The point of this module (besides the translation) is that it *replaces* the orbit-form statement
`no_converging_orbit_of_multiplier_not_root_of_unity` in the path chain: that statement is the
Snail principle itself (see `LandLeaves/convergingOrbitLinearizable.lean`,
`convergingOrbitLinearizable_iff_snailCore`) and is not available, whereas the path form is.
-/

open Filter
open scoped Topology

namespace Work.LandLeaves.Snail

/-- **Irrational case of the Snail lemma in path form.**  A germ at a fixed point with multiplier
of modulus one which is not a root of unity admits no forward path advancing by the germ and
converging to the fixed point. -/
theorem no_snail_of_not_rootOfUnity_path {g : ℂ → ℂ} {z₀ : ℂ} {p : ℝ → ℂ}
    (hg : AnalyticAt ℂ g z₀) (hfix : g z₀ = z₀) (h1 : ‖deriv g z₀‖ = 1)
    (hnr : ∀ q : ℕ, 0 < q → (deriv g z₀) ^ q ≠ 1)
    (hp : ContinuousOn p (Set.Ici 0)) (hne : ∀ t ∈ Set.Ici (0 : ℝ), p t ≠ z₀)
    (hshift : ∀ t ∈ Set.Ici (0 : ℝ), g (p t) = p (t + 1))
    (hlim : Tendsto p atTop (𝓝 z₀)) : False := by
  set f : ℂ → ℂ := fun w => g (w + z₀) - z₀ with hfdef
  set q : ℝ → ℂ := fun t => p t - z₀ with hqdef
  have hfa : AnalyticAt ℂ f 0 := by
    have h1' : AnalyticAt ℂ (fun w : ℂ => w + z₀) 0 := analyticAt_id.add analyticAt_const
    have h2' : AnalyticAt ℂ g ((fun w : ℂ => w + z₀) 0) := by simpa using hg
    have h3' : AnalyticAt ℂ (fun w : ℂ => g (w + z₀)) 0 := AnalyticAt.comp h2' h1'
    have h4' : AnalyticAt ℂ (fun w : ℂ => g (w + z₀) - z₀) 0 := h3'.sub analyticAt_const
    simpa [hfdef] using h4'
  have hf0 : f 0 = 0 := by simp [hfdef, hfix]
  have hfd : deriv f 0 = deriv g z₀ := by rw [hfdef]; exact deriv_shift_germ_path hg
  have hqc : ContinuousOn q (Set.Ici 0) := by
    rw [hqdef]; exact hp.sub continuousOn_const
  have hqne : ∀ t ∈ Set.Ici (0 : ℝ), q t ≠ 0 := by
    intro t ht h0
    simp only [hqdef, sub_eq_zero] at h0
    exact hne t ht h0
  have hqshift : ∀ t ∈ Set.Ici (0 : ℝ), f (q t) = q (t + 1) := by
    intro t ht
    simp only [hfdef, hqdef]
    have h1' : p t - z₀ + z₀ = p t := by ring
    rw [h1', hshift t ht]
  have hqlim : Tendsto q atTop (𝓝 0) := by
    rw [hqdef]; simpa using hlim.sub_const z₀
  refine noSnailOfNotRootOfUnityClean hfa hf0 hfd ?_ ?_ hqc hqne hqshift hqlim
  · exact h1
  · exact hnr

end Work.LandLeaves.Snail
