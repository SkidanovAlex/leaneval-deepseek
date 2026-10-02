import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option linter.unusedVariables false

namespace Work.Implosion.Chord

/-- If `f : ℝ → ℝ` is strictly increasing, surjective and satisfies `x < f x` for all `x`,
then iterating any "inverse" of `f` (via `Function.invFun`) drives every starting point to
`-∞`. -/
theorem orbit_invFun_tendsto_atBot (f : ℝ → ℝ) (hcont : Continuous f) (hmono : StrictMono f)
    (hgt : ∀ x : ℝ, x < f x) (hsurj : Function.Surjective f) (a : ℝ) :
    Filter.Tendsto (fun n : ℕ => (Function.invFun f)^[n] a) Filter.atTop Filter.atBot := by
  set g := Function.invFun f with hg
  -- `g` is a right inverse of `f`
  have hfg : ∀ y, f (g y) = y := fun y => Function.invFun_eq (hsurj y)
  -- consequently `g y < y` for every `y`
  have hlt : ∀ y, g y < y := fun y => by
    have h1 := hgt (g y); rwa [hfg y] at h1
  have hstep : ∀ n, g^[n+1] a = g (g^[n] a) := fun n => Function.iterate_succ_apply' ..
  -- the orbit is antitone (indeed strictly decreasing)
  have hanti : Antitone (fun n : ℕ => g^[n] a) :=
    antitone_nat_of_succ_le (fun n => by rw [hstep n]; exact le_of_lt (hlt _))
  -- a bounded antitone sequence would converge to a finite limit `l`
  rcases tendsto_atTop_of_antitone hanti with h | ⟨l, hl⟩
  · exact h
  · exfalso
    -- that limit `l` is the greatest lower bound of the range
    have hglb : IsGLB (Set.range (fun n : ℕ => g^[n] a)) l := isGLB_of_tendsto_atTop hanti hl
    -- so `f l` is below every term of the orbit ...
    have hfll : ∀ n, f l ≤ g^[n] a := by
      intro n
      have h1 : l ≤ g^[n+1] a := hglb.1 ⟨n+1, rfl⟩
      have h2 : f l ≤ f (g^[n+1] a) := hmono.monotone h1
      simp only [hstep n, hfg] at h2
      exact h2
    have hfl_lb : f l ∈ lowerBounds (Set.range (fun n : ℕ => g^[n] a)) := by
      intro y hy
      obtain ⟨n, rfl⟩ := hy
      exact hfll n
    -- ... hence `f l` is at most the greatest lower bound `l`, contradicting `l < f l`
    have h2 : f l ≤ l := hglb.2 hfl_lb
    linarith [hgt l]

end Work.Implosion.Chord
