import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.ELRig

/-- For an arbitrary function `f : ℝ → ℝ`, the set of values `v` that `f` attains
*constantly on some non-degenerate open interval* is countable.  The proof picks,
for each such value `v`, a witnessing interval `(lo v, hi v)` on which `f ≡ v` and a
rational `g v` inside it.  Distinct values yield disjoint witnessing intervals
(an overlapping point could not carry two distinct values of `f`), hence distinct
rationals, giving an injection of the set into `ℚ`. -/
theorem countable_setOf_interval_constant (f : ℝ → ℝ) :
    {v : ℝ | ∃ a b : ℝ, a < b ∧ ∀ t ∈ Set.Ioo a b, f t = v}.Countable := by
  classical
  set s : Set ℝ := {v : ℝ | ∃ a b : ℝ, a < b ∧ ∀ t ∈ Set.Ioo a b, f t = v} with hs
  -- For each `v ∈ s` choose a witnessing interval `(lo v, hi v)` on which `f` is `v`.
  let lo : s → ℝ := fun v => Classical.choose v.2
  let hi : s → ℝ := fun v => Classical.choose (Classical.choose_spec v.2)
  have hlt : ∀ v : s, lo v < hi v :=
    fun v => (Classical.choose_spec (Classical.choose_spec v.2)).1
  have hconst : ∀ v : s, ∀ t ∈ Set.Ioo (lo v) (hi v), f t = v.1 :=
    fun v => (Classical.choose_spec (Classical.choose_spec v.2)).2
  -- Pick a rational inside each witnessing interval.
  let g : s → ℚ := fun v => Classical.choose (exists_rat_btwn (hlt v))
  have gspec : ∀ v : s, lo v < (g v : ℝ) ∧ (g v : ℝ) < hi v :=
    fun v => Classical.choose_spec (exists_rat_btwn (hlt v))
  -- The chosen rationals are pairwise distinct: two values sharing one would force
  -- a single point to be labelled by both.
  have hinj : Function.Injective g := by
    intro v w hvw
    have hv : (g v : ℝ) ∈ Set.Ioo (lo v) (hi v) := ⟨(gspec v).1, (gspec v).2⟩
    have hw : (g v : ℝ) ∈ Set.Ioo (lo w) (hi w) := by
      have h := gspec w
      rw [← hvw] at h
      exact ⟨h.1, h.2⟩
    have h1 : f (g v) = v.1 := hconst v (g v) hv
    have h2 : f (g v) = w.1 := hconst w (g v) hw
    exact Subtype.ext (h1.symm.trans h2)
  exact Set.countable_coe_iff.mp (Function.Injective.countable hinj)

end Work.ELRig
