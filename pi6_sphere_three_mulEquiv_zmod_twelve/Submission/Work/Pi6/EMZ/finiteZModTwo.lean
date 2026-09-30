import Mathlib
import Submission.Work.Pi6.EMZ.Defs
import Submission.Work.Pi6.EMZ.groupZModTwo
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

namespace Work.Pi6.EMZ

/-- **A finite abelian group `G` with `|G ⧸ 2·G| ≤ 2`, divisible by every odd prime, without odd
torsion, and containing an element `a` of order `2` which is not a double, is `ℤ/2`.**

This is the finite companion of `Work.Pi6.EMZ.groupZModTwo` (which is stated for a finitely
generated `ℤ`-module).  The only bridges needed are

* `Finite G` gives `Module.Finite ℤ G` (`Module.Finite.of_finite`), and
* the "functional" hypotheses `hdiv`, `htor` are turned into the `Subsingleton` form of the
  quotient `G ⧸ p·G` and the torsion subgroup `G[p]`
  (`subsingleton_quot_pH_iff`, `subsingleton_torsP_iff`).

The conclusion of `groupZModTwo` is a `ℤ`-linear equivalence, whose underlying additive
equivalence is a `G ≃+ ZMod 2`. -/
theorem finiteZModTwo (G : Type) [AddCommGroup G] [Finite G]
    (h2 : Nat.card (G ⧸ Work.Pi6.EMZ.pH 2 G) ≤ 2)
    (hdiv : ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ x : G, ∃ y : G, p • y = x)
    (htor : ∀ p : ℕ, p.Prime → p ≠ 2 → ∀ x : G, p • x = 0 → x = 0)
    (ha : ∃ a : G, 2 • a = 0 ∧ ∀ b : G, 2 • b ≠ a) :
    Nonempty (G ≃+ ZMod 2) := by
  obtain ⟨e⟩ := groupZModTwo G h2
    (fun p hp hp2 => subsingleton_quot_pH_iff.mpr (hdiv p hp hp2))
    (fun p hp hp2 => subsingleton_torsP_iff.mpr (htor p hp hp2)) ha
  exact ⟨e.toAddEquiv⟩

end Work.Pi6.EMZ
