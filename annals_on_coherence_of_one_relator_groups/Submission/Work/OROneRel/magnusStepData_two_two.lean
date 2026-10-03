import Mathlib
import Submission.Work.OROneRel.magnusStepNielsenRoute
import Submission.Work.OROneRel.magnusStepData_of_conjWord
import Submission.Work.OROneRel.conjWordData_two_two

/-!
# A new case of the Magnus step: `u = x ^ 2 * y ^ 2`, every `l ≥ 1`

`u = x ^ 2 * y ^ 2` is *not* reached by any of the previously known families of the Magnus step:

* the divisibility (weighted Magnus) family needs `∃ t, c` with `c t = 1` and `cohom c u = 1`, i.e.
  `2 c x + 2 c y = 1`, which is unsolvable in `ℤ`;
* the transvection/Nielsen family `x ^ p y ^ q` with `p m + q = ±1` does not contain `(2,2)`
  (`2 m + 2 = ±1` is unsolvable);
* the free-kernel (`⊤`) route requires `l = 1`.

It is, however, reachable by the **Tietze ("conjugation word") route** of
`Submission/Work/OROneRel/magnusStepData_of_conjWord.lean`: in `F(x,y)` one has the word identity

  `x ^ 2 * y ^ 2 = x * (x * y) * x⁻¹ * (x * y)`,

i.e. `u = x₀ · s · x₀⁻¹ · s` with `x₀ = x` and `s = x * y`, and `{x, s}` generates `F(x,y)`
(`y = x⁻¹ s`).  The instance data are provided by
`Work.OROneRel.conjWordData_two_two` (`Submission/Work/OROneRel/conjWordData_two_two.lean`).

The resulting HNN extension has vertex `⟨s, c | c ^ l⟩ = ℤ ∗ ℤ/l`, associated subgroups
`⟨s⟩` and its image under `of 1 ↦ of 0 * (of 1)⁻¹`, and the class of `u` is the class `c` of the root
generator; the root has norm `1 < 4`.
-/

namespace Work.OROneRel

universe u

/-- **The Magnus step for `u = x ^ 2 * y ^ 2` at every `l ≥ 1`.** -/
theorem magnusStepData_two_two (l : ℕ) (hl : 1 ≤ l) :
    MagnusStepData (FreeGroup.of (0 : Fin 2) ^ 2 * FreeGroup.of (1 : Fin 2) ^ 2) l := by
  obtain ⟨x₀, s, sect, hgen, hsect, hsubst, hu, hn⟩ := conjWordData_two_two
  exact magnusStepData_of_conjWord
    (FreeGroup.of (0 : Fin 2) ^ 2 * FreeGroup.of (1 : Fin 2) ^ 2) l hl x₀ s sect
    hgen hsect hsubst hu hn

end Work.OROneRel
