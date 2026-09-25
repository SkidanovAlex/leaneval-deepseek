import Mathlib
import Submission.Work.ClassFieldTower.WallShrunk

namespace Work.ClassFieldTower

open scoped Classical

/-- **A finite `2`-group is residually a finite `2`-group.**  For `g ≠ 1` the trivial subgroup
`⊥` is a normal subgroup whose quotient `G ⧸ ⊥ ≃* G` is finite and a `2`-group, and in which
`g` survives. -/
theorem residuallyFiniteTwoGroup_of_finite_isPGroup_two {G : Type*} [Group G]
    (hfin : Finite G) (hp : IsPGroup 2 G) : ResiduallyFiniteTwoGroup G := by
  intro g hg
  refine ⟨⊥, inferInstance, ?_, hp.to_quotient ⊥, ?_⟩
  · exact Finite.of_surjective (QuotientGroup.mk' ⊥) (QuotientGroup.mk'_surjective ⊥)
  · intro h
    simp only [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_bot] at h
    exact hg h

/-- **`F2five = Fin 5 → Multiplicative (ZMod 2)` is residually a finite `2`-group**: it is itself a
finite `2`-group, so for `g ≠ 1` the subgroup `⊥` separates `g` from `1`.

(Used to transport `ResiduallyFiniteTwoGroup` to the explicit finite model `GF` of
`Submission/Work/ClassFieldTower/FiniteModelDefs.lean`.) -/
theorem residuallyFiniteTwoGroup_f2five : ResiduallyFiniteTwoGroup F2five :=
  residuallyFiniteTwoGroup_of_finite_isPGroup_two (Finite.of_fintype _) (by
    apply IsPGroup.of_card (n := 5)
    rw [F2five, Nat.card_fun]
    simp)

end Work.ClassFieldTower
