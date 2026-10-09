import Mathlib
import Submission.NK.LocalStructure.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.LocalStructure.Tower

/-- **The abelianisation has no more index-`p` subgroups than `G`.**

Passing to the abelianisation `Abelianization G = G ⧸ [G, G]` is a surjection
`G ↠ Gᵃᵇ`, so every index-`p` subgroup `H ≤ Gᵃᵇ` pulls back to an index-`p`
subgroup `H.comap of ≤ G` (`Subgroup.index_comap_of_surjective`), and the
pullback is injective because `of` is surjective.  Hence the pullback is an
injection from index-`p` subgroups of `Gᵃᵇ` into index-`p` subgroups of `G`.

The hypothesis `hpos` rules out the degenerate case in which `G` has infinitely
many index-`p` subgroups (typically non-normal ones, e.g. `G = F₂`): `Nat.card`
is `0` for infinite types, so without it the inequality would be false there.
With `0 < numIndexSubgroups p G` the count of index-`p` subgroups of `G` is an
honest finite positive number and the injection yields the inequality. -/
theorem numIndexSubgroups_abelianization_le (p : ℕ) {G : Type*} [Group G]
    (hpos : 0 < NK.LocalAnabelian.numIndexSubgroups p G) :
    NK.LocalAnabelian.numIndexSubgroups p (Abelianization G) ≤
      NK.LocalAnabelian.numIndexSubgroups p G := by
  have hsurj : Function.Surjective (Abelianization.of (G := G)) :=
    fun x => Quotient.inductionOn x fun g => ⟨g, rfl⟩
  unfold NK.LocalAnabelian.numIndexSubgroups
  refine Finite.card_le_of_injective'
    (f := fun H : {H : Subgroup (Abelianization G) // H.index = p} =>
      ⟨H.1.comap (Abelianization.of (G := G)),
        (Subgroup.index_comap_of_surjective H.1 hsurj).trans H.2⟩) ?_ ?_
  · rintro ⟨H1, h1⟩ ⟨H2, h2⟩ heq
    have hc : H1.comap (Abelianization.of (G := G)) =
        H2.comap (Abelianization.of (G := G)) := by
      simpa using congrArg Subtype.val heq
    have hH : H1 = H2 := by
      rw [← Subgroup.map_comap_eq_self_of_surjective hsurj H1, hc,
        Subgroup.map_comap_eq_self_of_surjective hsurj H2]
    exact Subtype.ext hH
  · intro h0
    exact absurd h0 (Nat.ne_of_gt hpos)

/-- **The number of index-`p` subgroups of `G` dominates the abelianised
Frattini rank.**

`HasAbelianFrattiniRank p r G` says that the abelianisation `Gᵃᵇ` has exactly
`(p ^ r - 1) / (p - 1)` index-`p` subgroups — i.e. its maximal elementary
abelian `p`-quotient is `(ℤ/p)^r`; equivalently `(ℤ/p)^r` is the maximal
abelian quotient of exponent `p` of `G`.  Since every index-`p` subgroup of
`Gᵃᵇ` pulls back to an index-`p` subgroup of `G`, this is a lower bound for
`numIndexSubgroups p G`. -/
theorem le_numIndexSubgroups_of_hasAbelianFrattiniRank {G : Type*} [Group G]
    {p r : ℕ} (hp : p.Prime) (h : NK.LocalAnabelian.HasAbelianFrattiniRank p r G)
    (hpos : 0 < NK.LocalAnabelian.numIndexSubgroups p G) :
    (p ^ r - 1) / (p - 1) ≤ NK.LocalAnabelian.numIndexSubgroups p G := by
  have hle := numIndexSubgroups_abelianization_le p hpos
  have hh : NK.LocalAnabelian.numIndexSubgroups p (Abelianization G) =
      (p ^ r - 1) / (p - 1) := h
  rw [← hh]
  exact hle

end NK.LocalStructure.Tower
