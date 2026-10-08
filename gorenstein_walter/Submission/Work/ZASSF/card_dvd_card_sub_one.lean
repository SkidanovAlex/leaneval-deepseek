import Mathlib
import Submission.Work.ZASS.dvd_card_sub_one_of_isConjInvariant

namespace Work.ZASSF

/-- If a nontrivial subgroup `W ≤ U` is invariant under conjugation by `H`, and every
nonidentity element of `H` fixes only the identity of `U`, then `|H|` divides `|W| - 1`.

Indeed `H` acts on `W` by conjugation (`h • w = h * w * h⁻¹`), the identity of `W` is fixed by
all of `H`, and by `hfix` no nonidentity element of `H` fixes any point of `W` other than
`1`.  Hence the action of `H` on `W \ {1}` is fixed-point-free, so `W \ {1}` is a disjoint
union of orbits of size `|H|` (`Work.ZASS.dvd_card_sub_one_of_fixedPointFree`), and therefore
`|H| ∣ |W| - 1`. -/
theorem card_dvd_card_sub_one {G : Type*} [Group G] [Finite G] {U H W : Subgroup G} (hWU : W ≤ U) (hfix : ∀ h ∈ H, h ≠ 1 → ∀ u ∈ U, h * u * h⁻¹ = u → u = 1) (hWne : W ≠ ⊥) (hWinv : ∀ h ∈ H, ∀ w ∈ W, h * w * h⁻¹ ∈ W) : Nat.card H ∣ Nat.card W - 1 := by
  classical
  -- Conjugation by `H` preserves `W` (`hWinv`), so `H` acts on `W` by conjugation.
  letI : MulAction H W :=
    { smul := fun h w => ⟨Work.ZASS.conjBy (h : G) (w : G), hWinv h h.2 w w.2⟩
      one_smul := fun w => Subtype.ext (by
        show Work.ZASS.conjBy ((1 : ↥H) : G) (w : G) = (w : G)
        simp [Work.ZASS.conjBy])
      mul_smul := fun h h' w => Subtype.ext (by
        show Work.ZASS.conjBy ((h * h' : ↥H) : G) (w : G)
          = Work.ZASS.conjBy (h : G) (Work.ZASS.conjBy (h' : G) (w : G))
        simp only [Work.ZASS.conjBy, Subgroup.coe_mul]
        group) }
  -- The identity of `W` is fixed by every element of `H`, and no nonidentity element of `H`
  -- fixes any other point of `W ⊆ U`.
  refine Work.ZASS.dvd_card_sub_one_of_fixedPointFree (G := H) (α := W) 1 ?_ ?_
  · intro g
    exact Subtype.ext (by
      show Work.ZASS.conjBy (g : G) ((1 : ↥W) : G) = ((1 : ↥W) : G)
      simp [Work.ZASS.conjBy])
  · intro g hg a ha
    have ha' : Work.ZASS.conjBy (g : G) (a : G) = (a : G) := Subtype.ext_iff.mp ha
    have hg' : (g : G) ≠ 1 := fun h => hg (Subtype.ext h)
    exact Subtype.ext (hfix (g : G) g.2 hg' (a : G) (hWU a.2) ha')

end Work.ZASSF
