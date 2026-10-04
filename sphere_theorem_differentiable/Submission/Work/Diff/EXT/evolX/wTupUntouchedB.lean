import Mathlib
import Submission.Work.Diff.EXT.evolX.mulOpJetsDefs
import Submission.Work.Diff.EXT.evolX.wTupUntouchedA

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The shuffle calculus: a `B`-position does not touch the `A`-sub-tuple

Updating the level-`(m+1)` tuple `F` at a `B`-position `wPosB K₁ K₂ m w ρ` of the word
`w : Word (m+1)` leaves the `A`-sub-tuple `wTupA K₁ K₂ (m+1) w` unchanged.

The content is the disjointness of the two position maps: on their respective index ranges
`[0, K₁ + wCntT w)` and `[0, K₂ + wCntF w)` the `A`-positions and the `B`-positions never coincide
(`Work.Diff.EXT.evolX.wPosA_ne_wPosB_of_lt`, proved in `wTupUntouchedA`).  Indeed the level-`(n+1)`
tuple positions are split between the `A`-tuple (the `wCntT w` derivative directions routed to the
first factor, followed by its `K₁` tensor slots) and the `B`-tuple (the `wCntF w` directions routed
to the second factor, followed by its `K₂` tensor slots), and the two position maps are the
corresponding injections.
-/

namespace Work.Diff.EXT.evolX

theorem wTupUntouchedB
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    (K₁ K₂ m : ℕ) (w : Work.Diff.EXT.evolX.Word (m + 1))
    (F : Fin (K₁ + K₂ + (m + 1)) → Work.Diff.EXT.TField (I := I) (M := M))
    (v : Work.Diff.EXT.TField (I := I) (M := M))
    (ρ : Fin (K₂ + Work.Diff.EXT.evolX.wCntF w)) :
    Work.Diff.EXT.evolX.wTupA (I := I) (M := M) K₁ K₂ (m + 1) w
        (Function.update F (Work.Diff.EXT.evolX.wPosB K₁ K₂ m w ρ.val) v)
      = Work.Diff.EXT.evolX.wTupA (I := I) (M := M) K₁ K₂ (m + 1) w F := by
  funext i
  -- both sub-tuples are "the tuple `F`, read at the corresponding positions"
  change Function.update F (wPosB K₁ K₂ m w ρ.val) v (wPosA K₁ K₂ m w i.val)
      = F (wPosA K₁ K₂ m w i.val)
  -- the update happens away from the position at which we evaluate
  rw [Function.update_of_ne
    (wPosA_ne_wPosB_of_lt K₁ K₂ m w i.val ρ.val i.isLt ρ.isLt) v F]

end Work.Diff.EXT.evolX
