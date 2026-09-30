/-
# The `Δ`-complex of the barycentric subdivision of `M̄`

**Work package W4** of `Submission/Work/NOTES_LEAD_eA.md`.

The `k`-simplices of the barycentric subdivision `K' = mbarSd` of `M̄` are the orbits of pairs
`(c, s)` — a copy bit and a flag of `Q̄` — under the identification relation `flagRel` at their
barycentres (`Submission/Work/MbarHomology/Mbar/Flags.lean`).  Dropping a vertex of a flag
descends to the quotient by `flagRel_face` (`Submission/Work/MbarHomology/Mbar/flagRel_face.lean`);
the construction below therefore takes that well-definedness as an explicit argument, so that the
`Δ`-complex can be defined without it and instantiated as soon as the lemma lands:

```lean
noncomputable def mbarSd : Work.DeltaHomology.DeltaCx :=
  mbarSdOf Work.MbarHomology.Mbar.flagRel_face
```
-/
import Mathlib
import Submission.Work.Subdivision.OrderComplex
import Submission.Work.Subdivision.exists_sd_deltaCx
import Submission.Work.DeltaHomology.Chain
import Submission.Work.MbarHomology.Mbar.Flags
import Submission.Work.FoldInst.Quotient

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option maxRecDepth 100000
set_option autoImplicit false

namespace Work.MbarHomology

open Work.Subdivision

noncomputable section

/-- The orbits of flags have decidable equality (classically; the relation is not decidable). -/
noncomputable instance flagQuotDecEq (k : ℕ) : DecidableEq (Quotient (flagSetoid k)) :=
  Classical.decEq _

/-- The orbits of flags form a finite type (the quotient of the finite type of flags). -/
noncomputable instance flagQuotFintype (k : ℕ) : Fintype (Quotient (flagSetoid k)) :=
  Fintype.ofSurjective (Quotient.mk (flagSetoid k)) (fun q => q.exists_rep)

/-- The number of `k`-simplices of the barycentric subdivision of `M̄`. -/
def mbarCard (k : ℕ) : ℕ := Fintype.card (Quotient (flagSetoid k))

/-- The numbering of the `k`-simplices of `mbarSd` by their orbits. -/
def mbarEquiv (k : ℕ) : Fin (mbarCard k) ≃ Quotient (flagSetoid k) :=
  (Fintype.equivFin (Quotient (flagSetoid k))).symm

/-- The well-definedness of the face maps on the orbits of flags: dropping a vertex of a flag does
not change its orbit.  This is `Work.MbarHomology.Mbar.flagRel_face`. -/
abbrev MbarFaceCompat : Prop :=
  ∀ {k : ℕ} (i : Fin (k + 2)) {x y : FlagQ (k + 1)}, flagRel x y →
    flagRel (x.1, Simplex.face i x.2) (y.1, Simplex.face i y.2)

/-- The face map on the orbits of flags. -/
def mbarFaceQ (hface : MbarFaceCompat) {k : ℕ} (i : Fin (k + 2)) :
    Quotient (flagSetoid (k + 1)) → Quotient (flagSetoid k) :=
  Quot.lift (fun x : FlagQ (k + 1) => Quot.mk (flagSetoid k) (x.1, Simplex.face i x.2))
    (fun a b hab => Quot.sound (hface i hab))

theorem mbarFaceQ_mk (hface : MbarFaceCompat) {k : ℕ} (i : Fin (k + 2)) (x : FlagQ (k + 1)) :
    mbarFaceQ hface i (Quot.mk (flagSetoid (k + 1)) x)
      = Quot.mk (flagSetoid k) (x.1, Simplex.face i x.2) := rfl

/-- The `Δ`-complex of the barycentric subdivision of `M̄`, given the well-definedness of the face
maps. -/
def mbarSdOf (hface : MbarFaceCompat) : Work.DeltaHomology.DeltaCx where
  dim := 4
  card := mbarCard
  face := fun {k} σ i => (mbarEquiv k).symm (mbarFaceQ hface i (mbarEquiv (k + 1) σ))
  face_face := by
    intro k σ i j hij
    refine congrArg (mbarEquiv k).symm ?_
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    refine Quot.inductionOn (mbarEquiv (k + 2) σ) ?_
    intro x
    rw [mbarFaceQ_mk, mbarFaceQ_mk, mbarFaceQ_mk]
    exact congrArg (Quot.mk (flagSetoid k))
      (Prod.ext rfl (Simplex.face_face_succ i j hij x.2))
  card_eq_zero := by
    intro k hk
    have hmax : QbarCW.maxDim = 4 := by decide
    haveI : IsEmpty (Simplex QbarCW.Cell k) := QbarCW.isEmpty_simplex_of_lt (by rw [hmax]; exact hk)
    haveI : IsEmpty (FlagQ k) := ⟨fun x => isEmptyElim x.2⟩
    haveI : IsEmpty (Quotient (flagSetoid k)) := ⟨fun q => q.inductionOn fun x => isEmptyElim x⟩
    rw [mbarCard]
    exact Fintype.card_eq_zero_iff.mpr inferInstance

end

end Work.MbarHomology
