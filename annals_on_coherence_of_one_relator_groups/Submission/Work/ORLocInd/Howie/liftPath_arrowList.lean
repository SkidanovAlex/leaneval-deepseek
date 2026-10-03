/-
# The arrow list of the lift of a path to the cyclic cover

The lift `liftPath L p n` of a path `p : a → b` of the base graph `Γ` to the cyclic cover `Γ̃`
starts at `(a, n)`, ends at `(b, n + pathSum θ p)`, and its arrows project one by one onto the
arrows of `p`.  This file records the latter statement:

`(liftPath L p n).arrowList.map (fun f => f.hom.1) = p.arrowList`.

The proof is by recursion on `p`; the only subtlety is that the defining recursion of `liftPath`
is indexed by the level `n + pathSum θ p`, so its *equation lemmas* (`liftPath.eq_1`,
`liftPath.eq_2`) express `liftPath` at `cons` as a *cast* of `(liftPath L p n).cons ·` along the
equality of the level expressions `n + pathSum θ (p.cons e)` and `(n + pathSum θ p) + θ e`.  We
convert these cast equations into `Quiver.Path.cast` form (`liftPath_nil_cast`,
`liftPath_cons_cast`) by an `HEq` argument, and use that `arrowList` after applying the projection
`coverProjTotal` is insensitive to `Quiver.Path.cast` along endpoint equalities
(`arrowList_map_coverProjTotal_cast`).
-/
import Mathlib
import Submission.Work.ORLocInd.Howie.CoverGraph

set_option autoImplicit false
set_option linter.unusedVariables false

universe u

namespace Work.ORLocInd.Howie

open Quiver

variable {V : Type u} [Quiver V] [Quiver.HasInvolutiveReverse V]

/-- The projection of the total space of the cyclic cover onto the total space of the base graph:
an arrow of the cover is an arrow of the base graph together with a level, and we forget the
levels.  Note that the *full* arrow list of the cover (before applying this projection) does record
the vertices of the cover; after applying `coverProjTotal` only the data of the base graph
remains. -/
def coverProjTotal (L : Labelling V) : Quiver.Total (CoverVertex L) → Quiver.Total V :=
  fun f => f.hom.1

@[simp] theorem coverProjTotal_mk (L : Labelling V) {p q : CoverVertex L} (f : CoverHom L p q) :
    coverProjTotal L (Quiver.Total.mk p q f) = f.1 := rfl

/-- `Eq.mpr` is a cast: this is the rephrasing used to turn the equation lemmas of `liftPath`
(which are stated with `Eq.mpr`) into `Quiver.Path.cast` form. -/
theorem eq_mpr_eq_cast_symm {α β : Sort u} (h : α = β) (a : β) : Eq.mpr h a = cast h.symm a := by
  cases h
  rfl

/-- Casting a path along equalities of its endpoints does not change the projection of its arrow
list onto the base graph. -/
theorem arrowList_map_coverProjTotal_cast (L : Labelling V) {u v u' v' : CoverVertex L}
    (hu : u = u') (hv : v = v') (q : Quiver.Path u v) :
    (((q.cast hu hv).arrowList).map (coverProjTotal L)) = q.arrowList.map (coverProjTotal L) := by
  cases hu
  cases hv
  rfl

/-- The equation lemma of `liftPath` at `nil`, in `Quiver.Path.cast` form. -/
theorem liftPath_nil_cast (L : Labelling V) (a : V) (n : ℤ) :
    liftPath L (Quiver.Path.nil : Quiver.Path a a) n
      = (Quiver.Path.nil : Quiver.Path (⟨a, n⟩ : CoverVertex L) (⟨a, n⟩ : CoverVertex L)).cast rfl
          (show (⟨a, n⟩ : CoverVertex L)
              = ⟨a, n + pathSum L.toFun (Quiver.Path.nil : Quiver.Path a a)⟩ from by
            rw [pathSum_nil, add_zero]) := by
  refine (Quiver.Path.eq_cast_iff_heq (rfl : (⟨a, n⟩ : CoverVertex L) = ⟨a, n⟩) _ _ _).2 ?_
  rw [liftPath.eq_1]
  rw [eq_mpr_eq_cast_symm, eq_mpr_eq_cast_symm]
  exact (cast_heq _ _).trans (cast_heq _ _)

/-- The equation lemma of `liftPath` at `cons`, in `Quiver.Path.cast` form: the lift of `p.cons e`
is the lift of `p` followed by the arrow `(e, n + pathSum θ p)`, re-indexed so that its endpoint
is `n + pathSum θ (p.cons e)`. -/
theorem liftPath_cons_cast (L : Labelling V) {a b c : V} (p : Quiver.Path a b) (e : b ⟶ c)
    (n : ℤ) :
    liftPath L (p.cons e) n =
      ((liftPath L p n).cons ⟨Quiver.Total.mk b c e, rfl, rfl, rfl⟩).cast rfl
        (show (⟨c, (n + pathSum L.toFun p) + L.toFun (Quiver.Total.mk b c e)⟩ : CoverVertex L)
            = ⟨c, n + pathSum L.toFun (p.cons e)⟩ from by rw [pathSum_cons, add_assoc]) := by
  refine (Quiver.Path.eq_cast_iff_heq (rfl : (⟨a, n⟩ : CoverVertex L) = ⟨a, n⟩) _ _ _).2 ?_
  rw [liftPath.eq_2]
  rw [eq_mpr_eq_cast_symm, eq_mpr_eq_cast_symm]
  exact (cast_heq _ _).trans (cast_heq _ _)

theorem liftPath_arrowList {V : Type u} [Quiver V] [Quiver.HasInvolutiveReverse V]
    (L : Labelling V) {a b : V} (p : Quiver.Path a b) (n : ℤ) :
    (liftPath L p n).arrowList.map (fun f => (f.hom.1 : Quiver.Total V)) = p.arrowList := by
  change (liftPath L p n).arrowList.map (coverProjTotal L) = p.arrowList
  induction p with
  | nil =>
    rw [liftPath_nil_cast L _ n]
    rw [arrowList_map_coverProjTotal_cast]
    rfl
  | cons p e ih =>
    rw [liftPath_cons_cast L p e n]
    rw [arrowList_map_coverProjTotal_cast]
    erw [Quiver.Path.arrowList_cons]
    rw [List.map_append, ih, Quiver.Path.arrowList_cons]
    rfl

end Work.ORLocInd.Howie
