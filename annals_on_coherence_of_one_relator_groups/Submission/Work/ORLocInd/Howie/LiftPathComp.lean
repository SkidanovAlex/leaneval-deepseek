/-
# The lift to the cyclic cover is functorial

This file collects the tools for the proof of `Work.ORLocInd.Howie.liftPath_pmul`, namely the
compatibility of the lift `liftPath L` (`Submission.Work.ORLocInd.Howie.CoverGraph`) with the
groupoid multiplication `pmul` (`Submission.Work.ORLocInd.Howie.Basic`).

The main ingredient is `liftPath_comp`: the lift of a concatenation of base paths is the
concatenation of the lifts (up to the change of endpoint described by `coverVertex_comp_eq`).

All the statements here are about paths in the *cover* `Γ̃` whose vertices are
`CoverVertex L = V × ℤ`, so they involve many casts of the endpoints; the bookkeeping is done
with the cast lemmas in `namespace Quiver` below (casts of arrows and of paths along equalities
of their endpoints).
-/
import Mathlib
import Submission.Work.ORLocInd.Howie.CoverGraph
import Submission.Work.ORLocInd.Howie.liftPath_isReduced
import Submission.Work.ORLocInd.Howie.liftPath_arrowList

set_option autoImplicit false

open Quiver

universe u

namespace Quiver

/-! ## Casts of paths and arrows

`Mathlib` provides `Quiver.Hom.cast` and `Quiver.Path.cast` (`Mathlib.Combinatorics.Quiver.Cast`)
together with the basic compatibilities.  Here we add the compatibilities with `Path.comp`,
`Path.cons`, `Hom.toPath` and `Quiver.reverse` that the cyclic-cover bookkeeping needs. -/

variable {U : Type*} [Quiver U]

/-- Casting the endpoints of a composition, with the outer cast on the left. -/
theorem Path.cast_comp' {u v w u' v' w' : U} (p : Path u v) (q : Path v w)
    (hu : u = u') (hv : v = v') (hw : w = w') :
    (p.cast hu hv).comp (q.cast hv hw) = (p.comp q).cast hu hw := by
  subst_vars
  simp

/-- Casting the endpoint of the *second* factor of a composition. -/
theorem Path.comp_cast_right' {u v w w' : U} (p : Path u v) (q : Path v w)
    (hw : w = w') : p.comp (q.cast rfl hw) = (p.comp q).cast rfl hw := by
  rw [← Path.cast_comp' p q rfl rfl hw]
  simp

/-- Casting the endpoint of the *first* factor of a composition. -/
theorem Path.cast_comp_left' {u v v' w : U} (p : Path u v) (q : Path v' w)
    (hv : v = v') : (p.cast rfl hv).comp q = (p.comp (q.cast hv.symm rfl)).cast rfl rfl := by
  rw [← Path.cast_comp' p (q.cast hv.symm rfl) rfl hv rfl]
  simp

/-- A cast in the middle of a composed path: `(p.cast rfl hv).cons e = p.cons (e.cast hv.symm rfl)`. -/
theorem Path.cons_cast' {u v v' w : U} (p : Path u v) (hv : v = v')
    (e : v' ⟶ w) : (p.cast rfl hv).cons e = p.cons (e.cast hv.symm rfl) := by
  subst_vars
  simp

/-- The casts of a path only depend on the two endpoints. -/
theorem Path.cast_proof_irrel {u v u' v' : U} (p : Path u v)
    (hu hu' : u = u') (hv hv' : v = v') : p.cast hu hv = p.cast hu' hv' := by
  rw [Subsingleton.elim hu hu', Subsingleton.elim hv hv']

/-- The casts of an arrow only depend on the two endpoints. -/
theorem Hom.cast_proof_irrel {u v u' v' : U} (e : u ⟶ v)
    (hu hu' : u = u') (hv hv' : v = v') : e.cast hu hv = e.cast hu' hv' := by
  rw [Subsingleton.elim hu hu', Subsingleton.elim hv hv']

/-- Two casts of arrows into a common pair of endpoints agree as soon as the arrows are `HEq`. -/
theorem Hom.cast_eq_cast_iff_heq {u v u' v' u'' v'' : U} (e : u ⟶ v) (e' : u' ⟶ v')
    (hu : u = u'') (hv : v = v'') (hu' : u' = u'') (hv' : v' = v'') :
    e.cast hu hv = e'.cast hu' hv' ↔ HEq e e' := by
  rw [Hom.cast_eq_iff_heq]
  constructor
  · intro h; exact h.trans (Hom.cast_heq hu' hv' e')
  · intro h; exact h.trans (Hom.cast_heq hu' hv' e').symm

/-- Casting commutes with `Hom.toPath`. -/
theorem Path.cast_toPath' {u v u' v' : U} (e : u ⟶ v) (hu : u = u') (hv : v = v') :
    (e.toPath).cast hu hv = (e.cast hu hv).toPath := by
  subst_vars
  simp

/-- Casting commutes with `Quiver.reverse`. -/
theorem Hom.cast_reverse' [Quiver.HasReverse U] {u v u' v' : U} (e : u ⟶ v)
    (hu : u = u') (hv : v = v') :
    Quiver.reverse (e.cast hu hv) = (Quiver.reverse e).cast hv hu := by
  subst_vars
  simp

/-- Backtrack deletion is compatible with casting the endpoints. -/
theorem Path.DeleteBacktrack.cast' [Quiver.HasInvolutiveReverse U] {A B A' B' : U}
    (hu : A = A') (hv : B = B') {p q : Path A B} (h : DeleteBacktrack p q) :
    DeleteBacktrack (p.cast hu hv) (q.cast hu hv) := by
  obtain ⟨x, y, p₁, e, p₂, rfl, rfl⟩ := Work.ORBassSerre.Path.Reduction.deleteBacktrack_cases h
  simp only [← Path.cast_comp', Path.cast_rfl_rfl]
  exact Path.DeleteBacktrack.intro _ _ _

/-- Reduction is compatible with casting the endpoints. -/
theorem Path.ReducesTo.cast' [Quiver.HasInvolutiveReverse U] {A B A' B' : U}
    (hu : A = A') (hv : B = B') {p q : Path A B} (h : p.ReducesTo q) :
    (p.cast hu hv).ReducesTo (q.cast hu hv) := by
  induction h with
  | refl => exact ReducesTo.refl _
  | tail _ hstep ih => exact ih.tail (Path.DeleteBacktrack.cast' hu hv hstep)

end Quiver

namespace Work.ORLocInd.Howie

variable {V : Type u} [Quiver V] [Quiver.HasInvolutiveReverse V]

/-! ## Endpoint bookkeeping in the cover -/

/-- The `CoverVertex` equality induced by an equality of the levels. -/
theorem coverVertex_level_eq (L : Labelling V) {b : V} {m m' : ℤ} (h : m = m') :
    (⟨b, m⟩ : CoverVertex L) = ⟨b, m'⟩ := by
  rw [h]

/-- The endpoint equality of `liftPath_comp`: `(n + pathSum p) + pathSum q = n + pathSum (p ++ q)`. -/
theorem coverVertex_comp_eq (L : Labelling V) {a b c : V} (p : Quiver.Path a b)
    (q : Quiver.Path b c) (n : ℤ) :
    (⟨c, (n + pathSum L.toFun p) + pathSum L.toFun q⟩ : CoverVertex L)
      = ⟨c, n + pathSum L.toFun (p.comp q)⟩ := by
  congr 1
  rw [pathSum_comp, add_assoc]

/-- The endpoint equality of the `cons` step for a concatenation `p ++ (q ++ e)`. -/
theorem coverVertex_comp_cons_eq (L : Labelling V) {a b c d : V} (p : Quiver.Path a b)
    (q : Quiver.Path b c) (e : c ⟶ d) (n : ℤ) :
    (⟨d, (n + pathSum L.toFun (p.comp q)) + L.toFun (Quiver.Total.mk c d e)⟩ : CoverVertex L)
      = ⟨d, n + pathSum L.toFun (p.comp (q.cons e))⟩ := by
  congr 1
  simp only [pathSum_comp, pathSum_cons]
  ring

/-! ## The equation lemma of `liftPath` at a `cons` of a concatenation -/

/-- The `cons` equation of `liftPath`, in the shape `p.comp (q.cons e)` (which is
definitionally `(p.comp q).cons e`, but whose endpoint is written so that the cast of the
equation lemma can be recorded without unfolding `Path.comp`). -/
theorem liftPath_comp_cons_cast (L : Labelling V) {a b c d : V} (p : Quiver.Path a b)
    (q : Quiver.Path b c) (e : c ⟶ d) (n : ℤ) :
    liftPath L (p.comp (q.cons e)) n =
      Quiver.Path.cast rfl (coverVertex_comp_cons_eq L p q e n)
        ((liftPath L (p.comp q) n).cons
          (coverLiftArrow L e (n + pathSum L.toFun (p.comp q)))) :=
  liftPath_cons_cast' L (p.comp q) e n

/-! ## The lifted arrows -/

/-- Casting the level of a lifted arrow. -/
theorem coverLiftArrow_cast_eq (L : Labelling V) {b c : V} (e : b ⟶ c) {m m' : ℤ}
    (hu : (⟨b, m⟩ : CoverVertex L) = ⟨b, m'⟩)
    (hv : (⟨c, m + L.toFun (Quiver.Total.mk b c e)⟩ : CoverVertex L)
      = ⟨c, m' + L.toFun (Quiver.Total.mk b c e)⟩) :
    (coverLiftArrow L e m).cast hu hv = coverLiftArrow L e m' := by
  have hm : m = m' := congrArg CoverVertex.level hu
  subst hm
  rw [Subsingleton.elim hu rfl, Subsingleton.elim hv rfl, Quiver.Hom.cast_rfl_rfl]

/-- Lifted arrows at the same level, up to the change of level. -/
theorem heq_coverLiftArrow (L : Labelling V) {b c : V} (e : b ⟶ c) {m m' : ℤ}
    (hm : (⟨b, m⟩ : CoverVertex L) = ⟨b, m'⟩) :
    HEq (coverLiftArrow L e m)
      (coverLiftArrow L e m' : (⟨b, m'⟩ : CoverVertex L) ⟶
        ⟨c, m' + L.toFun (Quiver.Total.mk b c e)⟩) := by
  have hm2 : m = m' := congrArg CoverVertex.level hm
  refine (Quiver.Hom.cast_eq_iff_heq hm (coverVertex_level_eq L (by rw [hm2])) _ _).mp ?_
  exact coverLiftArrow_cast_eq L e hm (coverVertex_level_eq L (by rw [hm2]))

/-! ## Reduction to normal form -/

/-- Reducing a path to its normal form commutes with casting the endpoints. -/
theorem red_cast' {a b a' b' : V} (hu : a = a') (hv : b = b') (p : Quiver.Path a b) :
    red (p.cast hu hv) = (red p).cast hu hv := by
  refine red_eq_of_reducesTo_isReduced (Quiver.Path.ReducesTo.cast' hu hv (reducesTo_red p)) ?_
  exact (isReduced_cast hu hv (red p)).mpr (isReduced_red p)

/-! ## Functoriality of the lift under concatenation -/

/-- **The lift of a concatenation is the concatenation of the lifts.** -/
theorem liftPath_comp (L : Labelling V) {a b c : V} (p : Quiver.Path a b) (q : Quiver.Path b c)
    (n : ℤ) :
    liftPath L (p.comp q) n =
      ((liftPath L p n).comp (liftPath L q (n + pathSum L.toFun p))).cast rfl
        (coverVertex_comp_eq L p q n) := by
  induction q with
  | nil =>
    rw [liftPath_nil_cast']
    rw [← Quiver.Path.comp_cast_right']
    rw [Quiver.Path.cast_cast]
    have he : (coverVertex_nil_eq L b (n + pathSum L.toFun p)).trans
        (coverVertex_comp_eq L p (Quiver.Path.nil : Quiver.Path b b) n) = rfl :=
      Subsingleton.elim _ _
    rw [he]
    simp
  | cons q e ih =>
    rw [liftPath_comp_cons_cast L p q e n]
    have hL : Quiver.Path.cast rfl (coverVertex_comp_cons_eq L p q e n)
        ((liftPath L (p.comp q) n).cons
          (coverLiftArrow L e (n + pathSum L.toFun (p.comp q))))
        = ((liftPath L p n).comp (liftPath L q (n + pathSum L.toFun p))).cons
            (((coverLiftArrow L e (n + pathSum L.toFun (p.comp q))).cast rfl
              (coverVertex_comp_cons_eq L p q e n)).cast
              (coverVertex_comp_eq L p q n).symm rfl) := by
      rw [Quiver.Path.cast_cons]
      rw [Quiver.Path.cast_rfl_rfl]
      rw [ih]
      rw [Quiver.Path.cons_cast']
    have hR : ((liftPath L p n).comp (liftPath L (q.cons e) (n + pathSum L.toFun p))).cast rfl
        (coverVertex_comp_eq L p (q.cons e) n)
        = (liftPath L p n).comp ((liftPath L q (n + pathSum L.toFun p)).cons
            ((coverLiftArrow L e (n + pathSum L.toFun p + pathSum L.toFun q)).cast rfl
              ((coverVertex_cons_eq L q e (n + pathSum L.toFun p)).trans
                (coverVertex_comp_eq L p (q.cons e) n)))) := by
      rw [liftPath_cons_cast']
      rw [← Quiver.Path.comp_cast_right']
      rw [Quiver.Path.cast_cast]
      rw [Quiver.Path.cast_cons]
      rw [Quiver.Path.cast_rfl_rfl]
    rw [hL, hR]
    have hX : ((coverLiftArrow L e (n + pathSum L.toFun (p.comp q))).cast rfl
          (coverVertex_comp_cons_eq L p q e n)).cast (coverVertex_comp_eq L p q n).symm rfl
        = (coverLiftArrow L e (n + pathSum L.toFun p + pathSum L.toFun q)).cast rfl
            ((coverVertex_cons_eq L q e (n + pathSum L.toFun p)).trans
              (coverVertex_comp_eq L p (q.cons e) n)) := by
      rw [Quiver.Hom.cast_cast]
      exact (Quiver.Hom.cast_eq_cast_iff_heq
        (e := coverLiftArrow L e (n + pathSum L.toFun (p.comp q)))
        (e' := coverLiftArrow L e (n + pathSum L.toFun p + pathSum L.toFun q))
        _ _ _ _).mpr (heq_coverLiftArrow L e (coverVertex_comp_eq L p q n).symm)
    show ((liftPath L p n).comp (liftPath L q (n + pathSum L.toFun p))).cons
        (((coverLiftArrow L e (n + pathSum L.toFun (p.comp q))).cast rfl
              (coverVertex_comp_cons_eq L p q e n)).cast
              (coverVertex_comp_eq L p q n).symm rfl)
      = ((liftPath L p n).comp (liftPath L q (n + pathSum L.toFun p))).cons
            ((coverLiftArrow L e (n + pathSum L.toFun p + pathSum L.toFun q)).cast rfl
              ((coverVertex_cons_eq L q e (n + pathSum L.toFun p)).trans
                (coverVertex_comp_eq L p (q.cons e) n)))
    exact congrArg (fun x => Quiver.Path.cons
      ((liftPath L p n).comp (liftPath L q (n + pathSum L.toFun p))) x) hX

end Work.ORLocInd.Howie
