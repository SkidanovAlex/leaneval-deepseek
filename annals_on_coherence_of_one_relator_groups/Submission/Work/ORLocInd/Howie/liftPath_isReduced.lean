/-
# The lift of a reduced path to the cyclic cover is reduced

The cyclic cover `Γ̃` of a `ℤ`-labelled graph `Γ` (`Submission.Work.ORLocInd.Howie.CoverGraph`)
has vertex set `V × ℤ`, and an arrow `(e, n) : (a, n) → (b, n + θ e)` for every arrow
`e : a → b` of `Γ` and every level `n`.  The lift `liftPath θ p n` of a path `p` starting at
`(a, n)` is the unique path of `Γ̃` projecting to `p`.

Because reversal in `Γ̃` is `(e, n)⁻¹ = (e⁻¹, n + θ e)`, a backtrack in the lift projects to a
backtrack in the base path; hence **the lift of a reduced path is reduced**.  This file proves
that fact, in the form needed by the Howie development.

The definitional (type-level) casts occurring in the definition of `liftPath` are handled using
`Quiver.Path.cast` and the fact that `HEq` of *same-typed* paths is equality
(`Quiver.Path.cast_eq_iff_heq`): `liftPath_nil_cast'` and `liftPath_cons_cast'` expose the
recursion of `liftPath` in `Quiver.Path.cast` form, and the reducedness proof is then a plain
induction.
-/
import Mathlib
import Submission.Work.ORLocInd.Howie.CoverGraph
import Submission.Work.ORLocInd.Howie.isReduced_cons_iff

set_option autoImplicit false
set_option linter.unusedVariables false

universe u

namespace Work.ORLocInd.Howie

open Quiver

variable {V : Type u} [Quiver V] [Quiver.HasInvolutiveReverse V]

/-! ## Casts of paths -/

/-- `Eq.mpr` is `HEq` to the term being cast. -/
theorem heq_eq_mpr {α β : Sort u} (h : α = β) (x : β) : HEq (Eq.mpr h x) x := by
  rw [eq_mpr_eq_cast]
  exact cast_heq h.symm x

/-- Reducedness is invariant under `Quiver.Path.cast`. -/
theorem isReduced_cast {a a' b b' : V} (hu : a = a') (hv : b = b') (p : Quiver.Path a b) :
    (p.cast hu hv).IsReduced ↔ p.IsReduced := by
  cases hu; cases hv; rw [Quiver.Path.cast_rfl_rfl]

/-- `EndsWith` is invariant under `Quiver.Path.cast`. -/
theorem endsWith_cast_iff {a a' b b' : V} (hu : a = a') (hv : b = b')
    (p : Quiver.Path a b) {y : V} (f : y ⟶ b') :
    Quiver.Path.EndsWith (p.cast hu hv) f ↔ Quiver.Path.EndsWith p (f.cast rfl hv.symm) := by
  cases hu; cases hv
  simp [Quiver.Hom.cast_rfl_rfl]

/-- `coverProjArrow` is compatible with `Quiver.Hom.cast` (up to `HEq`). -/
theorem coverProjArrow_homCast {L : Labelling V} {u v v' : CoverVertex L} (hv : v = v')
    (f : u ⟶ v) : HEq (coverProjArrow (f.cast rfl hv)) (coverProjArrow f) := by
  cases hv
  rw [Quiver.Hom.cast_rfl_rfl]

/-! ## The vertex bookkeeping and the arrow added by a lift of a `cons` -/

theorem coverVertex_nil_eq (L : Labelling V) (a : V) (n : ℤ) :
    (⟨a, n⟩ : CoverVertex L) = ⟨a, n + pathSum L.toFun (Quiver.Path.nil : Quiver.Path a a)⟩ := by
  congr 1
  rw [pathSum_nil, add_zero]

theorem coverVertex_cons_eq (L : Labelling V) {a b c : V} (p : Quiver.Path a b) (e : b ⟶ c)
    (n : ℤ) :
    (⟨c, (n + pathSum L.toFun p) + L.toFun (Quiver.Total.mk b c e)⟩ : CoverVertex L)
      = ⟨c, n + pathSum L.toFun (p.cons e)⟩ := by
  congr 1
  rw [pathSum_cons, add_assoc]

/-- The arrow of the cyclic cover added when lifting a `cons`. -/
def coverLiftArrow (L : Labelling V) {b c : V} (e : b ⟶ c) (m : ℤ) :
    (⟨b, m⟩ : CoverVertex L) ⟶ ⟨c, m + L.toFun (Quiver.Total.mk b c e)⟩ :=
  ⟨Quiver.Total.mk b c e, rfl, rfl, rfl⟩

@[simp] theorem coverProjArrow_coverLiftArrow (L : Labelling V) {b c : V} (e : b ⟶ c) (m : ℤ) :
    coverProjArrow (coverLiftArrow L e m) = e := rfl

@[simp] theorem coverProjArrow_coverLiftArrow_reverse (L : Labelling V) {b c : V} (e : b ⟶ c)
    (m : ℤ) :
    coverProjArrow (Quiver.reverse (coverLiftArrow L e m)) = Quiver.reverse e := rfl

/-! ## The recursion of `liftPath`, in `Quiver.Path.cast` form -/

theorem liftPath_nil_cast' (L : Labelling V) (a : V) (n : ℤ) :
    liftPath L (Quiver.Path.nil : Quiver.Path a a) n =
      Quiver.Path.cast rfl (coverVertex_nil_eq L a n)
        (Quiver.Path.nil : Quiver.Path (⟨a, n⟩ : CoverVertex L) ⟨a, n⟩) := by
  rw [liftPath.eq_1]
  refine (Quiver.Path.eq_cast_iff_heq rfl (coverVertex_nil_eq L a n) _ _).2 ?_
  exact (heq_eq_mpr _ _).trans (heq_eq_mpr _ _)

theorem liftPath_cons_cast' (L : Labelling V) {a b c : V} (p : Quiver.Path a b) (e : b ⟶ c)
    (n : ℤ) :
    liftPath L (p.cons e) n =
      Quiver.Path.cast rfl (coverVertex_cons_eq L p e n)
        ((liftPath L p n).cons (coverLiftArrow L e (n + pathSum L.toFun p))) := by
  rw [liftPath.eq_2]
  refine (Quiver.Path.eq_cast_iff_heq rfl (coverVertex_cons_eq L p e n) _ _).2 ?_
  exact (heq_eq_mpr _ _).trans ((heq_eq_mpr _ _).trans (HEq.refl _))

/-! ## The lift of a reduced path -/

/-- The last arrow of a lifted path projects to the last arrow of the base path. -/
theorem liftPath_endsWith (L : Labelling V) {a b : V} (p : Quiver.Path a b) (n : ℤ) :
    ∀ {u : CoverVertex L} (f : u ⟶ (⟨b, n + pathSum L.toFun p⟩ : CoverVertex L)),
      Quiver.Path.EndsWith (liftPath L p n) f → Quiver.Path.EndsWith p (coverProjArrow f) := by
  induction p with
  | nil =>
      intro u f h
      rw [liftPath_nil_cast'] at h
      rw [endsWith_cast_iff rfl (coverVertex_nil_eq L a n)] at h
      exact absurd h (Quiver.Path.not_endsWith_nil _)
  | cons p e ih =>
      intro u f h
      rw [liftPath_cons_cast'] at h
      rw [endsWith_cast_iff rfl (coverVertex_cons_eq L p e n)] at h
      obtain ⟨q', hq'⟩ := h
      obtain ⟨hmid, hpath, harrow⟩ := Quiver.Path.cons.inj hq'
      subst hmid
      have harrow_eq : coverLiftArrow L e (n + pathSum L.toFun p)
          = f.cast rfl (coverVertex_cons_eq L p e n).symm := eq_of_heq harrow
      have hf : coverProjArrow f = e := by
        have h2 : HEq (coverProjArrow (f.cast rfl (coverVertex_cons_eq L p e n).symm))
            (coverProjArrow f) := coverProjArrow_homCast _ f
        have h3 : coverProjArrow (f.cast rfl (coverVertex_cons_eq L p e n).symm) = e := by
          rw [← harrow_eq]
          exact coverProjArrow_coverLiftArrow L e (n + pathSum L.toFun p)
        exact (heq_iff_eq.mp h2).symm.trans h3
      rw [hf]
      exact Quiver.Path.endsWith_cons p e

theorem liftPath_isReduced {V : Type u} [Quiver V] [Quiver.HasInvolutiveReverse V]
    (L : Labelling V) {a b : V} (p : Quiver.Path a b) (hp : p.IsReduced) (n : ℤ) :
    (liftPath L p n).IsReduced := by
  induction p with
  | nil =>
      rw [liftPath_nil_cast']
      exact (isReduced_cast rfl (coverVertex_nil_eq L a n) _).2 (Quiver.Path.IsReduced.nil _)
  | cons p e ih =>
      rw [liftPath_cons_cast']
      refine (isReduced_cast rfl (coverVertex_cons_eq L p e n) _).2 ?_
      obtain ⟨hpred, hlast⟩ := isReduced_cons_iff.mp hp
      rw [isReduced_cons_iff]
      refine ⟨ih hpred, ?_⟩
      intro f hf hfeq
      have hfrev : Quiver.reverse (coverLiftArrow L e (n + pathSum L.toFun p)) = f := by
        rw [hfeq, Quiver.reverse_reverse]
      have hf2 : Quiver.Path.EndsWith (liftPath L p n)
          (Quiver.reverse (coverLiftArrow L e (n + pathSum L.toFun p))) := by
        rw [hfrev]; exact hf
      have hEnds := liftPath_endsWith L p n
        (Quiver.reverse (coverLiftArrow L e (n + pathSum L.toFun p))) hf2
      rw [coverProjArrow_coverLiftArrow_reverse] at hEnds
      exact (hlast (Quiver.reverse e) hEnds) (Quiver.reverse_reverse e).symm

end Work.ORLocInd.Howie
