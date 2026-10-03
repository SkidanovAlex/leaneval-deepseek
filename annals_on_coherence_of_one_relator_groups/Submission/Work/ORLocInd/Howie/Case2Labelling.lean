/-
# Labelling algebra for Howie's Case 2

This file collects the labelling constructions used by the proof of Howie's Case 2
(`Work.ORLocInd.Howie.case2`, L6 of `N4_LOCIND_LEAD.md`):

* `extendLabelling K L` — a labelling of `Γ` extending a labelling of `DelV K` by `0` on the
  deleted arrows, together with `pathSum_extendLabelling` and `pathSum_erasePath`;
* `Labelling.comb`, `Labelling.smul` — the `ℤ`-linear structure on labellings;
* `deltaLabelling P e` — the labelling which is `1` on `e`, `-1` on `e⁻¹` and `0` elsewhere.

They are separated from `case2.lean` so that the bridge-case lemmas proved by other files can
import them without importing the target theorem.
-/
import Mathlib
import Submission.Work.ORLocInd.Howie.Defs2
import Submission.Work.ORLocInd.Howie.Delete
import Submission.Work.ORLocInd.Howie.Relator
import Submission.Work.ORLocInd.Howie.span_noSelfLoop

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.ambiguousOpen false
set_option backward.isDefEq.respectTransparency false

universe u

namespace Work.ORLocInd.Howie

open Quiver

variable {V : Type u} [Quiver V] [Quiver.HasInvolutiveReverse V]

/-! ## Extending a labelling of the deleted graph -/

/-- The total arrow of `DelV K` associated with the reverse of a kept arrow is the reverse of the
associated arrow. -/
theorem ofTotal_totalReverse (K : Keep V) (e : Quiver.Total V) (h : K.pred e)
    (h' : K.pred (Quiver.totalReverse e)) :
    DelV.ofTotal K (Quiver.totalReverse e) h' = Quiver.totalReverse (DelV.ofTotal K e h) := by
  cases e with
  | mk a b f => rfl

/-- A labelling of `DelV K` extended by `0` on the deleted arrows. -/
noncomputable def extendLabelling (K : Keep V) (L : Labelling (DelV K)) : Labelling V := by
  classical
  exact
    { toFun := fun g => if h : K.pred g then L.toFun (DelV.ofTotal K g h) else 0
      balanced := by
        intro g
        by_cases h : K.pred g
        · have h' : K.pred (Quiver.totalReverse g) := (K.rev g).mpr h
          rw [dif_pos h', dif_pos h, ofTotal_totalReverse K g h h']
          exact L.balanced _
        · have h' : ¬ K.pred (Quiver.totalReverse g) := fun hh => h ((K.rev g).mp hh)
          rw [dif_neg h', dif_neg h, neg_zero] }

@[simp] theorem extendLabelling_apply_of (K : Keep V) (L : Labelling (DelV K)) (g : Quiver.Total V)
    (h : K.pred g) : (extendLabelling K L).toFun g = L.toFun (DelV.ofTotal K g h) := dif_pos h

@[simp] theorem extendLabelling_apply_not (K : Keep V) (L : Labelling (DelV K)) (g : Quiver.Total V)
    (h : ¬ K.pred g) : (extendLabelling K L).toFun g = 0 := dif_neg h

theorem pathSum_extendLabelling (K : Keep V) (L : Labelling (DelV K)) {a b : V}
    (p : Quiver.Path a b) (h : ∀ g ∈ p.arrowList, K.pred g) :
    pathSum (extendLabelling K L).toFun p =
      pathSum L.toFun (DelV.liftPath K a p h) := by
  induction p with
  | nil => rfl
  | cons p g ih =>
      have h' : ∀ g ∈ p.arrowList, K.pred g := fun g hg => h g (by
        rw [Quiver.Path.arrowList_cons]; exact List.mem_append.mpr (Or.inl hg))
      have hg : K.pred (Quiver.Total.mk _ _ g) := h (Quiver.Total.mk _ _ g) (by
        rw [Quiver.Path.arrowList_cons]; exact List.mem_append.mpr (Or.inr (by simp)))
      rw [pathSum_cons (extendLabelling K L).toFun p g,
        DelV.liftPath_cons K p g h h' hg,
        pathSum_cons L.toFun (DelV.liftPath K _ p h') ⟨g, hg⟩,
        ih h', extendLabelling_apply_of K L (Quiver.Total.mk _ _ g) hg]
      rfl

/-! ## The `pathSum` of an erased path -/

/-- The level of a path of the deleted graph equals the level of its erasure for the extended
labelling. -/
theorem pathSum_erasePath (K : Keep V) (L : Labelling (DelV K)) {a b : V}
    (q : @Quiver.Path (DelV K) (instDelQuiver K) a b) :
    pathSum L.toFun q = pathSum (extendLabelling K L).toFun (DelV.erasePath K a q) := by
  induction q with
  | nil => rfl
  | cons q g ih =>
      rw [DelV.erasePath_cons, pathSum_cons, pathSum_cons, ih,
        extendLabelling_apply_of K L (Quiver.Total.mk _ _ g.1) g.2]
      rfl

/-! ## Combining labellings -/

namespace Labelling

/-- The labelling `c * L + d * M`. -/
noncomputable def comb (c d : ℤ) (L M : Labelling V) : Labelling V where
  toFun := fun g => c * L.toFun g + d * M.toFun g
  balanced := by
    intro g
    rw [L.balanced g, M.balanced g]
    ring

@[simp] theorem comb_apply (c d : ℤ) (L M : Labelling V) (g : Quiver.Total V) :
    (comb c d L M).toFun g = c * L.toFun g + d * M.toFun g := rfl

theorem pathSum_comb (c d : ℤ) (L M : Labelling V) {a b : V} (p : Quiver.Path a b) :
    pathSum (comb c d L M).toFun p = c * pathSum L.toFun p + d * pathSum M.toFun p := by
  induction p with
  | nil => rw [pathSum_nil, pathSum_nil, pathSum_nil]; ring
  | cons p g ih =>
      rw [pathSum_cons, pathSum_cons, pathSum_cons, ih, comb_apply]
      ring

/-- The labelling `c * L`. -/
noncomputable def smul (c : ℤ) (L : Labelling V) : Labelling V where
  toFun := fun g => c * L.toFun g
  balanced := by
    intro g
    rw [L.balanced g]
    ring

@[simp] theorem smul_apply (c : ℤ) (L : Labelling V) (g : Quiver.Total V) :
    (smul c L).toFun g = c * L.toFun g := rfl

theorem pathSum_smul (c : ℤ) (L : Labelling V) {a b : V} (p : Quiver.Path a b) :
    pathSum (smul c L).toFun p = c * pathSum L.toFun p := by
  induction p with
  | nil => rw [pathSum_nil, pathSum_nil]; ring
  | cons p g ih => rw [pathSum_cons, pathSum_cons, ih, smul_apply]; ring

end Labelling

/-! ## The labelling `δₑ` of a single edge pair -/

/-- The labelling which is `1` on `e`, `-1` on `e⁻¹` and `0` elsewhere. -/
noncomputable def deltaLabelling (P : Presentation V) (e : Quiver.Total V) : Labelling V := by
  classical
  exact
    { toFun := fun g =>
        (if g = e then (1 : ℤ) else 0) - (if g = Quiver.totalReverse e then (1 : ℤ) else 0)
      balanced := by
        intro g
        have k1 : (Quiver.totalReverse g = e) ↔ (g = Quiver.totalReverse e) := by
          constructor
          · intro hh; rw [← Quiver.totalReverse_involutive g, hh]
          · intro hh; rw [hh, Quiver.totalReverse_involutive]
        have k2 : (Quiver.totalReverse g = Quiver.totalReverse e) ↔ (g = e) :=
          Quiver.totalReverse_injective.eq_iff
        show ((if Quiver.totalReverse g = e then (1 : ℤ) else 0) -
            (if Quiver.totalReverse g = Quiver.totalReverse e then (1 : ℤ) else 0)) =
          -((if g = e then (1 : ℤ) else 0) - (if g = Quiver.totalReverse e then (1 : ℤ) else 0))
        rw [if_congr k1 rfl rfl, if_congr k2 rfl rfl]
        ring }

theorem deltaLabelling_apply_self (P : Presentation V) (e : Quiver.Total V) :
    (deltaLabelling P e).toFun e = 1 := by
  classical
  have hns := totalReverse_ne_self P.noSelfLoop e
  show (if e = e then (1 : ℤ) else 0) - (if e = Quiver.totalReverse e then (1 : ℤ) else 0) = 1
  rw [if_pos (rfl : e = e), if_neg (fun hh : e = Quiver.totalReverse e => hns hh.symm)]
  norm_num

theorem deltaLabelling_apply_reverse (P : Presentation V) (e : Quiver.Total V) :
    (deltaLabelling P e).toFun (Quiver.totalReverse e) = -1 := by
  classical
  have hns := totalReverse_ne_self P.noSelfLoop e
  show (if Quiver.totalReverse e = e then (1 : ℤ) else 0) -
      (if Quiver.totalReverse e = Quiver.totalReverse e then (1 : ℤ) else 0) = -1
  rw [if_neg hns, if_pos (rfl : Quiver.totalReverse e = Quiver.totalReverse e)]
  norm_num

theorem deltaLabelling_apply_of_ne (P : Presentation V) (e g : Quiver.Total V)
    (h1 : g ≠ e) (h2 : g ≠ Quiver.totalReverse e) : (deltaLabelling P e).toFun g = 0 := by
  classical
  show (if g = e then (1 : ℤ) else 0) - (if g = Quiver.totalReverse e then (1 : ℤ) else 0) = 0
  rw [if_neg h1, if_neg h2]
  norm_num

/-- The labelling `δₑ` takes the value `0` on any path all of whose arrows avoid `e`. -/
theorem pathSum_deltaLabelling_eq_zero (P : Presentation V) (e : Quiver.Total V) {a b : V}
    (p : Quiver.Path a b) (h : ∀ g ∈ p.arrowList, g ≠ e ∧ g ≠ Quiver.totalReverse e) :
    pathSum (deltaLabelling P e).toFun p = 0 := by
  induction p with
  | nil => exact pathSum_nil _ _
  | cons p g ih =>
      have h' : ∀ g ∈ p.arrowList, g ≠ e ∧ g ≠ Quiver.totalReverse e := fun g hg => h g (by
        rw [Quiver.Path.arrowList_cons]; exact List.mem_append.mpr (Or.inl hg))
      have hg := h (Quiver.Total.mk _ _ g) (by
        rw [Quiver.Path.arrowList_cons]; exact List.mem_append.mpr (Or.inr (by simp)))
      rw [pathSum_cons, ih h', deltaLabelling_apply_of_ne P e _ hg.1 hg.2, add_zero]

end Work.ORLocInd.Howie
