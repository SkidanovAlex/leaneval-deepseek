import Mathlib
import Submission.Work.ORLyndon.cosetFinsetDefs

/-!
# Right cosets of `⟨w⟩` and chosen representatives

Let `G` be a group and `w : G`.  Two elements `x y : G` are in the same *right coset* of the cyclic
subgroup `⟨w⟩` when `y = x * w ^ m` for some `m : ℤ`.  This file packages that relation as a
`Setoid` and provides a classical representative function `cosetRep w` (via `Quotient.out`).

## Main definitions

* `Work.ORLyndon.SameRCoset`
* `Work.ORLyndon.sameRCosetSetoid`
* `Work.ORLyndon.cosetRep`

## Main results

* `Work.ORLyndon.cosetRep_spec`: `cosetRep w x` is in the right coset of `x`.
* `Work.ORLyndon.cosetRep_eq_of_sameRCoset`.
* `Work.ORLyndon.cosetRep_idem`: `cosetRep w` is idempotent.
* `Work.ORLyndon.sameRCoset_iff_mem_cosetFinset`: for `w ^ l = 1` and `0 < l`, the relation is
  membership in the finite coset `cosetFinset w l t`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Work.ORLyndon

variable {G : Type*} [Group G] [DecidableEq G]

/-- `SameRCoset w x y` holds when `x` and `y` lie in the same right coset of the cyclic subgroup
`⟨w⟩`, i.e. when `y = x * w ^ m` for some `m : ℤ`. -/
def SameRCoset (w x y : G) : Prop := ∃ m : ℤ, y = x * w ^ m

@[simp]
theorem sameRCoset_iff {w x y : G} : SameRCoset w x y ↔ ∃ m : ℤ, y = x * w ^ m := Iff.rfl

theorem sameRCoset_refl (w x : G) : SameRCoset w x x := ⟨0, by simp⟩

theorem sameRCoset_symm {w x y : G} (h : SameRCoset w x y) : SameRCoset w y x := by
  obtain ⟨m, hm⟩ := h
  exact ⟨-m, by rw [hm, zpow_neg, mul_assoc, mul_inv_cancel, mul_one]⟩

theorem sameRCoset_trans {w x y z : G} (h1 : SameRCoset w x y) (h2 : SameRCoset w y z) :
    SameRCoset w x z := by
  obtain ⟨m1, hm1⟩ := h1
  obtain ⟨m2, hm2⟩ := h2
  exact ⟨m1 + m2, by rw [hm2, hm1, zpow_add, mul_assoc]⟩

/-- The equivalence relation "lies in the same right coset of `⟨w⟩`". -/
def sameRCosetSetoid (w : G) : Setoid G where
  r := SameRCoset w
  iseqv := ⟨sameRCoset_refl w, fun h => sameRCoset_symm h, fun h1 h2 => sameRCoset_trans h1 h2⟩

/-- A classically chosen representative of the right `⟨w⟩`-coset of `x`. -/
noncomputable def cosetRep (w x : G) : G :=
  Quotient.out (Quotient.mk (sameRCosetSetoid w) x)

theorem cosetRep_spec (w x : G) : SameRCoset w (cosetRep w x) x :=
  Quotient.mk_out (s := sameRCosetSetoid w) x

theorem cosetRep_eq_of_sameRCoset {w x y : G} (h : SameRCoset w x y) :
    cosetRep w x = cosetRep w y :=
  congrArg Quotient.out (Quotient.sound h)

/-- `cosetRep w` is idempotent. -/
theorem cosetRep_idem (w x : G) : cosetRep w (cosetRep w x) = cosetRep w x :=
  cosetRep_eq_of_sameRCoset (cosetRep_spec w x)

/-- A representative that already lies in the image of `cosetRep` is fixed by `cosetRep`. -/
theorem cosetRep_eq_self_of_mem_image {w : G} {s : Finset G} {t : G}
    (ht : t ∈ s.image (cosetRep w)) : cosetRep w t = t := by
  obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp ht
  exact cosetRep_idem w x

/-- For `w ^ l = 1` with `0 < l`, the right-coset relation is membership in `cosetFinset`. -/
theorem sameRCoset_iff_mem_cosetFinset {w t h : G} {l : ℕ} (hl : 0 < l) (hw : w ^ l = 1) :
    SameRCoset w t h ↔ h ∈ cosetFinset w l t :=
  (mem_cosetFinset_iff hl hw).symm

/-- Elements of the same right coset have equal coset finsets. -/
theorem cosetFinset_eq_of_sameRCoset {w t t' : G} {l : ℕ} (hl : 0 < l) (hw : w ^ l = 1)
    (h : SameRCoset w t t') : cosetFinset w l t = cosetFinset w l t' :=
  (cosetFinset_eq_of_sameCoset hl hw h).symm

end Work.ORLyndon
