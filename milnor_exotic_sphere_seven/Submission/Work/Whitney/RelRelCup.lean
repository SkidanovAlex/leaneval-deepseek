import Mathlib
import Submission.Work.Thom.Cohomology
import Submission.Work.Whitney.exists_relRelCup
import Submission.Work.Whitney.Cup

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option linter.unusedSectionVars false

/-!
# The relative–relative cup product `H^m(X,A) ⊗ H^n(X,B) → H^{m+n}(X,A ∪ B)`

`Work.Whitney.exists_relRelCup` (proved in `Submission/Work/Whitney/RelABComplex.lean` and
`relABZ.lean`, `relABQuasiIso.lean`, `exists_relRelCup.lean`) is an *existence* statement: for open
`A B ⊆ X` there is a bilinear pairing `H^m(X,A;R) × H^n(X,B;R) → H^{m+n}(X,A∪B;R)` whose image
under the forgetful map `relToAbs` is the absolute cup product of the two images.

This module turns that `∃` into a **named operation** with its computation rule — the interface a
consumer (the Thom class of a direct sum, `Work.Whitney.chernClass_whitneySum_top`, and the THOM
area) uses instead of `Classical.choose`-ing its own witness.  Everything here is a `rfl`-level
consequence of `Classical.choose_spec` on `Work.Whitney.exists_relRelCup`, plus the module
structure of the target.

* `Work.Whitney.relRelCup` — the operation;
* `Work.Whitney.relRelCup_relToAbs` — **the computation rule** (the defining property);
* `Work.Whitney.relRelCup_add_left/right`, `relRelCup_smul_left/right`,
  `relRelCup_neg_left/right`, `relRelCup_sub_left/right`, `relRelCup_zero_left/right`,
  `relRelCup_sum_left/right` — bilinearity in the usable `simp`-friendly form;
* `Work.Whitney.relRelCup_relToAbs_eq_abs_cup` — the same computation rule with the forgetful maps
  written out of the composite of `relToAbs` with `cupH'`.
-/

namespace Work.Whitney

open Work.TangentClasses

noncomputable section

variable {R : Type} [CommRing R] {X : Type} [TopologicalSpace X] {A B : Set X}

/-- **The relative–relative cup product.**  For open `A B ⊆ X` and a commutative ring `R`, the
bilinear pairing `H^m(X,A;R) → H^n(X,B;R) → H^{m+n}(X,A∪B;R)` of
`Work.Whitney.exists_relRelCup`, made into a named operation by `Classical.choose`.

Its defining property is `Work.Whitney.relRelCup_relToAbs`: forgetting the relative data recovers
the ordinary cup product of the two classes.  (The operation is *not* determined by that property
alone — `relToAbs` is not injective in general — so the choice is genuine; but the property is all
that the applications use.) -/
noncomputable def relRelCup (hA : IsOpen A) (hB : IsOpen B) (m n : ℕ) :
    Work.Thom.RelCoh R m X A →ₗ[R] Work.Thom.RelCoh R n X B →ₗ[R]
      Work.Thom.RelCoh R (m + n) X (A ∪ B) :=
  Classical.choose (exists_relRelCup (R := R) (X := X) (A := A) (B := B) hA hB m n)

/-- **The computation rule of `Work.Whitney.relRelCup`**: the image of the relative–relative cup
under the forgetful map `relToAbs` is the absolute cup product of the two images. -/
theorem relRelCup_relToAbs (hA : IsOpen A) (hB : IsOpen B) (m n : ℕ)
    (a : Work.Thom.RelCoh R m X A) (b : Work.Thom.RelCoh R n X B) :
    (Work.Thom.relToAbs R (A ∪ B) (m + n)).hom (relRelCup hA hB m n a b)
      = Work.Cohomology.cupH' R (ssB X) m n
          ((Work.Thom.relToAbs R A m).hom a) ((Work.Thom.relToAbs R B n).hom b) :=
  Classical.choose_spec (exists_relRelCup (R := R) (X := X) (A := A) (B := B) hA hB m n) a b

/-- The computation rule in the form `relToAbs (x ⌣ y) = relToAbs x ⌣ relToAbs y` (the absolute cup
product written as a composite of the two forgetful maps with `cupH'`). -/
theorem relRelCup_relToAbs_eq_abs_cup (hA : IsOpen A) (hB : IsOpen B) (m n : ℕ)
    (a : Work.Thom.RelCoh R m X A) (b : Work.Thom.RelCoh R n X B) :
    (Work.Thom.relToAbs R (A ∪ B) (m + n)).hom (relRelCup hA hB m n a b)
      = (Work.Cohomology.cupH' R (ssB X) m n)
          ((Work.Thom.relToAbs R A m).hom a) ((Work.Thom.relToAbs R B n).hom b) :=
  relRelCup_relToAbs hA hB m n a b

/-! ## Bilinearity, in the form used by consumers -/

@[simp] theorem relRelCup_zero_left (hA : IsOpen A) (hB : IsOpen B) (m n : ℕ)
    (b : Work.Thom.RelCoh R n X B) : relRelCup hA hB m n 0 b = 0 := by
  rw [map_zero, LinearMap.zero_apply]

@[simp] theorem relRelCup_zero_right (hA : IsOpen A) (hB : IsOpen B) (m n : ℕ)
    (a : Work.Thom.RelCoh R m X A) : relRelCup hA hB m n a 0 = 0 :=
  map_zero _

theorem relRelCup_add_left (hA : IsOpen A) (hB : IsOpen B) (m n : ℕ)
    (a a' : Work.Thom.RelCoh R m X A) (b : Work.Thom.RelCoh R n X B) :
    relRelCup hA hB m n (a + a') b = relRelCup hA hB m n a b + relRelCup hA hB m n a' b := by
  rw [map_add, LinearMap.add_apply]

theorem relRelCup_add_right (hA : IsOpen A) (hB : IsOpen B) (m n : ℕ)
    (a : Work.Thom.RelCoh R m X A) (b b' : Work.Thom.RelCoh R n X B) :
    relRelCup hA hB m n a (b + b') = relRelCup hA hB m n a b + relRelCup hA hB m n a b' := by
  rw [map_add]

theorem relRelCup_smul_left (hA : IsOpen A) (hB : IsOpen B) (m n : ℕ) (r : R)
    (a : Work.Thom.RelCoh R m X A) (b : Work.Thom.RelCoh R n X B) :
    relRelCup hA hB m n (r • a) b = r • relRelCup hA hB m n a b := by
  rw [map_smul, LinearMap.smul_apply]

theorem relRelCup_smul_right (hA : IsOpen A) (hB : IsOpen B) (m n : ℕ) (r : R)
    (a : Work.Thom.RelCoh R m X A) (b : Work.Thom.RelCoh R n X B) :
    relRelCup hA hB m n a (r • b) = r • relRelCup hA hB m n a b := by
  rw [map_smul]

theorem relRelCup_neg_left (hA : IsOpen A) (hB : IsOpen B) (m n : ℕ)
    (a : Work.Thom.RelCoh R m X A) (b : Work.Thom.RelCoh R n X B) :
    relRelCup hA hB m n (-a) b = -relRelCup hA hB m n a b := by
  rw [map_neg, LinearMap.neg_apply]

theorem relRelCup_neg_right (hA : IsOpen A) (hB : IsOpen B) (m n : ℕ)
    (a : Work.Thom.RelCoh R m X A) (b : Work.Thom.RelCoh R n X B) :
    relRelCup hA hB m n a (-b) = -relRelCup hA hB m n a b := by
  rw [map_neg]

theorem relRelCup_sub_left (hA : IsOpen A) (hB : IsOpen B) (m n : ℕ)
    (a a' : Work.Thom.RelCoh R m X A) (b : Work.Thom.RelCoh R n X B) :
    relRelCup hA hB m n (a - a') b = relRelCup hA hB m n a b - relRelCup hA hB m n a' b := by
  rw [map_sub, LinearMap.sub_apply]

theorem relRelCup_sub_right (hA : IsOpen A) (hB : IsOpen B) (m n : ℕ)
    (a : Work.Thom.RelCoh R m X A) (b b' : Work.Thom.RelCoh R n X B) :
    relRelCup hA hB m n a (b - b') = relRelCup hA hB m n a b - relRelCup hA hB m n a b' := by
  rw [map_sub]

theorem relRelCup_sum_left {α : Type*} {s : Finset α} (hA : IsOpen A) (hB : IsOpen B) (m n : ℕ)
    (a : α → Work.Thom.RelCoh R m X A) (b : Work.Thom.RelCoh R n X B) :
    relRelCup hA hB m n (∑ i ∈ s, a i) b = ∑ i ∈ s, relRelCup hA hB m n (a i) b := by
  rw [map_sum, LinearMap.sum_apply]

theorem relRelCup_sum_right {α : Type*} {s : Finset α} (hA : IsOpen A) (hB : IsOpen B) (m n : ℕ)
    (a : Work.Thom.RelCoh R m X A) (b : α → Work.Thom.RelCoh R n X B) :
    relRelCup hA hB m n a (∑ i ∈ s, b i) = ∑ i ∈ s, relRelCup hA hB m n a (b i) := by
  rw [map_sum]

end

end Work.Whitney
