import Mathlib
import Submission.Work.LerayHirsch.Chapter
import Submission.Work.Projective.cpn_cohomology
import Submission.Work.Gen.ChernGenerator
import Submission.Work.Gen.uSqGenerates
import Submission.Work.Gen.chernClass_tautLine
import Submission.Work.Gen.ConjIso
import Submission.Work.Gen.tautDual_iso_conjLine

import Submission.Work.Gen.conjLine_euler_neg

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# Helper definitions for `lerayHirschFull_point`

This module contains the definitions and the elementary bookkeeping used by the proof of
`Work.Kunneth.lerayHirschFull_point` (`Submission/Work/Kunneth/lerayHirschFull_point.lean`):
`Work.LerayHirsch.LerayHirschFull (Work.LerayHirsch.trivCore m)`, i.e. Leray–Hirsch for the trivial
complex bundle of rank `m` over the point — H^*(P(ε^m)) ≅ H^*(ℂP^{m-1}).

* `Work.Kunneth.pow2 v j` — the `j`-th cup power of a class `v ∈ H²(X;ℤ)`, in the normalisation of
  `Work.LerayHirsch.zetaPow` (nested `Work.Whitney.cupChern`);
* `Work.Kunneth.pow2_zeta` — `pow2 (zeta Z) j = zetaPow Z j`;
* `Work.Kunneth.pow2_CohMap` — naturality of `pow2` under pullback;
* `Work.Kunneth.span_singleton_image_eq_top` — the image of a generator under a surjection generates.
-/

namespace Work.Kunneth

open Work.TangentClasses Work.Thom

noncomputable section

/-- **The `j`-th cup power of a class of degree `2`**, in the normalisation of
`Work.LerayHirsch.zetaPow`: `pow2 v 0 = 1` and `pow2 v (j+1) = cupChern j 1 (pow2 v j) v`. -/
noncomputable def pow2 {X : Type} [TopologicalSpace X] (v : Coh ℤ 2 X) :
    (j : ℕ) → Coh ℤ (2 * j) X :=
  Nat.rec (motive := fun j => Coh ℤ (2 * j) X)
    (cohTransport rfl (Work.Cohomology.oneH ℤ (Work.Whitney.ssB X)))
    (fun j rec => Work.Whitney.cupChern j 1 rec v)

@[simp] theorem pow2_zero {X : Type} [TopologicalSpace X] (v : Coh ℤ 2 X) :
    pow2 v 0 = cohTransport rfl (Work.Cohomology.oneH ℤ (Work.Whitney.ssB X)) := rfl

@[simp] theorem pow2_succ {X : Type} [TopologicalSpace X] (v : Coh ℤ 2 X) (j : ℕ) :
    pow2 v (j + 1) = Work.Whitney.cupChern j 1 (pow2 v j) v := rfl

/-- `zetaPow` is `pow2` of `zeta`. -/
theorem pow2_zeta {B : Type} [TopologicalSpace B] {ι : Type} {m : ℕ}
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) [Fintype ι] (j : ℕ) :
    pow2 (Work.LerayHirsch.zeta Z) j = Work.LerayHirsch.zetaPow Z j := by
  induction j with
  | zero => rfl
  | succ j ih => rw [pow2_succ, Work.LerayHirsch.zetaPow_succ, ih]

/-- **Naturality of `pow2` under pullback**. -/
theorem pow2_CohMap {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y] (f : C(X, Y))
    (v : Coh ℤ 2 Y) (j : ℕ) :
    (CohMap f ℤ (2 * j)).hom (pow2 v j) = pow2 ((CohMap f ℤ 2).hom v) j := by
  induction j with
  | zero =>
    rw [pow2_zero, pow2_zero, Work.Whitney.cohTransport_CohMap, CohMap_oneH]
  | succ j ih =>
    rw [pow2_succ, pow2_succ, Work.Whitney.cupChern_CohMap, ih]

/-- **The image of a generator under a surjective linear map generates.** -/
theorem span_singleton_image_eq_top {M N : Type*} [AddCommGroup M] [Module ℤ M]
    [AddCommGroup N] [Module ℤ N] (f : M →ₗ[ℤ] N) (hf : Function.Surjective f) {x : M}
    (hx : Submodule.span ℤ {x} = ⊤) : Submodule.span ℤ {f x} = ⊤ := by
  have h1 : Submodule.map f (Submodule.span ℤ {x}) = Submodule.span ℤ {f x} := by
    rw [Submodule.map_span]; simp
  rw [← h1, hx, Submodule.map_top]
  exact LinearMap.range_eq_top.mpr hf

end

end Work.Kunneth
