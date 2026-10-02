import Mathlib
import Submission.Work.Thom.chernClass
import Submission.Work.Thom.CohMap_oneH

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.Thom

/-- **The induction form of `chernClass_zero_eq_oneH`.**  For *every* base `B` and index type `ι`
(so that the induction hypothesis can be applied to the tautological quotient, whose base is the
punctured total space of `Z`), the `0`-th Chern class of a complex bundle of rank `m` is the unit
class `1 ∈ H⁰(B;ℤ)`.

The proof is the induction that mirrors the recursion defining `chernClass`: the rank-`0` case is
`chernClassZero` (where `c_0` is *defined* to be `1`), and the step is the descent
`chernClass_succ_of_le` together with the induction hypothesis on the tautological quotient and the
fact that pullback fixes the unit class (`CohMap_oneH`). -/
theorem chernClass_zero_eq_oneH_aux :
    ∀ (m : ℕ) (B : Type) [TopologicalSpace B] (ι : Type) [Fintype ι]
      (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι),
      chernClass m 0 Z = Work.Cohomology.oneH ℤ (TopCat.toSSet.obj (TopCat.of B)) := by
  intro m
  induction m with
  | zero =>
    intro B _ ι _ Z
    rw [chernClass_zero_rank]
    unfold chernClassZero
    rw [dif_pos rfl]
    exact cohTransport_rfl _
  | succ m ih =>
    intro B _ ι _ Z
    -- The descent equation for `j = 0`: `c_0(Z) = (pi^*)^{-1} c_0(Q)`.
    rw [chernClass_succ_of_le Z (Nat.zero_le m)]
    -- The induction hypothesis on the tautological quotient `Q` over the punctured total space.
    rw [ih (zeroComplement (realification Z)) (ι × Fin (m + 1)) (tautQuotient Z)]
    -- `pi^*` fixes the unit class, so it is the inverse image of the unit class that we must undo.
    rw [← CohMap_oneH ((bundleProj (realification Z)).comp
      (subtypeMap (zeroComplement (realification Z))))]
    exact LinearEquiv.symm_apply_apply _ _

/-- **The zeroth Chern class of a complex vector bundle is the unit class** `1 ∈ H⁰(B;ℤ)`.  This is
the `j = 0` case of the recursion defining the Chern classes (`Work.Thom.chernClass`): `c_0 = 1`. -/
theorem chernClass_zero_eq_oneH {m : ℕ} {B : Type} [TopologicalSpace B] {ι : Type} [Fintype ι]
    (Z : VectorBundleCore ℂ B (EuclideanSpace ℂ (Fin m)) ι) :
    Work.Thom.chernClass m 0 Z = Work.Cohomology.oneH ℤ (TopCat.toSSet.obj (TopCat.of B)) :=
  chernClass_zero_eq_oneH_aux m B ι Z

end Work.Thom
