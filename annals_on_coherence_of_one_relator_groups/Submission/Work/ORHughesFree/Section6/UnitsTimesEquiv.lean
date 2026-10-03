/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The two presentations of `E^× H`

In [JZLA20, §4.3] the rational semiring attached to a subgroup `H ≤ G` is `Rat(E^× H)`, and the
paper freely identifies `E^× H` with the subgroup `E^× H ≤ E^× G` of the units of the crossed
product.  Formally these are the two groups `Kˣ × H` and `unitsTimesSubgroup (K := K) H`, which are
canonically isomorphic; this file records that isomorphism and the transport of `RatU` along it
(`Rat.transportRingEquiv`), together with the two properties used in the induction of
[JZLA20, Theorem 6.1]: the transport is compatible with `ofGroup` and preserves the complexity
`Rat.treeOfRat`.
-/
import Mathlib
import Submission.Work.ORHughesFree.Rat.exists_ringEquiv_of_mulEquiv
import Submission.Work.ORHughesFree.Section6.Reduce

set_option autoImplicit false

namespace Work.ORHughesFree

variable {K : Type} [Monoid K] {G : Type} [Group G]

/-- The canonical isomorphism `Kˣ × H ≃* ↥(unitsTimesSubgroup H)`, `(λ, h) ↦ (λ, ↑h)`. -/
noncomputable def unitsTimesMulEquiv (H : Subgroup G) :
    (Kˣ × H) ≃* ↥(unitsTimesSubgroup (K := K) H) where
  toFun u := ⟨(u.1, (u.2 : G)), by
    rw [mem_unitsTimesSubgroup]
    exact u.2.2⟩
  invFun u := (u.1.1, ⟨u.1.2, mem_unitsTimesSubgroup.mp u.2⟩)
  left_inv u := by ext <;> rfl
  right_inv u := by ext <;> rfl
  map_mul' u v := by ext <;> rfl

@[simp] theorem unitsTimesMulEquiv_apply (H : Subgroup G) (u : Kˣ × H) :
    (unitsTimesMulEquiv (K := K) H u : Kˣ × G) = (u.1, (u.2 : G)) := rfl

end Work.ORHughesFree

namespace Work.ORHughesFree

variable {K : Type} [Field K] {G : Type} [Group G]

/-- The transport of `RatU` along `unitsTimesMulEquiv`, i.e. the canonical isomorphism
`Rat(E^× H) ≃+* Rat(↥(E^× H))`. -/
noncomputable def ratUnitsTimesEquiv (H : Subgroup G) :
    RatU (Kˣ × H) ≃+* RatU ↥(unitsTimesSubgroup (K := K) H) :=
  Rat.transportRingEquiv (unitsTimesMulEquiv (K := K) (G := G) H)

theorem ratUnitsTimesEquiv_ofGroup (H : Subgroup G) (u : Kˣ × H) :
    ratUnitsTimesEquiv (K := K) H (RatU.ofGroup u) =
      RatU.ofGroup (unitsTimesMulEquiv (K := K) (G := G) H u) :=
  Rat.transportRingEquiv_ofGroup _ u

theorem treeOfRat_ratUnitsTimesEquiv (H : Subgroup G) (α : RatU (Kˣ × H)) :
    Rat.treeOfRat ↥(unitsTimesSubgroup (K := K) H) (ratUnitsTimesEquiv (K := K) H α) =
      Rat.treeOfRat (Kˣ × H) α :=
  Rat.treeOfRat_transportRingEquiv _ α

end Work.ORHughesFree
