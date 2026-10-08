/-
Area A9, sub-area `Criterion`: the transfer kernel of `G →* P ⧸ P*` and the transfer criterion.

For a Sylow `p`-subgroup `P` of `G`, Mathlib's transfer homomorphism
`Subgroup.transferFocal P : G →* P ⧸ P.focalSubgroupOf` has kernel `K` with

* `K ⊓ P = P*` (= `(P : Subgroup G).focalSubgroup`, by `ker_transferFocal_inf_eq_focalSubgroup`),
* `G ⧸ K ≃* P ⧸ P*` (`transferFocal.quotientKerMulEquivQuotientFocalSubroupOf`), so `G ⧸ K` is a
  `p`-group.

Consequently the transfer criterion `P* = ⁅P, P⁆` is *equivalent* to `K ⊓ P = ⁅P, P⁆`, and the last
step of any induction proof of the criterion is the lifting step

    `HasNormalPComplement p ↥K  ⟹  HasNormalPComplement p G`

which holds because `G ⧸ K` is a `p`-group
(`Work.NPC.Frobenius.hasNormalPComplement_of_normal_pGroup_quotient`).
-/
import Mathlib
import Submission.Work.NPC.Defs
import Submission.Work.NPC.Frobenius.hasNormalPComplement_of_normal_pGroup_quotient

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

open scoped Pointwise commutatorElement

namespace Work.NPC.Criterion

variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

/-- **The transfer criterion, in terms of the transfer kernel.**  For a Sylow `p`-subgroup `P` of
`G` the following are equivalent:

* the focal subgroup of `P` is its commutator subgroup (`P* = ⁅P, P⁆`);
* the kernel `K` of the transfer `G →* P ⧸ P*` meets `P` in `⁅P, P⁆`.

This is the form in which the criterion is consumed by the strong-induction proof (the "descent"
is transferred to the kernel `K`, whose Sylow `p`-subgroup is `K ⊓ P`). -/
theorem focalSubgroup_eq_commutator_iff_transferKernel (P : Sylow p G) :
    (P : Subgroup G).focalSubgroup = ⁅(P : Subgroup G), (P : Subgroup G)⁆ ↔
      (P : Subgroup G).transferFocal.ker ⊓ (P : Subgroup G) =
        ⁅(P : Subgroup G), (P : Subgroup G)⁆ := by
  constructor
  · intro h
    rw [Subgroup.ker_transferFocal_inf_eq_focalSubgroup P, h]
  · intro h
    rw [← Subgroup.ker_transferFocal_inf_eq_focalSubgroup P, h]

/-- The quotient `G ⧸ K` of `G` by the kernel `K` of the transfer `G →* P ⧸ P*` is a `p`-group. -/
theorem isPGroup_quotient_transferKernel (P : Sylow p G) :
    IsPGroup p (G ⧸ (P : Subgroup G).transferFocal.ker) :=
  IsPGroup.of_equiv
    (IsPGroup.to_quotient P.isPGroup' (P : Subgroup G).focalSubgroupOf)
    (Subgroup.transferFocal.quotientKerMulEquivQuotientFocalSubroupOf P).symm

/-- **Lifting a normal `p`-complement through the transfer kernel.**  If the kernel `K` of the
transfer `G →* P ⧸ P*` has a normal `p`-complement, then so does `G`: `G ⧸ K` is a `p`-group
(isomorphic to `P ⧸ P*`). -/
theorem hasNormalPComplement_of_transferKernel (P : Sylow p G)
    (h : HasNormalPComplement p ↥((P : Subgroup G).transferFocal.ker)) :
    HasNormalPComplement p G :=
  Frobenius.hasNormalPComplement_of_normal_pGroup_quotient
    (isPGroup_quotient_transferKernel P) h

end Work.NPC.Criterion
