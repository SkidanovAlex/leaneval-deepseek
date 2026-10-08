import Mathlib
import Submission.Work.CohApps.sum_irr_deg_sq_le_ker
import Submission.Work.Clifford.irrDeg_eq_one_of_commutator_le_charKernel
import Submission.Work.CharCore.Main

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.style.haveILetI false

namespace Work.ZassenhausTwoGroup

theorem inflateFun_mem_Irr_triv {G : Type} [Group G] [Fintype G] {H Q : Subgroup G} [Fintype ↥H]
    [hN : (Q.subgroupOf H).Normal] (hH' : _root_.commutator ↥H ≤ Q.subgroupOf H)
    [Fintype (↥H ⧸ Q.subgroupOf H)]
    {β : ↥H ⧸ Q.subgroupOf H → ℂ} (hβ : β ∈ Work.CharCore.Irr (↥H ⧸ Q.subgroupOf H)) :
    (fun h : ↥H => β (QuotientGroup.mk h)) ∈ Work.CharCore.Irr ↥H ∧
    (∀ x : ↥H, (x : G) ∈ Q → β (QuotientGroup.mk x) = 1) := by
  classical
  constructor
  · -- The inflation of `β` to `↥H` is the function `h ↦ β (mk h)`, definitionally.
    exact Work.CohApps.inflateFun_mem_Irr (G := ↥H) (Q.subgroupOf H) hβ
  · intro x hx
    -- `⁅↥H, ↥H⁆ ≤ Q.subgroupOf H` makes the quotient `↥H ⧸ Q.subgroupOf H` commutative,
    -- so every irreducible character of it is linear: it takes the value `1` at the identity.
    haveI : IsMulCommutative (↥H ⧸ Q.subgroupOf H) :=
      Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr hH'
    have hxN : x ∈ Q.subgroupOf H := Subgroup.mem_subgroupOf.mpr hx
    rw [show QuotientGroup.mk x = (1 : ↥H ⧸ Q.subgroupOf H) from
          (QuotientGroup.eq_one_iff x).mpr hxN,
        Work.CharCore.irrDeg_spec hβ, Work.CharCore.irrDeg_eq_one_of_commutative hβ]
    norm_num

end Work.ZassenhausTwoGroup
