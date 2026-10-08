import Mathlib
import Submission.Work.BrauerSuzuki.Defs
import Submission.Work.BrauerSuzuki.Quaternion.genQuaternionData_basic
import Submission.Work.NPC.All
import Submission.Work.BrauerSuzuki.OddCore.le_of_normal_odd
import Submission.Work.BrauerSuzuki.OddCore.oddCard_oddCore
import Submission.Work.BrauerSuzuki.Sylow.genQuaternion_sylow_quotient
import Submission.Work.BrauerSuzuki.Q8.isPGroup_two_of_oddCore_eq_bot
import Submission.Work.BrauerSuzuki.Quaternion.card_center_of_genQuaternionData

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.BrauerSuzuki.Q8

/-- **Bender–Suzuki, step (4)(b), centre form.**  Let `G` be a finite group whose Sylow
`2`-subgroup `S` is generalized quaternion with `d.n = 2` (i.e. `S ≅ Q₈`).  Assume `O(G) = 1`
and that `G` has a normal `2`-complement.  Then `G` is a generalized quaternion group with
centre of order `2`.

Indeed the normal `2`-complement `N` is a normal subgroup of odd order, hence `N ≤ O(G) = ⊥`,
so `G` is a `2`-group.  Therefore the Sylow `2`-subgroup `S` is all of `G`, and the
generalized quaternion presentation `d` of `↥S` transports across `↥S ≃* G` to a presentation
of `G`; the centre of a generalized quaternion group has order `2`
(`Work.BrauerSuzuki.Quaternion.card_center_of_genQuaternionData`). -/
theorem step4b_center {G : Type*} [Group G] [Finite G]
    (S : Sylow 2 G) (d : Work.BrauerSuzuki.GenQuaternionData ↥S) (h2 : d.n = 2)
    (hO : Submission.Blueprint.oddCore G = ⊥)
    (hN : Work.NPC.HasNormalPComplement 2 G) :
    Nat.card ↥(Subgroup.center G) = 2 := by
  -- `G` is a `2`-group because its normal `2`-complement is a normal subgroup of odd order,
  -- hence lies in `O(G) = ⊥`.
  have hPG : IsPGroup 2 G := isPGroup_two_of_oddCore_eq_bot hO hN
  -- A Sylow `2`-subgroup of a `2`-group is the whole group.
  have hStop : (S : Subgroup G) = ⊤ := by
    have htop : IsPGroup 2 (⊤ : Subgroup G) :=
      IsPGroup.of_equiv hPG (Subgroup.topEquiv (G := G)).symm
    exact (S.is_maximal' htop le_top).symm
  -- Transport the generalized quaternion presentation across `↥S ≃* G`.
  have e : ↥S ≃* G := (MulEquiv.subgroupCongr hStop).trans (Subgroup.topEquiv (G := G))
  have hgen : Work.BrauerSuzuki.IsGenQuaternion G :=
    Work.BrauerSuzuki.Sylow.isGenQuaternion_of_mulEquiv e ⟨d⟩
  obtain ⟨d'⟩ := hgen
  exact Work.BrauerSuzuki.Quaternion.card_center_of_genQuaternionData d'

end Work.BrauerSuzuki.Q8
