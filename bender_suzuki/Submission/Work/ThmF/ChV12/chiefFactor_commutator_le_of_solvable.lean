import Mathlib
import Submission.Work.Fitting.Defs
import Submission.Work.Fitting.fitting_eq_sInf_chiefFactor_centralizer
import Submission.Work.Fitting.isChiefFactor_isMinimalNormal_map
import Submission.Work.Fitting.isMinimalNormal_isPGroup
import Submission.Work.Fitting.isMinimalNormal_isPGroup_commutative

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Chief factors of a solvable group are abelian

`Work.Fitting.IsChiefFactor H K` says that `H ⊴ K ⊴ G` and that `H < K` is a maximal
normal chain.  If `G` is finite solvable, then the section `K/H` is a minimal normal
subgroup of the solvable group `G/H`, hence elementary abelian; in particular `K/H`
is abelian, i.e. `⁅K, K⁆ ≤ H`.
-/

namespace Work.ThmF.ChV12

set_option linter.style.haveILetI false

open scoped commutatorElement

theorem chiefFactor_commutator_le_of_solvable {G : Type} [Group G] [Finite G]
    [Group.IsSolvable G] {H K : Subgroup G} (hHK : Work.Fitting.IsChiefFactor H K) :
    ∀ x ∈ K, ∀ y ∈ K, x * y * x⁻¹ * y⁻¹ ∈ H := by
  haveI : H.Normal := hHK.1
  -- the image of the chief factor `K/H` is a minimal normal subgroup of `G/H`
  have hN : Work.Fitting.IsMinimalNormal (K.map (QuotientGroup.mk' H)) :=
    Work.Fitting.isChiefFactor_isMinimalNormal_map hHK
  -- a minimal normal subgroup of a finite solvable group is a `p`-group, hence abelian
  obtain ⟨p, hp, hpg⟩ := Work.Fitting.isMinimalNormal_isPGroup (G ⧸ H) hN
  have hcomm : IsMulCommutative ↥(K.map (QuotientGroup.mk' H)) :=
    Work.Fitting.isMinimalNormal_isPGroup_commutative p (G ⧸ H) hp hN hpg
  -- commutativity of `K/H` means that `⁅K, K⁆` lies in the kernel of `K → K/H`
  have hbot : ⁅K.map (QuotientGroup.mk' H), K.map (QuotientGroup.mk' H)⁆ = ⊥ :=
    (Subgroup.commutator_self_eq_bot_iff (H := K.map (QuotientGroup.mk' H))).mpr hcomm
  have hmap : ⁅K, K⁆.map (QuotientGroup.mk' H) = ⊥ := by
    rw [Subgroup.map_commutator]
    exact hbot
  have hK'H : ⁅K, K⁆ ≤ H := by
    rw [← QuotientGroup.ker_mk' H, ← Subgroup.map_eq_bot_iff]
    exact hmap
  intro x hx y hy
  have hmem : ⁅x, y⁆ ∈ H := (Subgroup.commutator_le.mp hK'H) x hx y hy
  simpa only [commutatorElement_def] using hmem

end Work.ThmF.ChV12
