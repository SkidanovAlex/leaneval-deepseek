import Mathlib
import Submission.Work.ThmF.Setup
import Submission.Work.PSU3.StageA.oddIndexStrongEmbedded

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.PSU3.StageA

/-- **Bender–Suzuki, Stage A.**  If `H` is strongly embedded in `G`, `F` is a subgroup of `G`
not contained in `H`, and `H ∩ F` contains an involution, then `H ∩ F` is strongly embedded
in `F`.

Indeed `H ∩ F` is proper in `F` (else `F ≤ H`), has even order (it contains the involution),
and for `g ∈ F \ H` the two-point stabiliser `(H ∩ F) ∩ (H ∩ F)^g = H ∩ H^g ∩ F` is a subgroup
of `H ∩ H^g`, which has odd order by strong embeddedness of `H`. -/
theorem isStronglyEmbeddedInfSubgroupOf {G : Type} [Group G] [Finite G] {H F : Subgroup G}
    (hH : LeanEval.GroupTheory.Defs.IsStronglyEmbedded H) (hFH : ¬ F ≤ H)
    (hFinv : ∃ u ∈ H ⊓ F, orderOf u = 2) :
    LeanEval.GroupTheory.Defs.IsStronglyEmbedded ((H ⊓ F).subgroupOf F) := by
  obtain ⟨hHne, hHeven, hModd⟩ := hH
  obtain ⟨u, hu, hu2⟩ := hFinv
  refine ⟨?_, ?_, ?_⟩
  · -- `H ∩ F` is proper in `F`, since otherwise `F ≤ H`.
    rw [ne_eq, Subgroup.subgroupOf_eq_top]
    exact fun hle => hFH (hle.trans inf_le_left)
  · -- `H ∩ F` has even order: it contains an involution.
    rw [natCard_subgroupOf, inf_eq_left.mpr (inf_le_right : H ⊓ F ≤ F)]
    rw [even_iff_two_dvd]
    have hord : orderOf (⟨u, hu⟩ : ↥(H ⊓ F)) = 2 := by rw [Subgroup.orderOf_mk, hu2]
    rw [← hord]
    exact orderOf_dvd_natCard _
  · -- Two-point stabilisers inside `F` are subgroups of the corresponding ones inside `G`.
    intro g hg
    have hgG : (g : G) ∉ H := by
      intro h
      exact hg (by rw [Subgroup.mem_subgroupOf]; exact ⟨h, g.2⟩)
    have hodd := hModd (g : G) hgG
    have hcard : Nat.card ↥((H ⊓ F).subgroupOf F ⊓
          ((H ⊓ F).subgroupOf F).map (MulAut.conj g).toMonoidHom)
        = Nat.card ↥((H ⊓ F) ⊓ (H ⊓ F).map (MulAut.conj (g : G)).toMonoidHom) := by
      rw [conj_subgroupOf_inf (inf_le_right : H ⊓ F ≤ F) g, natCard_subgroupOf]
      rw [inf_eq_left.mpr
        (inf_le_left.trans inf_le_right :
          (H ⊓ F) ⊓ (H ⊓ F).map (MulAut.conj (g : G)).toMonoidHom ≤ F)]
    rw [hcard]
    exact odd_of_dvd (Subgroup.card_dvd_of_le (le_inf (inf_le_left.trans inf_le_left)
      (inf_le_right.trans (Subgroup.map_mono inf_le_left)))) hodd

end Work.PSU3.StageA
