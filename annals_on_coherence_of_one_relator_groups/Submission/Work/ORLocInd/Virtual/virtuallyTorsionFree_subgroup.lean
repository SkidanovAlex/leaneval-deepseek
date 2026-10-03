import Mathlib
import Submission.Work.ORLocInd.Basic

namespace Work.ORLocInd.Virtual

/-- Virtual torsion-freeness passes to arbitrary subgroups.

If `G` has a normal torsion-free subgroup `G'` of finite index, then for any `H ≤ G` the
intersection `G' ⊓ H` (realised as `G'.subgroupOf H`) is a normal subgroup of `H`, of finite
index in `H` (its index divides `[G : G']`), and torsion-free because it embeds in `G'`. -/
theorem virtuallyTorsionFree_subgroup {G : Type*} [Group G]
    (h : Work.ORLocInd.VirtuallyTorsionFree G) (H : Subgroup G) :
    Work.ORLocInd.VirtuallyTorsionFree H := by
  obtain ⟨G', hnorm, hidx, htf⟩ := h
  refine ⟨G'.subgroupOf H, ?_, ?_, ?_⟩
  · exact hnorm.comap H.subtype
  · exact @Subgroup.instFiniteIndex_subgroupOf G _ G' H hidx
  · intro g hg
    obtain ⟨n, hn, hgn⟩ := isOfFinOrder_iff_pow_eq_one.mp hg
    have h1 : (⟨((g : H) : G), g.2⟩ : G') ^ n = 1 := by
      apply Subtype.ext
      have hc := congrArg (fun x : ↥(G'.subgroupOf H) => ((x : H) : G)) hgn
      simpa using hc
    have h2 := htf ⟨((g : H) : G), g.2⟩ (isOfFinOrder_iff_pow_eq_one.mpr ⟨n, hn, h1⟩)
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun y : G' => (y : G)) h2

end Work.ORLocInd.Virtual
