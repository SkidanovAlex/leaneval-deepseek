import Mathlib
import Submission.Work.ThreePoints.ThmC.Defs
import Submission.Work.ThreePoints.TwoPointTransitive
import Submission.Work.ThreePoints.app2_6_uniform
import Submission.Work.ThreePoints.even_card_normalizer_of_maximal_p_subgroup_nofour
import Submission.Work.ThreePoints.involutions_conj_of_stronglyEmbedded
import Submission.Work.DoubleTransitivity.App2.app2_4
import Submission.Work.ThreePoints.ThmC.ch1_sec6_cor1

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ThreePoints.ThmC

open LeanEval.GroupTheory.Defs

open Submission.Blueprint

/-- **Peterfalvi I Ch. I §4 Prop. 2** (p. 156) in the form needed below: `G` is a finite group,
`H` strongly embedded, `G` acts `2`-transitively on `G ⧸ H`, `p ≠ 2` is a prime, and `Q ≤ H` is a
`p`-subgroup maximal among the `p`-subgroups of `H` with at least three fixed points.  Then
`|N_H(Q)|` is even.

This is `Work.ThreePoints.even_card_normalizer_of_maximal_p_subgroup` with Theorem A replaced by
the `2`-transitivity of the given action; the proof is the source's, using App. II (6)
(`Work.ThreePoints.app2_6_uniform`) and Ch. I §3 Prop. 1 in its Brauer–Suzuki form
(`Work.ThreePoints.sec3_prop1_transitive`). -/
theorem even_card_normalizer_h2t {G : Type} [Group G] [Finite G] {H : Subgroup G}
    (hH : IsStronglyEmbedded H) (h2t : IsTwoTransitiveOn H)
    (hBrSz : Submission.Blueprint.BrauerSuzukiProp)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {Q : Subgroup G}
    (hQH : Q ≤ H) (hQp : IsPGroup p Q) (hQ3 : 3 ≤ (fixedPts H Q).ncard)
    (hQmax : ∀ R : Subgroup G, Q ≤ R → R ≤ H → IsPGroup p R →
      3 ≤ (fixedPts H R).ncard → R = Q) :
    Even (Nat.card (Subgroup.normalizer (Q.subgroupOf H : Set H) : Subgroup H)) := by
  classical
  haveI : Fintype (G ⧸ H) := Fintype.ofFinite _
  set M : Subgroup G := Subgroup.normalizer (Q : Set G) with hMdef
  -- App. II (6): maximality in `G` and `2`-transitivity of `N_G(Q)` on the fixed points
  obtain ⟨hQmaxG, ht2⟩ := Work.ThreePoints.app2_6_uniform (G := G) h2t hp hQH hQp hQ3 hQmax
  have htrans : Work.DoubleTransitivity.IsTransitiveOnSub M (fixedPts H Q) :=
    ht2.isTransitiveOnSub
  -- Ch. I §3 Prop. 1: some point stabiliser of `N_G(Q)` is even
  obtain ⟨ω, hω, heven⟩ :=
    Work.ThreePoints.sec3_prop1_transitive (K := H) hH hBrSz hp hp2 hQp hQ3 hQmaxG htrans
  have hstab0 : MulAction.stabilizer G (((1 : G) : G ⧸ H)) = H := by
    rw [Work.ThreePoints.stabilizer_mk, Work.ThreePoints.conj_one]
  have hω₀ : (((1 : G) : G ⧸ H)) ∈ fixedPts H Q :=
    Work.ThreePoints.mem_fixedPts_iff_le_stabilizer.mpr (by rw [hstab0]; exact hQH)
  obtain ⟨n, hnM, hn⟩ := htrans _ hω₀ ω hω
  -- conjugation by `n ∈ N_G(Q)` does not change `M`
  have hMconj : Submission.Blueprint.conj n M = M := by
    have hstep : ∀ u ∈ M, Submission.Blueprint.conj u M ≤ M := by
      intro u hu m hm
      rw [Work.ThreePoints.mem_conj_iff] at hm
      have h := M.mul_mem (M.mul_mem hu hm) (M.inv_mem hu)
      rwa [show u * (u⁻¹ * m * u) * u⁻¹ = m from by group] at h
    refine le_antisymm (hstep n hnM) ?_
    calc M = Submission.Blueprint.conj n (Submission.Blueprint.conj n⁻¹ M) := by
          rw [← Work.ThreePoints.conj_mul, mul_inv_cancel, Work.ThreePoints.conj_one]
      _ ≤ Submission.Blueprint.conj n M := Subgroup.map_mono (hstep n⁻¹ (M.inv_mem hnM))
  have hcard_eq : Nat.card (MulAction.stabilizer G ω ⊓ M : Subgroup G) =
      Nat.card (MulAction.stabilizer G (((1 : G) : G ⧸ H)) ⊓ M : Subgroup G) := by
    have h1 : MulAction.stabilizer G ω =
        Submission.Blueprint.conj n (MulAction.stabilizer G (((1 : G) : G ⧸ H))) := by
      rw [← Work.DoubleTransitivity.App2.stabilizer_smul_eq_conj n (((1 : G) : G ⧸ H)), hn]
    have key2 : MulAction.stabilizer G ω ⊓ M =
        Submission.Blueprint.conj n (MulAction.stabilizer G (((1 : G) : G ⧸ H)) ⊓ M) := by
      rw [Work.ThreePoints.conj_inf, ← h1, hMconj]
    rw [key2]
    exact Subgroup.card_map_of_injective (MulAut.conj n).injective
  have hevenK : Even (Nat.card (MulAction.stabilizer G (((1 : G) : G ⧸ H)) ⊓ M : Subgroup G)) := by
    rw [← hcard_eq]; exact heven
  rw [Work.ThreePoints.card_normalizer_subgroupOf_eq_card_inf hQH, ← hstab0]
  exact hevenK

end Work.ThreePoints.ThmC
