import Mathlib
import Submission.Work.ThreePoints.ThmC.Defs
import Submission.Work.ThreePoints.even_card_normalizer_of_maximal_p_subgroup
import Submission.Work.ThreePoints.Basic
import Submission.Work.DoubleTransitivity.App2.app2_2

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ThreePoints.ThmC

theorem hA_s {G : Type} [Group G] [Finite G] {K : Subgroup G}
    (hK : LeanEval.GroupTheory.Defs.IsStronglyEmbedded K)
    {g : G} (hg : g ∉ K) {P : Subgroup G} {p : ℕ} (hp : p.Prime)
    (hprime : P ≤ Submission.Blueprint.twoPoint K g)
    (hmax : Work.ThreePoints.ThmC.IsMaxP3 K p P)
    (h2tM : Work.DoubleTransitivity.IsTwoTransitiveOnSub (Subgroup.normalizer (P : Set G))
      (Submission.Blueprint.fixedPts K P)) :
    ∃ s ∈ Subgroup.normalizer (P : Set G), orderOf s = 2 ∧
      Submission.Blueprint.twoPoint K s = Submission.Blueprint.twoPoint K g := by
  have hPK : P ≤ K := hprime.trans inf_le_left
  have hPg : P ≤ Submission.Blueprint.conj g K := hprime.trans inf_le_right
  have hω₀ : ((1 : G) : G ⧸ K) ∈ Submission.Blueprint.fixedPts K P := by
    rw [Work.ThreePoints.mem_fixedPts_iff_le_stabilizer, Work.ThreePoints.stabilizer_mk,
      Work.ThreePoints.conj_one]
    exact hPK
  have hω₂ : (g : G ⧸ K) ∈ Submission.Blueprint.fixedPts K P := by
    rw [Work.ThreePoints.mem_fixedPts_iff_le_stabilizer, Work.ThreePoints.stabilizer_mk]
    exact hPg
  have hne : ((1 : G) : G ⧸ K) ≠ (g : G ⧸ K) := by
    intro h
    exact hg (by simpa using (QuotientGroup.eq.mp h : (1 : G)⁻¹ * g ∈ K))
  obtain ⟨x, hxN, hx⟩ := h2tM.isTransitiveOnSub ((1 : G) : G ⧸ K) hω₀ (g : G ⧸ K) hω₂
  obtain ⟨s, hsN, hs2, hs⟩ :=
    Work.ThreePoints.sec3_lemma3 hK hp hmax.1 hmax.2.2 hω₀ hω₂ hne ⟨x, hxN, hx⟩
  refine ⟨s, hsN, hs2, ?_⟩
  show K ⊓ Submission.Blueprint.conj s K = K ⊓ Submission.Blueprint.conj g K
  have h1 : MulAction.stabilizer G (s • ((1 : G) : G ⧸ K)) =
      Submission.Blueprint.conj s (MulAction.stabilizer G ((1 : G) : G ⧸ K)) :=
    Work.DoubleTransitivity.App2.stabilizer_smul_eq_conj s ((1 : G) : G ⧸ K)
  rw [Work.ThreePoints.stabilizer_mk, Work.ThreePoints.conj_one] at h1
  rw [hs, Work.ThreePoints.stabilizer_mk] at h1
  rw [h1]

end Work.ThreePoints.ThmC
