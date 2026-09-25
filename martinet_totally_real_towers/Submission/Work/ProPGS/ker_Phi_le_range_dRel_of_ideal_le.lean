import Mathlib
import Submission.Work.ProPGS.CommonsBridge

namespace Work.ProPGS

open Commons.GroupTheory.ProPGroup

/-- **The ideal-theoretic form of the exactness of the Serre sequence at the middle term.**

Let `π : FreeGroup α →* Q` be surjective and let `S` be a finite set of relators whose
`relSpan`-ideal, together with `JrelK · IW`, already contains the whole relation ideal `JrelK`.
Then every `q : α → 𝔽_p[Q]` in the kernel of the Koszul-type map
`Φ = ∑ i, q i · t_i` is in the range of the differential `dRel`: i.e.

  `ker Φ ≤ range dRel`.

This is the version of the exactness statement
`Commons.GroupTheory.ProPGroup.ScratchSerre.ker_Phi_le_range_dRel` in which the hypothesis
`Subgroup.normalClosure S = π.ker` is replaced by the *weaker* ideal containment
`JrelK ≤ relSpan + JrelK · IW`, which is exactly what the spanning argument
(`Work.ProPGS.relSpan_add_JmulIW_of_spanning`) supplies from
`ker π ≤ normalClosure S ⊔ relFrattini p (ker π)`.  The proof is the same: lift `q` along
`ρ` and `Ψ⁻¹`, use that the lift lands in `IW`, decompose it via the hypothesis and kill the
`JrelK · IW` component. -/
theorem ker_Phi_le_range_dRel_of_ideal_le {p : ℕ} [Fact p.Prime] {α : Type} [Fintype α] [DecidableEq α]
    {Q : Type} [Group Q] (π : FreeGroup α →* Q) (S : Finset (FreeGroup α))
    (hπ : Function.Surjective π)
    (hideal : Commons.GroupTheory.ProPGroup.JrelK p α π ≤
      Commons.GroupTheory.ProPGroup.ScratchSerre.relSpan p α S +
        Commons.GroupTheory.ProPGroup.JrelK p α π * ScratchGS.IW p α) :
    (Commons.GroupTheory.ProPGroup.ScratchSerre.Phi p Q α π).ker ≤
      (Commons.GroupTheory.ProPGroup.ScratchSerre.dRel p α Q S π).range := by
  intro q hq
  choose w hw using fun i => ScratchSerre.rho_surjective p α Q π hπ (q i)
  let z : MonoidAlgebra (ZMod p) (FreeGroup α) := ∑ i : α, w i * ScratchGS.t p α i
  have hz_rho : rho p α π z = 0 := by
    change rho p α π (∑ i : α, w i * ScratchGS.t p α i) = 0
    rw [map_sum]
    have hq0 : (∑ i : α, q i * ScratchSerre.tG p Q α π i) = 0 := congrArg Subtype.val hq
    trans (∑ i : α, q i * ScratchSerre.tG p Q α π i)
    · apply Finset.sum_congr rfl
      intro i _
      rw [map_mul, hw i, ScratchSerre.rho_t]
    · exact hq0
  have hzJ : z ∈ JrelK p α π := by
    change rho p α π z = 0; exact hz_rho
  have hz_mem : z ∈ ScratchSerre.relSpan p α S + JrelK p α π * ScratchGS.IW p α := hideal hzJ
  rcases Submodule.mem_sup.mp hz_mem with ⟨s, hs, j, hj, hsj⟩
  have hz_eq : z = s + j := hsj.symm
  have hzIW : z ∈ ScratchGS.IW p α := by
    change (∑ i : α, w i * ScratchGS.t p α i) ∈ ScratchGS.IW p α
    exact Submodule.sum_mem _ (fun i _ => Ideal.mul_mem_left _ _ (ScratchSerre.t_mem_IW p α i))
  have hPsi_w : ScratchGS.Psi p α w = z := rfl
  have hPsi_PsiInv_z : ScratchGS.Psi p α (ScratchGS.PsiInv p α z) = z :=
    ScratchGS.Psi_PsiInv p α z hzIW
  have hw_eq : ScratchGS.PsiInv p α z = w := by
    apply ScratchSerre.Psi_injective p α
    rw [hPsi_PsiInv_z, hPsi_w]
  have hw_decomp : w = ScratchGS.PsiInv p α s + ScratchGS.PsiInv p α j := by
    rw [← hw_eq, hz_eq, ScratchSerre.PsiInv_add]
  have hw_q : ScratchSerre.rhoVec p α Q π w = q := by funext i; exact hw i
  have hq_eq : q = ScratchSerre.rhoVec p α Q π (ScratchGS.PsiInv p α s) := by
    rw [← hw_q, hw_decomp, ScratchSerre.rhoVec_add]
    rw [ScratchSerre.rhoVec_PsiInv_JmulIW_eq_zero p α Q π hj, add_zero]
  rcases ScratchSerre.rho_PsiInv_relSpan p α Q S π hs with ⟨f, hf⟩
  exact ⟨f, hf.trans hq_eq.symm⟩

end Work.ProPGS
