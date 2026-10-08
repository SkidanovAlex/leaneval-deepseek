import Mathlib
import Submission.Work.Higman.Defs
import Submission.Work.Higman.Basic
import Submission.Work.Higman.PowSub
import Submission.Work.Higman.higman_lemma1
import Submission.Work.Higman.homogeneous_structure
import Submission.Work.Higman.SuzukiMaximal
import Submission.Work.Higman.suzuki_unipotence
import Submission.Work.Higman.A_quot_irreducible
import Submission.Work.Higman.higman_lemma2
import Submission.Work.Higman.xi_trans_quot_sq
import Submission.Work.LocalPrelim.pgroup_commutator_ne_self
import Submission.Work.Higman.eq_top_of_sup_powSub_commutator_eq_top
import Submission.Work.Higman.higman_lemma3_aux
import Submission.Work.Higman.MSA.higman_lemma7_msa
import Submission.Work.Higman.MSA.higman_lemma8_msa
import Submission.Work.Higman.MSA.basic
import Submission.Work.Higman.MSA.endgame
import Submission.Work.Higman.MSA.exp_four
import Submission.Work.Higman.MSA.phi_le_of_maximal
import Submission.Work.Higman.maximal_abelian_assembly

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

open scoped commutatorElement

namespace Work.Higman

/-- **Higman 1963, Lemma 9 (existence form).**  In a Suzuki 2-group `P` there is a
`ξ`-invariant abelian normal subgroup `A`, maximal among the `ξ`-invariant abelian normal
subgroups, which contains `Ω₁(P)`, the commutator subgroup `[P,P]` and the squares of all
elements of `P` (equivalently `Φ(P) ≤ A`, since `Φ(P) = P²[P,P]`), and which has exponent at
most `4`.

Structure of the proof (Higman §3–§5, written out in `Submission/Work/Higman/MSA_NOTES.md`):

* `A` is a maximal `ξ`-invariant abelian normal subgroup (`exists_maximal_isXiAbelNormal`), so
  `Ω₁(P) ≤ A` (`omega1_le_of_maximal`);
* `A⁴ = ⊥` (`Work.Higman.MSA.powSub_four_bot_of_maximal`): a minimal covering `C > A` has
  `Φ(C) ∈ {A², A}`, and the two cases are Higman's Lemma 3 (giving `exp A | 4`), Higman's
  Lemma 8 (giving `exp A | 2`) and Higman's Lemma 7 (forcing `C` abelian, against maximality);
* `Φ(P) ≤ A` (`Work.Higman.MSA.phi_le_of_maximal`): the Higman §5 endgame, using a minimal
  covering `A < C ≤ A·Φ(P)` and `Φ(P) ≤ C_P(A)`, which follows from `A⁴ = ⊥`
  (`Work.Higman.MSA.commutator_frattini_centralizes`). -/
theorem maximal_abelian_invariant_ge_phi {P : Type} [Group P] [Finite P]
    (h : Work.Higman.IsSuzuki2Grp P) :
    ∃ A : Subgroup P, A.Normal ∧ A.map (h.xi : MulAut P).toMonoidHom = A ∧
      (∀ x ∈ A, ∀ y ∈ A, x * y = y * x) ∧
      (∀ B : Subgroup P, B.Normal → B.map (h.xi : MulAut P).toMonoidHom = B →
        (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) → A ≤ B → B = A) ∧
      Work.Higman.omega1 P ≤ A ∧ ⁅(⊤ : Subgroup P), ⊤⁆ ≤ A ∧ (∀ x : P, x ^ 2 ∈ A) ∧
      Work.Higman.powSub A 4 = ⊥ := by
  obtain ⟨A, hA, hmaxI⟩ := exists_maximal_isXiAbelNormal h
  have hmax' : ∀ B : Subgroup P, B.Normal → B.map (h.xi : MulAut P).toMonoidHom = B →
      (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) → A ≤ B → B = A :=
    fun B hn hi hab hAB => hmaxI B ⟨hn, hi, hab⟩ hAB
  -- `exp A | 4`
  have hA4 : powSub A 4 = ⊥ :=
    MSA.powSub_four_bot_of_maximal h hA hmaxI
      (fun hA' hCn hCinv hAC hACne hcover hPhi =>
        higman_lemma3_aux h hA' hCn hCinv hAC hACne hcover hPhi)
      (fun hA' hCn hCinv hAC hACne hcover hPhi hCd =>
        MSA.higman_lemma7_msa h hA' hCn hCinv hAC hACne hcover hPhi hCd)
      (fun hA' hCn hCinv hAC hACne hcover hC2 hCd =>
        MSA.higman_lemma8_msa h hA' hCn hCinv hAC hACne hcover hC2 hCd)
  -- `Φ(P) ≤ A`
  have hPhi : powSub (⊤ : Subgroup P) 2 ⊔ ⁅(⊤ : Subgroup P), ⊤⁆ ≤ A :=
    MSA.phi_le_of_maximal h hA hmaxI hA4
  refine ⟨A, hA.normal, hA.map_eq, hA.abelian, hmax', omega1_le_of_maximal h hA hmaxI, ?_, ?_, hA4⟩
  · exact le_trans le_sup_right hPhi
  · intro x
    exact hPhi (Subgroup.mem_sup_left (Work.Higman.pow_mem_powSub (Subgroup.mem_top x)))

end Work.Higman
