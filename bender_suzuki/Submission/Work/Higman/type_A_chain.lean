/-
Copyright (c) 2024. All rights reserved.

# Assembly of the type-`A` route (Higman's Lemmas 8 and 9) for `type_A_classification`

`Work.Higman.type_A_classification` needs two facts about a Suzuki 2-group `P` with
`|P| = |Z(P)|²`: every square of `P` is central, and `Z(P) = Ω₁(P)`.  Both follow from Higman's
Lemma 9 (existence form), which the workspace obtains from Higman's Lemmas 3, 7 and 8.

`Work.Higman.maximal_abelian_invariant_ge_phi` routes through `Work.Higman.higman_lemma8`, which
still carries a `sorry`.  Every other ingredient is axiom-clean:

* `Work.Higman.higman_lemma3_aux` (Higman's Lemma 3, the `Φ(C) = A²` case),
* `Work.Higman.MSA.higman_lemma7_msa` (Higman's Lemma 7, the `C' ≤ A²` case),
* `Work.Higman.MSA.powSub_four_bot_of_maximal`, `Work.Higman.MSA.phi_le_of_maximal`
  (the two halves of Lemma 9),
* `Work.Higman.clo_hard_v2` (the hard case `A ≠ ⊥`, `A² ≠ ⊥` of Higman's Lemma 8, routed through
  the module-theoretic core `Work.Higman.core_alt_pairing`),
* `Work.Higman.eq_center_of_lemma9`, `Work.Higman.map_center_xi_sq`.

This file re-wires them, replacing `higman_lemma8` by `clo_hard_v2`, so that
`Work.Higman.type_A_classification` rests on axiom-clean input only.
-/

import Mathlib
import Submission.Work.Higman.Defs
import Submission.Work.Higman.Basic
import Submission.Work.Higman.PowSub
import Submission.Work.Higman.SuzukiMaximal
import Submission.Work.Higman.higman_lemma3_aux
import Submission.Work.Higman.MSA.higman_lemma7_msa
import Submission.Work.Higman.MSA.exp_four
import Submission.Work.Higman.MSA.phi_le_of_maximal
import Submission.Work.Higman.clo_hard_v2
import Submission.Work.Higman.sq_mem_center_of_card_eq_center_sq

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open scoped commutatorElement

namespace Work.Higman

variable {P : Type} [Group P] [Finite P]

/-- **Higman 1963, Lemma 8**, in the form used by the Lemma-9 development, obtained from the
algebraic core `Work.Higman.clo_hard_v2` (the `A ≠ ⊥`, `A² ≠ ⊥` case) and the two degenerate
cases. -/
theorem higman_lemma8_wired {P : Type} [Group P] [Finite P]
    (h : Work.Higman.IsSuzuki2Grp P) {A C : Subgroup P}
    (hA : Work.Higman.IsXiAbelNormal h A)
    (hCn : C.Normal) (hCinv : C.map (h.xi : MulAut P).toMonoidHom = C)
    (hAC : A ≤ C) (hCA : A ≠ C)
    (hcover : ∀ D : Subgroup P, D.Normal → D.map (h.xi : MulAut P).toMonoidHom = D →
      A ≤ D → D ≤ C → D = A ∨ D = C)
    (hC2 : Work.Higman.powSub C 2 ≤ A)
    (hCd : ⁅C, C⁆ = A) :
    ∀ a ∈ A, a * a = 1 := by
  by_cases hA0 : A = ⊥
  · subst hA0
    intro a ha
    rw [Subgroup.mem_bot] at ha
    subst ha
    simp
  · by_cases hA2 : Work.Higman.powSub A 2 = ⊥
    · intro a ha
      have h2 : a ^ 2 ∈ Work.Higman.powSub A 2 := pow_mem_powSub ha
      rw [hA2, Subgroup.mem_bot] at h2
      rwa [← pow_two]
    · exact (clo_hard_v2 h hA hCn hCinv hAC hCA hcover hC2 hCd hA0 hA2).elim

/-- **Higman 1963, Lemma 9 (existence form)**, wired with the axiom-clean pieces
(`higman_lemma3_aux`, `MSA.higman_lemma7_msa`, `higman_lemma8_wired`). -/
theorem maximal_abelian_wired {P : Type} [Group P] [Finite P]
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
  have hA4 : Work.Higman.powSub A 4 = ⊥ :=
    MSA.powSub_four_bot_of_maximal h hA hmaxI
      (fun hA' hCn hCinv hAC hACne hcover hPhi =>
        higman_lemma3_aux h hA' hCn hCinv hAC hACne hcover hPhi)
      (fun hA' hCn hCinv hAC hACne hcover hPhi hCd =>
        MSA.higman_lemma7_msa h hA' hCn hCinv hAC hACne hcover hPhi hCd)
      (fun hA' hCn hCinv hAC hACne hcover hC2 hCd =>
        higman_lemma8_wired h hA' hCn hCinv hAC hACne hcover hC2 hCd)
  have hPhi : Work.Higman.powSub (⊤ : Subgroup P) 2 ⊔ ⁅(⊤ : Subgroup P), ⊤⁆ ≤ A :=
    MSA.phi_le_of_maximal h hA hmaxI hA4
  refine ⟨A, hA.normal, hA.map_eq, hA.abelian, hmax', omega1_le_of_maximal h hA hmaxI, ?_, ?_,
    hA4⟩
  · exact le_trans le_sup_right hPhi
  · intro x
    exact hPhi (Subgroup.mem_sup_left (Work.Higman.pow_mem_powSub (Subgroup.mem_top x)))

/-- **Every square is central in the `q ^ 2` case**, wired version of
`Work.Higman.sq_mem_center_of_card_eq_center_sq`: `A = Z(P)` by `eq_center_of_lemma9`, and
`Φ(P) ≤ A` gives `∀ x, x ^ 2 ∈ A = Z(P)`. -/
theorem sq_mem_center_wired {P : Type} [Group P] [Finite P]
    (h : Work.Higman.IsSuzuki2Grp P)
    (hcard : Nat.card P = Nat.card ↥(Subgroup.center P) ^ 2) :
    ∀ x : P, x ^ 2 ∈ Subgroup.center P := by
  obtain ⟨A, hAn, hAxi, hAab, hAmax, hOmegaA, _hcomm, hsqA, hpow4⟩ := maximal_abelian_wired h
  have hAZ : A = Subgroup.center P :=
    eq_center_of_lemma9 h hcard hAn hAxi hAab hAmax hOmegaA hpow4
  intro x
  rw [← hAZ]
  exact hsqA x

end Work.Higman
