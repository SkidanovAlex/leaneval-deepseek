import Mathlib
import Submission.Work.Higman.HS.centralizer_eq_A_of_comm_C_A
import Submission.Work.Higman.H8.alt_pairing_false
import Submission.Work.Higman.HS.c4_hs_aux
import Submission.Work.Higman.homogeneous_structure
import Submission.Work.Higman.commutator_powSub_A_C
import Submission.Work.Higman.MSA.basic
import Submission.Work.Higman.HS.cover_deriv_eq_A
import Submission.Work.Higman.HS.hard_two_cover

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

open scoped commutatorElement

namespace Work.Higman.HS

variable {P : Type} [Group P] [Finite P]

/-- `⁅C,A⁆ ≤ A ^ (2)` in the `C₄` setting (using `⁅A,P⁆ = A ^ (2)`). -/
theorem commutator_C_A_le (h : Work.Higman.IsSuzuki2Grp P) {A C : Subgroup P}
    (hGA : ⁅A, (⊤ : Subgroup P)⁆ = Work.Higman.powSub A 2) :
    (⁅C, A⁆ : Subgroup P) ≤ Work.Higman.powSub A 2 := by
  rw [Subgroup.commutator_comm]
  exact (Subgroup.commutator_mono le_rfl le_top).trans (le_of_eq hGA)

/-- `⁅C,A⁆` is `ξ`-invariant when `A` and `C` are. -/
theorem map_xi_commutator_C_A (h : Work.Higman.IsSuzuki2Grp P) {A C : Subgroup P}
    (hAxi : A.map (h.xi : MulAut P).toMonoidHom = A)
    (hCinv : C.map (h.xi : MulAut P).toMonoidHom = C) :
    (⁅C, A⁆ : Subgroup P).map (h.xi : MulAut P).toMonoidHom = ⁅C, A⁆ := by
  rw [Subgroup.map_commutator, hCinv, hAxi]

/-- **Case `⁅C,A⁆ = ⊥` of the `C₄` exclusion of the derived subgroup of square shape.**
`C` centralises `A`, so Gorenstein–Thompson (`H8.alt_pairing_false`) applies: the fourth power
map `C/A → Ω₁(P)` is onto a `ξ`-irreducible module, and the alternating `ξ`-equivariant
commutator pairing on `C/A` with values in `Ω₁(P)` has to be trivial, contradicting
`⁅C,C⁆ = A² ≠ ⊥`. -/
theorem case_deriv_sq_false_central (h : Work.Higman.IsSuzuki2Grp P) {A C : Subgroup P}
    (hAxi : A.map (h.xi : MulAut P).toMonoidHom = A)
    (hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hNA : Work.Higman.omega1 P ≤ A)
    (hGs : ⁅(⊤ : Subgroup P), ⊤⁆ = A)
    (hsq : ∀ x : P, x ^ 2 ∈ A)
    (hA4 : Work.Higman.powSub A 4 = ⊥)
    (htop : Work.Higman.powSub A 2 = Work.Higman.omega1 P)
    (hcard : Nat.card ↥A = (Nat.card ↥(Work.Higman.omega1 P)) ^ 2)
    (hCn : C.Normal) (hCinv : C.map (h.xi : MulAut P).toMonoidHom = C)
    (hAC : A ≤ C) (hCA : A ≠ C)
    (hcover : ∀ D : Subgroup P, D.Normal → D.map (h.xi : MulAut P).toMonoidHom = D →
      A ≤ D → D ≤ C → D = A ∨ D = C)
    (hC2 : Work.Higman.powSub C 2 ≤ A)
    (hCd : ⁅C, C⁆ = Work.Higman.powSub A 2)
    (hZ : ∀ c ∈ C, ∀ a ∈ A, c * a = a * c) : False := by
  have hAn : A.Normal := normal_of_commutator_top_eq hGs
  have hA : Work.Higman.IsXiAbelNormal h A := ⟨hAn, hAxi, hAab⟩
  have hA2ne : Work.Higman.powSub A 2 ≠ ⊥ := by
    intro hb
    have h1 : Nat.card ↥(Work.Higman.omega1 P) = 1 := by
      rw [← htop, hb, Subgroup.card_bot]
    have h4 := h.omega1_card_ge_four
    omega
  have hexp : ∀ a ∈ A, a ^ 4 = 1 := by
    intro a ha
    have hmem : a ^ 4 ∈ Work.Higman.powSub A 4 := Work.Higman.pow_mem_powSub ha
    rw [hA4] at hmem
    simpa using hmem
  exact H8.alt_pairing_false h hA hCn hCinv hAC hCA.symm hcover hZ hC2 hCd htop.symm hA2ne hexp

/-- **`A` is a maximal abelian normal `ξ`-subgroup of `P` once `C_P(A) = A`.**

Any abelian subgroup `B ≥ A` lies in `C_P(A) = A`.  Consequently the hard case of
`case_deriv_sq_false` satisfies verbatim the hypotheses of `Work.Higman.no_square_of_maximal`
(the same obligation in the "maximality" formulation; that theorem's own proof is blocked on the
present case). -/
theorem isMaxAbelianNormal_of_centralizer_eq_A {P : Type} [Group P] [Finite P]
    (h : Work.Higman.IsSuzuki2Grp P) {A : Subgroup P}
    (hcent : Subgroup.centralizer (A : Set P) = A) :
    ∀ B : Subgroup P, Work.Higman.IsXiAbelNormal h B → A ≤ B → B = A := by
  intro B hB hAB
  have hBle : B ≤ Subgroup.centralizer (A : Set P) := by
    intro b hb
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact Work.Higman.IsXiAbelNormal.abelian hB a (hAB ha) b hb
  rw [hcent] at hBle
  exact le_antisymm hBle hAB

/-- **In the hard case `⁅C,A⁆ = A²`, `A` is a maximal abelian normal `ξ`-subgroup of `P`.**

This is `isMaxAbelianNormal_of_centralizer_eq_A` fed with
`Work.Higman.HS.centralizer_eq_A_of_comm_C_A`, which proves `C_P(A) = A` from the clean
`MSA.lemma8_clean`, `RedAux.deriv_eq_sq_false` and `RedAux.abelian_case`. -/
theorem isMaxAbelianNormal_of_comm_C_A {P : Type} [Group P] [Finite P]
    (h : Work.Higman.IsSuzuki2Grp P) {A C : Subgroup P} [hAn : A.Normal]
    (hAxi : A.map (h.xi : MulAut P).toMonoidHom = A)
    (hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hNA : Work.Higman.omega1 P ≤ A)
    (hGs : ⁅(⊤ : Subgroup P), ⊤⁆ = A)
    (hsq : ∀ x : P, x ^ 2 ∈ A)
    (hA4 : Work.Higman.powSub A 4 = ⊥)
    (htop : Work.Higman.powSub A 2 = Work.Higman.omega1 P)
    (hcard : Nat.card ↥A = (Nat.card ↥(Work.Higman.omega1 P)) ^ 2)
    (hCn : C.Normal) (hCinv : C.map (h.xi : MulAut P).toMonoidHom = C)
    (hAC : A ≤ C)
    (hcover : ∀ D : Subgroup P, D.Normal → D.map (h.xi : MulAut P).toMonoidHom = D →
      A ≤ D → D ≤ C → D = A ∨ D = C)
    (hCAd : ⁅C, A⁆ = Work.Higman.powSub A 2) :
    ∀ B : Subgroup P, Work.Higman.IsXiAbelNormal h B → A ≤ B → B = A :=
  isMaxAbelianNormal_of_centralizer_eq_A h
    (Work.Higman.HS.centralizer_eq_A_of_comm_C_A h hAxi hAab hNA hGs hsq hA4 htop hcard hCn hCinv
      hAC hcover hCAd)

theorem case_deriv_sq_false {P : Type} [Group P] [Finite P] (h : Work.Higman.IsSuzuki2Grp P)
    {A C : Subgroup P} (hAxi : A.map (h.xi : MulAut P).toMonoidHom = A)
    (hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x)
    (hNA : Work.Higman.omega1 P ≤ A)
    (hGs : ⁅(⊤ : Subgroup P), ⊤⁆ = A)
    (hsq : ∀ x : P, x ^ 2 ∈ A)
    (hA4 : Work.Higman.powSub A 4 = ⊥)
    (htop : Work.Higman.powSub A 2 = Work.Higman.omega1 P)
    (hcard : Nat.card ↥A = (Nat.card ↥(Work.Higman.omega1 P)) ^ 2)
    (hCn : C.Normal) (hCinv : C.map (h.xi : MulAut P).toMonoidHom = C)
    (hAC : A ≤ C) (hCA : A ≠ C)
    (hcover : ∀ D : Subgroup P, D.Normal → D.map (h.xi : MulAut P).toMonoidHom = D →
      A ≤ D → D ≤ C → D = A ∨ D = C)
    (hC2 : Work.Higman.powSub C 2 ≤ A)
    (hGA : ⁅A, (⊤ : Subgroup P)⁆ = Work.Higman.powSub A 2)
    (hCd : ⁅C, C⁆ = Work.Higman.powSub A 2) : False := by
  classical
  -- `A ≠ A²` (from `|A| = |Ω₁(P)|²` and `4 ≤ |Ω₁(P)|`)
  have hAne2 : A ≠ Work.Higman.powSub A 2 := by
    intro heq
    have hc : Nat.card ↥A = Nat.card ↥(Work.Higman.powSub A 2) :=
      congrArg (fun X : Subgroup P => Nat.card ↥X) heq
    rw [htop] at hc
    have hq : Nat.card ↥(Work.Higman.omega1 P) = (Nat.card ↥(Work.Higman.omega1 P)) ^ 2 := by
      rw [← hcard, hc]
    have h4 := h.omega1_card_ge_four
    have hpos : 0 < Nat.card ↥(Work.Higman.omega1 P) := Nat.card_pos
    nlinarith [hq, h4, hpos]
  -- the dichotomy for `⁅C,A⁆`
  have hCAle : (⁅C, A⁆ : Subgroup P) ≤ A :=
    (commutator_C_A_le h hGA).trans (Work.Higman.powSub_le (by norm_num))
  have hCAinv : (⁅C, A⁆ : Subgroup P).map (h.xi : MulAut P).toMonoidHom = ⁅C, A⁆ :=
    map_xi_commutator_C_A h hAxi hCinv
  rcases xi_inv_sub_dichotomy h hAab hAxi htop hA4 hCAle hCAinv with hbot | hmid | hAeq
  · -- Case `⁅C,A⁆ = ⊥`: Gorenstein–Thompson
    exact case_deriv_sq_false_central h hAxi hAab hNA hGs hsq hA4 htop hcard hCn hCinv hAC hCA
      hcover hC2 hCd (fun c hc a ha => by
        have h1 : (⁅c, a⁆ : P) ∈ (⊥ : Subgroup P) := by
          rw [← hbot]
          exact Subgroup.commutator_mem_commutator hc ha
        exact commutatorElement_eq_one_iff_mul_comm.mp (Subgroup.mem_bot.mp h1))
  · -- Case `⁅C,A⁆ = A²`: the hard case (`C` is a minimal `ξ`-invariant normal cover of `A`,
    -- `⁅C,C⁆ = C² = A²`, `C_P(A) = A`, `A` maximal `ξ`-abelian normal, `Z(P) = A²`).
    --
    -- If `C = ⊤` then `[P,P] = [C,C] = A² ≠ A = [P,P]`, contradiction.  Otherwise pass to a
    -- minimal `ξ`-invariant normal `M` with `C < M ≤ P`; then `[M,M] ∈ {A², A}` and
    -- `[M,M] = A²` would force `|M| = |C| = |Ω₁(P)|³` (Chevalley–Warning + orbit counting),
    -- i.e. `M = C`; so `[M,M] = A`, which is excluded by the delegated lemma `hard_two_cover`.
    have hAn : A.Normal := normal_of_commutator_top_eq hGs
    haveI : A.Normal := hAn
    have hmax : ∀ B : Subgroup P, Work.Higman.IsXiAbelNormal h B → A ≤ B → B = A :=
      isMaxAbelianNormal_of_comm_C_A h hAxi hAab hNA hGs hsq hA4 htop hcard hCn hCinv hAC
        hcover hmid
    by_cases hCtop : C = ⊤
    · exact hAne2 (hGs.symm.trans (by rw [← hCtop]; exact hCd))
    · obtain ⟨M, hMn, hMinv, hCM, -, hCMne, hMcover⟩ :=
        Work.Higman.MSA.exists_minimal_covering h Subgroup.normal_top
          (Subgroup.map_top_of_surjective _ (h.xi : MulAut P).surjective) le_top
          (fun hc => hCtop hc.symm)
      have hMd : ⁅M, M⁆ = A :=
        Work.Higman.HS.cover_deriv_eq_A h hAxi hAab hmax hNA hGs hsq hA4 htop hcard hCn hCinv
          hAC hCA hcover hC2 hmid hCd hMn hMinv hCM hCMne.symm hMcover
      exact Work.Higman.HS.hard_two_cover h hAxi hAab hmax hNA hGs hsq hA4 htop hcard hCn hCinv
        hAC hCA hcover hC2 hmid hCd hMn hMinv hCM hCMne.symm hMcover hMd
  · -- Case `⁅C,A⁆ = A`: impossible, since `⁅C,A⁆ ≤ A²` and `A ≠ A²`
    have hAle2 : A ≤ Work.Higman.powSub A 2 := by
      have h0 : (⁅C, A⁆ : Subgroup P) ≤ Work.Higman.powSub A 2 := commutator_C_A_le h hGA
      rwa [hAeq] at h0
    exact hAne2 (le_antisymm hAle2 (Work.Higman.powSub_le (by norm_num)))

end Work.Higman.HS
