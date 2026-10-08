import Mathlib
import Submission.Work.Higman.Defs
import Submission.Work.Higman.PowSub
import Submission.Work.Higman.SuzukiMaximal
import Submission.Work.Higman.HS.c4_hs_aux
import Submission.Work.Higman.RedAux.invariant_compl_subgroup
import Submission.Work.Higman.RedAux.step2_eta_triv
import Submission.Work.Higman.MSA.lemma8_clean

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 4000000

open scoped commutatorElement

namespace Work.Higman.HS

/-- **The two-cover configuration exists in the residual `C₄` case.**

Let `A ⊴ P` be a maximal `ξ`-invariant abelian normal subgroup of a Suzuki 2-group `P` with
`Ω₁(P) ≤ A`, `[P,P] = A`, all squares of `P` in `A`, `A⁴ = ⊥`, `A² = Ω₁(P)`,
`|A| = |Ω₁(P)|²`, and `[A,⊤] = A²`; let `C ⊴ P` be `ξ`-invariant with `A < C`,
`[C,A] = A²`, `[C,C] = A²`, `[C,⊤] = A`, `C` minimal over `A` and maximal below `⊤`
(`hcover`, `hMcover`, `C ≠ ⊤`), and `C_P(A) = A`.

Then there is a `ξ`-invariant normal complement `E` of `C` over `A` with all the two-cover
properties: `A < E`, `E` minimal over `A`, `C ⊓ E = A`, `C ⊔ E = ⊤`, `[C,E] = A` and
`[E,E] = [E,A] = A²`.

Construction: `ξ ^ (|Ω₁(P)| - 1)` acts trivially on `P/A` (`RedAux.xi_pow_triv_quot_full`), so
Maschke over `𝔽₂` (`RedAux.invariant_compl_subgroup`) supplies a `ξ`-invariant complement `N`
of `C` modulo `A`; `[P,P] = A ≤ N` makes `N` normal.  A minimal `ξ`-invariant normal `E` with
`A < E ≤ N` is the required cover: `E/A` is `ξ`-irreducible, `[E,E] ∈ {⊥, A², A}` by the
dichotomy, `⊥` is excluded by maximality of `A` and `= A` is excluded by Higman's Lemma 8
(`MSA.lemma8_clean`, which would force `A ≤ Ω₁(P) = A²` and contradict `|A| = |Ω₁(P)|²`). -/
theorem two_cover_of_residual {P : Type} [Group P] [Finite P]
    (h : Work.Higman.IsSuzuki2Grp P) {A C : Subgroup P} [hAn : A.Normal]
    (hA : Work.Higman.IsXiAbelNormal h A)
    (hmax : ∀ B : Subgroup P, Work.Higman.IsXiAbelNormal h B → A ≤ B → B = A)
    (hNA : Work.Higman.omega1 P ≤ A)
    (hGs : Bracket.bracket (⊤ : Subgroup P) (⊤ : Subgroup P) = A)
    (hsq : ∀ x : P, x ^ 2 ∈ A)
    (hA4 : Work.Higman.powSub A 4 = ⊥)
    (htop : Work.Higman.powSub A 2 = Work.Higman.omega1 P)
    (hcard : Nat.card ↥A = (Nat.card ↥(Work.Higman.omega1 P)) ^ 2)
    (hAP : Bracket.bracket A (⊤ : Subgroup P) = Work.Higman.powSub A 2)
    (hcent : Subgroup.centralizer (A : Set P) = A)
    (hCn : C.Normal) (hCinv : C.map (h.xi : MulAut P).toMonoidHom = C)
    (hAC : A ≤ C) (hCA : A ≠ C) (hCne : C ≠ ⊤)
    (hcover : ∀ D : Subgroup P, D.Normal → D.map (h.xi : MulAut P).toMonoidHom = D →
      A ≤ D → D ≤ C → D = A ∨ D = C)
    (hC2 : Work.Higman.powSub C 2 ≤ A)
    (hCAd : Bracket.bracket C A = Work.Higman.powSub A 2)
    (hCd : Bracket.bracket C C = Work.Higman.powSub A 2)
    (hMcover : ∀ D : Subgroup P, D.Normal → D.map (h.xi : MulAut P).toMonoidHom = D →
      C ≤ D → D = C ∨ D = ⊤)
    (hCT : Bracket.bracket C (⊤ : Subgroup P) = A) :
    ∃ E : Subgroup P, E.Normal ∧ E.map (h.xi : MulAut P).toMonoidHom = E ∧ A ≤ E ∧ A ≠ E ∧
      (∀ D : Subgroup P, D.Normal → D.map (h.xi : MulAut P).toMonoidHom = D →
        A ≤ D → D ≤ E → D = A ∨ D = E) ∧
      Bracket.bracket C E = A ∧ C ⊓ E = A ∧ C ⊔ E = ⊤ ∧
      Bracket.bracket E E = Work.Higman.powSub A 2 ∧
      Bracket.bracket E A = Work.Higman.powSub A 2 := by
  classical
  -- ## 0. `A = A²` is contradictory
  have hcontra : A = Work.Higman.powSub A 2 → False := by
    intro hAeq
    obtain ⟨n, hn⟩ := h.exists_card_omega1_eq_two_pow
    have heq : Nat.card ↥(Work.Higman.omega1 P) = Nat.card ↥A := by
      rw [← htop, ← hAeq]
    have h2sq : Nat.card ↥A = (Nat.card ↥A) ^ 2 := by
      calc Nat.card ↥A = (Nat.card ↥(Work.Higman.omega1 P)) ^ 2 := hcard
        _ = (Nat.card ↥A) ^ 2 := by rw [heq]
    have hne : Nat.card ↥A ≠ 0 := by rw [← heq, hn]; exact pow_ne_zero n (by norm_num)
    have hmul : Nat.card ↥A * 1 = Nat.card ↥A * Nat.card ↥A := by
      simpa [pow_two] using h2sq
    have hk : Nat.card ↥A = 1 := (Nat.mul_left_cancel (Nat.pos_of_ne_zero hne) hmul).symm
    have hq1 : Nat.card ↥(Work.Higman.omega1 P) = 1 := by rw [heq, hk]
    have hfour := h.omega1_card_ge_four
    omega
  -- ## 1. every commutator lies in `A`
  have hAb : ∀ x y : P, x * y * x⁻¹ * y⁻¹ ∈ A := by
    intro x y
    have h1 : ⁅x, y⁆ ∈ ⁅(⊤ : Subgroup P), (⊤ : Subgroup P)⁆ :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top y)
    rw [hGs] at h1
    simpa [commutatorElement_def] using h1
  -- ## 2. the Maschke complement
  obtain ⟨n, hn⟩ := h.exists_card_omega1_eq_two_pow
  have hn2 : 2 ≤ n := by
    have hfour := h.omega1_card_ge_four
    rw [hn] at hfour
    by_contra hcon
    have hcon' : n ≤ 1 := by omega
    have h2 : 2 ^ n ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) hcon'
    omega
  have hodd : Odd (Nat.card ↥(Work.Higman.omega1 P) - 1) := by
    rw [hn]
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    exact ⟨2 ^ m - 1, by
      have h1 : 1 ≤ 2 ^ m := Nat.one_le_two_pow
      rw [pow_succ]; omega⟩
  have he1 : ∀ x : P, (h.xi ^ (Nat.card ↥(Work.Higman.omega1 P) - 1)) x * x⁻¹ ∈ A :=
    Work.Higman.RedAux.xi_pow_triv_quot_full h hA hmax hNA hGs hsq hA4 htop hcard
  obtain ⟨N, hAN, hNinv, hNinf, hNsup⟩ :=
    Work.Higman.RedAux.invariant_compl_subgroup h.xi hA.normal hA.map_eq hAC hCinv hAb hsq
      hodd he1
  -- ## 3. `N` is normal
  have hNnormal : N.Normal := by
    refine ⟨fun x hx g => ?_⟩
    have h1 : ⁅g, x⁆ ∈ A := by
      have h2 : ⁅g, x⁆ ∈ ⁅(⊤ : Subgroup P), (⊤ : Subgroup P)⁆ :=
        Subgroup.commutator_mem_commutator (Subgroup.mem_top g) (Subgroup.mem_top x)
      rwa [hGs] at h2
    have h3 : g * x * g⁻¹ = ⁅g, x⁆ * x := by rw [commutatorElement_def]; group
    rw [h3]
    exact N.mul_mem (hAN h1) hx
  -- ## 4. `A < N`
  have hANlt : A < N := by
    refine lt_of_le_of_ne hAN (fun hEq => hCne ?_)
    have h1 : A ⊔ C = ⊤ := by rw [← hNsup, hEq]
    rwa [sup_eq_right.mpr hAC] at h1
  -- ## 5. a minimal `ξ`-invariant normal `E` with `A < E ≤ N`
  have hfin : ({E : Subgroup P | A < E ∧ E ≤ N ∧ E.Normal ∧
      E.map (h.xi : MulAut P).toMonoidHom = E} : Set (Subgroup P)).Finite :=
    Set.finite_univ.subset (fun _ _ => trivial)
  obtain ⟨E, hEmin⟩ :=
    hfin.exists_minimal ⟨N, hANlt, le_rfl, hNnormal, hNinv⟩
  obtain ⟨hElt, hEN, hENormal, hEinv⟩ := hEmin.1
  have hEmin' : ∀ D : Subgroup P, D.Normal → D.map (h.xi : MulAut P).toMonoidHom = D →
      A ≤ D → D ≤ E → D = A ∨ D = E := by
    intro D hDn hDinv hAD hDE
    by_cases hDA : D = A
    · exact Or.inl hDA
    · refine Or.inr ?_
      have hDlt : A < D := lt_of_le_of_ne hAD (Ne.symm hDA)
      have hDmem : D ∈ ({E : Subgroup P | A < E ∧ E ≤ N ∧ E.Normal ∧
          E.map (h.xi : MulAut P).toMonoidHom = E} : Set (Subgroup P)) :=
        ⟨hDlt, hDE.trans hEN, hDn, hDinv⟩
      exact le_antisymm hDE (hEmin.2 hDmem hDE)
  have hAEl : A ≤ E := le_of_lt hElt
  have hEAne : A ≠ E := ne_of_lt hElt
  have hEAneE : E ≠ A := Ne.symm hEAne
  -- ## 6. the two-cover identities
  have hEinfC : E ⊓ C = A := by
    refine le_antisymm ?_ ?_
    · intro x hx
      rw [Subgroup.mem_inf] at hx
      have h1 : x ∈ N ⊓ C := ⟨hEN hx.1, hx.2⟩
      rwa [hNinf] at h1
    · intro x hx
      exact ⟨hAEl hx, hAC hx⟩
  haveI hEi : E.Normal := hENormal
  haveI hCi : C.Normal := hCn
  have hEsupC : E ⊔ C = ⊤ := by
    have hsupinv : (E ⊔ C).map (h.xi : MulAut P).toMonoidHom = E ⊔ C := by
      rw [Subgroup.map_sup, hEinv, hCinv]
    rcases hMcover (E ⊔ C) inferInstance hsupinv le_sup_right with h1 | h1
    · exfalso
      have hEC : E ≤ C := le_sup_left.trans (le_of_eq h1)
      have hEA : E ≤ A := by
        rw [← hEinfC]
        exact le_inf le_rfl hEC
      exact hEAneE (le_antisymm hEA hAEl)
    · exact h1
  -- ## 7. `[E,E] = A²`
  have hEE_le_A : Bracket.bracket E E ≤ A := by
    have h1 : Bracket.bracket E E ≤ Bracket.bracket (⊤ : Subgroup P) (⊤ : Subgroup P) :=
      Subgroup.commutator_mono le_top le_top
    rwa [hGs] at h1
  have hEE_inv : (Bracket.bracket E E).map (h.xi : MulAut P).toMonoidHom =
      Bracket.bracket E E := by
    rw [Subgroup.map_commutator, hEinv]
  have hE2 : Work.Higman.powSub E 2 ≤ A := by
    rw [Work.Higman.powSub, Subgroup.closure_le]
    rintro y ⟨x, -, rfl⟩
    exact hsq x
  have hEd : Bracket.bracket E E = Work.Higman.powSub A 2 := by
    rcases xi_inv_sub_dichotomy h hA.abelian hA.map_eq htop hA4 hEE_le_A hEE_inv with
      hb | h2 | h3
    · exfalso
      have hEab : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := by
        intro x hx y hy
        have h1 : ⁅x, y⁆ ∈ (⊥ : Subgroup P) := by
          rw [← hb]
          exact Subgroup.commutator_mem_commutator hx hy
        exact commutatorElement_eq_one_iff_mul_comm.mp (Subgroup.mem_bot.mp h1)
      exact hEAneE (hmax E ⟨hENormal, hEinv, hEab⟩ hAEl)
    · exact h2
    · exfalso
      have h1 : ∀ a ∈ A, a * a = 1 :=
        MSA.lemma8_clean h hA hENormal hEinv hAEl hEAne hEmin' hE2 h3
      have hAle : A ≤ Work.Higman.omega1 P := by
        intro a ha
        rw [h.mem_omega1]
        simpa [pow_two] using h1 a ha
      have hAeq : A = Work.Higman.powSub A 2 := by
        rw [htop]
        exact le_antisymm hAle hNA
      exact hcontra hAeq
  -- ## 8. `[C,E] = A`
  have hCE : Bracket.bracket C E = A := by
    have hCE_le : Bracket.bracket C E ≤ A := by
      have h1 : Bracket.bracket C E ≤ Bracket.bracket (⊤ : Subgroup P) (⊤ : Subgroup P) :=
        Subgroup.commutator_mono le_top le_top
      rwa [hGs] at h1
    have hCE_inv : (Bracket.bracket C E).map (h.xi : MulAut P).toMonoidHom =
        Bracket.bracket C E := by
      rw [Subgroup.map_commutator, hCinv, hEinv]
    have hkey : A ≤ Bracket.bracket C E ⊔ Work.Higman.powSub A 2 := by
      have h1 : Bracket.bracket C E ⊔ Bracket.bracket C C =
          Bracket.bracket C (⊤ : Subgroup P) := by
        rw [← hEsupC, Subgroup.commutator_sup_left C E C]
      rw [← hCd, h1, hCT]
    rcases xi_inv_sub_dichotomy h hA.abelian hA.map_eq htop hA4 hCE_le hCE_inv with
      hb | h2 | h3
    · exfalso
      have h1 : A ≤ Work.Higman.powSub A 2 := by simpa [hb] using hkey
      exact hcontra (le_antisymm h1 (Work.Higman.powSub_le (by norm_num)))
    · exfalso
      have h1 : A ≤ Work.Higman.powSub A 2 := by simpa [h2] using hkey
      exact hcontra (le_antisymm h1 (Work.Higman.powSub_le (by norm_num)))
    · exact h3
  -- ## 9. `[E,A] = A²`
  have hEA : Bracket.bracket E A = Work.Higman.powSub A 2 := by
    have hEA_le : Bracket.bracket E A ≤ Work.Higman.powSub A 2 := by
      have h1 : Bracket.bracket E A ≤ Bracket.bracket (⊤ : Subgroup P) A :=
        Subgroup.commutator_mono le_top le_rfl
      have h2 : Bracket.bracket (⊤ : Subgroup P) A = Bracket.bracket A (⊤ : Subgroup P) :=
        Subgroup.commutator_comm _ _
      rw [h2, hAP] at h1
      exact h1
    have hEA_inv : (Bracket.bracket E A).map (h.xi : MulAut P).toMonoidHom =
        Bracket.bracket E A := by
      rw [Subgroup.map_commutator, hEinv, hA.map_eq]
    have hne : Bracket.bracket E A ≠ ⊥ := by
      intro hb
      have hAE : Bracket.bracket A E = ⊥ := (Subgroup.commutator_comm A E).trans hb
      have hle : E ≤ Subgroup.centralizer (A : Set P) := by
        intro e he
        rw [Subgroup.mem_centralizer_iff]
        intro a ha
        have h1 : ⁅a, e⁆ ∈ (⊥ : Subgroup P) := by
          rw [← hAE]
          exact Subgroup.commutator_mem_commutator ha he
        exact commutatorElement_eq_one_iff_mul_comm.mp (Subgroup.mem_bot.mp h1)
      rw [hcent] at hle
      exact hEAneE (le_antisymm hle hAEl)
    have hEA_leA : Bracket.bracket E A ≤ A := hEA_le.trans (Work.Higman.powSub_le (by norm_num))
    rcases xi_inv_sub_dichotomy h hA.abelian hA.map_eq htop hA4 hEA_leA hEA_inv with
      hb | h2 | h3
    · exact absurd hb hne
    · exact h2
    · exfalso
      have h1 : A ≤ Work.Higman.powSub A 2 := h3.ge.trans hEA_le
      exact hcontra (le_antisymm h1 (Work.Higman.powSub_le (by norm_num)))
  exact ⟨E, hENormal, hEinv, hAEl, hEAne, hEmin', hCE, (inf_comm C E).trans hEinfC,
    (sup_comm C E).trans hEsupC, hEd, hEA⟩

end Work.Higman.HS
