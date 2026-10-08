import Mathlib
import Submission.Work.Higman.NSM.dsq_setup
import Submission.Work.Higman.HS.two_cover_of_residual
import Submission.Work.Higman.Q3.twin_cover_of_odd_order
import Submission.Work.Higman.H8.c4_card_le
import Submission.Work.Higman.H8.cw_cube_bound
import Submission.Work.Higman.C4Cover.c4_cover_card_eq_cube
import Submission.Work.Higman.H8.c4_reducible_deriv_eq_A_false
import Submission.Work.Higman.MSA.lemma8_clean
import Submission.Work.Higman.MSA.basic
import Submission.Work.Higman.RedAux.invariant_compl_subgroup
import Submission.Work.Higman.RedAux.step2_eta_triv
import Submission.Work.Higman.RedAux.deriv_eq_sq_false
import Submission.Work.Higman.HS.htc_transport
import Submission.Work.Higman.H8.c4_comm_A_top
import Submission.Work.Higman.C4Cover.c4_no_five_chain
import Submission.Work.Higman.HS.c4_hs_aux

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open scoped commutatorElement

namespace Work.Higman.NSM

theorem two_cover_exists {P : Type} [Group P] [Finite P] (h : Work.Higman.IsSuzuki2Grp P)
    {A C : Subgroup P}
    (hA : Work.Higman.IsXiAbelNormal h A)
    (hmax : ∀ B : Subgroup P, Work.Higman.IsXiAbelNormal h B → A ≤ B → B = A)
    (hNA : Work.Higman.omega1 P ≤ A)
    (hGs : ⁅(⊤ : Subgroup P), ⊤⁆ = A)
    (hsq : ∀ x : P, x ^ 2 ∈ A)
    (hA4 : Work.Higman.powSub A 4 = ⊥)
    (htop : Work.Higman.powSub A 2 = Work.Higman.omega1 P)
    (hcard : Nat.card ↥A = (Nat.card ↥(Work.Higman.omega1 P)) ^ 2)
    (hcent : Subgroup.centralizer (A : Set P) = A)
    (hCn : C.Normal) (hCinv : C.map (h.xi : MulAut P).toMonoidHom = C)
    (hAC : A ≤ C) (hCA : A ≠ C)
    (hcover : ∀ D : Subgroup P, D.Normal → D.map (h.xi : MulAut P).toMonoidHom = D →
      A ≤ D → D ≤ C → D = A ∨ D = C)
    (hCpow2 : Work.Higman.powSub C 2 = Work.Higman.powSub A 2)
    (hCd : ⁅C, C⁆ = Work.Higman.powSub A 2)
    (hCT : ⁅C, (⊤ : Subgroup P)⁆ = A)
    (hsmall : ∀ {Q : Type} [Group Q] [Finite Q] (hQ : Work.Higman.IsSuzuki2Grp Q),
      Nat.card Q < Nat.card P →
      ∀ (A' C' : Subgroup Q), Work.Higman.IsXiAbelNormal hQ A' →
        Work.Higman.omega1 Q ≤ A' → ⁅(⊤ : Subgroup Q), ⊤⁆ = A' → (∀ x : Q, x ^ 2 ∈ A') →
        Work.Higman.powSub A' 4 = ⊥ → Work.Higman.powSub A' 2 = Work.Higman.omega1 Q →
        Nat.card ↥A' = (Nat.card ↥(Work.Higman.omega1 Q)) ^ 2 →
        C'.Normal → C'.map (hQ.xi : MulAut Q).toMonoidHom = C' → A' ≤ C' → A' ≠ C' →
        (∀ D : Subgroup Q, D.Normal → D.map (hQ.xi : MulAut Q).toMonoidHom = D →
          A' ≤ D → D ≤ C' → D = A' ∨ D = C') →
        Work.Higman.powSub C' 2 = Work.Higman.powSub A' 2 → ⁅C', C'⁆ = Work.Higman.powSub A' 2 →
        ⁅C', (⊤ : Subgroup Q)⁆ = A' → False) :
    ∃ E : Subgroup P, E.Normal ∧ E.map (h.xi : MulAut P).toMonoidHom = E ∧ A ≤ E ∧ A ≠ E ∧
      (∀ D : Subgroup P, D.Normal → D.map (h.xi : MulAut P).toMonoidHom = D →
        A ≤ D → D ≤ E → D = A ∨ D = E) ∧
      C ⊓ E = A ∧ C ⊔ E = ⊤ ∧
      Work.Higman.powSub E 2 = Work.Higman.powSub A 2 ∧ ⁅E, E⁆ = Work.Higman.powSub A 2 ∧
      ⁅E, A⁆ = Work.Higman.powSub A 2 ∧ ⁅C, E⁆ = A := by
  classical
  haveI hAn : A.Normal := hA.normal
  have hAab := hA.abelian
  have hAxi := hA.map_eq
  have hA2le : Work.Higman.powSub A 2 ≤ A := Work.Higman.powSub_le (by norm_num)
  have hA2ne : Work.Higman.powSub A 2 ≠ ⊥ := by
    intro hb
    have h1 : Nat.card ↥(Work.Higman.omega1 P) = 1 := by rw [← htop, hb]; simp
    have h4 := h.omega1_card_ge_four
    omega
  have hAne2 : A ≠ Work.Higman.powSub A 2 :=
    Work.Higman.H8.c4_A_ne_powSub_two h htop hcard
  have hAne : A ≠ ⊥ := by
    intro hb
    have h1 : Work.Higman.omega1 P ≤ (⊥ : Subgroup P) := hb ▸ hNA
    have h2 : Nat.card ↥(Work.Higman.omega1 P) = 1 := by
      rw [le_bot_iff.mp h1, Subgroup.card_bot]
    have h4 := h.omega1_card_ge_four
    omega
  have hCne : C ≠ ⊤ := Work.Higman.C4Cover.c4_C_ne_top h hGs htop hcard hCd
  -- ## Step 1: `[C,A] = A²`
  have hCAd : ⁅C, A⁆ = Work.Higman.powSub A 2 := by
    have hCA_le : ⁅C, A⁆ ≤ Work.Higman.powSub A 2 := by
      calc ⁅C, A⁆ ≤ ⁅C, C⁆ := Subgroup.commutator_mono le_rfl hAC
        _ = Work.Higman.powSub A 2 := hCd
    have hCAinv : (⁅C, A⁆ : Subgroup P).map (h.xi : MulAut P).toMonoidHom = ⁅C, A⁆ := by
      rw [Subgroup.map_commutator, hCinv, hAxi]
    rcases Work.Higman.HS.xi_inv_sub_dichotomy h hAab hAxi htop hA4
      (hCA_le.trans hA2le) hCAinv with hb | h2 | h3
    · exfalso
      have hcent' : C ≤ A := by
        rw [← hcent]
        intro c hc
        rw [Subgroup.mem_centralizer_iff]
        intro a ha
        have h1 : ⁅c, a⁆ ∈ (⊥ : Subgroup P) := by
          rw [← hb]
          exact Subgroup.commutator_mem_commutator hc ha
        exact (commutatorElement_eq_one_iff_mul_comm.mp (Subgroup.mem_bot.mp h1)).symm
      exact hCA (le_antisymm hAC hcent')
    · exact h2
    · exfalso
      have hAe : A ≤ Work.Higman.powSub A 2 := (le_of_eq h3.symm).trans hCA_le
      exact hAne2 (le_antisymm hAe hA2le)
  -- ## Step 2: `[A,⊤] = A²`
  have hAtop : ⁅A, (⊤ : Subgroup P)⁆ = Work.Higman.powSub A 2 := by
    refine Work.Higman.comm_A_top_eq_powSub_two h hAn hAab hAxi hNA hGs hA4 htop ?_
    calc Work.Higman.powSub A 2 = ⁅C, A⁆ := hCAd.symm
      _ ≤ ⁅A, C⁆ := le_of_eq (Subgroup.commutator_comm C A)
      _ ≤ ⁅A, (⊤ : Subgroup P)⁆ := Subgroup.commutator_mono le_rfl le_top
  -- ## Step 3: the `ξ`-invariant complement `N` of `C` modulo `A`
  have hAb : ∀ x y : P, x * y * x⁻¹ * y⁻¹ ∈ A := by
    intro x y
    have h1 : ⁅x, y⁆ ∈ ⁅(⊤ : Subgroup P), (⊤ : Subgroup P)⁆ :=
      Subgroup.commutator_mem_commutator (Subgroup.mem_top x) (Subgroup.mem_top y)
    rw [hGs] at h1
    simpa [commutatorElement_def] using h1
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
    Work.Higman.RedAux.invariant_compl_subgroup h.xi hAn hAxi hAC hCinv hAb hsq hodd he1
  have hNnormal : N.Normal := by
    refine ⟨fun x hx g => ?_⟩
    have h1 : ⁅g, x⁆ ∈ A := by
      have h2 : ⁅g, x⁆ ∈ ⁅(⊤ : Subgroup P), (⊤ : Subgroup P)⁆ :=
        Subgroup.commutator_mem_commutator (Subgroup.mem_top g) (Subgroup.mem_top x)
      rwa [hGs] at h2
    have h3 : g * x * g⁻¹ = ⁅g, x⁆ * x := by rw [commutatorElement_def]; group
    rw [h3]
    exact N.mul_mem (hAN h1) hx
  have hANlt : A < N := by
    refine lt_of_le_of_ne hAN (fun hEq => hCne ?_)
    have h1 : A ⊔ C = ⊤ := by rw [← hNsup, hEq]
    rwa [sup_eq_right.mpr hAC] at h1
  -- ## Step 4: a minimal `ξ`-invariant normal `A < E ≤ N`
  obtain ⟨E, hEn, hEinv, hAE, hEN, hEAne, hEcover⟩ :=
    Work.Higman.MSA.exists_minimal_covering h hNnormal hNinv hAN (ne_of_gt hANlt)
  have hEirr : ∀ F : Subgroup P, A ≤ F → F ≤ E → F.map (h.xi : MulAut P).toMonoidHom = F →
      F = A ∨ F = E := by
    intro F hAF hFE hFinv
    refine hEcover F (Work.Higman.HS.htc_normal_of_commutator_le ?_) hFinv hAF hFE
    rw [hGs]; exact hAF
  -- ## Step 5: `[E,E] = A²`
  have hEE : ⁅E, E⁆ = Work.Higman.powSub A 2 := by
    have hEE_le : ⁅E, E⁆ ≤ A := (Subgroup.commutator_mono le_top le_top).trans (le_of_eq hGs)
    have hEE_inv : (⁅E, E⁆ : Subgroup P).map (h.xi : MulAut P).toMonoidHom = ⁅E, E⁆ := by
      rw [Subgroup.map_commutator, hEinv]
    rcases Work.Higman.HS.xi_inv_sub_dichotomy h hAab hAxi htop hA4 hEE_le hEE_inv
      with hb | h2 | h3
    · exfalso
      have hEab : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := by
        intro x hx y hy
        have h1 : ⁅x, y⁆ ∈ (⊥ : Subgroup P) := by
          rw [← hb]
          exact Subgroup.commutator_mem_commutator hx hy
        exact commutatorElement_eq_one_iff_mul_comm.mp (Subgroup.mem_bot.mp h1)
      exact hEAne (hmax E ⟨hEn, hEinv, hEab⟩ hAE)
    · exact h2
    · exfalso
      exact Work.Higman.H8.c4_reducible_deriv_eq_A_false h hA hNA htop hcard hsq hEn hEinv
        hAE hEAne hEcover h3
  -- ## Step 6: `E² = A²`
  have hE2 : Work.Higman.powSub E 2 = Work.Higman.powSub A 2 := by
    have hE2_le : Work.Higman.powSub E 2 ≤ A := by
      rw [Work.Higman.powSub, Subgroup.closure_le]
      rintro y ⟨x, -, rfl⟩
      exact hsq x
    have hE2_inv : (Work.Higman.powSub E 2).map (h.xi : MulAut P).toMonoidHom
        = Work.Higman.powSub E 2 := Work.Higman.map_powSub h.xi hEinv 2
    have hE2_ge : Work.Higman.powSub A 2 ≤ Work.Higman.powSub E 2 :=
      Work.Higman.powSub_mono hAE
    rcases Work.Higman.HS.xi_inv_sub_dichotomy h hAab hAxi htop hA4 hE2_le hE2_inv
      with hb | h2 | h3
    · exfalso
      exact hA2ne (le_bot_iff.mp (hE2_ge.trans (le_of_eq hb)))
    · exact h2
    · exfalso
      have hGs' : commutator P = A := by
        rw [show (commutator P : Subgroup P) = ⁅(⊤ : Subgroup P), ⊤⁆ from rfl, hGs]
      exact Work.Higman.RedAux.deriv_eq_sq_false h hAxi hAab hNA hGs' hsq hA4 htop hcard
        hAE hEAne hEinv hEirr hEE h3
  -- ## Step 7: cardinalities
  have hCcard3 : Nat.card ↥C = (Nat.card ↥(Work.Higman.omega1 P)) ^ 3 :=
    Work.Higman.C4Cover.c4_cover_card_eq_cube h hAab hNA hGs hsq htop hcard hCn hCinv
      hAC hCA hcover hCd
  have hEcard3 : Nat.card ↥E = (Nat.card ↥(Work.Higman.omega1 P)) ^ 3 :=
    Work.Higman.C4Cover.c4_cover_card_eq_cube h hAab hNA hGs hsq htop hcard hEn hEinv
      hAE hEAne.symm hEcover hEE
  have hCEinf : C ⊓ E = A := by
    refine le_antisymm ?_ (le_inf hAC hAE)
    intro x hx
    rw [Subgroup.mem_inf] at hx
    have h1 : x ∈ N ⊓ C := ⟨hEN hx.2, hx.1⟩
    rwa [hNinf] at h1
  -- ## Step 8: `[C,E] ∈ {A², A}`
  have hCE_le : ⁅C, E⁆ ≤ A := (Subgroup.commutator_mono le_top le_top).trans (le_of_eq hGs)
  have hCE_inv : (⁅C, E⁆ : Subgroup P).map (h.xi : MulAut P).toMonoidHom = ⁅C, E⁆ := by
    rw [Subgroup.map_commutator, hCinv, hEinv]
  have hCE_ge : Work.Higman.powSub A 2 ≤ ⁅C, E⁆ := by
    rw [← hCAd]; exact Subgroup.commutator_mono le_rfl hAE
  have hCE_ge' : ⁅C, E⁆ ≠ ⊥ := fun hb => hA2ne (le_bot_iff.mp (hCE_ge.trans (le_of_eq hb)))
  have hCEdich : ⁅C, E⁆ = Work.Higman.powSub A 2 ∨ ⁅C, E⁆ = A := by
    rcases Work.Higman.HS.xi_inv_sub_dichotomy h hAab hAxi htop hA4 hCE_le hCE_inv
      with hb | h2 | h3
    · exact absurd hb hCE_ge'
    · exact Or.inl h2
    · exact Or.inr h3
  -- ## Step 9: `C ⊔ E = ⊤`
  have hCsupE : C ⊔ E = ⊤ := by
    by_contra hne
    have hFlt : C ⊔ E < ⊤ := lt_top_iff_ne_top.mpr hne
    have hFinv : (C ⊔ E).map (h.xi : MulAut P).toMonoidHom = C ⊔ E := by
      rw [Subgroup.map_sup, hCinv, hEinv]
    have hOmF : Work.Higman.omega1 P ≤ C ⊔ E := hNA.trans (hAC.trans le_sup_left)
    have hFcard_gt : (Nat.card ↥(Work.Higman.omega1 P)) ^ 3 < Nat.card ↥(C ⊔ E) := by
      have h1 : C < C ⊔ E := lt_of_le_of_ne le_sup_left (fun hEq => hEAne (le_antisymm
        ((le_inf ((le_sup_right : E ≤ C ⊔ E).trans (le_of_eq hEq.symm)) le_rfl).trans
          (le_of_eq hCEinf)) hAE))
      have h2 : Nat.card ↥C < Nat.card ↥(C ⊔ E) := Subgroup.card_lt_of_lt h1
      rwa [hCcard3] at h2
    have hAF : A ≤ C ⊔ E := hAC.trans le_sup_left
    have hkey : ∀ (K : Subgroup P) (hKF : K ≤ C ⊔ E) (n : ℕ),
        (Work.Higman.powSub (K.subgroupOf (C ⊔ E)) n).map (C ⊔ E).subtype
          = Work.Higman.powSub K n := by
      intro K hKF n
      rw [Work.Higman.powSub, Work.Higman.powSub, MonoidHom.map_closure]
      congr 1
      ext y
      constructor
      · rintro ⟨x, ⟨z, hz, rfl⟩, rfl⟩
        exact ⟨(z : P), Subgroup.mem_subgroupOf.mp hz, rfl⟩
      · rintro ⟨z, hz, rfl⟩
        exact ⟨(⟨z, hKF hz⟩ : ↥(C ⊔ E)) ^ n,
          ⟨⟨z, hKF hz⟩, Subgroup.mem_subgroupOf.mpr hz, rfl⟩, by simp⟩
    rcases hCEdich with hCE2 | hCE1
    · -- ## Case `[C,E] = A²`: the Chevalley–Warning bound
      have hF2 : Work.Higman.powSub (C ⊔ E) 2 ≤ Work.Higman.omega1 P := by
        have hsqce : ∀ c ∈ C, ∀ e ∈ E, (c * e) ^ 2 = ⁅e, c⁆ * c ^ 2 * e ^ 2 := by
          intro c hc e he
          have hmem : ⁅e, c⁆ ∈ Work.Higman.powSub A 2 := by
            have h1 : ⁅e, c⁆ ∈ ⁅E, C⁆ := Subgroup.commutator_mem_commutator he hc
            rw [Subgroup.commutator_comm E C] at h1
            rwa [hCE2] at h1
          have hcent' : ∀ g : P, g * ⁅e, c⁆ = ⁅e, c⁆ * g := fun g =>
            Subgroup.mem_center_iff.mp (h.omega1_le_center (htop ▸ hmem)) g
          rw [pow_two, pow_two, pow_two]
          calc c * e * (c * e) = c * (e * c) * e := by group
            _ = c * (⁅e, c⁆ * (c * e)) * e := by
                  rw [show e * c = ⁅e, c⁆ * (c * e) from by rw [commutatorElement_def]; group]
            _ = ⁅e, c⁆ * (c * (c * e)) * e := by
                  rw [show c * (⁅e, c⁆ * (c * e)) = (c * ⁅e, c⁆) * (c * e) by group,
                    hcent' c]
                  group
            _ = ⁅e, c⁆ * (c * c) * (e * e) := by group
        rw [Work.Higman.powSub, Subgroup.closure_le]
        rintro y ⟨x, hx, rfl⟩
        haveI : C.Normal := hCn
        haveI : E.Normal := hEn
        obtain ⟨c, hc, e, he, rfl⟩ := (Subgroup.mem_sup_of_normal_right (s := C) (t := E)).mp hx
        rw [hsqce c hc e he, ← htop]
        have hmem : ⁅e, c⁆ ∈ Work.Higman.powSub A 2 := by
          have h1 : ⁅e, c⁆ ∈ ⁅E, C⁆ := Subgroup.commutator_mem_commutator he hc
          rw [Subgroup.commutator_comm E C] at h1
          rwa [hCE2] at h1
        have hc2 : c ^ 2 ∈ Work.Higman.powSub A 2 := by
          rw [← hCpow2]; exact Work.Higman.pow_mem_powSub hc
        have he2 : e ^ 2 ∈ Work.Higman.powSub A 2 := by
          rw [← hE2]; exact Work.Higman.pow_mem_powSub he
        exact (Work.Higman.powSub A 2).mul_mem ((Work.Higman.powSub A 2).mul_mem hmem hc2) he2
      have hFF_le : ⁅(C ⊔ E), (C ⊔ E)⁆ ≤ Work.Higman.omega1 P := by
        have h1 : ⁅(C ⊔ E), (C ⊔ E)⁆ ≤ Work.Higman.powSub A 2 := by
          have h2 : ⁅(C ⊔ E), (C ⊔ E)⁆
              = (⁅C, C⁆ ⊔ ⁅C, E⁆) ⊔ (⁅E, C⁆ ⊔ ⁅E, E⁆) := by
            rw [Subgroup.commutator_sup_right C E (C ⊔ E),
              Subgroup.commutator_sup_left C C E, Subgroup.commutator_sup_left E C E]
          rw [h2, hCd, hCE2, Subgroup.commutator_comm E C, hCE2, hEE]
          exact sup_le (sup_le le_rfl le_rfl) (sup_le le_rfl le_rfl)
        rwa [htop] at h1
      have hcw : Nat.card ↥(C ⊔ E) ≤ (Nat.card ↥(Work.Higman.omega1 P)) ^ 3 :=
        Work.Higman.H8.card_le_cube_of_sq_le_omega1 h hOmF hF2 hFF_le
      omega
    · -- ## Case `[C,E] = A`: `↥(C ⊔ E)` is a smaller instance
      have hFF : ⁅(C ⊔ E), (C ⊔ E)⁆ = A := by
        refine le_antisymm ((Subgroup.commutator_mono le_top le_top).trans (le_of_eq hGs)) ?_
        calc A = ⁅C, E⁆ := hCE1.symm
          _ ≤ ⁅C ⊔ E, C ⊔ E⁆ := Subgroup.commutator_mono le_sup_left le_sup_right
      have hFFne : ⁅(C ⊔ E), (C ⊔ E)⁆ ≠ ⊥ := by rw [hFF]; exact hAne
      let hF : Work.Higman.IsSuzuki2Grp ↥(C ⊔ E) :=
        Work.Higman.HS.htc_isSuzuki2Grp_subgroup h hFinv hOmF hFFne
      have hFlt_card : Nat.card ↥(C ⊔ E) < Nat.card P := by
        rw [← Subgroup.card_top (G := P)]
        exact Subgroup.card_lt_of_lt hFlt
      have hxi : (hF.xi : MulAut ↥(C ⊔ E)) = Work.Higman.HS.htc_restrictAut h.xi hFinv := rfl
      have hA' : Work.Higman.IsXiAbelNormal hF (A.subgroupOf (C ⊔ E)) := by
        refine ⟨inferInstance, ?_, ?_⟩
        · rw [hxi, Work.Higman.HS.htc_map_subgroupOf_restrictAut, hAxi]
        · intro x hx y hy
          exact Subtype.ext (hAab (x : P) (Subgroup.mem_subgroupOf.mp hx) (y : P)
            (Subgroup.mem_subgroupOf.mp hy))
      have hNA' : Work.Higman.omega1 ↥(C ⊔ E) ≤ A.subgroupOf (C ⊔ E) := by
        rw [Work.Higman.HS.htc_omega1_subgroupOf_eq h hF]
        exact Subgroup.comap_mono hNA
      have hGs'' : ⁅(⊤ : Subgroup ↥(C ⊔ E)), (⊤ : Subgroup ↥(C ⊔ E))⁆
          = A.subgroupOf (C ⊔ E) := by
        apply Subgroup.map_injective (Subgroup.subtype_injective (C ⊔ E))
        rw [Subgroup.map_commutator, Work.Higman.HS.htc_map_subtype_top,
          Work.Higman.HS.htc_map_subtype_subgroupOf_eq hAF, hFF]
      have hsq' : ∀ x : ↥(C ⊔ E), x ^ 2 ∈ A.subgroupOf (C ⊔ E) := by
        intro x
        rw [Subgroup.mem_subgroupOf, Subgroup.coe_pow]
        exact hsq (x : P)
      have hA4' : Work.Higman.powSub (A.subgroupOf (C ⊔ E)) 4 = ⊥ := by
        rw [Work.Higman.HS.htc_powSub_subgroupOf_eq hAF hAab 4, hA4,
          Subgroup.bot_subgroupOf]
      have htop' : Work.Higman.powSub (A.subgroupOf (C ⊔ E)) 2
          = Work.Higman.omega1 ↥(C ⊔ E) := by
        rw [Work.Higman.HS.htc_powSub_subgroupOf_eq hAF hAab 2, htop,
          Work.Higman.HS.htc_omega1_subgroupOf_eq h hF]
      have hcard' : Nat.card ↥(A.subgroupOf (C ⊔ E))
          = (Nat.card ↥(Work.Higman.omega1 ↥(C ⊔ E))) ^ 2 := by
        rw [Work.Higman.HS.htc_card_subgroupOf_eq_card hAF,
          Work.Higman.HS.htc_omega1_subgroupOf_eq h hF,
          Work.Higman.HS.htc_card_subgroupOf_eq_card (hNA.trans hAF), hcard]
      have hCn' : (C.subgroupOf (C ⊔ E)).Normal := hCn.subgroupOf (C ⊔ E)
      have hCinv' : (C.subgroupOf (C ⊔ E)).map (hF.xi : MulAut ↥(C ⊔ E)).toMonoidHom
          = C.subgroupOf (C ⊔ E) := by
        rw [hxi, Work.Higman.HS.htc_map_subgroupOf_restrictAut, hCinv]
      have hAC' : A.subgroupOf (C ⊔ E) ≤ C.subgroupOf (C ⊔ E) := Subgroup.comap_mono hAC
      have hCA' : A.subgroupOf (C ⊔ E) ≠ C.subgroupOf (C ⊔ E) := by
        intro hh
        apply hCA
        have h1 := congrArg (fun X : Subgroup ↥(C ⊔ E) => X.map (C ⊔ E).subtype) hh
        rwa [Work.Higman.HS.htc_map_subtype_subgroupOf_eq hAF,
          Work.Higman.HS.htc_map_subtype_subgroupOf_eq le_sup_left] at h1
      have hcover' : ∀ D : Subgroup ↥(C ⊔ E), D.Normal →
          D.map (hF.xi : MulAut ↥(C ⊔ E)).toMonoidHom = D →
          A.subgroupOf (C ⊔ E) ≤ D → D ≤ C.subgroupOf (C ⊔ E) →
          D = A.subgroupOf (C ⊔ E) ∨ D = C.subgroupOf (C ⊔ E) := by
        intro D _ hDinv hAD' hDC'
        have hDinv' : D.map (Work.Higman.HS.htc_restrictAut h.xi hFinv
            : MulAut ↥(C ⊔ E)).toMonoidHom = D := hDinv
        have hDbar_xi : (D.map (C ⊔ E).subtype).map (h.xi : MulAut P).toMonoidHom
            = D.map (C ⊔ E).subtype := by
          rw [Work.Higman.HS.htc_map_xi_map_subtype h hFinv D, hDinv']
        have hDbar_n : (D.map (C ⊔ E).subtype).Normal := by
          refine Work.Higman.HS.htc_normal_of_commutator_le ?_
          calc ⁅(⊤ : Subgroup P), ⊤⁆ = A := hGs
            _ = (A.subgroupOf (C ⊔ E)).map (C ⊔ E).subtype :=
                (Work.Higman.HS.htc_map_subtype_subgroupOf_eq hAF).symm
            _ ≤ D.map (C ⊔ E).subtype := Subgroup.map_mono hAD'
        have hDbar_le_C : D.map (C ⊔ E).subtype ≤ C := by
          calc D.map (C ⊔ E).subtype ≤ (C.subgroupOf (C ⊔ E)).map (C ⊔ E).subtype :=
                Subgroup.map_mono hDC'
            _ = C := Work.Higman.HS.htc_map_subtype_subgroupOf_eq le_sup_left
        have hADbar : A ≤ D.map (C ⊔ E).subtype := by
          calc A = (A.subgroupOf (C ⊔ E)).map (C ⊔ E).subtype :=
                (Work.Higman.HS.htc_map_subtype_subgroupOf_eq hAF).symm
            _ ≤ D.map (C ⊔ E).subtype := Subgroup.map_mono hAD'
        rcases hcover (D.map (C ⊔ E).subtype) hDbar_n hDbar_xi hADbar hDbar_le_C with h | h
        · left
          have h2 := congrArg (fun X : Subgroup P => X.subgroupOf (C ⊔ E)) h
          rwa [Work.Higman.HS.htc_subgroupOf_map_subtype_eq D] at h2
        · right
          have h2 := congrArg (fun X : Subgroup P => X.subgroupOf (C ⊔ E)) h
          rwa [Work.Higman.HS.htc_subgroupOf_map_subtype_eq D] at h2
      have hCpow2' : Work.Higman.powSub (C.subgroupOf (C ⊔ E)) 2
          = Work.Higman.powSub (A.subgroupOf (C ⊔ E)) 2 := by
        apply Subgroup.map_injective (Subgroup.subtype_injective (C ⊔ E))
        rw [hkey C le_sup_left 2, hkey A hAF 2, hCpow2]
      have hCd' : ⁅C.subgroupOf (C ⊔ E), C.subgroupOf (C ⊔ E)⁆
          = Work.Higman.powSub (A.subgroupOf (C ⊔ E)) 2 := by
        apply Subgroup.map_injective (Subgroup.subtype_injective (C ⊔ E))
        rw [Subgroup.map_commutator,
          Work.Higman.HS.htc_map_subtype_subgroupOf_eq le_sup_left, hCd,
          Work.Higman.HS.htc_powSub_subgroupOf_eq hAF hAab 2,
          Work.Higman.HS.htc_map_subtype_subgroupOf_eq (hA2le.trans hAF)]
      have hCT' : ⁅C.subgroupOf (C ⊔ E), (⊤ : Subgroup ↥(C ⊔ E))⁆
          = A.subgroupOf (C ⊔ E) := by
        apply Subgroup.map_injective (Subgroup.subtype_injective (C ⊔ E))
        rw [Subgroup.map_commutator,
          Work.Higman.HS.htc_map_subtype_subgroupOf_eq le_sup_left,
          Work.Higman.HS.htc_map_subtype_top,
          Work.Higman.HS.htc_map_subtype_subgroupOf_eq hAF]
        rw [show ⁅C, C ⊔ E⁆ = A from by
          rw [Subgroup.commutator_sup_left C C E, hCd, hCE1, sup_eq_right.mpr hA2le]]
      exact hsmall hF hFlt_card (A.subgroupOf (C ⊔ E)) (C.subgroupOf (C ⊔ E)) hA' hNA' hGs''
        hsq' hA4' htop' hcard' hCn' hCinv' hAC' hCA' hcover' hCpow2' hCd' hCT'
  -- ## Step 10: `[C,E] = A`
  have hCEeq : ⁅C, E⁆ = A := by
    rcases hCEdich with h | h
    · exfalso
      have h1 : A ≤ Work.Higman.powSub A 2 ⊔ ⁅C, E⁆ := by
        have h2 : ⁅C ⊔ E, C ⊔ E⁆ ≤ Work.Higman.powSub A 2 ⊔ ⁅C, E⁆ := by
          rw [Subgroup.commutator_sup_right C E (C ⊔ E),
            Subgroup.commutator_sup_left C C E, Subgroup.commutator_sup_left E C E,
            hCd, Subgroup.commutator_comm E C, hEE]
          exact sup_le (sup_le le_sup_left le_sup_right) (sup_le le_sup_right le_sup_left)
        calc A = ⁅(⊤ : Subgroup P), ⊤⁆ := hGs.symm
          _ = ⁅C ⊔ E, C ⊔ E⁆ := by rw [hCsupE]
          _ ≤ Work.Higman.powSub A 2 ⊔ ⁅C, E⁆ := h2
      rw [h, sup_idem] at h1
      exact hAne2 (le_antisymm h1 hA2le)
    · exact h
  -- ## Step 11: `[E,A] = A²`
  have hEAeq : ⁅E, A⁆ = Work.Higman.powSub A 2 := by
    have hEA_le : ⁅E, A⁆ ≤ Work.Higman.powSub A 2 := by
      calc ⁅E, A⁆ ≤ ⁅E, E⁆ := Subgroup.commutator_mono le_rfl hAE
        _ = Work.Higman.powSub A 2 := hEE
    have hEA_inv : (⁅E, A⁆ : Subgroup P).map (h.xi : MulAut P).toMonoidHom = ⁅E, A⁆ := by
      rw [Subgroup.map_commutator, hEinv, hAxi]
    have hEA_ne : ⁅E, A⁆ ≠ ⊥ := by
      intro hb
      have hle : E ≤ A := by
        rw [← hcent]
        intro e he
        rw [Subgroup.mem_centralizer_iff]
        intro a ha
        have h1 : ⁅e, a⁆ ∈ (⊥ : Subgroup P) := by
          rw [← hb]
          exact Subgroup.commutator_mem_commutator he ha
        exact (commutatorElement_eq_one_iff_mul_comm.mp (Subgroup.mem_bot.mp h1)).symm
      exact hEAne (le_antisymm hle hAE)
    have h1 : ⁅E, A⁆ = Work.Higman.omega1 P :=
      Work.Higman.HS.eq_omega1_of_ne_bot_of_map_eq h (hEA_le.trans (le_of_eq htop))
        hEA_inv hEA_ne
    rw [h1, ← htop]
  exact ⟨E, hEn, hEinv, hAE, hEAne.symm, hEcover, hCEinf, hCsupE, hE2, hEE, hEAeq, hCEeq⟩

end Work.Higman.NSM
