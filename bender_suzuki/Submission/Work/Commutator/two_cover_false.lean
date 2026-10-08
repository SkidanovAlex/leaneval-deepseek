import Mathlib
import Submission.Work.Higman.SuzukiMaximal
import Submission.Work.Higman.H8.c4_resonance_false
import Submission.Work.Higman.H8.c4_comm_A_top
import Submission.Work.Higman.C4Cover.c4_cover_card_eq_cube
import Submission.Work.Higman.H8.c4_sq_a2_card_quot
import Submission.Work.Commutator.counting_hU_false
import Submission.Work.Commutator.two_cover_psi_form_sq
import Submission.Work.Commutator.two_cover_ce_pairing
import Submission.Work.Commutator.two_cover_relations

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000

open scoped commutatorElement

namespace Work.Commutator

theorem two_cover_false {P : Type} [Group P] [Finite P]
    (h : Work.Higman.IsSuzuki2Grp P) {A C E : Subgroup P}
    (hA : Work.Higman.IsXiAbelNormal h A)
    (hmax : ∀ B : Subgroup P, Work.Higman.IsXiAbelNormal h B → A ≤ B → B = A)
    (hNA : Work.Higman.omega1 P ≤ A)
    (hGs : ⁅(⊤ : Subgroup P), ⊤⁆ = A)
    (hsq : ∀ x : P, x ^ 2 ∈ A)
    (hA4 : Work.Higman.powSub A 4 = ⊥)
    (htop : Work.Higman.powSub A 2 = Work.Higman.omega1 P)
    (hcard : Nat.card ↥A = (Nat.card ↥(Work.Higman.omega1 P)) ^ 2)
    (hcent : Subgroup.centralizer (A : Set P) = A)
    (hCn : C.Normal) (hEn : E.Normal)
    (hCinv : C.map (h.xi : MulAut P).toMonoidHom = C)
    (hEinv : E.map (h.xi : MulAut P).toMonoidHom = E)
    (hAC : A ≤ C) (hAE : A ≤ E) (hCA : A ≠ C) (hEA : A ≠ E)
    (hCcover : ∀ D : Subgroup P, D.Normal → D.map (h.xi : MulAut P).toMonoidHom = D →
      A ≤ D → D ≤ C → D = A ∨ D = C)
    (hEcover : ∀ D : Subgroup P, D.Normal → D.map (h.xi : MulAut P).toMonoidHom = D →
      A ≤ D → D ≤ E → D = A ∨ D = E)
    (hCd : ⁅C, C⁆ = Work.Higman.powSub A 2) (hEd : ⁅E, E⁆ = Work.Higman.powSub A 2)
    (hCpow2 : Work.Higman.powSub C 2 = Work.Higman.powSub A 2)
    (hEpow2 : Work.Higman.powSub E 2 = Work.Higman.powSub A 2)
    (hCAd : ⁅C, A⁆ = Work.Higman.powSub A 2) (hEAd : ⁅E, A⁆ = Work.Higman.powSub A 2)
    (hCE : C ⊓ E = A) (hCEsup : C ⊔ E = ⊤) :
    False := by
  classical
  haveI hAn : A.Normal := hA.normal
  haveI hN1 : ((Work.Higman.powSub A 2).subgroupOf A).Normal :=
    (Work.Higman.powSub_normal hAn 2).subgroupOf A
  haveI hN2C : (A.subgroupOf C).Normal := hAn.subgroupOf C
  haveI hN2E : (A.subgroupOf E).Normal := hAn.subgroupOf E
  -- ## The two-cover relations
  obtain ⟨_hcommA, _honeC, _honeE, hrelC, _hrelE⟩ :=
    two_cover_relations (h := h) (A := A) (C := C) (E := E) hA hNA hGs hsq hA4 htop hcard
      hCn hEn hCinv hEinv hAC hAE hCcover hEcover hCd hEd hCpow2 hEpow2 hCAd hEAd hCE hCEsup
  -- ## Cardinalities of the two covers
  have hACA : C ≠ A := fun hh => hCA hh.symm
  have hEAE : E ≠ A := fun hh => hEA hh.symm
  have hPhiC : Work.Higman.powSub C 2 ⊔ ⁅C, C⁆ = Work.Higman.powSub A 2 := by
    rw [hCpow2, hCd, sup_idem]
  have hPhiE : Work.Higman.powSub E 2 ⊔ ⁅E, E⁆ = Work.Higman.powSub A 2 := by
    rw [hEpow2, hEd, sup_idem]
  have hAD2C : ⁅A, C⁆ = Work.Higman.powSub A 2 := by
    rw [Subgroup.commutator_comm, hCAd]
  have hAD2E : ⁅A, E⁆ = Work.Higman.powSub A 2 := by
    rw [Subgroup.commutator_comm, hEAd]
  have hquotC : Nat.card (↥C ⧸ (A.subgroupOf C)) = Nat.card ↥(Work.Higman.omega1 P) :=
    Work.Higman.H8.c4_sq_a2_card_quot h hA hGs hNA htop hcent hCn hCinv hAC hACA hCd hPhiC
      hCcover hAD2C
  have hquotE : Nat.card (↥E ⧸ (A.subgroupOf E)) = Nat.card ↥(Work.Higman.omega1 P) :=
    Work.Higman.H8.c4_sq_a2_card_quot h hA hGs hNA htop hcent hEn hEinv hAE hEAE hEd hPhiE
      hEcover hAD2E
  have hcardC : Nat.card ↥C = (Nat.card ↥(Work.Higman.omega1 P)) ^ 3 := by
    have h1 : Nat.card ↥C = Nat.card (↥C ⧸ (A.subgroupOf C)) * Nat.card ↥(A.subgroupOf C) :=
      Subgroup.card_eq_card_quotient_mul_card_subgroup (A.subgroupOf C)
    have h2 : Nat.card ↥(A.subgroupOf C) = Nat.card ↥A :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAC).toEquiv
    rw [h1, hquotC, h2, hcard]; ring
  have hcardE : Nat.card ↥E = (Nat.card ↥(Work.Higman.omega1 P)) ^ 3 := by
    have h1 : Nat.card ↥E = Nat.card (↥E ⧸ (A.subgroupOf E)) * Nat.card ↥(A.subgroupOf E) :=
      Subgroup.card_eq_card_quotient_mul_card_subgroup (A.subgroupOf E)
    have h2 : Nat.card ↥(A.subgroupOf E) = Nat.card ↥A :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAE).toEquiv
    rw [h1, hquotE, h2, hcard]; ring
  -- ## Frobenius/field data for the cover `C`
  obtain ⟨n, ν, ζ, k, φC, νq, βC, hn2, _hνord, _hk, hζadd, _hζmul, hβdef, hφker, hform,
    hφadd, hνqsq⟩ :=
    two_cover_psi_form_sq (h := h) (A := A) (D := C) hA hNA hGs hsq htop hcard hcent hCn
      hCinv hAC hCA hCcover hCd hcardC
  have hq_n : Nat.card ↥(Work.Higman.omega1 P) = 2 ^ n := by
    rw [← Nat.card_congr ζ]
    exact Work.Higman.H8.card_galois (by omega)
  -- ## Frobenius/field data for the cover `E`
  obtain ⟨nE, _νE, ζE, _kE, φE, _νqE, _βE, _hnE2, _hνEord, _hkE, _hζEadd, _hζEmul, _hβEdef,
    hφEker, _hφEform, hφEadd, _hνqEsq⟩ :=
    two_cover_psi_form_sq (h := h) (A := A) (D := E) hA hNA hGs hsq htop hcard hcent hEn
      hEinv hAE hEA hEcover hEd hcardE
  have hq_nE : Nat.card ↥(Work.Higman.omega1 P) = 2 ^ nE := by
    rw [← Nat.card_congr ζE]
    exact Work.Higman.H8.card_galois (by omega)
  have hnE_eq : nE = n := by
    refine Nat.pow_right_injective (a := 2) (by norm_num) ?_
    change (2 : ℕ) ^ nE = (2 : ℕ) ^ n
    rw [← hq_nE, hq_n]
  subst nE
  -- ## The commutator pairing `C/A × E/A → A/A²`
  obtain ⟨B, hBdef, hBadd1, hBadd2, hBnd1, hBnd2⟩ :=
    two_cover_ce_pairing (h := h) (A := A) (C := C) (E := E) hA hNA hGs hsq hA4 htop hcard
      hcent hCn hEn hCinv hEinv hAC hAE hCcover hEcover hCd hEd hCAd hEAd hCE hCEsup
  -- ## Elementary facts about `ζ`
  have hζ0 : ζ (0 : GaloisField 2 n) = 1 := by
    have h1 := hζadd 0 0
    rw [add_zero] at h1
    have h2 := congrArg (fun t => (ζ 0)⁻¹ * t) h1
    simp only [← mul_assoc, inv_mul_cancel, one_mul] at h2
    exact h2.symm
  have hζsymm_mul : ∀ a b : ↥(Work.Higman.omega1 P),
      ζ.symm (a * b) = ζ.symm a + ζ.symm b := by
    intro a b
    apply ζ.injective
    rw [Equiv.apply_symm_apply, hζadd, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  have hζsymm_one : ζ.symm (1 : ↥(Work.Higman.omega1 P)) = 0 := by
    rw [← hζ0, Equiv.symm_apply_apply]
  -- ## The `W`-coordinate `ψ = ζ⁻¹ ∘ νq`, with `νq` the squaring map
  let ψ : (↥A ⧸ (Work.Higman.powSub A 2).subgroupOf A) → GaloisField 2 n :=
    fun q => ζ.symm (νq q)
  have hψadd : ∀ q q', ψ (q * q') = ψ q + ψ q' := by
    intro q q'
    show ζ.symm (νq (q * q')) = ζ.symm (νq q) + ζ.symm (νq q')
    rw [map_mul, hζsymm_mul]
  have hψone : ψ 1 = 0 := by
    show ζ.symm (νq 1) = 0
    rw [map_one, hζsymm_one]
  have hψmem : ∀ q, ψ q = 0 ↔ q = 1 := by
    intro q
    constructor
    · intro hq
      apply νq.injective
      rw [map_one]
      have h1 := congrArg ζ hq
      rwa [Equiv.apply_symm_apply, hζ0] at h1
    · intro hq
      rw [hq, hψone]
  -- ## `φC` and `φE` are bijections
  have hφC_one : φC (1 : (↥C ⧸ (A.subgroupOf C))) = 0 := (hφker 1).mpr rfl
  have hφC_inv : ∀ x : (↥C ⧸ (A.subgroupOf C)), φC x⁻¹ = -φC x := by
    intro x
    have h1 := hφadd x x⁻¹
    rw [mul_inv_cancel, hφC_one] at h1
    rw [eq_neg_iff_add_eq_zero, add_comm]
    exact h1.symm
  have hφC_inj : Function.Injective φC := by
    intro x y hxy
    have h1 : φC (x * y⁻¹) = 0 := by
      rw [hφadd x y⁻¹, hφC_inv y, hxy, add_neg_cancel]
    exact mul_inv_eq_one.mp ((hφker (x * y⁻¹)).mp h1)
  have hφE_one : φE (1 : (↥E ⧸ (A.subgroupOf E))) = 0 := (hφEker 1).mpr rfl
  have hφE_inv : ∀ x : (↥E ⧸ (A.subgroupOf E)), φE x⁻¹ = -φE x := by
    intro x
    have h1 := hφEadd x x⁻¹
    rw [mul_inv_cancel, hφE_one] at h1
    rw [eq_neg_iff_add_eq_zero, add_comm]
    exact h1.symm
  have hφE_inj : Function.Injective φE := by
    intro x y hxy
    have h1 : φE (x * y⁻¹) = 0 := by
      rw [hφEadd x y⁻¹, hφE_inv y, hxy, add_neg_cancel]
    exact mul_inv_eq_one.mp ((hφEker (x * y⁻¹)).mp h1)
  haveI hFgF : Fintype (GaloisField 2 n) := Fintype.ofFinite _
  haveI hFgC : Fintype (↥C ⧸ (A.subgroupOf C)) := Fintype.ofFinite _
  haveI hFgE : Fintype (↥E ⧸ (A.subgroupOf E)) := Fintype.ofFinite _
  have hcardGF : Fintype.card (GaloisField 2 n) = 2 ^ n := by
    rw [← Nat.card_eq_fintype_card, Work.Higman.H8.card_galois (by omega)]
  have hφC_surj : Function.Surjective φC := by
    have hc : Fintype.card (↥C ⧸ (A.subgroupOf C)) = Fintype.card (GaloisField 2 n) := by
      rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hquotC, hq_n,
        ← Work.Higman.H8.card_galois (by omega)]
    exact hφC_inj.surjective_of_finite (Fintype.equivOfCardEq hc)
  have hφE_surj : Function.Surjective φE := by
    have hc : Fintype.card (↥E ⧸ (A.subgroupOf E)) = Fintype.card (GaloisField 2 n) := by
      rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hquotE, hq_n,
        ← Work.Higman.H8.card_galois (by omega)]
    exact hφE_inj.surjective_of_finite (Fintype.equivOfCardEq hc)
  let eC : (↥C ⧸ (A.subgroupOf C)) ≃ GaloisField 2 n := Equiv.ofBijective φC ⟨hφC_inj, hφC_surj⟩
  have heC : ∀ x, (eC x : GaloisField 2 n) = φC x := fun x => rfl
  let eE : (↥E ⧸ (A.subgroupOf E)) ≃ GaloisField 2 n := Equiv.ofBijective φE ⟨hφE_inj, hφE_surj⟩
  have heE : ∀ x, (eE x : GaloisField 2 n) = φE x := fun x => rfl
  have heC_symm_add : ∀ u u' : GaloisField 2 n, eC.symm (u + u') = eC.symm u * eC.symm u' := by
    intro u u'
    apply eC.injective
    rw [Equiv.apply_symm_apply, heC, hφadd]
    rw [show φC (eC.symm u) = u from by rw [← heC, Equiv.apply_symm_apply],
      show φC (eC.symm u') = u' from by rw [← heC, Equiv.apply_symm_apply]]
  have heE_symm_add : ∀ u u' : GaloisField 2 n, eE.symm (u + u') = eE.symm u * eE.symm u' := by
    intro u u'
    apply eE.injective
    rw [Equiv.apply_symm_apply, heE, hφEadd]
    rw [show φE (eE.symm u) = u from by rw [← heE, Equiv.apply_symm_apply],
      show φE (eE.symm u') = u' from by rw [← heE, Equiv.apply_symm_apply]]
  -- ## The coordinate pairing `b u v = ψ (B (eC.symm u) (eE.symm v))`
  let b : GaloisField 2 n → GaloisField 2 n → GaloisField 2 n :=
    fun u v => ψ (B (eC.symm u) (eE.symm v))
  have hb1 : ∀ u u' v : GaloisField 2 n, b (u + u') v = b u v + b u' v := by
    intro u u' v
    show ψ (B (eC.symm (u + u')) (eE.symm v))
      = ψ (B (eC.symm u) (eE.symm v)) + ψ (B (eC.symm u') (eE.symm v))
    rw [heC_symm_add u u', hBadd1, hψadd]
  have hb2 : ∀ u v v' : GaloisField 2 n, b u (v + v') = b u v + b u v' := by
    intro u v v'
    show ψ (B (eC.symm u) (eE.symm (v + v')))
      = ψ (B (eC.symm u) (eE.symm v)) + ψ (B (eC.symm u) (eE.symm v'))
    rw [heE_symm_add v v', hBadd2, hψadd]
  have heC_one : eC 1 = 0 := by rw [heC]; exact hφC_one
  have heE_one : eE 1 = 0 := by rw [heE]; exact hφE_one
  have hdu : ∀ u : GaloisField 2 n, u ≠ 0 → ∃ v : GaloisField 2 n, b u v ≠ 0 := by
    intro u hu
    have hx1 : eC.symm u ≠ 1 := by
      intro h1
      have h2 : u = eC 1 := by rw [← h1, Equiv.apply_symm_apply]
      exact hu (by rw [h2, heC_one])
    obtain ⟨y, hy⟩ := hBnd1 (eC.symm u) hx1
    refine ⟨eE y, ?_⟩
    show ψ (B (eC.symm u) (eE.symm (eE y))) ≠ 0
    rw [Equiv.symm_apply_apply]
    intro h0
    exact hy ((hψmem _).mp h0)
  have hdv : ∀ v : GaloisField 2 n, v ≠ 0 → ∃ u : GaloisField 2 n, b u v ≠ 0 := by
    intro v hv
    have hy1 : eE.symm v ≠ 1 := by
      intro h1
      have h2 : v = eE 1 := by rw [← h1, Equiv.apply_symm_apply]
      exact hv (by rw [h2, heE_one])
    obtain ⟨x, hx⟩ := hBnd2 (eE.symm v) hy1
    refine ⟨eC x, ?_⟩
    show ψ (B (eC.symm (eC x)) (eE.symm v)) ≠ 0
    rw [Equiv.symm_apply_apply]
    intro h0
    exact hx ((hψmem _).mp h0)
  -- ## The Frobenius-component relation `u * (b u v)^(2^k) = b u v`
  have hU : ∀ u v : GaloisField 2 n, id u * (b u v) ^ (2 ^ k) = 1 * b u v := by
    intro u v
    obtain ⟨c, hc⟩ := QuotientGroup.mk_surjective (eC.symm u)
    obtain ⟨e, he⟩ := QuotientGroup.mk_surjective (eE.symm v)
    have hmem : (c : P) * (e : P) * (c : P)⁻¹ * (e : P)⁻¹ ∈ A := by
      have h1 : ⁅(c : P), (e : P)⁆ ∈ ⁅(⊤ : Subgroup P), ⊤⁆ :=
        Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)
      rwa [hGs] at h1
    let z : ↥A := ⟨(c : P) * (e : P) * (c : P)⁻¹ * (e : P)⁻¹, hmem⟩
    have hzP : (z : P) = (c : P) * (e : P) * (c : P)⁻¹ * (e : P)⁻¹ := rfl
    have hdiag : (z : P) * (c : P) * (z : P)⁻¹ * (c : P)⁻¹ = (z : P) ^ 2 := by
      rw [hzP]
      exact hrelC (c : P) c.2 (e : P) e.2
    have hβeq : βC (QuotientGroup.mk z) (QuotientGroup.mk c) = νq (QuotientGroup.mk z) := by
      apply Subtype.ext
      rw [hβdef z c, hνqsq z]
      exact hdiag
    have hBval : B (eC.symm u) (eE.symm v) = QuotientGroup.mk z := by
      rw [← hc, ← he]
      exact hBdef c e z hzP
    have hφC_mk : φC (QuotientGroup.mk c) = u := by
      rw [hc, ← heC, Equiv.apply_symm_apply]
    have hbuv : b u v = ζ.symm (νq (QuotientGroup.mk z)) := by
      show ψ (B (eC.symm u) (eE.symm v)) = ζ.symm (νq (QuotientGroup.mk z))
      rw [hBval]
    have hrel := hform (QuotientGroup.mk z) (QuotientGroup.mk c)
    rw [hβeq] at hrel
    rw [hφC_mk, ← hbuv] at hrel
    change u * (b u v) ^ (2 ^ k) = 1 * b u v
    rw [one_mul, ← hrel]
  -- ## Contradiction
  exact counting_hU_false hn2 hcardGF (1 : GaloisField 2 n) one_ne_zero b hb1 hb2 id
    (fun _ _ => rfl) hdu hdv hU

end Work.Commutator
