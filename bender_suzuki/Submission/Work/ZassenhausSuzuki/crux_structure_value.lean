import Mathlib
import Submission.Work.ZassenhausSuzuki.frel_center
import Submission.Work.ZassenhausSuzuki.structPair_sq_fix
import Submission.Work.ZassenhausSuzuki.TitsAux
import Submission.Work.ZassenhausSuzuki.canon_relations
import Submission.Work.ZassenhausSuzuki.canon_aux
import Submission.Work.ZassenhausPSL2.ZData.dStab_fpf_on_Q
import Submission.Work.ZassenhausPSL2.Basic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

open LeanEval.GroupTheory.Defs
open Submission.Blueprint

namespace Work.ZassenhausSuzuki

/-- **Field step of the crux.** -/
theorem crux_field {K : Type*} [Field K] [CharP K 2] (θ : K ≃+* K)
    (hfix : ∀ x : K, θ x = x → x = 0 ∨ x = 1)
    {μ σ lam : K} (hμ0 : μ ≠ 0) (hμ1 : μ ≠ 1)
    (hσθσ : σ * θ σ = 1 + μ * θ μ)
    (hlam1 : lam * (1 + μ⁻¹) = 1)
    (hlam2 : lam = μ ^ 2 * σ⁻¹ + μ) : False := by
  have hμ1' : (1 : K) + μ ≠ 0 := by
    intro h
    apply hμ1
    have h2 : μ = -(1 : K) := eq_neg_of_add_eq_zero_right h
    rwa [CharTwo.neg_eq] at h2
  have hlam1' : lam * (1 + μ) = μ := by
    have h : lam * (1 + μ⁻¹) * μ = 1 * μ := by rw [hlam1]
    have h2 : (1 + μ⁻¹) * μ = 1 + μ := by
      rw [add_mul, one_mul, inv_mul_cancel₀ hμ0]; ring
    rw [mul_assoc, h2] at h
    simpa using h
  have hkey : (μ ^ 2 * σ⁻¹ + μ) * (1 + μ) = μ := by rw [← hlam2]; exact hlam1'
  have hzero : μ * μ * (σ⁻¹ * (1 + μ) + 1) = 0 := by
    have h2 : (μ ^ 2 * σ⁻¹ + μ) * (1 + μ)
        = μ ^ 2 * σ⁻¹ * (1 + μ) + μ * (1 + μ) := by ring
    rw [h2] at hkey
    have h3 : μ * (1 + μ) = μ + μ ^ 2 := by ring
    rw [h3] at hkey
    have h4 : μ * μ * (σ⁻¹ * (1 + μ) + 1) = μ ^ 2 * σ⁻¹ * (1 + μ) + μ ^ 2 := by ring
    rw [h4]
    linear_combination hkey
  have hμμ : μ * μ ≠ 0 := mul_ne_zero hμ0 hμ0
  have hsum : σ⁻¹ * (1 + μ) + 1 = 0 := by
    rcases mul_eq_zero.mp hzero with h | h
    · exact absurd h hμμ
    · exact h
  have hfinal : σ⁻¹ * (1 + μ) = 1 := by
    have h := eq_neg_of_add_eq_zero_left hsum
    rwa [CharTwo.neg_eq] at h
  have hσ0 : σ ≠ 0 := by
    intro h
    rw [h, inv_zero, zero_mul] at hfinal
    exact one_ne_zero hfinal.symm
  have hσeq : σ = 1 + μ := by
    have h := congrArg (fun z => σ * z) hfinal
    rw [← mul_assoc, mul_inv_cancel₀ hσ0, one_mul, mul_one] at h
    exact h.symm
  have hfixeq : θ μ = μ := by
    have h := hσθσ
    rw [hσeq, map_add, map_one] at h
    have h2 : (1 + μ) * (1 + θ μ) = 1 + θ μ + μ + μ * θ μ := by ring
    rw [h2] at h
    have h3 : θ μ + μ = 0 := by linear_combination h
    have h4 := eq_neg_of_add_eq_zero_left h3
    rwa [CharTwo.neg_eq] at h4
  rcases hfix μ hfixeq with h | h
  · exact hμ0 h
  · exact hμ1 h

/-- **`C.g` commutes with conjugation by `D`**: `g(d x d⁻¹) = d⁻¹ · g(x) · d`. -/
theorem canon_g_conj {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (hsplit : IsSplitRankOne H Q t) (hzass : IsZassenhaus H) (h2 : IsPGroup 2 Q)
    (C : Work.ZassenhausPSL2.Canon H Q t) (dd : twoPoint H t) (x : Q) (hx : (x : G) ≠ 1)
    (hd : (dd : G) * (x : G) * (dd : G)⁻¹ ∈ Q)
    (hd' : (dd : G)⁻¹ * ((C.g x : Q) : G) * (dd : G) ∈ Q) :
    C.g ⟨(dd : G) * (x : G) * (dd : G)⁻¹, hd⟩
      = ⟨(dd : G)⁻¹ * ((C.g x : Q) : G) * (dd : G), hd'⟩ := by
  have hxinv : ((x⁻¹ : Q) : G) ≠ 1 := by
    intro h; exact hx (by simpa using congrArg Inv.inv h)
  have hdne : ((⟨(dd : G) * (x : G) * (dd : G)⁻¹, hd⟩ : Q) : G) ≠ 1 := by
    intro hc
    have hc' : (dd : G) * (x : G) * (dd : G)⁻¹ = 1 := hc
    apply hx
    have hh : (dd : G)⁻¹ * ((dd : G) * (x : G) * (dd : G)⁻¹) * (dd : G) = (x : G) := by group
    rw [hc'] at hh
    simpa using hh.symm
  have h1 := canon_H1 hsplit C ⟨(dd : G) * (x : G) * (dd : G)⁻¹, hd⟩ hdne
  have hy : (⟨(dd : G) * (x : G) * (dd : G)⁻¹, hd⟩ : Q)⁻¹
      = ⟨(dd : G) * (x⁻¹ : G) * (dd : G)⁻¹,
          canon_D_conj_Q_mem hsplit dd x⁻¹⟩ := by
    refine Subtype.ext ?_
    simp only [Subgroup.coe_inv, Subgroup.coe_mk]
    group
  rw [hy] at h1
  have h5 := canon_H5 hsplit hzass h2 C dd (x⁻¹) hxinv
    (canon_D_conj_Q_mem hsplit dd x⁻¹)
    (by simpa using canon_D_conj_Q_mem hsplit dd⁻¹ (C.f (x⁻¹)))
  simp only [Subgroup.coe_inv] at h5
  rw [h5] at h1
  have h6 := congrArg Inv.inv h1
  simp only [inv_inv] at h6
  rw [h6]
  refine Subtype.ext ?_
  simp only [Subgroup.coe_inv, Subgroup.coe_mk]
  have h3 : ((C.f (x⁻¹) : Q) : G) = ((C.g x : Q) : G)⁻¹ :=
    congrArg Subtype.val (canon_H1 hsplit C x hx).symm
  rw [show ((dd : G)⁻¹ * ((C.f (x⁻¹) : Q) : G) * (dd : G))⁻¹
      = (dd : G)⁻¹ * (((C.f (x⁻¹) : Q) : G))⁻¹ * (dd : G) by group]
  rw [h3, inv_inv]

theorem crux_structure_value {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (hsplit : Submission.Blueprint.IsSplitRankOne H Q t)
    (hzass : Submission.Blueprint.IsZassenhaus H) (h2 : IsPGroup 2 Q)
    {m : ℕ} {θ : GaloisField 2 m ≃+* GaloisField 2 m} (hθ1 : θ ≠ 1)
    (hθodd : Odd (orderOf θ))
    (hfix : ∀ x : GaloisField 2 m, θ x = x → x = 0 ∨ x = 1)
    (e : Q ≃* Work.ZassenhausSuzuki.SzA (GaloisField 2 m) θ)
    (htorus : Work.ZassenhausSuzuki.TorusCoords (GaloisField 2 m) θ H Q t e) :
    ∀ d : G, d ∈ Submission.Blueprint.twoPoint H t → d ≠ 1 →
      ¬ ∃ d' : G, d' ∈ Submission.Blueprint.twoPoint H t ∧
        (d' * ((Work.ZassenhausSuzuki.structPair hsplit).2⁻¹ * d⁻¹
          * (Work.ZassenhausSuzuki.structPair hsplit).2 * d) * d'⁻¹
          = (Work.ZassenhausSuzuki.structPair hsplit).2) := by
  classical
  intro d hdD hdne
  rintro ⟨d', hd'D, hconj⟩
  obtain ⟨C⟩ := Work.ZassenhausPSL2.canon_exists hsplit
  have hH1 := canon_H1 hsplit C
  have hH5 := canon_H5 hsplit hzass h2 C
  have hH6 := canon_H6 hsplit hzass h2 C
  have hH7 := canon_H7 hsplit hzass h2 C
  obtain ⟨hsQ, hsord, hgQ, hstruct0⟩ := structPair_spec hsplit
  have ht2 : t * t = 1 := ht_mul_self hsplit
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  set sg : Q := ⟨(structPair hsplit).2, hgQ⟩ with hsg
  set ss : Q := ⟨(structPair hsplit).1, hsQ⟩ with hss
  have hsgG : (sg : G) = (structPair hsplit).2 := by rw [hsg]
  have hssG : (ss : G) = (structPair hsplit).1 := by rw [hss]
  have hsg_ne : (sg : G) ≠ 1 := by rw [hsgG]; exact structPair_snd_ne_one hsplit
  have hss_ne : (ss : G) ≠ 1 := by rw [hssG]; exact structPair_fst_ne_one hsplit
  have hss_sq : (ss : G) * (ss : G) = 1 := by rw [hssG]; exact structPair_fst_sq hsplit
  -- `ρ² = s`
  have hsq_gs : sg * sg = ss := by
    apply Subtype.ext
    show (sg : G) * (sg : G) = (ss : G)
    rw [hsgG, hssG]
    exact structPair_sq_fix hsplit hzass hθ1 hθodd hfix e htorus h2
  have he_sq : e sg * e sg = e ss := by rw [← map_mul, hsq_gs]
  -- `e s = (0,c)`, `c ≠ 0`
  have hss_inv : (e ss) * (e ss) = 1 := by
    have h : ss * ss = 1 := by
      apply Subtype.ext; rw [Subgroup.coe_mul, Subgroup.coe_one]; exact hss_sq
    rw [← map_mul, h, map_one]
  have hsa : (e ss).a = 0 := a_eq_zero_of_sq_eq_one θ (e ss) hss_inv
  have hsb : (e ss).b ≠ 0 := by
    intro hb
    have h1 : e ss = 1 := by ext <;> simp [hsa, hb]
    apply hss_ne
    have h2 : ss = 1 := e.injective (by rw [h1, map_one])
    rw [h2]; rfl
  -- `p := (e ρ).a ≠ 0`
  have hp : (e sg).a ≠ 0 := by
    intro hp0
    have hb : (e sg * e sg).b = (e sg).a * θ ((e sg).a) := by
      rw [SzA.mul_b, CharTwo.add_self_eq_zero, zero_add]
    have : (e ss).b = 0 := by rw [← he_sq, hb, hp0, zero_mul]
    exact hsb this
  -- torus data for `d`
  obtain ⟨μu, hμu⟩ := htorus d hdD
  have hact : ∀ x : Q, ((e.symm (SzA.hLam θ (μu : GaloisField 2 m) (e x)) : Q) : G) = d * (x : G) * d⁻¹ := by
    intro x
    obtain ⟨y, hy, hye⟩ := hμu x
    have h1 : e.symm (SzA.hLam θ (μu : GaloisField 2 m) (e x)) = y := (MulEquiv.symm_apply_eq e).mpr hye.symm
    rw [h1]; exact hy
  have hactinv : ∀ x : Q, ((e.symm (SzA.hLam θ ((μu : GaloisField 2 m)⁻¹) (e x)) : Q) : G)
      = d⁻¹ * (x : G) * d := by
    intro x
    have h := hact (e.symm (SzA.hLam θ ((μu : GaloisField 2 m)⁻¹) (e x)))
    rw [MulEquiv.apply_symm_apply] at h
    have hcomp : SzA.hLam θ (μu : GaloisField 2 m) (SzA.hLam θ ((μu : GaloisField 2 m)⁻¹) (e x)) = e x := by
      rw [← SzA.hLam_mul]
      have h1 : (μu : GaloisField 2 m) * (μu : GaloisField 2 m)⁻¹ = 1 := by simp
      rw [h1, SzA.hLam_one]
    rw [hcomp, MulEquiv.symm_apply_apply] at h
    show ((e.symm (SzA.hLam θ ((μu : GaloisField 2 m)⁻¹) (e x)) : Q) : G) = d⁻¹ * (x : G) * d
    calc ((e.symm (SzA.hLam θ ((μu : GaloisField 2 m)⁻¹) (e x)) : Q) : G)
        = d⁻¹ * (d * ((e.symm (SzA.hLam θ ((μu : GaloisField 2 m)⁻¹) (e x)) : Q) : G) * d⁻¹) * d := by
          group
      _ = d⁻¹ * (x : G) * d := by rw [← h]
  have hμne : (μu : GaloisField 2 m) ≠ 1 := by
    intro h1
    have hconj : d * (sg : G) * d⁻¹ = (sg : G) := by
      have h := hact sg
      rw [h1, SzA.hLam_one, MulEquiv.symm_apply_apply] at h
      exact h.symm
    exact hsg_ne (Work.ZassenhausPSL2.ZData.dStab_fpf_on_Q H Q t hsplit hzass d hdD hdne (sg : G) sg.2 hconj)
  have hμ0 : (μu : GaloisField 2 m) ≠ 0 := Units.ne_zero μu
  -- torus data for `d'`
  obtain ⟨lam, hlam⟩ := htorus d' hd'D
  have dact : ∀ x : Q, ((e.symm (SzA.hLam θ (lam : GaloisField 2 m) (e x)) : Q) : G)
      = d' * (x : G) * d'⁻¹ := by
    intro x
    obtain ⟨y, hy, hye⟩ := hlam x
    have h1 : e.symm (SzA.hLam θ (lam : GaloisField 2 m) (e x)) = y := (MulEquiv.symm_apply_eq e).mpr hye.symm
    rw [h1]; exact hy
  -- the element `u`
  set dI : twoPoint H t := ⟨d⁻¹, (twoPoint H t).inv_mem hdD⟩ with hdI
  have hdIG : (dI : G) = d⁻¹ := by rw [hdI]
  set x2 : Q := ⟨(dI : G) * (sg : G) * (dI : G)⁻¹, canon_D_conj_Q_mem hsplit dI sg⟩ with hx2
  have hx2G : (x2 : G) = d⁻¹ * (sg : G) * d := by
    have h1 : (x2 : G) = (dI : G) * (sg : G) * (dI : G)⁻¹ := rfl
    rw [h1, hdIG, inv_inv]
  have hx2_e : e x2 = SzA.hLam θ ((μu : GaloisField 2 m)⁻¹) (e sg) := by
    have h := hactinv sg
    have he : e.symm (SzA.hLam θ ((μu : GaloisField 2 m)⁻¹) (e sg)) = x2 :=
      Subtype.ext (by rw [h, hx2G])
    have := congrArg e he
    rw [MulEquiv.apply_symm_apply] at this
    first | exact this | exact this.symm
  set su : Q := sg⁻¹ * x2 with hsu
  have hsuG : (su : G)
      = (structPair hsplit).2⁻¹ * d⁻¹ * (structPair hsplit).2 * d := by
    rw [hsu, Subgroup.coe_mul]
    rw [show ((sg⁻¹ : Q) : G) = (sg : G)⁻¹ from rfl, hx2G, hsgG]
    group
  have hconj' : d' * (su : G) * d'⁻¹ = (sg : G) := by
    rw [hsuG, hsgG]; exact hconj
  have hsu_ne : (su : G) ≠ 1 := fun h1 => hsg_ne (by rw [← hconj', h1]; group)
  -- the a-coordinate equation
  have hlam_eq : SzA.hLam θ (lam : GaloisField 2 m) (e su) = e sg := by
    have h := dact su
    rw [hconj'] at h
    have he : e.symm (SzA.hLam θ (lam : GaloisField 2 m) (e su)) = sg := Subtype.ext h
    have := congrArg e he
    rw [MulEquiv.apply_symm_apply] at this
    first | exact this | exact this.symm
  have hcoord : (lam : GaloisField 2 m) * (e su).a = (e sg).a := by
    have := congrArg SzA.a hlam_eq
    simpa [SzA.hLam_a] using this
  have hsu_a : (e su).a = (e sg).a * (1 + (μu : GaloisField 2 m)⁻¹) := by
    rw [hsu, map_mul, map_inv, hx2_e]
    simp only [SzA.mul_a, SzA.inv_a, SzA.hLam_a, CharTwo.neg_eq]
    ring
  have hlam1 : (lam : GaloisField 2 m) * (1 + (μu : GaloisField 2 m)⁻¹) = 1 := by
    have h1 := hcoord
    rw [hsu_a] at h1
    refine mul_right_cancel₀ hp ?_
    rw [one_mul]
    linear_combination h1
  -- structure identities
  have hstruct1 : t * (ss : G) * t = (sg : G) * t * (sg : G)⁻¹ := by
    simpa only [htinv, ← hsgG, ← hssG] using hstruct0
  have hgtg : t * (sg : G) * t = (ss : G) * t * (sg : G) := by
    have h3 : (ss : G) * t = t * (sg : G) * t * (sg : G)⁻¹ := by
      have hh := congrArg (fun z => t * z) hstruct1
      have e1 : t * (t * (ss : G) * t) = (ss : G) * t := by
        calc t * (t * (ss : G) * t) = (t * t) * (ss : G) * t := by group
          _ = (ss : G) * t := by rw [ht2, one_mul]
      have e2 : t * ((sg : G) * t * (sg : G)⁻¹)
          = t * (sg : G) * t * (sg : G)⁻¹ := by group
      rw [e1, e2] at hh
      exact hh
    have h4 : (ss : G) * t * (sg : G) = t * (sg : G) * t := by
      calc (ss : G) * t * (sg : G)
          = (t * (sg : G) * t * (sg : G)⁻¹) * (sg : G) := by rw [h3]
        _ = t * (sg : G) * t := by group
    exact h4.symm
  have hgi : t * ((sg⁻¹ : Q) : G) * t = ((sg⁻¹ : Q) : G) * t * (ss : G) := by
    have hcoe : ((sg⁻¹ : Q) : G) = (sg : G)⁻¹ := rfl
    rw [hcoe]
    have h := congrArg Inv.inv hgtg
    have hL : (t * (sg : G) * t)⁻¹ = t * (sg : G)⁻¹ * t := by
      rw [mul_inv_rev, mul_inv_rev, htinv]; group
    have hR : ((ss : G) * t * (sg : G))⁻¹ = (sg : G)⁻¹ * t * (ss : G) := by
      rw [mul_inv_rev, mul_inv_rev, htinv, inv_eq_of_mul_eq_one_right hss_sq]; group
    rw [hL, hR] at h
    exact h
  have hgi_ne : ((sg⁻¹ : Q) : G) ≠ 1 := by
    intro h; exact hsg_ne (by simpa using congrArg Inv.inv h)
  have hx2_ne : (x2 : G) ≠ 1 := by
    intro hc
    apply hsg_ne
    have : (sg : G) = (d : G) * 1 * (d : G)⁻¹ := by rw [← hc, hx2G]; group
    simpa using this
  -- Canon values
  have hcu1 := Work.RankOneUniqueness.canon_unique hsplit
    (H.mul_mem (hsplit.le (C.g sg).2) (C.h sg).2.1) (hsplit.le hsQ) (C.f sg).2 sg.2
    ((C.spec sg hsg_ne).symm.trans hgtg)
  have hQD_sg : ((C.g sg : Q) : G) * ((C.h sg : twoPoint H t) : G) = (ss : G) := hcu1.1
  have hCf_sg : C.f sg = sg := Subtype.ext hcu1.2
  have hCg_sg : C.g sg = ss :=
    (canon_QD_unique hsplit (q₁ := C.g sg) (d₁ := C.h sg) (q₂ := ss) (d₂ := 1)
      (by rw [Subgroup.coe_one, mul_one]; exact hQD_sg)).1
  have hCh_sg : C.h sg = 1 :=
    (canon_QD_unique hsplit (q₁ := C.g sg) (d₁ := C.h sg) (q₂ := ss) (d₂ := 1)
      (by rw [Subgroup.coe_one, mul_one]; exact hQD_sg)).2
  have hcu2 := Work.RankOneUniqueness.canon_unique hsplit
    (H.mul_mem (hsplit.le (C.g (sg⁻¹)).2) (C.h (sg⁻¹)).2.1) (hsplit.le (sg⁻¹).2)
    (C.f (sg⁻¹)).2 ss.2 ((C.spec (sg⁻¹) hgi_ne).symm.trans hgi)
  have hQD_gi : ((C.g (sg⁻¹) : Q) : G) * ((C.h (sg⁻¹) : twoPoint H t) : G) = ((sg⁻¹ : Q) : G) :=
    hcu2.1
  have hCf_gi : C.f (sg⁻¹) = ss := Subtype.ext hcu2.2
  have hcu3 := Work.RankOneUniqueness.canon_unique hsplit
    (H.mul_mem (hsplit.le (C.g ss).2) (C.h ss).2.1) (hsplit.le hgQ)
    (C.f ss).2 (by simpa using (sg⁻¹).2) ((C.spec ss hss_ne).symm.trans hstruct1)
  have hQD_ss : ((C.g ss : Q) : G) * ((C.h ss : twoPoint H t) : G) = (sg : G) := hcu3.1
  have hCf_ss : C.f ss = sg⁻¹ := Subtype.ext (by simpa using hcu3.2)
  -- `C.g x2 = d s d⁻¹`, `C.f x2 = d g d⁻¹`, `C.h x2 = d²`
  have hCg_x2 : ((C.g x2 : Q) : G) = (d : G) * (ss : G) * (d : G)⁻¹ := by
    have h5 := canon_g_conj hsplit hzass h2 C dI sg hsg_ne
      (canon_D_conj_Q_mem hsplit dI sg) (by simpa using canon_D_conj_Q_mem hsplit dI⁻¹ (C.g sg))
    rw [hCg_sg] at h5
    refine (congrArg Subtype.val h5).trans ?_
    show (dI : G)⁻¹ * (ss : G) * (dI : G) = (d : G) * (ss : G) * (d : G)⁻¹
    rw [hdIG, inv_inv]
  have hCf_x2 : ((C.f x2 : Q) : G) = (d : G) * (sg : G) * (d : G)⁻¹ := by
    have h5 := hH5 dI sg hsg_ne (canon_D_conj_Q_mem hsplit dI sg)
      (by simpa using canon_D_conj_Q_mem hsplit dI⁻¹ (C.f sg))
    rw [hCf_sg] at h5
    refine (congrArg Subtype.val h5).trans ?_
    show (dI : G)⁻¹ * (sg : G) * (dI : G) = (d : G) * (sg : G) * (d : G)⁻¹
    rw [hdIG, inv_inv]
  have hCh_x2 : ((C.h x2 : twoPoint H t) : G) = (d : G) * (d : G) := by
    have h5 := hH6 dI sg hsg_ne (canon_D_conj_Q_mem hsplit dI sg)
    rw [hCh_sg] at h5
    refine h5.trans ?_
    show (dI : G)⁻¹ * (dI : G)⁻¹ * (1 : G) = (d : G) * (d : G)
    rw [hdIG, inv_inv]; simp
  -- e-images of the D-conjugates
  have hCg_x2_e : e (C.g x2) = SzA.hLam θ (μu : GaloisField 2 m) (e ss) := by
    have h := hact ss
    have he : e.symm (SzA.hLam θ (μu : GaloisField 2 m) (e ss)) = C.g x2 := by
      refine Subtype.ext ?_; rw [h, hCg_x2]
    have := congrArg e he
    rw [MulEquiv.apply_symm_apply] at this
    first | exact this | exact this.symm
  have hCf_x2_e : e (C.f x2) = SzA.hLam θ (μu : GaloisField 2 m) (e sg) := by
    have h := hact sg
    have he : e.symm (SzA.hLam θ (μu : GaloisField 2 m) (e sg)) = C.f x2 := by
      refine Subtype.ext ?_; rw [h, hCf_x2]
    have := congrArg e he
    rw [MulEquiv.apply_symm_apply] at this
    first | exact this | exact this.symm
  -- σ = v with `v * θ v = 1 + μ θ μ`
  have h1pw : (1 : GaloisField 2 m) + (μu : GaloisField 2 m) * θ (μu : GaloisField 2 m) ≠ 0 := by
    intro hz
    have h1 : (μu : GaloisField 2 m) * θ (μu : GaloisField 2 m) = 1 := by
      have h2 := eq_neg_of_add_eq_zero_right hz
      rwa [CharTwo.neg_eq] at h2
    exact hμne (eq_one_of_mul_map_eq_one θ hθodd hμ0 h1)
  obtain ⟨v, hv⟩ := units_mul_map_surjective θ hθodd
    (Units.mk0 ((1 : GaloisField 2 m) + (μu : GaloisField 2 m) * θ (μu : GaloisField 2 m)) h1pw)
  have hvK : (v : GaloisField 2 m) * θ (v : GaloisField 2 m) = 1 + (μu : GaloisField 2 m) * θ (μu : GaloisField 2 m) := by
    have := congrArg (fun u : (GaloisField 2 m)ˣ => (u : GaloisField 2 m)) hv
    simpa [Units.val_mul] using this
  obtain ⟨dw, hdwD, hdwact⟩ := exists_torus_action hsplit hzass htorus v
  set z : Q := ⟨(dw : G) * (ss : G) * (dw : G)⁻¹,
    canon_D_conj_Q_mem hsplit ⟨dw, hdwD⟩ ss⟩ with hz
  have hez : e z = SzA.hLam θ (v : GaloisField 2 m) (e ss) := by
    have h := hdwact ss
    have he : e.symm (SzA.hLam θ (v : GaloisField 2 m) (e ss)) = z := Subtype.ext h
    have := congrArg e he
    rw [MulEquiv.apply_symm_apply] at this
    first | exact this | exact this.symm
  -- `C.f (g⁻¹) * C.g x2 = z`
  have hdz_e : e (C.f (sg⁻¹) * C.g x2) = e z := by
    rw [map_mul, hCf_gi, hCg_x2_e, hez]
    have hss0 : e ss = (⟨0, (e ss).b⟩ : SzA (GaloisField 2 m) θ) := by ext <;> simp [hsa]
    rw [hss0]
    ext
    · simp [SzA.mul_a, SzA.hLam_a]
    · simp only [SzA.mul_b, SzA.hLam_b, zero_mul, zero_add, map_zero]
      rw [hvK]; ring
  have hWeq : C.f (sg⁻¹) * C.g x2 = z := e.injective hdz_e
  -- `e (C.f z) = h_{v⁻¹}(e g⁻¹)`
  have hCf_z_G : ((C.f z : Q) : G) = (dw : G)⁻¹ * ((sg⁻¹ : Q) : G) * (dw : G) := by
    have h5 := hH5 ⟨dw, hdwD⟩ ss hss_ne (canon_D_conj_Q_mem hsplit ⟨dw, hdwD⟩ ss)
      (by simpa using canon_D_conj_Q_mem hsplit ⟨dw, hdwD⟩⁻¹ (C.f ss))
    rw [hCf_ss] at h5
    simpa using (congrArg Subtype.val h5)
  have hdwinv : ∀ x : Q, ((e.symm (SzA.hLam θ ((v : GaloisField 2 m)⁻¹) (e x)) : Q) : G)
      = (dw : G)⁻¹ * (x : G) * (dw : G) := by
    intro x
    have h := hdwact (e.symm (SzA.hLam θ ((v : GaloisField 2 m)⁻¹) (e x)))
    rw [MulEquiv.apply_symm_apply] at h
    have hcomp : SzA.hLam θ (v : GaloisField 2 m) (SzA.hLam θ ((v : GaloisField 2 m)⁻¹) (e x)) = e x := by
      rw [← SzA.hLam_mul]
      have h1 : (v : GaloisField 2 m) * (v : GaloisField 2 m)⁻¹ = 1 := by simp
      rw [h1, SzA.hLam_one]
    rw [hcomp, MulEquiv.symm_apply_apply] at h
    show ((e.symm (SzA.hLam θ ((v : GaloisField 2 m)⁻¹) (e x)) : Q) : G) = (dw : G)⁻¹ * (x : G) * (dw : G)
    calc ((e.symm (SzA.hLam θ ((v : GaloisField 2 m)⁻¹) (e x)) : Q) : G)
        = (dw : G)⁻¹ * ((dw : G) * ((e.symm (SzA.hLam θ ((v : GaloisField 2 m)⁻¹) (e x)) : Q) : G)
            * (dw : G)⁻¹) * (dw : G) := by group
      _ = (dw : G)⁻¹ * (x : G) * (dw : G) := by rw [← h]
  have hCf_z_e : e (C.f z) = SzA.hLam θ ((v : GaloisField 2 m)⁻¹) (e (sg⁻¹)) := by
    have he : e.symm (SzA.hLam θ ((v : GaloisField 2 m)⁻¹) (e (sg⁻¹))) = C.f z := by
      refine Subtype.ext ?_
      rw [hdwinv (sg⁻¹), hCf_z_G]
    have := congrArg e he
    rw [MulEquiv.apply_symm_apply] at this
    first | exact this | exact this.symm
  have hCf_z_a : (e (C.f z)).a = (v : GaloisField 2 m)⁻¹ * (e sg).a := by
    rw [hCf_z_e, SzA.hLam_a]
    congr 1
    simp [SzA.inv_a, CharTwo.neg_eq]
  -- `C.f su` via the product relation
  have h7 := hH7 (sg⁻¹) x2 hgi_ne hx2_ne hsu_ne
  rw [← hsu, hCh_x2, hWeq, hCf_x2] at h7
  -- Step C, a-coordinate
  set A1 : Q := ⟨(d : G) * ((C.f z : Q) : G) * (d : G)⁻¹,
    canon_D_conj_Q_mem hsplit ⟨d, hdD⟩ (C.f z)⟩ with hA1
  set A2 : Q := ⟨(d : G) * (A1 : G) * (d : G)⁻¹,
    canon_D_conj_Q_mem hsplit ⟨d, hdD⟩ A1⟩ with hA2
  have hA1_e : e A1 = SzA.hLam θ (μu : GaloisField 2 m) (e (C.f z)) := by
    have h := hact (C.f z)
    have he : e.symm (SzA.hLam θ (μu : GaloisField 2 m) (e (C.f z))) = A1 := by
      refine Subtype.ext ?_; rw [h]
    have := congrArg e he
    rw [MulEquiv.apply_symm_apply] at this
    first | exact this | exact this.symm
  have hA2_e : e A2 = SzA.hLam θ (μu : GaloisField 2 m) (e A1) := by
    have h := hact A1
    have he : e.symm (SzA.hLam θ (μu : GaloisField 2 m) (e A1)) = A2 := by
      refine Subtype.ext ?_; rw [h]
    have := congrArg e he
    rw [MulEquiv.apply_symm_apply] at this
    first | exact this | exact this.symm
  have hA_eq : A2 * (C.f x2) = C.f su := by
    apply Subtype.ext
    show ((A2 : Q) : G) * ((C.f x2 : Q) : G) = ((C.f su : Q) : G)
    rw [hA2, hA1, hCf_x2]
    rw [h7]
    group
  have hCfsu_C : (e (C.f su)).a
      = (e sg).a * ((μu : GaloisField 2 m) ^ 2 * (v : GaloisField 2 m)⁻¹ + (μu : GaloisField 2 m)) := by
    rw [← hA_eq, map_mul, hA2_e, hA1_e, hCf_x2_e]
    simp only [SzA.mul_a, SzA.hLam_a]
    rw [hCf_z_a]
    ring
  -- Step B, a-coordinate
  have hd_su : (⟨(d' : G) * (su : G) * (d' : G)⁻¹,
      canon_D_conj_Q_mem hsplit ⟨d', hd'D⟩ su⟩ : Q) = sg := Subtype.ext hconj'
  have hCf_su_G : ((C.f su : Q) : G) = (d' : G) * (sg : G) * (d' : G)⁻¹ := by
    have h5 := hH5 ⟨d', hd'D⟩ su hsu_ne (canon_D_conj_Q_mem hsplit ⟨d', hd'D⟩ su)
      (by simpa using canon_D_conj_Q_mem hsplit ⟨d', hd'D⟩⁻¹ (C.f su))
    rw [hd_su, hCf_sg] at h5
    have h6 : (sg : G) = (d' : G)⁻¹ * ((C.f su : Q) : G) * (d' : G) := by
      simpa using (congrArg Subtype.val h5)
    calc ((C.f su : Q) : G)
        = (d' : G) * ((d' : G)⁻¹ * ((C.f su : Q) : G) * (d' : G)) * (d' : G)⁻¹ := by group
      _ = (d' : G) * (sg : G) * (d' : G)⁻¹ := by rw [← h6]
  have hCf_su_e : e (C.f su) = SzA.hLam θ (lam : GaloisField 2 m) (e sg) := by
    have h := dact sg
    have he : e.symm (SzA.hLam θ (lam : GaloisField 2 m) (e sg)) = C.f su := by
      refine Subtype.ext ?_; rw [h, hCf_su_G]
    have := congrArg e he
    rw [MulEquiv.apply_symm_apply] at this
    first | exact this | exact this.symm
  have hB : (e (C.f su)).a = (lam : GaloisField 2 m) * (e sg).a := by
    rw [hCf_su_e]; simp [SzA.hLam_a]
  -- conclusion
  have hlam2 : (lam : GaloisField 2 m) = (μu : GaloisField 2 m) ^ 2 * (v : GaloisField 2 m)⁻¹ + (μu : GaloisField 2 m) := by
    have h2 : (lam : GaloisField 2 m) * (e sg).a
        = ((μu : GaloisField 2 m) ^ 2 * (v : GaloisField 2 m)⁻¹ + (μu : GaloisField 2 m)) * (e sg).a := by
      rw [← hB, hCfsu_C]; ring
    exact mul_right_cancel₀ hp h2
  exact crux_field θ hfix hμ0 hμne hvK hlam1 hlam2

end Work.ZassenhausSuzuki
