import Mathlib
import Submission.Work.PSU3.Defs
import Submission.Work.ThmF.Setup
import Submission.Work.PSU3.StageA.coarseFrame_defs
import Submission.Work.PSU3.StageA.caseC_setup
import Submission.Work.PSU3.StageA.caseC_phi_rho_data
import Submission.Work.PSU3.StageA.singer_data
import Submission.Work.PSU3.StageA.singer_frame_data
import Submission.Work.PSU3.StageA.nm_extend

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

namespace Work.PSU3.StageA

open LeanEval.GroupTheory.Defs
open Submission.Blueprint

/-! Finite-field / Singer-cycle input used by `caseC_frame_core` (proved in
`Submission.Work.PSU3.StageA.singer_frame_data`). -/

section Setup

variable {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G} {n : ℕ}

/-- `ζ` commutes with every element of `Ksub H t`: `ζ ∈ W = C_D(Kset)` and `Ksub = ⟨Kset⟩`. -/
theorem zeta_comm_Ksub (hS : Work.PSU3.PSU3Hyp H Q t) {ζ : G} (hζ : ζ ∈ Work.ThmF.W H t) :
    ∀ k ∈ Work.ThmF.Ksub H t, ζ * k = k * ζ := by
  have hζc : ζ ∈ Subgroup.centralizer (Work.ThmF.Kset H t) := (Subgroup.mem_inf.mp hζ).2
  have hle : Work.ThmF.Ksub H t ≤ Subgroup.centralizer ({ζ} : Set G) := by
    rw [Work.ThmF.Ksub]
    refine (Subgroup.closure_le _).mpr ?_
    intro x hx
    exact Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hζc x hx)
  intro k hk
  exact (Subgroup.mem_centralizer_singleton_iff.mp (hle hk)).symm

/-- The intersection `Ksub H t ∩ ⟨ζ⟩` is trivial (case `c`). -/
theorem Ksub_inf_zpowers_eq_bot (hS : Work.PSU3.PSU3Hyp H Q t)
    (hC4 : Submission.Blueprint.ChIIFourProp) (hWne : Work.ThmF.W H t ≠ ⊥)
    {ζ : G} (hζ : ζ ∈ Work.ThmF.W H t) (hζodd : Odd (orderOf ζ)) :
    Work.ThmF.Ksub H t ⊓ Subgroup.zpowers ζ = ⊥ := by
  refine le_antisymm ?_ bot_le
  intro x hx
  rw [Subgroup.mem_inf] at hx
  obtain ⟨hxK, hxz⟩ := hx
  have hxKset : x ∈ Work.ThmF.Kset H t := (caseC_Ksub_cyc hS hC4 hWne).1 ▸ hxK
  have hxinv : t * x * t⁻¹ = x⁻¹ := hxKset.2
  have hxt : t * x * t⁻¹ = x := by
    obtain ⟨j, hj⟩ := pow_eq_of_mem_zpowers (orderOf_pos ζ) hxz
    rw [← hj]
    have hζt : t * ζ * t⁻¹ = ζ := by
      have h := Subgroup.mem_centralizer_singleton_iff.mp
        (Subgroup.mem_inf.mp (Work.ThmF.W_le_centD H t hζ)).2
      rw [← h, mul_assoc, mul_inv_cancel, mul_one]
    rw [show t * ζ ^ j * t⁻¹ = (t * ζ * t⁻¹) ^ j from by
      have := map_pow (MulAut.conj t).toMonoidHom ζ j
      simpa [MulAut.conj_apply] using this]
    rw [hζt]
  have hx2 : x * x = 1 := by
    have h : x = x⁻¹ := by
      calc x = t * x * t⁻¹ := hxt.symm
        _ = x⁻¹ := hxinv
    exact mul_eq_one_iff_eq_inv.mpr h
  have hdvd : orderOf x ∣ orderOf ζ := by
    obtain ⟨j, hj⟩ := pow_eq_of_mem_zpowers (orderOf_pos ζ) hxz
    rw [← hj]
    exact orderOf_pow_dvd j
  have hdvd2 : orderOf x ∣ 2 := by
    rw [orderOf_dvd_iff_pow_eq_one, pow_two]; exact hx2
  refine Subgroup.mem_bot.mpr (orderOf_eq_one_iff.mp ?_)
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd2 with h | h
  · exact h
  · exfalso
    rw [h] at hdvd
    exact (Nat.not_even_iff_odd.mpr hζodd) (even_iff_two_dvd.mpr hdvd)

end Setup

theorem caseC_frame_core {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G} {n : ℕ}
    (hS : Work.PSU3.PSU3Hyp H Q t) (hC4 : Submission.Blueprint.ChIIFourProp)
    (D : Work.PSU3.StageA.CaseCModuleData H Q t)
    (hn : 2 ≤ n) (hcard : Nat.card ↥(Work.ThmF.Q0sub H) = 2 ^ n)
    (hZ : ∀ x : ↥Q, (x : G) ∈ Work.ThmF.Q0sub H ↔ x * x = 1)
    (hW : ∀ w ∈ Work.ThmF.W H t, w ≠ 1 → ∀ x ∈ Q, w * x = x * w →
      x ∈ Work.ThmF.Q0sub H)
    {s : G} (hs : s ∈ Q) (hs2 : orderOf s = 2) (hst : t * s * t = s * t * s)
    {ζ : G} (hζ : ζ ∈ Work.ThmF.W H t) (hζ1 : ζ ≠ 1)
    (hζd : orderOf ζ ∣ Nat.card ↥(Work.ThmF.Q0sub H) + 1)
    (hζf : ∀ x : ↥Q, ζ⁻¹ * (x : G) * ζ * (x : G)⁻¹ ∈ Work.ThmF.Q0sub H →
      (x : G) ∈ Work.ThmF.Q0sub H) :
    ∃ fr : Work.PSU3.CoarseFrame H Q t n, fr.zc 1 = s ∧ (fr.ζ : G) = ζ := by
  classical
  have hsplit : IsSplitRankOne H Q t := D.hsplit
  have hWne : Work.ThmF.W H t ≠ ⊥ := caseC_W_ne_bot (Q := Q) hζ hζ1
  have hKset_eq : (Work.ThmF.Ksub H t : Set G) = Work.ThmF.Kset H t :=
    (caseC_Ksub_cyc hS hC4 hWne).1
  have hn1 : 1 ≤ n := by omega
  have hζodd : Odd (orderOf ζ) := by
    have h2n : Even (2 ^ n) := even_iff_two_dvd.mpr (dvd_pow_self 2 (by omega))
    have hodd1 : Odd (2 ^ n + 1) := h2n.add_one
    exact Odd.of_dvd_nat hodd1 (by rw [← hcard]; exact hζd)
  letI : Field D.F := D.instField
  letI : Fintype D.F := D.instFintype
  have hcardF : Nat.card D.F = 2 ^ n := by rw [D.cardF, hcard]
  haveI : CharP D.F 2 := by
    have h2 : Fintype.card D.F % 2 = 0 := by
      rw [← Nat.card_eq_fintype_card, hcardF]
      exact Nat.dvd_iff_mod_eq_zero.mp (dvd_pow_self 2 (by omega))
    exact ringChar.of_eq ((FiniteField.even_card_iff_char_two (F := D.F)).mpr h2)
  have hchar2 : ∀ v : D.F × D.F, v + v = 0 := fun v => by
    ext <;> exact CharTwo.add_self_eq_zero _
  have hQ0leQ : Work.ThmF.Q0sub H ≤ Q := Q0sub_le_Q hsplit
  have hQ0central := caseC_Q0sub_central hS hC4
  have hmemQ0 : ∀ x ∈ (Q : Set G), x ∈ Work.ThmF.Q0sub H ↔ x ^ 2 = 1 := by
    intro x hx
    have h := hZ ⟨x, hx⟩
    rw [pow_two]
    constructor
    · intro hh
      simpa [Subgroup.coe_mul] using Subtype.ext_iff.mp (h.mp hh)
    · intro hh
      exact h.mpr (Subtype.ext (by simpa [Subgroup.coe_mul, pow_two] using hh))
  have hsq : ∀ x ∈ (Q : Set G), x ^ 2 ∈ Work.ThmF.Q0sub H := by
    intro x hx
    have h1 : D.psi ((⟨x, hx⟩ : ↥Q) * ⟨x, hx⟩) = 0 := by
      rw [D.psi_add]; exact hchar2 _
    have h2 : (((⟨x, hx⟩ : ↥Q) * ⟨x, hx⟩ : ↥Q) : G) ∈ Work.ThmF.Q0sub H :=
      (D.psi_ker _).mp h1
    simpa [Subgroup.coe_mul, pow_two] using h2
  -- psi facts
  have hpsi_one : D.psi (1 : ↥Q) = 0 := by
    have h := D.psi_add (1:↥Q) 1
    rw [mul_one] at h
    exact add_left_cancel (h.symm.trans (by rw [add_zero]))
  have hpsi_inv : ∀ y : ↥Q, D.psi y⁻¹ = - D.psi y := by
    intro y
    have h := D.psi_add y y⁻¹
    rw [mul_inv_cancel, hpsi_one] at h
    exact eq_neg_of_add_eq_zero_right h.symm
  -- the zeta action on Q
  have hζD : ζ ∈ twoPoint H t :=
    (Work.ThmF.centD_le_twoPoint (H := H) t) (Work.ThmF.W_le_centD H t hζ)
  have hζH : ζ ∈ H := (Subgroup.mem_inf.mp hζD).1
  have hζNm : ζ ∈ Subgroup.normalizer (Q : Set G) := hsplit.normal hζH
  have hζNm' : ζ⁻¹ ∈ Subgroup.normalizer (Q : Set G) :=
    (Subgroup.normalizer (Q:Set G)).inv_mem hζNm
  let zetaAct : MulAut ↥Q := conjOnQ ζ⁻¹ hζNm'
  have zetaAct_coe : ∀ x : ↥Q, ((zetaAct x : ↥Q) : G) = ζ⁻¹ * (x:G) * ζ := by
    intro x; simp [zetaAct, conjOnQ_coe]
  have hW_eq : Work.ThmF.W H t =
      twoPoint H t ⊓ Subgroup.centralizer (involutions (H : Set G)) :=
    (hC4 G hS.situation H hsplit.stronglyEmbedded t hsplit.invol hsplit.not_mem).2.2.2.2.1
  have hζcen : ζ ∈ Subgroup.centralizer (involutions (H : Set G)) :=
    (Subgroup.mem_inf.mp (hW_eq ▸ hζ)).2
  have hζcenQ0sub : Work.ThmF.Q0sub H ≤ Subgroup.centralizer ({ζ} : Set G) := by
    rw [Work.ThmF.Q0sub]
    refine (Subgroup.closure_le _).mpr ?_
    intro x hx
    rcases Work.ThmF.mem_Q0_iff.mp hx with ⟨hxH, hx2⟩ | rfl
    · exact Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_iff.mp hζcen x ⟨hxH, hx2⟩)
    · exact Subgroup.mem_centralizer_singleton_iff.mpr (by rw [one_mul, mul_one])
  have hzetaAct_Q0 : ∀ z ∈ Work.ThmF.Q0sub H, ζ⁻¹ * z * ζ = z := by
    intro z hz
    have h := Subgroup.mem_centralizer_singleton_iff.mp (hζcenQ0sub hz)
    rw [mul_assoc, h, ← mul_assoc, inv_mul_cancel, one_mul]
  have zetaAct_psi_congr : ∀ x y : ↥Q, D.psi x = D.psi y →
      D.psi (zetaAct x) = D.psi (zetaAct y) := by
    intro x y hxy
    have hprod : D.psi (x⁻¹ * y) = 0 := by
      rw [D.psi_add, hpsi_inv, hxy, neg_add_cancel]
    have hmem : ((x⁻¹ * y : ↥Q) : G) ∈ Work.ThmF.Q0sub H := (D.psi_ker _).mp hprod
    have hmem2 : ((zetaAct (x⁻¹ * y) : ↥Q) : G) ∈ Work.ThmF.Q0sub H := by
      rw [zetaAct_coe, hzetaAct_Q0 _ hmem]; exact hmem
    have hz0 : D.psi (zetaAct (x⁻¹ * y)) = 0 := (D.psi_ker _).mpr hmem2
    have h3 : zetaAct (x⁻¹ * y) = (zetaAct x)⁻¹ * (zetaAct y) := by rw [map_mul, map_inv]
    rw [h3, D.psi_add, hpsi_inv] at hz0
    exact neg_inj.mp (add_eq_zero_iff_eq_neg.mp hz0)
  -- the section of psi
  let psiSec : D.F × D.F → ↥Q := fun v => Classical.choose (D.psi_surj v)
  have psiSec_spec : ∀ v, D.psi (psiSec v) = v := fun v => Classical.choose_spec (D.psi_surj v)
  -- Lam is surjective
  have hLam_surj : Function.Surjective D.Lam := by
    have hcardK : Nat.card ↥(Work.ThmF.Ksub H t) = Nat.card D.F - 1 := by
      rw [caseC_card_Ksub hS hC4 hWne]
      have h1 : (involutions (H : Set G)).ncard = Nat.card ↥(Work.ThmF.Q0sub H) - 1 := by
        have h := caseC_card_Q0sub_eq hS hC4; omega
      rw [h1, D.cardF]
    have hcardU : Nat.card D.Fˣ = Nat.card D.F - 1 := Nat.card_units D.F
    haveI : Fintype ↥(Work.ThmF.Ksub H t) := Fintype.ofFinite _
    haveI : Fintype D.Fˣ := Fintype.ofFinite _
    have hcard_eq : Fintype.card ↥(Work.ThmF.Ksub H t) = Fintype.card D.Fˣ := by
      rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hcardK, hcardU]
    exact ((Fintype.bijective_iff_injective_and_card D.Lam).mpr
      ⟨D.Lam_injective, hcard_eq⟩).2
  -- psi is equivariant for the K-action
  have hpsi_conj_smul : ∀ (k : ↥(Work.ThmF.Ksub H t)) (x : ↥Q),
      D.psi (conjQK hsplit k x) = (D.Lam k : D.F) • D.psi x := by
    intro k x
    rw [D.psi_conj]
    rfl
  -- zetaAct commutes with conjQK
  have hconjQK_zeta : ∀ (k : ↥(Work.ThmF.Ksub H t)) (x : ↥Q),
      zetaAct (conjQK hsplit k x) = conjQK hsplit k (zetaAct x) := by
    intro k x
    apply Subtype.ext
    simp only [conjQK_coe, zetaAct_coe]
    have hck : ζ * (k : G) = (k : G) * ζ :=
      zeta_comm_Ksub hS hζ k k.2
    have hck1 : ζ⁻¹ * (k:G) = (k:G) * ζ⁻¹ := by
      have h2 : ζ⁻¹ * (k:G) * ζ = (k:G) := by
        rw [mul_assoc, ← hck, ← mul_assoc, inv_mul_cancel, one_mul]
      calc ζ⁻¹ * (k:G) = (ζ⁻¹ * (k:G) * ζ) * ζ⁻¹ := by group
        _ = (k:G) * ζ⁻¹ := by rw [h2]
    have hck2 : (k:G)⁻¹ * ζ = ζ * (k:G)⁻¹ := by
      have h := congrArg Inv.inv hck1
      simpa [mul_inv_rev] using h
    calc ζ⁻¹ * ((k:G) * (x:G) * (k:G)⁻¹) * ζ
        = (ζ⁻¹ * (k:G)) * (x:G) * ((k:G)⁻¹ * ζ) := by group
      _ = ((k:G) * ζ⁻¹) * (x:G) * (ζ * (k:G)⁻¹) := by rw [hck1, hck2]
      _ = (k:G) * (ζ⁻¹ * (x:G) * ζ) * (k:G)⁻¹ := by group
  -- The linear map T
  let T : D.F × D.F →ₗ[D.F] D.F × D.F :=
    { toFun := fun v => D.psi (zetaAct (psiSec v))
      map_add' := by
        intro v w
        have h1 : D.psi (psiSec (v + w)) = D.psi (psiSec v * psiSec w) := by
          simp only [D.psi_add, psiSec_spec]
        have h2 := zetaAct_psi_congr _ _ h1
        show D.psi (zetaAct (psiSec (v + w))) =
          D.psi (zetaAct (psiSec v)) + D.psi (zetaAct (psiSec w))
        rw [h2, map_mul, D.psi_add]
      map_smul' := by
        intro c v
        by_cases hc : c = 0
        · subst hc
          have hT0 : D.psi (zetaAct (psiSec (0 : D.F × D.F))) = 0 := by
            refine (D.psi_ker _).mpr ?_
            rw [zetaAct_coe]
            have hm : ((psiSec (0 : D.F × D.F) : ↥Q) : G) ∈ Work.ThmF.Q0sub H :=
              (D.psi_ker _).mp (psiSec_spec 0)
            rw [hzetaAct_Q0 _ hm]; exact hm
          show D.psi (zetaAct (psiSec ((0 : D.F) • v))) =
            (0 : D.F) • D.psi (zetaAct (psiSec v))
          rw [zero_smul, hT0, zero_smul]
        · obtain ⟨k, hk⟩ := hLam_surj (Units.mk0 c hc)
          have hkval : (D.Lam k : D.F) = c := by rw [hk]; rfl
          have hcv : c • v = (D.Lam k : D.F) • v := by rw [hkval]
          have h1 : D.psi (psiSec ((D.Lam k : D.F) • v)) =
              D.psi (conjQK hsplit k (psiSec v)) := by
            rw [psiSec_spec, hpsi_conj_smul, psiSec_spec]
          have h2 := zetaAct_psi_congr _ _ h1
          rw [hconjQK_zeta, hpsi_conj_smul] at h2
          show D.psi (zetaAct (psiSec (c • v))) = c • D.psi (zetaAct (psiSec v))
          rw [hcv, h2, hkval] }
  have hTapply : ∀ v, T v = D.psi (zetaAct (psiSec v)) := fun v => rfl
  have hTfpf : ∀ v : D.F × D.F, T v = v → v = 0 := by
    intro v hv
    change D.psi (zetaAct (psiSec v)) = v at hv
    have h0 : D.psi ((zetaAct (psiSec v))⁻¹ * psiSec v) = 0 := by
      rw [D.psi_add, hpsi_inv, hv, psiSec_spec, neg_add_cancel]
    have hmem : (((zetaAct (psiSec v))⁻¹ * psiSec v : ↥Q) : G) ∈ Work.ThmF.Q0sub H :=
      (D.psi_ker _).mp h0
    have hcoe : (((zetaAct (psiSec v))⁻¹ * psiSec v : ↥Q) : G) =
        ζ⁻¹ * ((psiSec v : ↥Q) : G)⁻¹ * ζ * ((psiSec v : ↥Q) : G) := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, zetaAct_coe]; group
    rw [hcoe] at hmem
    have hx : (((psiSec v)⁻¹ : ↥Q) : G) ∈ Work.ThmF.Q0sub H :=
      hζf (psiSec v)⁻¹ (by rw [Subgroup.coe_inv]; convert hmem using 1; group)
    have hz : D.psi ((psiSec v)⁻¹) = 0 := (D.psi_ker _).mpr hx
    rw [hpsi_inv] at hz
    have hz2 : D.psi (psiSec v) = 0 := neg_eq_zero.mp hz
    rw [psiSec_spec] at hz2
    exact hz2
  have hTpow : ∀ j : ℕ, ∀ v, (T ^ j) v = D.psi ((zetaAct ^ j) (psiSec v)) := by
    intro j
    induction j with
    | zero => intro v; simp [psiSec_spec]
    | succ j ih =>
        intro v
        rw [pow_succ']
        change T ((T ^ j) v) = D.psi ((zetaAct ^ (j+1)) (psiSec v))
        rw [ih, hTapply]
        have h2 : (zetaAct ^ (j+1)) (psiSec v) = zetaAct ((zetaAct^j) (psiSec v)) := by
          rw [pow_succ']; rfl
        rw [h2]
        exact zetaAct_psi_congr _ _ (by rw [psiSec_spec])
  have hzetaAct_pow_order : zetaAct ^ (orderOf ζ) = 1 := by
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    rw [show (((zetaAct ^ (orderOf ζ)) x : ↥Q) : G) =
        (ζ⁻¹)^(orderOf ζ) * (x:G) * ((ζ⁻¹)^(orderOf ζ))⁻¹ from
      conjOnQ_pow_coe ζ⁻¹ hζNm' (orderOf ζ) x]
    rw [show (ζ⁻¹)^(orderOf ζ) = 1 from by rw [inv_pow, pow_orderOf_eq_one, inv_one]]
    simp
  have hTorder : T ^ (orderOf ζ) = 1 := by
    apply LinearMap.ext
    intro v
    rw [hTpow (orderOf ζ) v, hzetaAct_pow_order]
    simp [psiSec_spec]
  have hTdvd : orderOf T ∣ Nat.card D.F + 1 := by
    have h1 : orderOf T ∣ orderOf ζ := by
      rw [orderOf_dvd_iff_pow_eq_one]; exact hTorder
    have h2 : orderOf ζ ∣ Nat.card D.F + 1 := by rw [D.cardF]; exact hζd
    exact h1.trans h2
  -- apply the field-theoretic input
  obtain ⟨e, ι, β, he1, heord, hιfix, hιinj, hιsurj, hβadd, hβbij, hβT, hβsmul⟩ :=
    singer_frame_data hn1 D.F hcardF T hTfpf hTdvd
  -- normalise the additive isomorphism `Q0sub ≅ F` so that `s ↦ 1`
  have hsne1 : s ≠ 1 := by intro h; rw [h] at hs2; simp at hs2
  have hsQ0 : s ∈ Work.ThmF.Q0sub H := (hZ ⟨s, hs⟩).mpr (Subtype.ext (by
    rw [Subgroup.coe_mul, ← pow_two, ← hs2]; exact pow_orderOf_eq_one s))
  have hphi0 : D.phi (1 : ↥(Work.ThmF.Q0sub H)) = 0 := by
    have h := D.phi_add 1 1
    rw [mul_one] at h
    exact add_left_cancel (by rw [add_zero]; exact h.symm)
  have hlamne : D.phi ⟨s, hsQ0⟩ ≠ 0 := by
    intro h
    have h1 : (⟨s, hsQ0⟩ : ↥(Work.ThmF.Q0sub H)) = 1 :=
      D.phi_bij.injective (by rw [h, hphi0])
    exact hsne1 (Subtype.ext_iff.mp h1)
  let ι0 : ↥(Work.ThmF.Q0sub H) ≃ D.F := Equiv.ofBijective D.phi D.phi_bij
  let φ' : ↥(Work.ThmF.Q0sub H) → D.F := fun y => ι0 y * (ι0 ⟨s, hsQ0⟩)⁻¹
  have hφ's : φ' ⟨s, hsQ0⟩ = 1 := by
    show ι0 ⟨s, hsQ0⟩ * (ι0 ⟨s, hsQ0⟩)⁻¹ = 1
    exact mul_inv_cancel₀ hlamne
  have hφ'add : ∀ a b : ↥(Work.ThmF.Q0sub H), φ' (a * b) = φ' a + φ' b := by
    intro a b
    show ι0 (a * b) * (ι0 ⟨s, hsQ0⟩)⁻¹ = ι0 a * (ι0 ⟨s, hsQ0⟩)⁻¹ + ι0 b * (ι0 ⟨s, hsQ0⟩)⁻¹
    rw [show ι0 (a * b) = ι0 a + ι0 b from D.phi_add a b, add_mul]
  have hφ'bij : Function.Bijective φ' := by
    refine ⟨?_, ?_⟩
    · intro a b hab
      apply ι0.injective
      exact mul_right_cancel₀ (inv_ne_zero hlamne) hab
    · intro c
      exact ⟨ι0.symm (c * ι0 ⟨s, hsQ0⟩), by
        show ι0 (ι0.symm (c * ι0 ⟨s, hsQ0⟩)) * (ι0 ⟨s, hsQ0⟩)⁻¹ = c
        rw [ι0.apply_symm_apply, mul_assoc,
          show ι0 ⟨s, hsQ0⟩ * (ι0 ⟨s, hsQ0⟩)⁻¹ = 1 from mul_inv_cancel₀ hlamne, mul_one]⟩
  let ephi : ↥(Work.ThmF.Q0sub H) ≃ D.F := Equiv.ofBijective φ' hφ'bij
  have hephi_apply : ∀ x : ↥(Work.ThmF.Q0sub H), ephi x = φ' x := fun x => rfl
  have hephi_add : ∀ a b : ↥(Work.ThmF.Q0sub H), ephi (a * b) = ephi a + ephi b :=
    fun a b => hφ'add a b
  -- zc : fixed field of σE ≅ Q0sub
  let ιsec : Work.PSU3.E n → D.F := fun y =>
    if hy : Work.PSU3.σE y = y then Classical.choose (hιsurj y hy) else 0
  have ιsec_spec : ∀ y (hy : Work.PSU3.σE y = y), ι (ιsec y) = y := by
    intro y hy
    simp only [ιsec, dif_pos hy]
    exact Classical.choose_spec (hιsurj y hy)
  let zc : Work.PSU3.E n → G := fun y =>
    if hy : Work.PSU3.σE y = y then
      ((ephi.symm (ιsec y) : ↥(Work.ThmF.Q0sub H)) : G) else 1
  have zc_fixed : ∀ y (hy : Work.PSU3.σE y = y),
      zc y = ((ephi.symm (ιsec y) : ↥(Work.ThmF.Q0sub H)) : G) := by
    intro y hy; simp only [zc, dif_pos hy]
  have hzc_one : zc 1 = s := by
    have hy : Work.PSU3.σE (1 : Work.PSU3.E n) = 1 := map_one _
    rw [zc_fixed 1 hy]
    have hιsec1 : ιsec 1 = 1 := by
      apply hιinj
      rw [ιsec_spec 1 hy, map_one]
    rw [hιsec1]
    have hmem : ephi ⟨s, hsQ0⟩ = (1 : D.F) := hφ's
    have : ephi.symm (1 : D.F) = ⟨s, hsQ0⟩ := by
      apply ephi.injective
      rw [ephi.apply_symm_apply, hmem]
    rw [this]
  have hzc_mem : ∀ y, Work.PSU3.σE y = y → zc y ∈ Work.ThmF.Q0sub H := by
    intro y hy
    rw [zc_fixed y hy]
    exact (ephi.symm (ιsec y)).2
  have hzc_add : ∀ y y', Work.PSU3.σE y = y → Work.PSU3.σE y' = y' →
      zc (y + y') = zc y * zc y' := by
    intro y y' hy hy'
    have hyy : Work.PSU3.σE (y + y') = y + y' := by rw [map_add, hy, hy']
    rw [zc_fixed _ hyy, zc_fixed y hy, zc_fixed y' hy']
    have hsum : ιsec (y + y') = ιsec y + ιsec y' := by
      apply hιinj
      rw [ιsec_spec _ hyy, map_add, ιsec_spec y hy, ιsec_spec y' hy']
    have h2 : ∀ a b : D.F, ephi.symm (a + b) = ephi.symm a * ephi.symm b := by
      intro a b
      apply ephi.injective
      rw [ephi.apply_symm_apply, hephi_add, ephi.apply_symm_apply, ephi.apply_symm_apply]
    rw [hsum]
    exact congrArg Subtype.val (h2 (ιsec y) (ιsec y'))
  have hzc_surj : ∀ z ∈ Work.ThmF.Q0sub H, ∃ y, Work.PSU3.σE y = y ∧ zc y = z := by
    intro z hz
    refine ⟨ι (ephi ⟨z, hz⟩), hιfix _, ?_⟩
    rw [zc_fixed _ (hιfix _)]
    have hz' : ιsec (ι (ephi ⟨z, hz⟩)) = ephi ⟨z, hz⟩ := by
      apply hιinj
      rw [ιsec_spec _ (hιfix _)]
    rw [hz', ephi.symm_apply_apply]
  have hzc_inj : ∀ y y', Work.PSU3.σE y = y → Work.PSU3.σE y' = y' →
      zc y = zc y' → y = y' := by
    intro y y' hy hy' h
    rw [zc_fixed y hy, zc_fixed y' hy'] at h
    have h1 : ιsec y = ιsec y' := by
      apply ephi.symm.injective
      exact Subtype.coe_injective h
    rw [← ιsec_spec y hy, h1, ιsec_spec y' hy']
  -- bar : Q →* Multiplicative (E n)
  have hβ0 : β (0 : D.F × D.F) = 0 := by
    have h := hβadd 0 0
    rw [add_zero] at h
    exact add_left_cancel (by rw [add_zero]; exact h.symm)
  let bar : ↥Q →* Multiplicative (Work.PSU3.E n) :=
    { toFun := fun x => Multiplicative.ofAdd (β (D.psi x))
      map_one' := by
        show Multiplicative.ofAdd (β (D.psi (1 : ↥Q))) = 1
        rw [hpsi_one, hβ0]
        rfl
      map_mul' := by
        intro x y
        show Multiplicative.ofAdd (β (D.psi (x * y))) =
          Multiplicative.ofAdd (β (D.psi x)) * Multiplicative.ofAdd (β (D.psi y))
        rw [D.psi_add, hβadd]
        rfl }
  have hbar_surj : Function.Surjective bar := by
    intro z
    obtain ⟨u, hu⟩ := hβbij.2 (Multiplicative.toAdd z)
    obtain ⟨x, hx⟩ := D.psi_surj u
    exact ⟨x, by
      show Multiplicative.ofAdd (β (D.psi x)) = z
      rw [hx, hu]
      exact Multiplicative.ofAdd.apply_symm_apply z⟩
  have hbar_ker : ∀ x : ↥Q, bar x = 1 ↔ (x : G) ∈ Work.ThmF.Q0sub H := by
    intro x
    have h1 : (bar x = 1) ↔ β (D.psi x) = 0 := by
      have hb : bar x = Multiplicative.ofAdd (β (D.psi x)) := rfl
      rw [hb]
      constructor
      · intro h
        exact Multiplicative.ofAdd.injective h
      · intro h
        show Multiplicative.ofAdd (β (D.psi x)) = 1
        rw [h]
        rfl
    rw [h1]
    constructor
    · intro h
      exact (D.psi_ker x).mp (hβbij.injective (by rw [h, hβ0]))
    · intro h
      rw [(D.psi_ker x).mpr h, hβ0]
  -- faithfulness of the action of ⟨ζ⟩ on Q/Q₀
  have hzetaInv_pow_Q0 : ∀ n : ℕ, ∀ z ∈ Work.ThmF.Q0sub H,
      (ζ⁻¹)^n * z * ((ζ⁻¹)^n)⁻¹ = z := by
    intro n z hz
    have hc : Commute (ζ⁻¹) z := by
      have h := hzetaAct_Q0 z hz
      show (ζ⁻¹) * z = z * (ζ⁻¹)
      conv_rhs => rw [← h]
      group
    have h2 : Commute ((ζ⁻¹)^n) z := hc.pow_left n
    rw [show (ζ⁻¹)^n * z = z * (ζ⁻¹)^n from h2, mul_assoc, mul_inv_cancel, mul_one]
  have hfaith : ∀ j : ℕ, T ^ j = 1 → ζ ^ j = 1 := by
    intro j hTj
    by_contra hne
    have hwW : ζ^j ∈ Work.ThmF.W H t := (Work.ThmF.W H t).pow_mem hζ j
    have hactj : ∀ x : ↥Q, ((zetaAct^j) x : G) = (ζ^j)⁻¹ * (x:G) * (ζ^j) := by
      intro x
      rw [conjOnQ_pow_coe ζ⁻¹ hζNm' j, inv_pow, inv_inv]
    have hact : ∀ x : ↥Q, D.psi ((zetaAct^j) x) = D.psi x := by
      intro x
      have hz0 : D.psi (x * (psiSec (D.psi x))⁻¹) = 0 := by
        rw [D.psi_add, hpsi_inv, psiSec_spec, add_neg_cancel]
      have hz : ((x * (psiSec (D.psi x))⁻¹ : ↥Q) : G) ∈ Work.ThmF.Q0sub H :=
        (D.psi_ker _).mp hz0
      have hfix : (zetaAct^j) (x * (psiSec (D.psi x))⁻¹) = x * (psiSec (D.psi x))⁻¹ := by
        apply Subtype.ext
        rw [conjOnQ_pow_coe ζ⁻¹ hζNm' j]
        exact hzetaInv_pow_Q0 j _ hz
      have hxre : (x * (psiSec (D.psi x))⁻¹) * psiSec (D.psi x) = x := by
        rw [mul_assoc, inv_mul_cancel, mul_one]
      calc D.psi ((zetaAct^j) x)
          = D.psi ((zetaAct^j) ((x * (psiSec (D.psi x))⁻¹) * psiSec (D.psi x))) := by rw [hxre]
        _ = D.psi ((zetaAct^j) (x * (psiSec (D.psi x))⁻¹) * (zetaAct^j) (psiSec (D.psi x))) := by
              rw [map_mul]
        _ = D.psi ((zetaAct^j) (psiSec (D.psi x))) := by rw [D.psi_add, hfix, hz0, zero_add]
        _ = (T^j) (D.psi x) := by rw [← hTpow j (D.psi x)]
        _ = D.psi x := by rw [hTj]; rfl
    have hθmem : ∀ x : ↥Q, ((((zetaAct^j) x) * x⁻¹ : ↥Q) : G) ∈ Work.ThmF.Q0sub H := by
      intro x
      show ((((zetaAct^j) x) * x⁻¹ : ↥Q) : G) ∈ Work.ThmF.Q0sub H
      rw [← D.psi_ker, D.psi_add, hpsi_inv, hact x, add_neg_cancel]
    have hθmul : ∀ x y : ↥Q, (((zetaAct^j) (x * y)) * (x*y)⁻¹ : ↥Q) =
        (((zetaAct^j) x) * x⁻¹ : ↥Q) * (((zetaAct^j) y) * y⁻¹ : ↥Q) := by
      intro x y
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul]
      rw [mul_inv_rev]
      have h := hQ0central (((zetaAct^j) y) * y⁻¹ : ↥Q) (hθmem y) ((x:G)⁻¹) (Q.inv_mem x.2)
      calc ((zetaAct^j) x : G) * ((zetaAct^j) y : G) * ((y:G)⁻¹ * (x:G)⁻¹)
          = ((zetaAct^j) x : G) * ((((zetaAct^j) y : G) * (y:G)⁻¹) * (x:G)⁻¹) := by group
        _ = ((zetaAct^j) x : G) * ((x:G)⁻¹ * (((zetaAct^j) y : G) * (y:G)⁻¹)) := by
              rw [show (((zetaAct^j) y : G) * (y:G)⁻¹) * (x:G)⁻¹ =
                (x:G)⁻¹ * (((zetaAct^j) y : G) * (y:G)⁻¹) from h]
        _ = (((zetaAct^j) x : G) * (x:G)⁻¹) * (((zetaAct^j) y : G) * (y:G)⁻¹) := by group
    let θ : ↥Q →* ↥(Work.ThmF.Q0sub H) :=
      { toFun := fun x => ⟨((((zetaAct^j) x) * x⁻¹ : ↥Q) : G), hθmem x⟩
        map_one' := by
          apply Subtype.ext
          simp
        map_mul' := by
          intro x y
          refine Subtype.ext ?_
          exact congrArg (fun t : ↥Q => ((t : G))) (hθmul x y) }
    have hθker : θ.ker = (Work.ThmF.Q0sub H).subgroupOf Q := by
      ext x
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
      constructor
      · intro h
        have h2 : ((((zetaAct^j) x) * x⁻¹ : ↥Q) : G) = 1 := Subtype.ext_iff.mp h
        have h3 : (zetaAct^j) x = x := mul_inv_eq_one.mp (Subtype.ext h2)
        have h4 : ((zetaAct^j) x : G) = (x:G) := congrArg Subtype.val h3
        rw [hactj x] at h4
        have hxc : (ζ^j) * (x:G) = (x:G) * (ζ^j) := by
          calc (ζ^j) * (x:G) = (ζ^j) * ((ζ^j)⁻¹ * (x:G) * (ζ^j)) := by rw [h4]
            _ = (x:G) * (ζ^j) := by group
        exact hW (ζ^j) hwW hne (x:G) x.2 hxc
      · intro hx
        apply Subtype.ext
        change ((((zetaAct^j) x) * x⁻¹ : ↥Q) : G) = (1 : G)
        have hc0 : Commute (x:G) ζ := Subgroup.mem_centralizer_singleton_iff.mp (hζcenQ0sub hx)
        have hxc : (x:G) * (ζ^j) = (ζ^j) * (x:G) := hc0.pow_right j
        rw [Subgroup.coe_mul, Subgroup.coe_inv, hactj x,
          show (ζ^j)⁻¹ * (x:G) * (ζ^j) = (x:G) from by
            rw [mul_assoc, hxc, ← mul_assoc, inv_mul_cancel, one_mul],
          mul_inv_cancel]
    let φ : D.F × D.F → ↥(Work.ThmF.Q0sub H) := fun v => θ (psiSec v)
    have hφinj : Function.Injective φ := by
      intro v w hvw
      have h1 : θ (psiSec v * (psiSec w)⁻¹) = 1 := by
        have hvw' : θ (psiSec v) = θ (psiSec w) := hvw
        rw [map_mul, map_inv, hvw', mul_inv_cancel]
      have h2 : (psiSec v * (psiSec w)⁻¹ : ↥Q) ∈ θ.ker := h1
      rw [hθker, Subgroup.mem_subgroupOf] at h2
      have h3 : D.psi (psiSec v) - D.psi (psiSec w) = 0 := by
        have h4 : D.psi (psiSec v) + (- D.psi (psiSec w)) = 0 := by
          have h5 : D.psi (psiSec v * (psiSec w)⁻¹) = 0 := (D.psi_ker _).mpr h2
          rw [D.psi_add, hpsi_inv] at h5
          exact h5
        rwa [sub_eq_add_neg]
      rw [psiSec_spec, psiSec_spec] at h3
      exact sub_eq_zero.mp h3
    have hle := Nat.card_le_card_of_injective φ hφinj
    rw [Nat.card_prod, ← D.cardF] at hle
    have hge : 4 ≤ Nat.card D.F := by
      rw [hcardF]
      calc 4 = 2^2 := by norm_num
        _ ≤ 2^n := Nat.pow_le_pow_right (by norm_num) (by omega : 2 ≤ n)
    nlinarith [hle, hge]
  have hTord_eq : orderOf T = orderOf ζ := by
    apply Nat.dvd_antisymm
    · rw [orderOf_dvd_iff_pow_eq_one]; exact hTorder
    · rw [orderOf_dvd_iff_pow_eq_one]; exact hfaith (orderOf T) (pow_orderOf_eq_one T)
  have he_ord : orderOf e = orderOf ζ := by rw [heord, hTord_eq]
  -- KW = Ksub ⊔ ⟨ζ⟩
  have hζcommK : ∀ k ∈ Work.ThmF.Ksub H t, ζ * k = k * ζ := zeta_comm_Ksub hS hζ
  have hζpowcommK : ∀ (z : ↥(Subgroup.zpowers ζ)) (k : ↥(Work.ThmF.Ksub H t)),
      (z:G) * (k:G) = (k:G) * (z:G) := by
    intro z k
    have h : Subgroup.zpowers ζ ≤ Subgroup.centralizer ({(k:G)} : Set G) := by
      rw [Subgroup.zpowers_le]
      exact Subgroup.mem_centralizer_singleton_iff.mpr (hζcommK k k.2)
    exact Subgroup.mem_centralizer_singleton_iff.mp (h z.2)
  let prodHom : ↥(Work.ThmF.Ksub H t) × ↥(Subgroup.zpowers ζ) →* G :=
    { toFun := fun p => (p.1 : G) * (p.2 : G)
      map_one' := by simp
      map_mul' := by
        intro p q
        show ((p.1 * q.1 : ↥(Work.ThmF.Ksub H t)) : G) *
            ((p.2 * q.2 : ↥(Subgroup.zpowers ζ)) : G) =
          ((p.1 : G) * (p.2 : G)) * ((q.1 : G) * (q.2 : G))
        simp only [Subgroup.coe_mul]
        calc (p.1 : G) * (q.1 : G) * ((p.2 : G) * (q.2 : G))
            = (p.1 : G) * ((q.1 : G) * (p.2 : G)) * (q.2 : G) := by group
          _ = (p.1 : G) * ((p.2 : G) * (q.1 : G)) * (q.2 : G) := by rw [hζpowcommK p.2 q.1]
          _ = ((p.1 : G) * (p.2 : G)) * ((q.1 : G) * (q.2 : G)) := by group }
  have hKsub_inf_zpow : Work.ThmF.Ksub H t ⊓ Subgroup.zpowers ζ = ⊥ :=
    Ksub_inf_zpowers_eq_bot hS hC4 hWne hζ hζodd
  have hprod_inj : Function.Injective prodHom := by
    intro p q hpq
    have hpq' : (p.1:G) * (p.2:G) = (q.1:G) * (q.2:G) := hpq
    have h1 : (p.2:G) * (q.2:G)⁻¹ = (p.1:G)⁻¹ * (q.1:G) := by
      have h2 : (p.1:G) * ((p.2:G) * (q.2:G)⁻¹) = (q.1:G) := by
        rw [← mul_assoc, hpq', mul_assoc, mul_inv_cancel, mul_one]
      calc (p.2:G) * (q.2:G)⁻¹ =
            (p.1:G)⁻¹ * ((p.1:G) * ((p.2:G) * (q.2:G)⁻¹)) := by group
        _ = (p.1:G)⁻¹ * (q.1:G) := by rw [h2]
    have hL : (p.2:G) * (q.2:G)⁻¹ ∈ Work.ThmF.Ksub H t ⊓ Subgroup.zpowers ζ := by
      refine ⟨?_, ?_⟩
      · rw [h1]
        exact (Work.ThmF.Ksub H t).mul_mem ((Work.ThmF.Ksub H t).inv_mem p.1.2) q.1.2
      · exact (Subgroup.zpowers ζ).mul_mem p.2.2 ((Subgroup.zpowers ζ).inv_mem q.2.2)
    have hbot : (p.2:G) * (q.2:G)⁻¹ = 1 := by
      rw [hKsub_inf_zpow] at hL
      exact Subgroup.mem_bot.mp hL
    have hpq2 : (p.2:G) = (q.2:G) := mul_inv_eq_one.mp hbot
    have hpq1 : (p.1:G) = (q.1:G) := by
      have h' : (p.1:G) * (p.2:G) = (q.1:G) * (p.2:G) := by rw [hpq', hpq2]
      exact mul_right_cancel h'
    exact Prod.ext (Subtype.ext hpq1) (Subtype.ext hpq2)
  let KW : Subgroup G := prodHom.range
  have hKW_eq : KW = Work.ThmF.Ksub H t ⊔ Subgroup.zpowers ζ := by
    apply le_antisymm
    · rintro _ ⟨p, rfl⟩
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left p.1.2) (Subgroup.mem_sup_right p.2.2)
    · refine sup_le ?_ ?_
      · intro k hk
        exact ⟨(⟨k, hk⟩, 1), by show (k:G) * 1 = k; rw [mul_one]⟩
      · intro z hz
        exact ⟨(1, ⟨z, hz⟩), by show (1:G) * (z:G) = z; rw [one_mul]⟩
  have hKW_le : KW ≤ twoPoint H t := by
    rw [hKW_eq]
    exact sup_le ((Subgroup.closure_le _).mpr (fun x hx => Work.ThmF.Kset_subset H t hx))
      (Subgroup.zpowers_le.mpr hζD)
  have hKW_norm : ∀ d : KW, ∀ x ∈ Q, (d : G)⁻¹ * x * (d : G) ∈ Q := by
    intro d x hx
    have hdH : (d : G) ∈ H := (Subgroup.mem_inf.mp (hKW_le d.2)).1
    have hdn : (d : G)⁻¹ ∈ Subgroup.normalizer (Q : Set G) :=
      (Subgroup.normalizer (Q:Set G)).inv_mem (hsplit.normal hdH)
    simpa using (Subgroup.mem_normalizer_iff.mp hdn x).mp hx
  have hK_le : Work.ThmF.Ksub H t ≤ KW := by
    rw [hKW_eq]; exact le_sup_left
  let prodEquiv : ↥(Work.ThmF.Ksub H t) × ↥(Subgroup.zpowers ζ) ≃* KW :=
    MulEquiv.ofBijective prodHom.rangeRestrict
      ⟨fun a b h => hprod_inj (Subtype.ext_iff.mp h), MonoidHom.rangeRestrict_surjective prodHom⟩
  have hcoe_prodEquiv : ∀ p : ↥(Work.ThmF.Ksub H t) × ↥(Subgroup.zpowers ζ),
      (prodEquiv p : G) = (p.1 : G) * (p.2 : G) := fun p => rfl
  -- κ
  let κK : ↥(Work.ThmF.Ksub H t) →* (Work.PSU3.E n)ˣ :=
    invMonoidHom.comp ((Units.map ι.toMonoidWithZeroHom).comp D.Lam)
  let ζgen : ↥(Subgroup.zpowers ζ) := ⟨ζ, Subgroup.mem_zpowers ζ⟩
  let egen : ↥(Subgroup.zpowers (e : (Work.PSU3.E n)ˣ)) :=
    ⟨e, Subgroup.mem_zpowers e⟩
  have hζgen : ∀ x : ↥(Subgroup.zpowers ζ), x ∈ Subgroup.zpowers ζgen := by
    intro x
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp x.2
    exact Subgroup.mem_zpowers_iff.mpr ⟨j, Subtype.ext (by
      change (ζgen : G) ^ j = (x : G)
      exact hj)⟩
  have hegen : ∀ x : ↥(Subgroup.zpowers (e : (Work.PSU3.E n)ˣ)),
      x ∈ Subgroup.zpowers egen := by
    intro x
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp x.2
    exact Subgroup.mem_zpowers_iff.mpr ⟨j, Subtype.ext (by
      change (egen : (Work.PSU3.E n)ˣ) ^ j = (x : (Work.PSU3.E n)ˣ)
      exact hj)⟩
  let ζiso : Multiplicative (ZMod (orderOf ζ)) ≃* ↥(Subgroup.zpowers ζ) :=
    zmodMulEquivOfGenerator (G := ↥(Subgroup.zpowers ζ)) (g := ζgen) hζgen
      (n := orderOf ζ) (by rw [Nat.card_zpowers])
  let eiso : Multiplicative (ZMod (orderOf ζ)) ≃* ↥(Subgroup.zpowers (e : (Work.PSU3.E n)ˣ)) :=
    zmodMulEquivOfGenerator (G := ↥(Subgroup.zpowers (e : (Work.PSU3.E n)ˣ))) (g := egen) hegen
      (n := orderOf ζ) (by rw [Nat.card_zpowers]; exact he_ord)
  let κz : ↥(Subgroup.zpowers ζ) →* (Work.PSU3.E n)ˣ :=
    (Subgroup.subtype (Subgroup.zpowers (e : (Work.PSU3.E n)ˣ))).comp
      (eiso.toMonoidHom.comp ζiso.symm.toMonoidHom)
  let κabs : ↥(Work.ThmF.Ksub H t) × ↥(Subgroup.zpowers ζ) →* (Work.PSU3.E n)ˣ :=
    { toFun := fun p => κK p.1 * κz p.2
      map_one' := by simp
      map_mul' := by
        intro p q
        show κK (p.1 * q.1) * κz (p.2 * q.2) =
          κK p.1 * κz p.2 * (κK q.1 * κz q.2)
        rw [map_mul, map_mul]
        exact mul_mul_mul_comm _ _ _ _ }
  let κ : KW →* (Work.PSU3.E n)ˣ := κabs.comp prodEquiv.symm.toMonoidHom
  have hκabs_apply : ∀ p : ↥(Work.ThmF.Ksub H t) × ↥(Subgroup.zpowers ζ),
      κ (prodEquiv p) = κK p.1 * κz p.2 := by
    intro p
    show κabs (prodEquiv.symm (prodEquiv p)) = _
    rw [prodEquiv.symm_apply_apply]; rfl
  -- nm via nm_extend
  let LamEquiv : ↥(Work.ThmF.Ksub H t) ≃* D.Fˣ :=
    MulEquiv.ofBijective D.Lam ⟨D.Lam_injective, hLam_surj⟩
  let φnm : D.Fˣ →* D.Fˣ :=
    invMonoidHom.comp (D.rho.comp (LamEquiv.symm.toMonoidHom.comp invMonoidHom))
  obtain ⟨nm, hnm_ext, hnm_F⟩ := nm_extend hn1 D.F hcardF ι hιfix hιinj φnm
  have hκK_apply : ∀ k : ↥(Work.ThmF.Ksub H t),
      (κK k : (Work.PSU3.E n)ˣ) = (Units.map ι.toMonoidWithZeroHom (D.Lam k))⁻¹ := fun k => rfl
  have hκK_coe : ∀ k : ↥(Work.ThmF.Ksub H t), (κK k : Work.PSU3.E n) = (ι (D.Lam k))⁻¹ := by
    intro k
    rw [hκK_apply k, Units.val_inv_eq_inv_val, Units.coe_map]
    rfl
  have hκK_fixed : ∀ k : ↥(Work.ThmF.Ksub H t),
      Work.PSU3.σE ((κK k : (Work.PSU3.E n)ˣ) : Work.PSU3.E n) = (κK k : Work.PSU3.E n) := by
    intro k
    rw [hκK_coe k, map_inv₀, hιfix]
  have hκK_inj : Function.Injective κK := by
    intro a b hab
    have h2 := congrArg (fun u : (Work.PSU3.E n)ˣ => (u : Work.PSU3.E n)) hab
    rw [hκK_coe a, hκK_coe b] at h2
    exact D.Lam_injective (Units.ext (hιinj (inv_injective h2)))
  have hκz_mem : ∀ z : ↥(Subgroup.zpowers ζ), κz z ∈ Subgroup.zpowers (e : (Work.PSU3.E n)ˣ) := by
    intro z
    show ((eiso (ζiso.symm z) : ↥(Subgroup.zpowers (e : (Work.PSU3.E n)ˣ))) : (Work.PSU3.E n)ˣ) ∈ _
    exact (eiso (ζiso.symm z)).2
  have hκz_inj : Function.Injective κz := by
    intro a b hab
    have h1 : eiso (ζiso.symm a) = eiso (ζiso.symm b) := by
      apply Subtype.ext
      exact hab
    exact ζiso.symm.injective (eiso.injective h1)
  have hdisj : ∀ u : (Work.PSU3.E n)ˣ, u ∈ Subgroup.zpowers (e : (Work.PSU3.E n)ˣ) →
      Work.PSU3.σE (u : Work.PSU3.E n) = (u : Work.PSU3.E n) → u = 1 := by
    intro u hu hfix
    obtain ⟨m, hm⟩ := pow_eq_of_mem_zpowers (orderOf_pos (e : (Work.PSU3.E n)ˣ)) hu
    have hee : Work.PSU3.σE (e : Work.PSU3.E n) = ((e : (Work.PSU3.E n)ˣ) : Work.PSU3.E n)⁻¹ := by
      have h := congrArg (fun t : Work.PSU3.E n => ((e : (Work.PSU3.E n)ˣ) : Work.PSU3.E n)⁻¹ * t) he1
      simpa [mul_assoc] using h
    have hu2 : Work.PSU3.σE (u : Work.PSU3.E n) = (u : Work.PSU3.E n)⁻¹ := by
      rw [← hm, Units.val_pow_eq_pow_val, map_pow, hee, inv_pow]
    have h2 : (u : Work.PSU3.E n) = (u : Work.PSU3.E n)⁻¹ := by rw [← hu2, hfix]
    have h3 : u * u = 1 := by
      have hh : (u : Work.PSU3.E n) * (u : Work.PSU3.E n) = 1 := by
        nth_rewrite 1 [h2]; exact inv_mul_cancel₀ (Units.ne_zero u)
      exact Units.ext (by rwa [Units.val_mul, Units.val_one])
    have hord : orderOf u ∣ orderOf ζ := by
      have h1 : orderOf u ∣ Nat.card ↥(Subgroup.zpowers (e : (Work.PSU3.E n)ˣ)) := by
        rw [Subgroup.orderOf_coe (⟨u, hu⟩ : ↥(Subgroup.zpowers (e : (Work.PSU3.E n)ˣ)))]
        exact orderOf_dvd_natCard _
      rwa [Nat.card_zpowers, he_ord] at h1
    have hdvd2 : orderOf u ∣ 2 := by
      rw [orderOf_dvd_iff_pow_eq_one, pow_two]; exact h3
    have hg : Nat.gcd (orderOf ζ) 2 = 1 := (Nat.coprime_two_right.mpr hζodd).gcd_eq_one
    have hgcd := Nat.dvd_gcd hord hdvd2
    rw [hg] at hgcd
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hgcd)
  have hκabs_inj : Function.Injective κabs := by
    intro p q hpq
    have h1 : κabs (p * q⁻¹) = 1 := by rw [map_mul, map_inv, hpq, mul_inv_cancel]
    have h2 : κK (p.1 * q.1⁻¹) * κz (p.2 * q.2⁻¹) = 1 := h1
    have h3 : κK (p.1 * q.1⁻¹) = (κz (p.2 * q.2⁻¹))⁻¹ := mul_eq_one_iff_eq_inv.mp h2
    have h4 : κK (p.1 * q.1⁻¹) = 1 := by
      refine hdisj _ ?_ ?_
      · rw [h3]
        exact (Subgroup.zpowers (e : (Work.PSU3.E n)ˣ)).inv_mem (hκz_mem _)
      · exact hκK_fixed _
    have hr : p.1 * q.1⁻¹ = 1 := hκK_inj (h4.trans (map_one κK).symm)
    have hs : p.2 * q.2⁻¹ = 1 := by
      apply hκz_inj
      have : (κz (p.2 * q.2⁻¹))⁻¹ = 1 := by rw [← h3, h4]
      rw [inv_eq_one] at this
      rw [this, map_one]
    exact Prod.ext (mul_inv_eq_one.mp hr) (mul_inv_eq_one.mp hs)
  have hκ_inj : Function.Injective κ := hκabs_inj.comp prodEquiv.symm.injective
  have hβTpow : ∀ j : ℕ, ∀ v : D.F × D.F,
      β ((T^j) v) = ((e : (Work.PSU3.E n)ˣ) : Work.PSU3.E n)^j * β v := by
    intro j
    induction j with
    | zero => intro v; simp
    | succ j ih =>
        intro v
        have h1 : (T^(j+1)) v = T ((T^j) v) := by rw [pow_succ']; rfl
        rw [h1, hβT, ih, pow_succ]
        ring
  have hactT : ∀ j : ℕ, ∀ w : ↥Q, D.psi ((zetaAct^j) w) = (T^j) (D.psi w) := by
    intro j w
    have hz0 : D.psi (w * (psiSec (D.psi w))⁻¹) = 0 := by
      rw [D.psi_add, hpsi_inv, psiSec_spec, add_neg_cancel]
    have hz : ((w * (psiSec (D.psi w))⁻¹ : ↥Q) : G) ∈ Work.ThmF.Q0sub H :=
      (D.psi_ker _).mp hz0
    have hfix : (zetaAct^j) (w * (psiSec (D.psi w))⁻¹) = w * (psiSec (D.psi w))⁻¹ := by
      apply Subtype.ext
      rw [conjOnQ_pow_coe ζ⁻¹ hζNm' j]
      exact hzetaInv_pow_Q0 j _ hz
    have hre : (w * (psiSec (D.psi w))⁻¹) * psiSec (D.psi w) = w := by
      rw [mul_assoc, inv_mul_cancel, mul_one]
    calc D.psi ((zetaAct^j) w)
        = D.psi ((zetaAct^j) ((w * (psiSec (D.psi w))⁻¹) * psiSec (D.psi w))) := by rw [hre]
      _ = D.psi ((zetaAct^j) (w * (psiSec (D.psi w))⁻¹) * (zetaAct^j) (psiSec (D.psi w))) := by
            rw [map_mul]
      _ = D.psi ((zetaAct^j) (psiSec (D.psi w))) := by rw [D.psi_add, hfix, hz0, zero_add]
      _ = (T^j) (D.psi w) := by rw [← hTpow j (D.psi w)]
  have hκz_gen : κz ζgen = e := by
    show (Subgroup.subtype (Subgroup.zpowers (e : (Work.PSU3.E n)ˣ)))
      (eiso (ζiso.symm ζgen)) = e
    rw [zmodMulEquivOfGenerator_symm_apply_generator,
      zmodMulEquivOfGenerator_apply_ofAdd_one]
    rfl
  have hκz_pow : ∀ j : ℕ, κz (ζgen^j) = e^j := by
    intro j
    rw [map_pow, hκz_gen]
  have hζKW_mem : ζ ∈ KW := by
    rw [hKW_eq]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers ζ)
  let ζKW : KW := ⟨ζ, hζKW_mem⟩
  have hζKW_coe : (ζKW : G) = ζ := rfl
  have hζKW_ne : ζKW ≠ 1 := by
    intro h
    exact hζ1 (by rw [← hζKW_coe, h]; rfl)
  have hκζ : κ ζKW = e := by
    show κabs (prodEquiv.symm ζKW) = e
    have h1 : prodEquiv (1, ζgen) = ζKW := by
      apply Subtype.ext
      show (1 : G) * ζ = ζ
      rw [one_mul]
    rw [← h1, prodEquiv.symm_apply_apply]
    show κK 1 * κz ζgen = e
    rw [hκz_gen]
    simp
  have hζnorm : (κ ζKW : Work.PSU3.E n) * Work.PSU3.σE (κ ζKW : Work.PSU3.E n) = 1 := by
    rw [hκζ]; exact he1
  have hKsurj : ∀ a : (Work.PSU3.E n)ˣ, Work.PSU3.σE (a : Work.PSU3.E n) = (a : Work.PSU3.E n) →
      ∃ d : KW, κ d = a := by
    intro a ha
    obtain ⟨c, hc⟩ := hιsurj (a : Work.PSU3.E n) ha
    have hcne : c ≠ 0 := by
      intro h0
      rw [h0, map_zero] at hc
      exact Units.ne_zero a hc.symm
    obtain ⟨k, hk⟩ := hLam_surj (Units.mk0 c⁻¹ (inv_ne_zero hcne))
    refine ⟨prodEquiv (k, 1), ?_⟩
    show κabs (prodEquiv.symm (prodEquiv (k, 1))) = a
    rw [prodEquiv.symm_apply_apply]
    show κK k * κz 1 = a
    have hkval : (D.Lam k : D.F) = c⁻¹ := by rw [hk]; rfl
    rw [map_one, mul_one]
    apply Units.ext
    rw [hκK_coe k, hkval, map_inv₀, hc, inv_inv]
  have hκ_mul : ∀ p : ↥(Work.ThmF.Ksub H t) × ↥(Subgroup.zpowers ζ),
      (κ (prodEquiv p) : Work.PSU3.E n) = (κK p.1 : Work.PSU3.E n) * (κz p.2 : Work.PSU3.E n) := by
    intro p
    show (κabs (prodEquiv.symm (prodEquiv p)) : Work.PSU3.E n) = _
    rw [prodEquiv.symm_apply_apply]
    rfl
  have hmκ : ∀ p : ↥(Work.ThmF.Ksub H t) × ↥(Subgroup.zpowers ζ),
      (prodEquiv p : G) ∈ Work.ThmF.Ksub H t ↔ p.2 = 1 := by
    intro p
    rw [hcoe_prodEquiv p]
    constructor
    · intro h
      have h2 : (p.2 : G) ∈ Work.ThmF.Ksub H t := by
        have h3 := (Work.ThmF.Ksub H t).mul_mem ((Work.ThmF.Ksub H t).inv_mem p.1.2) h
        simpa using h3
      have h3 : (p.2 : G) ∈ Work.ThmF.Ksub H t ⊓ Subgroup.zpowers ζ := ⟨h2, p.2.2⟩
      rw [hKsub_inf_zpow] at h3
      exact Subtype.ext (Subgroup.mem_bot.mp h3)
    · intro h
      rw [h]
      simpa using p.1.2
  have hκz_fixed_iff : ∀ z : ↥(Subgroup.zpowers ζ),
      Work.PSU3.σE (κz z : Work.PSU3.E n) = (κz z : Work.PSU3.E n) ↔ z = 1 := by
    intro z
    constructor
    · intro hz
      exact hκz_inj (by rw [hdisj (κz z) (hκz_mem z) hz, map_one])
    · intro hz
      rw [hz, map_one]; simp
  have hmemK : ∀ d : KW, (d : G) ∈ Work.ThmF.Ksub H t ↔
      Work.PSU3.σE (κ d : Work.PSU3.E n) = (κ d : Work.PSU3.E n) := by
    intro d
    obtain ⟨p, rfl⟩ := prodEquiv.surjective d
    rw [hmκ p]
    constructor
    · intro hp
      rw [hκ_mul p, hp, map_one, Units.val_one, mul_one]
      exact hκK_fixed p.1
    · intro h
      rw [hκ_mul p, map_mul, hκK_fixed p.1] at h
      exact (hκz_fixed_iff p.2).mp (mul_left_cancel₀ (Units.ne_zero (κK p.1)) h)
  have hKWgen : ∀ d : KW, ∃ k : KW, (k : G) ∈ Work.ThmF.Ksub H t ∧ ∃ j : ℕ, d = k * ζKW ^ j := by
    intro d
    obtain ⟨p, rfl⟩ := prodEquiv.surjective d
    have hposζ : 0 < orderOf ζgen := orderOf_pos ζgen
    obtain ⟨j, hj⟩ := pow_eq_of_mem_zpowers hposζ (hζgen p.2)
    refine ⟨prodEquiv (p.1, 1), ?_, j, ?_⟩
    · have hk1 : (prodEquiv (p.1, 1) : G) = (p.1 : G) := by
        rw [hcoe_prodEquiv, Subgroup.coe_one, mul_one]
      rw [hk1]; exact p.1.2
    · have h2 : ζKW = prodEquiv (1, ζgen) := by
        apply Subtype.ext
        show (ζ : G) = (prodEquiv (1, ζgen) : G)
        show (ζ : G) = (1 : G) * ζ
        rw [one_mul]
      rw [h2, ← map_pow, ← map_mul]
      congr 1
      show (p.1, p.2) = (p.1, 1) * (1, ζgen)^j
      rw [← hj]
      ext <;> simp
  have hposζ0 : 0 < orderOf ζgen := orderOf_pos ζgen
  have hφ'_conj : ∀ (k : ↥(Work.ThmF.Ksub H t)) (w : ↥(Work.ThmF.Q0sub H)),
      φ' (conjQ0 H t k w) = (D.rho k : D.F) * φ' w := by
    intro k w
    show D.phi (conjQ0 H t k w) * (D.phi ⟨s, hsQ0⟩)⁻¹ =
      (D.rho k : D.F) * (D.phi w * (D.phi ⟨s, hsQ0⟩)⁻¹)
    rw [D.phi_conj]; ring
  have hιsec_apply : ∀ c : D.F, Work.PSU3.σE (ι c) = ι c → ιsec (ι c) = c := by
    intro c hc
    apply hιinj
    rw [ιsec_spec _ hc]
  have hactbar : ∀ d : KW, ∀ x y : ↥Q, (y : G) = (d : G)⁻¹ * (x : G) * (d : G) →
      Multiplicative.toAdd (bar y) = (κ d : Work.PSU3.E n) * Multiplicative.toAdd (bar x) := by
    intro d x y hy
    obtain ⟨p, rfl⟩ := prodEquiv.surjective d
    obtain ⟨j, hj⟩ := pow_eq_of_mem_zpowers hposζ0 (hζgen p.2)
    have hzv : (p.2 : G) = ζ^j := by rw [← hj]; rfl
    set w : ↥Q := conjQK hsplit (p.1⁻¹) x with hw
    have hwc : (w : G) = (p.1 : G)⁻¹ * (x : G) * (p.1 : G) := by
      rw [hw]; simp only [conjQK_coe, Subgroup.coe_inv]; group
    have hψw : D.psi w = (D.Lam (p.1⁻¹) : D.F) • D.psi x := by
      rw [hw]; exact hpsi_conj_smul (p.1⁻¹) x
    have hyw : y = (zetaAct^j) w := by
      apply Subtype.ext
      rw [hy, hcoe_prodEquiv p]
      rw [conjOnQ_pow_coe ζ⁻¹ hζNm' j, inv_pow, inv_inv, ← hzv, hwc]
      group
    have hψy : D.psi y = (D.Lam (p.1⁻¹) : D.F) • ((T^j) (D.psi x)) := by
      rw [hyw, hactT j w, hψw, map_smul]
    have hR : (κ (prodEquiv p) : Work.PSU3.E n) =
        ((ι (D.Lam p.1))⁻¹) * ((e : (Work.PSU3.E n)ˣ) : Work.PSU3.E n)^j := by
      rw [hκ_mul p, hκK_coe p.1, ← hj, hκz_pow j, Units.val_pow_eq_pow_val]
    have hL : β (D.psi y) =
        (ι (D.Lam p.1))⁻¹ * (((e : (Work.PSU3.E n)ˣ) : Work.PSU3.E n)^j * β (D.psi x)) := by
      rw [hψy, hβsmul, hβTpow j (D.psi x),
        show (D.Lam (p.1⁻¹) : D.F) = (D.Lam p.1 : D.F)⁻¹ from by
          rw [map_inv, Units.val_inv_eq_inv_val],
        map_inv₀]
    show β (D.psi y) = (κ (prodEquiv p) : Work.PSU3.E n) * β (D.psi x)
    rw [hL, hR]; ring
  have hactzcK : ∀ d : KW, (d : G) ∈ Work.ThmF.Ksub H t → ∀ y : Work.PSU3.E n,
      Work.PSU3.σE y = y → (d : G)⁻¹ * zc y * d = zc ((nm (κ d) : Work.PSU3.E n) * y) := by
    intro d hd y hy
    obtain ⟨p, rfl⟩ := prodEquiv.surjective d
    have hp2 : p.2 = 1 := (hmκ p).mp hd
    have hdc : (prodEquiv p : G) = (p.1 : G) := by
      rw [hcoe_prodEquiv p, hp2, Subgroup.coe_one, mul_one]
    have hnmκ : nm (κ (prodEquiv p)) = Units.map ι.toMonoidWithZeroHom ((D.rho p.1)⁻¹) := by
      have hφnm : φnm ((D.Lam p.1)⁻¹) = (D.rho p.1)⁻¹ := by
        show (D.rho (LamEquiv.symm (((D.Lam p.1)⁻¹)⁻¹)))⁻¹ = (D.rho p.1)⁻¹
        rw [inv_inv, show LamEquiv.symm (D.Lam p.1) = p.1 from LamEquiv.symm_apply_apply p.1]
      have h1 : κ (prodEquiv p) = Units.map ι.toMonoidWithZeroHom ((D.Lam p.1)⁻¹) := by
        rw [hκabs_apply p, hp2, map_one, mul_one, hκK_apply p.1, map_inv]
      rw [h1, hnm_ext ((D.Lam p.1)⁻¹), hφnm]
    have hyι : y = ι (ιsec y) := (ιsec_spec y hy).symm
    have hcaux : Work.PSU3.σE (ι ((D.rho p.1 : D.F)⁻¹ * ιsec y)) =
        ι ((D.rho p.1 : D.F)⁻¹ * ιsec y) := by
      have hιc : ι ((D.rho p.1 : D.F)⁻¹ * ιsec y) = (ι (D.rho p.1))⁻¹ * y := by
        rw [map_mul, map_inv₀, ιsec_spec y hy]
      rw [hιc, map_mul, map_inv₀, hιfix, hy]
    have harg : (nm (κ (prodEquiv p)) : Work.PSU3.E n) * y =
        ι ((D.rho p.1 : D.F)⁻¹ * ιsec y) := by
      have hnm : (nm (κ (prodEquiv p)) : Work.PSU3.E n) = ι ((D.rho p.1 : D.F)⁻¹) := by
        rw [hnmκ, Units.coe_map]; simp
      rw [hnm]
      conv_lhs => rw [hyι]
      rw [← map_mul]
    have hW1 : (p.1 : G)⁻¹ * zc y * (p.1 : G) =
        ((conjQ0 H t (p.1⁻¹) ⟨zc y, hzc_mem y hy⟩ : ↥(Work.ThmF.Q0sub H)) : G) := by
      rw [conjQ0_coe, Subgroup.coe_inv]; group
    have hkey : φ' (conjQ0 H t (p.1⁻¹) ⟨zc y, hzc_mem y hy⟩) =
        φ' (ephi.symm ((D.rho p.1 : D.F)⁻¹ * ιsec y)) := by
      rw [hφ'_conj (p.1⁻¹),
        show (⟨zc y, hzc_mem y hy⟩ : ↥(Work.ThmF.Q0sub H)) = ephi.symm (ιsec y) from by
          apply Subtype.ext; exact zc_fixed y hy]
      rw [← hephi_apply, ephi.apply_symm_apply, ← hephi_apply, ephi.apply_symm_apply]
      rw [show (D.rho (p.1⁻¹) : D.F) = (D.rho p.1 : D.F)⁻¹ from by
        rw [map_inv, Units.val_inv_eq_inv_val]]
    have hW : ((conjQ0 H t (p.1⁻¹) ⟨zc y, hzc_mem y hy⟩ : ↥(Work.ThmF.Q0sub H)) : G) =
        ((ephi.symm ((D.rho p.1 : D.F)⁻¹ * ιsec y) : ↥(Work.ThmF.Q0sub H)) : G) :=
      congrArg Subtype.val (ephi.injective hkey)
    have hR : zc ((nm (κ (prodEquiv p)) : Work.PSU3.E n) * y) =
        ((ephi.symm ((D.rho p.1 : D.F)⁻¹ * ιsec y) : ↥(Work.ThmF.Q0sub H)) : G) := by
      rw [harg, zc_fixed _ (hιfix _), hιsec_apply ((D.rho p.1 : D.F)⁻¹ * ιsec y) hcaux]
    rw [hdc, hW1, hR, hW]
  have hactzcζ : ∀ y : Work.PSU3.E n, Work.PSU3.σE y = y →
      (ζKW : G)⁻¹ * zc y * ζKW = zc y := by
    intro y hy
    have hz0 : zc y ∈ Work.ThmF.Q0sub H := hzc_mem y hy
    have hcomm : (zc y) * ζ = ζ * (zc y) :=
      Subgroup.mem_centralizer_singleton_iff.mp (hζcenQ0sub hz0)
    rw [hζKW_coe, mul_assoc, hcomm, ← mul_assoc, inv_mul_cancel, one_mul]
  have hzc_s : t * zc 1 * t = zc 1 * t * zc 1 := by rw [hzc_one]; exact hst
  exact ⟨{ Q0 := Work.ThmF.Q0sub H
           Q0_le := hQ0leQ
           Q0_central := hQ0central
           mem_Q0_iff := hmemQ0
           sq_mem_Q0 := hsq
           bar := bar
           bar_surjective := hbar_surj
           bar_eq_one_iff := hbar_ker
           zc := zc
           zc_mem := hzc_mem
           zc_add := hzc_add
           zc_surj := hzc_surj
           zc_inj := hzc_inj
           s_struct := hzc_s
           KW := KW
           KW_le := hKW_le
           KW_normal := hKW_norm
           K_le := hK_le
           κ := κ
           κ_injective := hκ_inj
           mem_K_iff := hmemK
           K_surj := hKsurj
           ζ := ζKW
           ζ_mem_W := hζ
           ζ_ne_one := hζKW_ne
           ζ_norm := hζnorm
           KW_gen := hKWgen
           W_semireg := hW
           act_bar := hactbar
           nm := nm
           nm_F := hnm_F
           act_zc_K := hactzcK
           act_zc_ζ := hactzcζ }, hzc_one, rfl⟩

end Work.PSU3.StageA
