import Mathlib
import Submission.Work.PSU3.StageB.Omega.API
import Submission.Work.PSU3.StageB.Omega.Seq
import Submission.Work.PSU3.StageB.ThetaOmegaAux
import Submission.Work.PSU3.StageB.Omega.fcan_step10
import Submission.Work.PSU3.StageB.Omega.uSeq_rec
import Submission.Work.PSU3.StageB.Omega.uSeq_div
import Submission.Work.PSU3.StageB.Omega.uSeq_telescope
import Submission.Work.PSU3.StageB.Omega.beta_pow_m_eq_one
import Submission.Work.PSU3.StageB.Omega.exists_beta
import Submission.Work.PSU3.StageB.Omega.orderOf_beta_eq

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false
set_option maxHeartbeats 2000000

open LeanEval.GroupTheory.Defs
open Submission.Blueprint
open Classical

namespace Work.PSU3.StageB.Omega

open Work.PSU3
open Work.PSU3.StageB
open Work.ThmF

variable {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G} {n : ℕ}

/-! ## `E 0` and the non-degeneracy `1 ≤ n` -/

open Polynomial in
/-- `E 0 = GF(2^0)`: the degenerate exponent still gives a two-element field (the splitting
field of `0`), whose unit group is trivial. -/
private lemma card_E_zero : Nat.card (E 0) = 2 := by
  have h1 : (E 0) = Polynomial.SplittingField (0 : (ZMod 2)[X]) := by
    show GaloisField 2 (2 * 0) = _
    rw [show (2 : ℕ) * 0 = 0 from rfl]
    show Polynomial.SplittingField (X ^ 2 ^ 0 - X : (ZMod 2)[X]) = _
    rw [show (2 : ℕ) ^ 0 = 1 from rfl, pow_one, sub_self]
  rw [h1]
  rw [Nat.card_congr (Polynomial.SplittingField.algEquivSplittingFieldAux
    (0 : (ZMod 2)[X])).toEquiv]
  rw [show (0 : (ZMod 2)[X]).natDegree = 0 from Polynomial.natDegree_zero]
  show Nat.card (Polynomial.SplittingFieldAux 0 (0 : (ZMod 2)[X])) = 2
  rw [show Polynomial.SplittingFieldAux 0 (0 : (ZMod 2)[X]) = ZMod 2 from rfl]
  simp

/-- A `CoarseFrame` at exponent `n` forces `1 ≤ n`: at `n = 0` the field `E 0` is
`ZMod 2`, so its unit group is trivial and `κ` could not be injective on `KW ∋ ζ ≠ 1`. -/
theorem frame_one_le_n {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G} {n : ℕ}
    (fr : Work.PSU3.CoarseFrame H Q t n) : 1 ≤ n := by
  by_contra h
  have hn : n = 0 := by omega
  subst hn
  have hunits : Nat.card ((E 0)ˣ) = 1 := by
    have h1 := Nat.card_eq_card_units_add_one (α := E 0)
    rw [card_E_zero] at h1
    omega
  haveI : Subsingleton ((E 0)ˣ) := (Nat.card_eq_one_iff_unique.mp hunits).1
  exact fr.ζ_ne_one (fr.κ_injective (Subsingleton.elim _ _))

/-! ## The units `u_i = uSeq β i` of §2 (13) -/

/-- `fval` as a monoid homomorphism (into `E n` with its multiplicative structure). -/
noncomputable def fvalHom (n : ℕ) : ↥(FX n) →* E n where
  toFun u := fval u
  map_one' := fval_one
  map_mul' u v := fval_mul u v

/-- `u_i = uSeq β i` as an element of `F*` (junk value `1` where `uSeq β i = 0`). -/
noncomputable def uSeqUnit (β : E n) (hβ : β ≠ 0) (hσ : σE β = β ∨ σE β = β⁻¹) :
    ℕ → ↥(FX n) :=
  fun i => if h : uSeq β i ≠ 0 then mkFX (uSeq β i) (uSeq_fixed β hβ hσ i) h else 1

lemma fval_uSeqUnit (β : E n) (hβ : β ≠ 0) (hσ : σE β = β ∨ σE β = β⁻¹) {i : ℕ}
    (h : uSeq β i ≠ 0) : fval (uSeqUnit β hβ hσ i) = uSeq β i := by
  unfold uSeqUnit
  rw [dite_eq_left h]
  exact fval_mkFX (uSeq β i) (uSeq_fixed β hβ hσ i) h

lemma zU_eq_zcQF (fr : CoarseFrame H Q t n) (β : E n) (hβ : β ≠ 0)
    (hσ : σE β = β ∨ σE β = β⁻¹) {i : ℕ} (h : uSeq β i ≠ 0) :
    zU fr β hβ hσ i = zcQF fr (uSeqUnit β hβ hσ i) := by
  apply Subtype.ext
  rw [zU_coe, zcQF_coe, fval_uSeqUnit β hβ hσ h]

/-! ## The `h`-component of H6, §2 (18) recursion -/

/-- The `h`-part of H6 for `x = ω ∈ Q ∖ Q₀` and `y = zc u`: for `σE v = v` with
`v = fval α + (fval u)⁻¹`,

  `h(ω · zc u) = h(ω) · ζ⁻¹ · h(ω · zc v) · ζ · (kElF (τ u))²`.

This is the recursion underlying §2 (18). -/
theorem hcan_mul_zcQF_rec (hS : PSU3Hyp H Q t) (fr : CoarseFrame H Q t n)
    {ω : ↥Q} (hω : (ω : G) ∉ fr.Q0) {α : ↥(FX n)}
    (hωf : fcan hS.split ω = qconj hS.split (zetaD fr) (ω * zcQF fr α))
    {U : ↥(FX n)} {v : E n} (hv : σE v = v) (huv : v = fval α + (fval U)⁻¹) :
    (hcan hS.split (ω * zcQF fr U) : G) =
      (hcan hS.split ω : G) * (fr.ζ : G)⁻¹ *
        (hcan hS.split (ω * zcQ fr v hv) : G) * (fr.ζ : G) *
        (((kElF fr (tau hS fr U)) ^ 2 : fr.KW) : G) := by
  have hω1 : (ω : G) ≠ 1 := fun hc => hω (by rw [hc]; exact Q0_one_mem fr)
  have hzUQ0 : (zcQF fr U : G) ∈ fr.Q0 := by rw [zcQF_coe]; exact fr.zc_mem (fval U) U.2
  have hy1 : ((zcQF fr U : ↥Q) : G) ≠ 1 := zcQF_ne_one fr U
  have hxy : ((ω * zcQF fr U : ↥Q) : G) ≠ 1 := by
    intro hc
    have h2 : (ω : G) = ((ω * zcQF fr U : ↥Q) : G) * ((zcQF fr U : ↥Q) : G)⁻¹ := by
      rw [Subgroup.coe_mul]; group
    exact hω (by rw [h2, hc, one_mul]; exact fr.Q0.inv_mem hzUQ0)
  have hX : ((ω * zcQ fr v hv : ↥Q) : G) ≠ 1 := by
    intro hc
    have hmem : (zcQ fr v hv : G) ∈ fr.Q0 := by rw [zcQ_coe]; exact fr.zc_mem v hv
    have h2 : (ω : G) = ((ω * zcQ fr v hv : ↥Q) : G) * (zcQ fr v hv : G)⁻¹ := by
      rw [Subgroup.coe_mul]; group
    exact hω (by rw [h2, hc, one_mul]; exact fr.Q0.inv_mem hmem)
  -- the middle term of H6
  have hmid : fcan hS.split ω * zcQF fr U⁻¹ =
      qconj hS.split ⟨(fr.ζ : G), zeta_mem_D fr⟩ (ω * zcQ fr v hv) := by
    apply Subtype.ext
    show (fcan hS.split ω : G) * (zcQF fr U⁻¹ : G)
        = (fr.ζ : G)⁻¹ * ((ω : G) * (zcQ fr v hv : G)) * (fr.ζ : G)
    have hf : (fcan hS.split ω : G)
        = (fr.ζ : G)⁻¹ * ((ω : G) * (zcQF fr α : G)) * (fr.ζ : G) := by
      have hh := congrArg (fun z : ↥Q => (z : G)) hωf
      rw [qconj_coe, Subgroup.coe_mul] at hh
      exact hh
    have hzc : (zcQ fr v hv : G) = (zcQF fr α : G) * (zcQF fr U⁻¹ : G) := by
      rw [zcQ_coe, zcQF_coe, zcQF_coe, huv]
      rw [fr.zc_add (fval α) ((fval U)⁻¹) α.2 (by rw [map_inv₀, U.2]), fval_inv]
    rw [hf, hzc]
    have hcz' : (fr.ζ : G) * (zcQF fr U⁻¹ : G) = (zcQF fr U⁻¹ : G) * (fr.ζ : G) :=
      zeta_comm_zcQF fr U⁻¹
    calc (fr.ζ : G)⁻¹ * ((ω : G) * (zcQF fr α : G)) * (fr.ζ : G) * (zcQF fr U⁻¹ : G)
        = (fr.ζ : G)⁻¹ * (ω : G) * (zcQF fr α : G) * ((fr.ζ : G) * (zcQF fr U⁻¹ : G)) := by
          group
      _ = (fr.ζ : G)⁻¹ * (ω : G) * (zcQF fr α : G) * ((zcQF fr U⁻¹ : G) * (fr.ζ : G)) := by
          rw [hcz']
      _ = (fr.ζ : G)⁻¹ * ((ω : G) * ((zcQF fr α : G) * (zcQF fr U⁻¹ : G))) *
            (fr.ζ : G) := by group
  have hconj : (hcan hS.split (fcan hS.split ω * zcQF fr U⁻¹) : G)
      = (fr.ζ : G)⁻¹ * (hcan hS.split (ω * zcQ fr v hv) : G) * (fr.ζ : G) := by
    rw [hmid, hcan_qconj hS.split hX ⟨(fr.ζ : G), zeta_mem_D fr⟩, t_zeta_t hS.split fr]
  have h6 : (hcan hS.split (ω * zcQF fr U) : G)
      = (hcan hS.split ω : G) *
          (hcan hS.split (fcan hS.split ω * gcan hS.split (zcQF fr U)) : G) *
          (hcan hS.split (zcQF fr U) : G) := (canon_mul_fun hS.split hω1 hy1 hxy).2
  rw [gcan_zcQF' hS fr U, (canon_zcQF fr hS U).2.2, hconj] at h6
  rw [show (((kElF fr (tau hS fr U)) ^ 2 : fr.KW) : G)
      = (kElF fr (tau hS fr U) : G) * (kElF fr (tau hS fr U) : G) from by
    rw [pow_two, Subgroup.coe_mul]]
  rw [h6]
  group

/-! ## The main theorem -/

theorem hcan_pow_m_eq_one {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G} {n : ℕ}
    (hS : Work.PSU3.PSU3Hyp H Q t) (fr : Work.PSU3.CoarseFrame H Q t n)
    {ω : ↥Q} (hω : (ω : G) ∉ fr.Q0) {α : ↥(Work.PSU3.StageB.FX n)}
    (hωf : Work.PSU3.StageB.fcan hS.split ω =
      Work.PSU3.StageB.qconj hS.split (Work.PSU3.StageB.zetaD fr)
        (ω * Work.PSU3.StageB.zcQF fr α)) :
    (((Work.PSU3.StageB.hcan hS.split ω : G) * (fr.ζ : G)⁻¹) ^ (orderOf fr.ζ)) = 1 := by
  have hn : 1 ≤ n := frame_one_le_n fr
  have hα0 : fval α ≠ 0 := Units.ne_zero α.1
  obtain ⟨β, hβ0, hβα, hσ0⟩ := exists_beta hn (fval α) α.2
  have hσ : σE β = β ∨ σE β = β⁻¹ := hσ0.symm
  set X : G := (hcan hS.split ω : G) * (fr.ζ : G)⁻¹ with hXdef
  obtain ⟨m, hmdef, hm, hβord⟩ : ∃ m : ℕ, m = orderOf fr.ζ ∧ β ^ m = 1 ∧ orderOf β = m :=
    ⟨orderOf fr.ζ, rfl, beta_pow_m_eq_one hS fr hω hωf hβ0 hβα,
      orderOf_beta_eq hS fr hω hωf hβ0 hβα⟩
  have hmne1 : m ≠ 1 := by
    rw [hmdef]
    intro h
    exact fr.ζ_ne_one (orderOf_eq_one_iff.mp h)
  have hmne0 : m ≠ 0 := by
    rw [hmdef]
    exact orderOf_ne_zero_iff.mpr (isOfFinOrder_of_finite fr.ζ)
  have hm2 : 2 ≤ m := by omega
  have hm3 : 3 ≤ m := by
    by_contra hcon
    have h2 : m = 2 := by omega
    have hm' := hm
    rw [h2] at hm'
    have hb2 : β * β = 1 := by rwa [pow_two] at hm'
    have hβ1 : β = 1 := eq_one_of_mul_self_eq_one hb2
    rw [hβ1, inv_one, CharTwo.add_self_eq_zero] at hβα
    exact hα0 hβα.symm
  have hβj : ∀ j, 1 ≤ j → j < m → β ^ j ≠ 1 := by
    intro j hj hjlt h
    have hdvd : orderOf β ∣ j := orderOf_dvd_iff_pow_eq_one.mpr h
    rw [hβord] at hdvd
    have := Nat.le_of_dvd hj hdvd
    omega
  have hbS : ∀ j, 1 ≤ j → j ≤ m - 1 → bS β j ≠ 0 := by
    intro j hj hjm
    rw [bS_ne_zero_iff β hβ0 j]
    exact hβj j hj (by omega)
  -- the units `u_i ∈ F*`
  have hUval : ∀ i, 2 ≤ i → i ≤ m - 1 → fval (uSeqUnit β hβ0 hσ i) = uSeq β i := by
    intro i hi hiN
    refine fval_uSeqUnit β hβ0 hσ ?_
    rw [uSeq_eq_div' β hβ0 (show 1 ≤ i by omega)]
    exact div_ne_zero (hbS (i - 1) (by omega) (by omega)) (hbS i (by omega) hiN)
  -- `u_{m-1} = α`
  have huN : uSeq β (m - 1) = fval α :=
    uSeq_ord_sub_one hβ0 hβα hα0 hm2 hm
  -- `∏_{j = 2}^{m-1} u_j = 1`
  have hprodU : (∏ j ∈ Finset.Icc 2 (m - 1), uSeqUnit β hβ0 hσ j : ↥(FX n)) = 1 := by
    apply fval_inj
    rw [fval_one]
    show fvalHom n (∏ j ∈ Finset.Icc 2 (m - 1), uSeqUnit β hβ0 hσ j) = 1
    rw [map_prod]
    have h1 : ∀ j ∈ Finset.Icc 2 (m - 1), fvalHom n (uSeqUnit β hβ0 hσ j) = uSeq β j := by
      intro j hj
      rw [Finset.mem_Icc] at hj
      exact hUval j (by omega) (by omega)
    rw [Finset.prod_congr rfl h1]
    rw [uSeq_telescope (fval α) β hβα hβ0 (by omega)
      (fun j hj hjk => hbS j (by omega) (by omega))]
    have hbm1 : β ^ (m - 1) = β⁻¹ := by
      have h2 : β ^ (m - 1) * β = 1 := by
        rw [← pow_succ, show m - 1 + 1 = m from by omega]
        exact hm
      exact eq_inv_of_mul_eq_one_left h2
    rw [hbm1, inv_inv, add_comm, hβα, div_self hα0]
  -- abbreviations for the induction
  let hpU : ℕ → ↥(FX n) := fun i => (tau hS fr (uSeqUnit β hβ0 hσ i)) ^ 2
  let P : ℕ → ↥(FX n) := fun i => ∏ j ∈ Finset.Icc 2 i, hpU j
  let z : ℕ → G := fun i => (hcan hS.split (ω * zU fr β hβ0 hσ i) : G)
  have hkeq : ∀ i, kElF fr (hpU i)
      = ((kElF fr (tau hS fr (uSeqUnit β hβ0 hσ i))) ^ 2 : fr.KW) := by
    intro i
    show kElF fr ((tau hS fr (uSeqUnit β hβ0 hσ i)) ^ 2) = _
    rw [pow_two, kElF_mul, pow_two]
  -- `P (m-1) = 1`
  have hP1 : P (m - 1) = 1 := by
    show (∏ j ∈ Finset.Icc 2 (m - 1), hpU j : ↥(FX n)) = 1
    show (∏ j ∈ Finset.Icc 2 (m - 1),
        (tau hS fr (uSeqUnit β hβ0 hσ j)) ^ 2 : ↥(FX n)) = 1
    rw [Finset.prod_pow]
    have h2 : (∏ j ∈ Finset.Icc 2 (m - 1), tau hS fr (uSeqUnit β hβ0 hσ j))
        = tau hS fr (∏ j ∈ Finset.Icc 2 (m - 1), uSeqUnit β hβ0 hσ j) := by
      rw [map_prod]
    rw [h2, hprodU, map_one, one_pow]
  -- the recursion
  have hrec : ∀ i, 2 ≤ i → i ≤ m - 1 →
      z i = X * z (i - 1) * (fr.ζ : G) * ((kElF fr (hpU i) : fr.KW) : G) := by
    intro i hi hiN
    have hUi : uSeq β i ≠ 0 := by
      rw [uSeq_eq_div' β hβ0 (show 1 ≤ i by omega)]
      exact div_ne_zero (hbS (i - 1) (by omega) (by omega)) (hbS i (by omega) hiN)
    have hzi : zU fr β hβ0 hσ i = zcQF fr (uSeqUnit β hβ0 hσ i) :=
      zU_eq_zcQF fr β hβ0 hσ hUi
    have hzim1 : ω * zcQ fr (uSeq β (i - 1)) (uSeq_fixed β hβ0 hσ (i - 1))
        = ω * zU fr β hβ0 hσ (i - 1) := rfl
    have huv : uSeq β (i - 1) = fval α + (fval (uSeqUnit β hβ0 hσ i))⁻¹ := by
      rw [hUval i hi hiN]
      have hr := uSeq_rec_alpha (fval α) β hβα hβ0 (show 1 ≤ i - 1 by omega)
        (hbS (i - 1) (by omega) (by omega))
        (by rw [show i - 1 + 1 = i from by omega]; exact hbS i (by omega) hiN)
      rw [show i - 1 + 1 = i from by omega] at hr
      exact hr.symm
    have h := hcan_mul_zcQF_rec hS fr hω hωf (uSeq_fixed β hβ0 hσ (i - 1)) huv
    rw [← hzi, hzim1, ← hkeq i] at h
    rw [hXdef]
    show (hcan hS.split (ω * zU fr β hβ0 hσ i) : G)
        = (hcan hS.split ω : G) * (fr.ζ : G)⁻¹ *
          (hcan hS.split (ω * zU fr β hβ0 hσ (i - 1)) : G) * (fr.ζ : G) *
          ((kElF fr (hpU i) : fr.KW) : G)
    rw [h]
  have keybase : z 1 = X ^ 1 * ((kElF fr (P 1) : fr.KW) : G) * (fr.ζ : G) ^ 1 := by
    have hz1 : zU fr β hβ0 hσ 1 = (1 : ↥Q) := by
      apply Subtype.ext
      rw [zU_coe, uSeq_one, zc_zero]
      rfl
    have hP1' : P 1 = 1 := by
      show (∏ j ∈ Finset.Icc 2 1, hpU j : ↥(FX n)) = 1
      rw [Finset.Icc_eq_empty_of_lt (show 1 < 2 by omega), Finset.prod_empty]
    have hz : z 1 = (hcan hS.split ω : G) := by
      show (hcan hS.split (ω * zU fr β hβ0 hσ 1) : G) = (hcan hS.split ω : G)
      rw [hz1, mul_one]
    have hK : ((kElF fr (P 1) : fr.KW) : G) = 1 := by
      rw [hP1', kElF_one, Subgroup.coe_one]
    rw [hz, hK, pow_one, pow_one, hXdef]
    group
  have hPstep : ∀ i, 1 ≤ i → kElF fr (P (i + 1))
      = kElF fr (P i) * kElF fr (hpU (i + 1)) := by
    intro i hi
    show kElF fr (∏ j ∈ Finset.Icc 2 (i + 1), hpU j)
        = kElF fr (∏ j ∈ Finset.Icc 2 i, hpU j) * kElF fr (hpU (i + 1))
    rw [Finset.prod_Icc_succ_top (a := 2) (b := i) (f := hpU) (by omega), kElF_mul]
  have key : ∀ i, 1 ≤ i → i ≤ m - 1 →
      z i = X ^ i * ((kElF fr (P i) : fr.KW) : G) * (fr.ζ : G) ^ i := by
    have aux : ∀ k, 1 + k ≤ m - 1 →
        z (1 + k) = X ^ (1 + k) * ((kElF fr (P (1 + k)) : fr.KW) : G) *
          (fr.ζ : G) ^ (1 + k) := by
      intro k
      induction k with
      | zero => intro _; simpa using keybase
      | succ k ih =>
          intro hk
          show z (1 + k + 1) = X ^ (1 + k + 1) * ((kElF fr (P (1 + k + 1)) : fr.KW) : G) *
            (fr.ζ : G) ^ (1 + k + 1)
          have hprev : 1 + k ≤ m - 1 := by omega
          have hile : 1 + k + 1 ≤ m - 1 := by omega
          have hrc := hrec (1 + k + 1) (by omega) hile
          rw [show 1 + k + 1 - 1 = 1 + k from by omega] at hrc
          rw [ih hprev] at hrc
          rw [hPstep (1 + k) (by omega), Subgroup.coe_mul]
          rw [hrc]
          have hcomm : (fr.ζ : G) ^ (1 + k + 1) * ((kElF fr (hpU (1 + k + 1)) : fr.KW) : G)
              = ((kElF fr (hpU (1 + k + 1)) : fr.KW) : G) * (fr.ζ : G) ^ (1 + k + 1) := by
            rw [← Subgroup.coe_pow]
            exact KW_comm fr (fr.ζ ^ (1 + k + 1)) (kElF fr (hpU (1 + k + 1)))
          rw [show X * (X ^ (1 + k) * ((kElF fr (P (1 + k)) : fr.KW) : G) * (fr.ζ : G) ^ (1 + k))
                * (fr.ζ : G) * ((kElF fr (hpU (1 + k + 1)) : fr.KW) : G)
              = (X * X ^ (1 + k)) *
                  ((kElF fr (P (1 + k)) : fr.KW) : G)
                * ((fr.ζ : G) ^ (1 + k) * (fr.ζ : G))
                * ((kElF fr (hpU (1 + k + 1)) : fr.KW) : G) from by group]
          rw [← pow_succ', ← pow_succ]
          rw [show X ^ (1 + k + 1) * ((kElF fr (P (1 + k)) : fr.KW) : G) * (fr.ζ : G) ^ (1 + k + 1)
                * ((kElF fr (hpU (1 + k + 1)) : fr.KW) : G)
              = X ^ (1 + k + 1) * ((kElF fr (P (1 + k)) : fr.KW) : G)
                * ((fr.ζ : G) ^ (1 + k + 1) * ((kElF fr (hpU (1 + k + 1)) : fr.KW) : G))
              from by group]
          rw [hcomm]
          group
    intro i hi hiN
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hi
    exact aux k hiN
  -- evaluate at `i = m - 1`
  have keym := key (m - 1) (by omega) le_rfl
  have hzα : z (m - 1) = (hcan hS.split (ω * zcQF fr α) : G) := by
    show (hcan hS.split (ω * zU fr β hβ0 hσ (m - 1)) : G)
        = (hcan hS.split (ω * zcQF fr α) : G)
    have hz : zU fr β hβ0 hσ (m - 1) = zcQF fr α := by
      apply Subtype.ext
      rw [zU_coe, zcQF_coe, huN]
    rw [hz]
  have hzαinv : (hcan hS.split (ω * zcQF fr α) : G)
      = (fr.ζ : G) * (hcan hS.split ω : G)⁻¹ * (fr.ζ : G)⁻¹ := by
    have hω1 : (ω : G) ≠ 1 := fun hc => hω (by rw [hc]; exact Q0_one_mem fr)
    have hx : ((ω * zcQF fr α : ↥Q) : G) ≠ 1 := by
      intro hc
      have hmem : (zcQF fr α : G) ∈ fr.Q0 := by rw [zcQF_coe]; exact fr.zc_mem (fval α) α.2
      have h2 : (ω : G) = ((ω * zcQF fr α : ↥Q) : G) * (zcQF fr α : G)⁻¹ := by
        rw [Subgroup.coe_mul]; group
      exact hω (by rw [h2, hc, one_mul]; exact fr.Q0.inv_mem hmem)
    have hq : qconj hS.split ⟨(fr.ζ : G), zeta_mem_D fr⟩ (ω * zcQF fr α)
        = fcan hS.split ω := hωf.symm
    have h1 : (hcan hS.split (fcan hS.split ω) : G) = (hcan hS.split ω : G)⁻¹ :=
      (fcan_fcan hS.split hω1).2.1
    have h2 : (hcan hS.split (qconj hS.split ⟨(fr.ζ : G), zeta_mem_D fr⟩ (ω * zcQF fr α)) : G)
        = (fr.ζ : G)⁻¹ * (hcan hS.split (ω * zcQF fr α) : G) * (fr.ζ : G) := by
      rw [hcan_qconj hS.split hx ⟨(fr.ζ : G), zeta_mem_D fr⟩, t_zeta_t hS.split fr]
    have hkey : (fr.ζ : G)⁻¹ * (hcan hS.split (ω * zcQF fr α) : G) * (fr.ζ : G)
        = (hcan hS.split ω : G)⁻¹ := by rw [← h2, hq]; exact h1
    have hgoal : (fr.ζ : G) * ((fr.ζ : G)⁻¹ * (hcan hS.split (ω * zcQF fr α) : G)
        * (fr.ζ : G)) * (fr.ζ : G)⁻¹ = (hcan hS.split (ω * zcQF fr α) : G) := by group
    rw [hkey] at hgoal
    exact hgoal.symm
  rw [hzα, hzαinv, hP1, kElF_one, Subgroup.coe_one, mul_one] at keym
  -- keym : ζ * h(ω)⁻¹ * ζ⁻¹ = X^(m-1) * ζ^(m-1)
  have hmul := congrArg (fun y : G => X * y) keym
  have hlhs : X * ((fr.ζ : G) * (hcan hS.split ω : G)⁻¹ * (fr.ζ : G)⁻¹)
      = (fr.ζ : G)⁻¹ := by rw [hXdef]; group
  have hrhs : X * (X ^ (m - 1) * (fr.ζ : G) ^ (m - 1)) = X ^ m * (fr.ζ : G) ^ (m - 1) := by
    rw [show X * (X ^ (m - 1) * (fr.ζ : G) ^ (m - 1))
        = (X * X ^ (m - 1)) * (fr.ζ : G) ^ (m - 1) from by group]
    rw [← pow_succ', show m - 1 + 1 = m from by omega]
  have hstep : X ^ m * (fr.ζ : G) ^ (m - 1) = (fr.ζ : G)⁻¹ := by
    rw [← hrhs]
    exact hmul.symm.trans hlhs
  have hζmKW : (fr.ζ : fr.KW) ^ m = 1 := by rw [hmdef]; exact pow_orderOf_eq_one fr.ζ
  have hζm : (fr.ζ : G) ^ m = 1 := by
    rw [← Subgroup.coe_pow, hζmKW, Subgroup.coe_one]
  have hfin : X ^ m = 1 := by
    have h3 : X ^ m = (fr.ζ : G)⁻¹ * ((fr.ζ : G) ^ (m - 1))⁻¹ := by
      rw [← hstep]; group
    rw [h3, ← mul_inv_rev, ← pow_succ, show m - 1 + 1 = m from by omega, hζm, inv_one]
  rw [← hmdef]
  exact hfin

end Work.PSU3.StageB.Omega
