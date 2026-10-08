import Mathlib
import Submission.Work.PSU3.Defs
import Submission.Work.ThmF.Setup
import Submission.Work.PSU3.StageB.Step1
import Submission.Work.PSU3.StageB.Frame
import Submission.Work.PSU3.StageB.Omega.API
import Submission.Work.PSU3.StageB.Omega.alpha_eq_of_two_orbits
import Submission.Work.PSU3.StageB.Omega.hcan_pow_m_eq_one
import Submission.Work.PSU3.StageB.Canon
import Submission.Work.PSU3.StageB.ThetaOmegaAux
import Submission.Work.PSU3.StageB.NotFpfStep4.etaAction_semilinear
import Submission.Work.PSU3.StageB.NotFpfStep4.bar_fcan_step4_3
import Submission.Work.PSU3.StageB.NotFpfStep4.step4_rel4
import Submission.Work.PSU3.StageB.NotFpfStep4.step4_algebra

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace Work.PSU3.StageB.NotFpfStep4

open LeanEval.GroupTheory.Defs
open Submission.Blueprint
open Work.RankOneUniqueness
open Work.ThmF
open Work.PSU3
open Work.PSU3.StageB

variable {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G} {n : ℕ}

/-- If the ring automorphism `μ` of `E = Q/Q₀` induced by `η ∈ V` fixes the fixed field of
`σE` pointwise, then `η` centralises `KW`; together with `η ∈ V` this gives `η ∈ W`. -/
lemma mem_W_of_mu_fix_F (hS : PSU3Hyp H Q t) {fr : CoarseFrame H Q t n} {η : G}
    (hηV : η ∈ centD H t)
    (hηN : ∀ d : fr.KW, ∃ e : fr.KW, (e : G) = η⁻¹ * (d : G) * η)
    {μ : Work.PSU3.E n ≃+* Work.PSU3.E n}
    (hμκ : ∀ (d e : fr.KW), (e : G) = η⁻¹ * (d : G) * η → fr.κ e = μ (fr.κ d))
    (hfix : ∀ x : Work.PSU3.E n, Work.PSU3.σE x = x → μ x = x) :
    η ∈ W H t := by
  rw [le_W_iff]
  refine ⟨hηV, ?_⟩
  intro a ha
  have haKW : a ∈ fr.KW := mem_KW_of_mem_Kset fr ha
  have haKsub : a ∈ Ksub H t := Kset_le_Ksub H t ha
  obtain ⟨e, he⟩ := hηN ⟨a, haKW⟩
  have hκa : Work.PSU3.σE (fr.κ (⟨a, haKW⟩ : fr.KW) : Work.PSU3.E n)
      = (fr.κ (⟨a, haKW⟩ : fr.KW) : Work.PSU3.E n) :=
    (fr.mem_K_iff ⟨a, haKW⟩).mp (by simpa using haKsub)
  have hκe : (fr.κ e : Work.PSU3.E n) = (fr.κ (⟨a, haKW⟩ : fr.KW) : Work.PSU3.E n) := by
    rw [hμκ ⟨a, haKW⟩ e he, hfix _ hκa]
  have hee : e = ⟨a, haKW⟩ := fr.κ_injective (Units.ext hκe)
  have hea : (e : G) = a := by rw [hee]
  have hconj : η⁻¹ * a * η = a := by rw [← he, hea]
  have h2 : a * η = η * a := by
    have h := congrArg (fun z => η * z) hconj
    simpa [mul_assoc] using h
  exact h2

/-- `μ` (the `η`-action on `E`) preserves the fixed field `F` of `σE`. -/
lemma mu_mem_F (hS : PSU3Hyp H Q t) {fr : CoarseFrame H Q t n} {η : G}
    (hηV : η ∈ centD H t)
    (hηN : ∀ d : fr.KW, ∃ e : fr.KW, (e : G) = η⁻¹ * (d : G) * η)
    {μ : Work.PSU3.E n ≃+* Work.PSU3.E n}
    (hμκ : ∀ (d e : fr.KW), (e : G) = η⁻¹ * (d : G) * η → fr.κ e = μ (fr.κ d)) :
    ∀ x : Work.PSU3.E n, Work.PSU3.σE x = x → Work.PSU3.σE (μ x) = μ x := by
  have ht : t * t = 1 := mul_self_eq_one hS.split
  have htinv : t⁻¹ = t := inv_eq_self hS.split
  have hnorm : ∀ d : fr.KW, (d : G) ∈ Ksub H t → η⁻¹ * (d : G) * η ∈ Ksub H t := by
    intro d hd
    have hdD : (d : G) ∈ twoPoint H t := fr.KW_le d.2
    have hed : η⁻¹ * (d : G) * η ∈ twoPoint H t := by
      refine (twoPoint H t).mul_mem ((twoPoint H t).mul_mem ((twoPoint H t).inv_mem
        (centD_le_twoPoint (H := H) t hηV)) hdD) (centD_le_twoPoint (H := H) t hηV)
    have htd : t * (d : G) * t = (d : G)⁻¹ := tconj_eq_inv hS.split fr hd
    have htη : t * η * t = η := by
      have hcomm : η * t = t * η :=
        ((Subgroup.mem_inf.mp hηV).2 t (Set.mem_singleton t)).symm
      rw [show t * η = η * t from hcomm.symm, mul_assoc, ht, mul_one]
    have htηinv : t * η⁻¹ * t = η⁻¹ := by
      have hcomm : t * η = η * t :=
        ((Subgroup.mem_inf.mp hηV).2 t (Set.mem_singleton t))
      have h2 : t * η⁻¹ = η⁻¹ * t := by
        have h3 := congrArg Inv.inv hcomm
        simp only [mul_inv_rev] at h3
        simpa [htinv] using h3.symm
      rw [h2, mul_assoc, ht, mul_one]
    have hconj : t * (η⁻¹ * (d : G) * η) * t = (η⁻¹ * (d : G) * η)⁻¹ := by
      rw [conj_mul_self ht (η⁻¹ * (d : G)) η, conj_mul_self ht η⁻¹ (d : G),
        htηinv, htd, htη]
      group
    exact Kset_le_Ksub H t ⟨hed, by rw [htinv]; exact hconj⟩
  intro x hx
  rcases eq_or_ne x 0 with rfl | hx0
  · rw [map_zero, map_zero]
  · obtain ⟨d, hd⟩ := fr.K_surj (Units.mk0 x hx0) hx
    have hdx : (fr.κ d : Work.PSU3.E n) = x := by rw [hd]; exact Units.val_mk0 hx0
    have hdK : (d : G) ∈ Ksub H t := (fr.mem_K_iff d).mpr (by rw [hdx]; exact hx)
    obtain ⟨e, he⟩ := hηN d
    have hκe : fr.κ e = μ (fr.κ d) := hμκ d e he
    have heK : (e : G) ∈ Ksub H t := by
      have h2 : (e : G) = η⁻¹ * (d : G) * η := he
      rw [h2]; exact hnorm d hdK
    have hfixe : Work.PSU3.σE (fr.κ e : Work.PSU3.E n) = (fr.κ e : Work.PSU3.E n) :=
      (fr.mem_K_iff e).mp heK
    rw [← hdx, ← hκe]
    exact hfixe

/-- From §2 (18) (`hcan_pow_m_eq_one`) and `h(ω) = ζ³η⁻¹`: `η ^ orderOf ζ = 1`. -/
lemma orderOf_eta_dvd_orderOf_zeta (hS : PSU3Hyp H Q t) {fr : CoarseFrame H Q t n}
    {ω : ↥Q} (hω : (ω : G) ∉ fr.Q0) {α : ↥(Work.PSU3.StageB.FX n)}
    (hf : fcan hS.split ω = qconj hS.split (zetaD fr) (ω * zcQF fr α))
    {η : G} (hh : (hcan hS.split ω : G) = (fr.ζ : G) ^ 3 * η⁻¹)
    (hcentζ : η * (fr.ζ : G) = (fr.ζ : G) * η) :
    orderOf η ∣ orderOf (fr.ζ : G) := by
  rw [orderOf_dvd_iff_pow_eq_one]
  have hm : ((hcan hS.split ω : G) * (fr.ζ : G)⁻¹) ^ (orderOf (fr.ζ : G)) = 1 := by
    have h := Work.PSU3.StageB.Omega.hcan_pow_m_eq_one hS fr hω hf
    convert h using 2
    exact Subgroup.orderOf_coe fr.ζ
  -- rewrite the base as `ζ² η⁻¹`
  have hX : (hcan hS.split ω : G) * (fr.ζ : G)⁻¹ = (fr.ζ : G) ^ 2 * η⁻¹ := by
    rw [hh]
    have hc : η⁻¹ * (fr.ζ : G)⁻¹ = (fr.ζ : G)⁻¹ * η⁻¹ := by
      have h3 := congrArg Inv.inv hcentζ
      simpa [mul_inv_rev] using h3.symm
    rw [mul_assoc, hc]
    group
  rw [hX] at hm
  -- `(ζ² η⁻¹)^m = 1`; since ζ, η commute this is `ζ^(2m) (η⁻¹)^m = 1`
  have hc : Commute ((fr.ζ : G) ^ 2) η⁻¹ := by
    have h1 : Commute η (fr.ζ : G) := hcentζ
    exact (h1.inv_left.pow_right 2).symm
  rw [hc.mul_pow] at hm
  have hz : ((fr.ζ : G) ^ 2) ^ (orderOf (fr.ζ : G)) = 1 := by
    rw [← pow_mul, Nat.mul_comm, pow_mul, pow_orderOf_eq_one, one_pow]
  rw [hz, one_mul] at hm
  -- `(η⁻¹)^m = 1` gives `η^m = 1`
  have : η ^ (orderOf (fr.ζ : G)) = 1 := by
    have h4 := congrArg Inv.inv hm
    simpa using h4
  exact this

/-- `orderOf fr.ζ` is odd: `fr.ζ` lies in `D = twoPoint H t`, whose order is odd. -/
lemma odd_orderOf_zeta (hS : PSU3Hyp H Q t) (fr : CoarseFrame H Q t n) :
    Odd (orderOf (fr.ζ : G)) := by
  have hodd : Odd (Nat.card ↥(twoPoint H t)) := split_odd_card_twoPoint hS.split
  have h2 : orderOf (fr.ζ : G)
      = orderOf (⟨(fr.ζ : G), fr.KW_le fr.ζ.2⟩ : ↥(twoPoint H t)) :=
    Subgroup.orderOf_coe (⟨(fr.ζ : G), fr.KW_le fr.ζ.2⟩ : ↥(twoPoint H t))
  have hdvd : orderOf (fr.ζ : G) ∣ Nat.card ↥(twoPoint H t) := by
    rw [h2]
    exact orderOf_dvd_natCard _
  exact hodd.of_dvd_nat hdvd

/-- `μ ^ k` acts on `E` as the `k`-th power of `η` acts on `Q/Q₀`. -/
lemma mu_pow_eq (hS : PSU3Hyp H Q t) {fr : CoarseFrame H Q t n} {η : G}
    (hηV : η ∈ centD H t)
    {μ : Work.PSU3.E n ≃+* Work.PSU3.E n}
    (hμbar : ∀ x : ↥Q, Multiplicative.toAdd (fr.bar (qconj hS.split
        (⟨η, centD_le_twoPoint (H := H) t hηV⟩ : twoPoint H t) x))
      = μ (Multiplicative.toAdd (fr.bar x))) :
    ∀ (k : ℕ) (x : ↥Q), (μ ^ k) (Multiplicative.toAdd (fr.bar x)) =
      Multiplicative.toAdd (fr.bar (qconj hS.split
        (⟨η ^ k, centD_le_twoPoint (H := H) t ((centD H t).pow_mem hηV k)⟩ :
          twoPoint H t) x)) := by
  intro k
  induction k with
  | zero =>
    intro x
    have h1 : (⟨η ^ 0, centD_le_twoPoint (H := H) t ((centD H t).pow_mem hηV 0)⟩ :
        twoPoint H t) = 1 := by
      apply Subtype.ext
      simp
    rw [pow_zero, h1, Work.PSU3.StageB.Omega.qconj_one_eq]
    rfl
  | succ k ih =>
    intro x
    rw [pow_succ']
    change μ ((μ ^ k) (Multiplicative.toAdd (fr.bar x))) = _
    rw [ih, ← hμbar]
    have hqq : qconj hS.split (⟨η, centD_le_twoPoint (H := H) t hηV⟩ : twoPoint H t)
        (qconj hS.split (⟨η ^ k, centD_le_twoPoint (H := H) t ((centD H t).pow_mem hηV k)⟩ :
          twoPoint H t) x)
        = qconj hS.split (⟨η ^ (k + 1), centD_le_twoPoint (H := H) t
            ((centD H t).pow_mem hηV (k + 1))⟩ : twoPoint H t) x := by
      rw [Work.PSU3.StageB.Omega.qconj_mul']
      apply congr_arg (fun (a : twoPoint H t) => qconj hS.split a x)
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subtype.coe_mk]
      rw [pow_succ]
    rw [hqq]

/-- `orderOf μ` divides `orderOf η`. -/
lemma orderOf_mu_dvd_orderOf_eta (hS : PSU3Hyp H Q t) {fr : CoarseFrame H Q t n} {η : G}
    (hηV : η ∈ centD H t)
    {μ : Work.PSU3.E n ≃+* Work.PSU3.E n}
    (hμbar : ∀ x : ↥Q, Multiplicative.toAdd (fr.bar (qconj hS.split
        (⟨η, centD_le_twoPoint (H := H) t hηV⟩ : twoPoint H t) x))
      = μ (Multiplicative.toAdd (fr.bar x))) :
    orderOf μ ∣ orderOf η := by
  rw [orderOf_dvd_iff_pow_eq_one]
  apply RingEquiv.ext
  intro y
  obtain ⟨x, hx⟩ := fr.bar_surjective (Multiplicative.ofAdd y)
  have hy : Multiplicative.toAdd (fr.bar x) = y := by
    rw [hx, toAdd_ofAdd]
  rw [← hy, mu_pow_eq hS hηV hμbar (orderOf η) x]
  have hq : qconj hS.split (⟨η ^ orderOf η, centD_le_twoPoint (H := H) t
      ((centD H t).pow_mem hηV (orderOf η))⟩ : twoPoint H t) x = x := by
    apply Subtype.ext
    rw [qconj_coe]
    show (η ^ orderOf η : G)⁻¹ * (x : G) * (η ^ orderOf η : G) = (x : G)
    rw [pow_orderOf_eq_one η]
    group
  rw [hq]
  rfl

theorem hcan_mem_W_of_step4 {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G} {n : ℕ}
    (hS : Work.PSU3.PSU3Hyp H Q t) (fr : Work.PSU3.CoarseFrame H Q t n)
    {P : Subgroup G} (hPV : P ≤ Submission.Blueprint.centD H t)
    {ω : ↥Q} (hω : (ω : G) ∉ fr.Q0) {α : ↥(Work.PSU3.StageB.FX n)}
    (hf : Work.PSU3.StageB.fcan hS.split ω =
      Work.PSU3.StageB.qconj hS.split (Work.PSU3.StageB.zetaD fr)
        (ω * Work.PSU3.StageB.zcQF fr α))
    (hsq : ω * ω = Work.PSU3.StageB.zcQF fr α)
    {η : G} (hηP : η ∈ P) (hηV : η ∈ Submission.Blueprint.centD H t)
    (hh : (Work.PSU3.StageB.hcan hS.split ω : G) = (fr.ζ : G) ^ 3 * η⁻¹)
    (hcentω : η * (ω : G) = (ω : G) * η) (hcentζ : η * (fr.ζ : G) = (fr.ζ : G) * η)
    (hηN : ∀ d : fr.KW, ∃ e : fr.KW, (e : G) = η⁻¹ * (d : G) * η)
    (hη1 : ∃ s : ↥Q, (s : G) ∉ fr.Q0 ∧ Multiplicative.toAdd (fr.bar s) = 1 ∧
      ((Work.PSU3.StageB.qconj hS.split
          (⟨η, Work.ThmF.centD_le_twoPoint (H := H) t hηV⟩ :
            ↥(Submission.Blueprint.twoPoint H t)) s * s⁻¹ : ↥Q) : G) ∈ fr.Q0) :
    (Work.PSU3.StageB.hcan hS.split ω : G) ∈ Work.ThmF.W H t := by
  -- relation (3) of §4: `bar_fcan_step4_3`
  have h3 : ∀ a b : ↥(Work.PSU3.StageB.FX n),
      Work.PSU3.StageB.fval (Work.PSU3.StageB.nmF fr b) =
        Work.PSU3.StageB.fval α + (Work.PSU3.StageB.fval (Work.PSU3.StageB.nmF fr a))⁻¹ →
      Multiplicative.toAdd (fr.bar (Work.PSU3.StageB.fcan hS.split
          (ω * Work.PSU3.StageB.sconjF fr a))) =
        (fr.κ fr.ζ : Work.PSU3.E n) *
          ((Work.PSU3.StageB.fval a)⁻¹ * (Work.PSU3.StageB.fval a)⁻¹) *
          Multiplicative.toAdd (fr.bar (Work.PSU3.StageB.fcan hS.split
            (ω * Work.PSU3.StageB.sconjF fr b))) :=
    fun a b hab => bar_fcan_step4_3 hS fr hω hf hab
  -- the `η`-action on `E`
  obtain ⟨μ, hμbar, hμκ⟩ := etaAction_semilinear hS fr hηV hηN hη1
  have hμF := mu_mem_F hS hηV hηN hμκ
  -- relation (4) of §4
  have h4 : ∀ a : ↥(Work.PSU3.StageB.FX n),
      (Work.PSU3.StageB.fval a) ^ 2 *
          Multiplicative.toAdd (fr.bar (Work.PSU3.StageB.fcan hS.split
            (ω * Work.PSU3.StageB.sconjF fr a))) =
        ((fr.κ fr.ζ : Work.PSU3.E n))⁻¹ *
          μ (Multiplicative.toAdd (fr.bar (Work.PSU3.StageB.fcan hS.split
            (ω * Work.PSU3.StageB.sconjF fr a))))
        + Multiplicative.toAdd (fr.bar ω) := by
    intro a
    rw [step4_rel4 hS fr hω hf hsq hηV hh hcentζ hηN hη1 a, hμbar]
  -- `μ²` fixes the fixed field of `σE`
  have hfix2 := step4_algebra hS fr hω hηV hμbar hμκ hcentω hcentζ hμF h4 h3
  -- `orderOf μ` is odd
  have hodd : Odd (orderOf μ) :=
    (odd_orderOf_zeta hS fr).of_dvd_nat
      ((orderOf_mu_dvd_orderOf_eta hS hηV hμbar).trans
        (orderOf_eta_dvd_orderOf_zeta hS hω hf hh hcentζ))
  -- hence `μ` fixes the fixed field; so `η ∈ W`
  have hfix : ∀ x : Work.PSU3.E n, Work.PSU3.σE x = x → μ x = x := by
    intro x hx
    have h2 := hfix2 x hx
    obtain ⟨k, hk⟩ := hodd
    have hμ : (μ ^ 2) ^ (k + 1) = μ := by
      rw [← pow_mul, show 2 * (k + 1) = orderOf μ + 1 by omega, pow_succ,
        pow_orderOf_eq_one, one_mul]
    rw [← hμ]
    have hx2 : ∀ m : ℕ, ((μ ^ 2) ^ m) x = x := by
      intro m
      induction m with
      | zero => rw [pow_zero]; rfl
      | succ j ih =>
        rw [pow_succ']
        change (μ ^ 2) (((μ ^ 2) ^ j) x) = x
        rw [ih]
        simpa [pow_two] using h2
    exact hx2 (k + 1)
  have hηW : η ∈ W H t := mem_W_of_mu_fix_F hS hηV hηN hμκ hfix
  rw [hh]
  exact (W H t).mul_mem ((W H t).pow_mem fr.ζ_mem_W 3) ((W H t).inv_mem hηW)

end Work.PSU3.StageB.NotFpfStep4
