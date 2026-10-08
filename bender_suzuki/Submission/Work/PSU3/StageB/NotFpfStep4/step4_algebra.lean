import Mathlib
import Submission.Work.PSU3.Defs
import Submission.Work.ThmF.Setup
import Submission.Work.PSU3.StageB.Frame
import Submission.Work.PSU3.StageB.Omega.API
import Submission.Work.PSU3.StageB.Canon
import Submission.Work.PSU3.StageB.ThetaOmegaAux
import Submission.Work.PSU3.StageB.NotFpfStep4.etaAction_semilinear
import Submission.Work.PSU3.StageB.NotFpfStep4.bar_fcan_step4_3
import Submission.Work.PSU3.GaloisField.fixedField_card
import Submission.Work.PSU3.GaloisField.card_zero
import Submission.Work.PSU3.StageB.NotFpfStep4.step4_rel9
import Submission.Work.PSU3.StageB.NotFpfStep4.step4_case
import Submission.Work.PSU3.StageB.NotFpfStep4.step4_final

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
open Work.ThmF
open Work.PSU3
open Work.PSU3.StageB

namespace Work.PSU3.StageB.NotFpfStep4

variable {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G} {n : ℕ}

/-- For `X` in the fixed field of `σE`, not equal to `A₀⁻¹ * A₀⁻¹`, there is a `σE`-fixed
`A ≠ 0`, `A ≠ A₀` with `A⁻¹ * A⁻¹ = X`. -/
private theorem step4_param_aux {n : ℕ} (hn : 1 ≤ n) {A₀ X : E n}
    (hX : σE X = X) (hX0 : X ≠ 0) (hXb : X ≠ A₀⁻¹ * A₀⁻¹) :
    ∃ A : E n, σE A = A ∧ A ≠ 0 ∧ A ≠ A₀ ∧ A⁻¹ * A⁻¹ = X := by
  have h1 : σE X⁻¹ = X⁻¹ := by rw [map_inv₀, hX]
  have hpow : (X⁻¹) ^ 2 ^ n = X⁻¹ := by
    rw [← iterateFrobenius_def]
    exact h1
  have hk : 2 ^ (n - 1) * 2 = 2 ^ n := by
    rw [← pow_succ, Nat.sub_add_cancel hn]
  have hA2 : (X⁻¹) ^ 2 ^ (n - 1) * (X⁻¹) ^ 2 ^ (n - 1) = X⁻¹ := by
    calc (X⁻¹) ^ 2 ^ (n - 1) * (X⁻¹) ^ 2 ^ (n - 1)
        = (X⁻¹) ^ (2 ^ (n - 1) + 2 ^ (n - 1)) := by rw [← pow_add]
      _ = (X⁻¹) ^ (2 ^ (n - 1) * 2) := by
          rw [show 2 ^ (n - 1) + 2 ^ (n - 1) = 2 ^ (n - 1) * 2 by ring]
      _ = (X⁻¹) ^ 2 ^ n := by rw [hk]
      _ = X⁻¹ := hpow
  have hAX : ((X⁻¹) ^ 2 ^ (n - 1))⁻¹ * ((X⁻¹) ^ 2 ^ (n - 1))⁻¹ = X := by
    rw [← mul_inv_rev, hA2, inv_inv]
  have hAfix : σE ((X⁻¹) ^ 2 ^ (n - 1)) = (X⁻¹) ^ 2 ^ (n - 1) := by
    rw [map_pow, h1]
  exact ⟨(X⁻¹) ^ 2 ^ (n - 1), hAfix, pow_ne_zero _ (inv_ne_zero hX0),
    fun h => hXb (by rw [← h]; exact hAX.symm), hAX⟩

private theorem step4_pair_aux (hS : PSU3Hyp H Q t) (fr : CoarseFrame H Q t n)
    {ω : ↥Q} (hω : (ω : G) ∉ fr.Q0) {α : ↥(FX n)}
    {η : G} (hηV : η ∈ centD H t)
    {μ : E n ≃+* E n}
    (hμbar : ∀ x : ↥Q, Multiplicative.toAdd (fr.bar (qconj hS.split
        (⟨η, centD_le_twoPoint (H := H) t hηV⟩ : ↥(twoPoint H t)) x)) = μ (Multiplicative.toAdd (fr.bar x)))
    (hμκ : ∀ (d e : fr.KW), (e : G) = η⁻¹ * (d : G) * η → fr.κ e = μ (fr.κ d))
    (hcentω : η * (ω : G) = (ω : G) * η) (hcentζ : η * (fr.ζ : G) = (fr.ζ : G) * η)
    (hμF : ∀ x : E n, σE x = x → σE (μ x) = μ x)
    (h4 : ∀ a : ↥(FX n),
      (fval a) ^ 2 * Multiplicative.toAdd (fr.bar (fcan hS.split (ω * sconjF fr a))) =
      ((fr.κ fr.ζ : E n))⁻¹ * μ (Multiplicative.toAdd (fr.bar (fcan hS.split (ω * sconjF fr a))))
      + Multiplicative.toAdd (fr.bar ω))
    (h3 : ∀ a b : ↥(FX n),
      fval (nmF fr b) = fval α + (fval (nmF fr a))⁻¹ →
      Multiplicative.toAdd (fr.bar (fcan hS.split (ω * sconjF fr a))) =
        (fr.κ fr.ζ : E n) * ((fval a)⁻¹ * (fval a)⁻¹) *
          Multiplicative.toAdd (fr.bar (fcan hS.split (ω * sconjF fr b))))
    (u : ↥(FX n)) (hu : fval (nmF fr u) ≠ (fval α)⁻¹) :
    ((fr.κ fr.ζ : E n) + ((fr.κ fr.ζ : E n))⁻¹ + μ ((fval u)⁻¹ * (fval u)⁻¹))
        * ((fval u)⁻¹ * (fval u)⁻¹)
      = ((fr.κ fr.ζ : E n) + ((fr.κ fr.ζ : E n))⁻¹
          + μ (μ ((fval u)⁻¹ * (fval u)⁻¹))) * (μ ((fval u)⁻¹ * (fval u)⁻¹)) := by
  have hcentω' : (ω : G) = η⁻¹ * (ω : G) * η := by
    calc (ω : G) = η⁻¹ * (η * (ω : G)) := by group
      _ = η⁻¹ * ((ω : G) * η) := by rw [hcentω]
      _ = η⁻¹ * (ω : G) * η := by group
  have hqconjω : qconj hS.split (⟨η, centD_le_twoPoint (H := H) t hηV⟩ : ↥(twoPoint H t)) ω = ω := by
    apply Subtype.ext
    rw [qconj_coe]
    exact hcentω'.symm
  have hμw : μ (Multiplicative.toAdd (fr.bar ω)) = Multiplicative.toAdd (fr.bar ω) := by
    have h := hμbar ω
    rw [hqconjω] at h
    exact h.symm
  have hζcent : (fr.ζ : G) = η⁻¹ * (fr.ζ : G) * η := by
    calc (fr.ζ : G) = η⁻¹ * (η * (fr.ζ : G)) := by group
      _ = η⁻¹ * ((fr.ζ : G) * η) := by rw [hcentζ]
      _ = η⁻¹ * (fr.ζ : G) * η := by group
  have hμc : μ (fr.κ fr.ζ : E n) = (fr.κ fr.ζ : E n) := (hμκ fr.ζ fr.ζ hζcent).symm
  have hcσ : σE (fr.κ fr.ζ : E n) = ((fr.κ fr.ζ : E n))⁻¹ := eta_sigmaE_zetaE fr
  have hc0 : (fr.κ fr.ζ : E n) ≠ 0 := Units.ne_zero _
  have hcF : σE (fr.κ fr.ζ : E n) ≠ (fr.κ fr.ζ : E n) := by
    intro h
    have h2 : (fr.κ fr.ζ : E n) = ((fr.κ fr.ζ : E n))⁻¹ := h.symm.trans hcσ
    have h1 : (fr.κ fr.ζ : E n) ^ 2 = 1 := by
      rw [pow_two]
      nth_rewrite 1 [h2]
      rw [inv_mul_cancel₀ hc0]
    have h3' : ((fr.κ fr.ζ : E n) + 1) ^ 2 = 0 := by
      rw [CharTwo.add_sq, h1, one_pow, CharTwo.add_self_eq_zero]
    have h5 : (fr.κ fr.ζ : E n) + 1 = 0 := sq_eq_zero_iff.mp h3'
    have h6 : (fr.κ fr.ζ : E n) = -1 := eq_neg_of_add_eq_zero_left h5
    rw [CharTwo.neg_eq] at h6
    exact eta_kappa_zeta_ne_one fr (Units.ext h6)
  have hw0 : Multiplicative.toAdd (fr.bar ω) ≠ 0 := by
    intro h
    exact bar_ne_one_of_not_mem_Q0 fr hω (toAdd_eq_zero.mp h)
  have hα0 : (fval α)⁻¹ ≠ 0 := inv_ne_zero α.1.ne_zero
  have hαfix : σE ((fval α)⁻¹) = (fval α)⁻¹ := by rw [map_inv₀, α.2]
  let a₀ : ↥(FX n) := (nmEquiv hS fr).symm (mkFX ((fval α)⁻¹) hαfix hα0)
  have ha₀ : fval (nmF fr a₀) = (fval α)⁻¹ := by
    show fval (nmF fr ((nmEquiv hS fr).symm (mkFX ((fval α)⁻¹) hαfix hα0))) = (fval α)⁻¹
    rw [← nmEquiv_apply hS fr ((nmEquiv hS fr).symm (mkFX ((fval α)⁻¹) hαfix hα0)),
      MulEquiv.apply_symm_apply, fval_mkFX]
  have hua₀ : u ≠ a₀ := fun h => hu (by rw [h, ha₀])
  have hw'fix : σE (fval α + (fval (nmF fr u))⁻¹) = fval α + (fval (nmF fr u))⁻¹ := by
    have h1 : σE (fval (nmF fr u)) = fval (nmF fr u) := (nmF fr u).2
    rw [map_add, map_inv₀, h1, α.2]
  have hw'ne : fval α + (fval (nmF fr u))⁻¹ ≠ 0 := by
    intro h
    apply hu
    have h2 : (fval (nmF fr u))⁻¹ = fval α := by
      rw [add_eq_zero_iff_eq_neg, CharTwo.neg_eq] at h
      exact h.symm
    have := congrArg Inv.inv h2
    simpa using this
  let v : ↥(FX n) := (nmEquiv hS fr).symm (mkFX (fval α + (fval (nmF fr u))⁻¹) hw'fix hw'ne)
  have hv : fval (nmF fr v) = fval α + (fval (nmF fr u))⁻¹ := by
    show fval (nmF fr ((nmEquiv hS fr).symm (mkFX (fval α + (fval (nmF fr u))⁻¹) hw'fix hw'ne)))
      = fval α + (fval (nmF fr u))⁻¹
    rw [← nmEquiv_apply hS fr ((nmEquiv hS fr).symm (mkFX (fval α + (fval (nmF fr u))⁻¹) hw'fix hw'ne)),
      MulEquiv.apply_symm_apply, fval_mkFX]
  set Bu : E n := Multiplicative.toAdd (fr.bar (fcan hS.split (ω * sconjF fr u))) with hBu
  set Bv : E n := Multiplicative.toAdd (fr.bar (fcan hS.split (ω * sconjF fr v))) with hBv
  have h3uv : Bu = (fr.κ fr.ζ : E n) * ((fval u)⁻¹ * (fval u)⁻¹) * Bv := by
    rw [hBu, hBv]; exact h3 u v hv
  have h4u : (fval u) ^ 2 * Bu = ((fr.κ fr.ζ : E n))⁻¹ * μ Bu + Multiplicative.toAdd (fr.bar ω) := by
    rw [hBu]; exact h4 u
  have h4v : (fval v) ^ 2 * Bv = ((fr.κ fr.ζ : E n))⁻¹ * μ Bv + Multiplicative.toAdd (fr.bar ω) := by
    rw [hBv]; exact h4 v
  have hu0 : fval u ≠ 0 := u.1.ne_zero
  have hv0 : fval v ≠ 0 := v.1.ne_zero
  have hAu0 : μ (fval u) ≠ 0 := fun h => hu0 (μ.injective (by simpa using h))
  have e2 : (fval v) ^ 2 * Bv = ((fr.κ fr.ζ : E n))⁻¹ * μ Bv + Multiplicative.toAdd (fr.bar ω) := h4v
  have e1 : (fr.κ fr.ζ : E n) * Bv
      = (μ (fval u))⁻¹ * (μ (fval u))⁻¹ * μ Bv + Multiplicative.toAdd (fr.bar ω) := by
    have h1 : (fval u) ^ 2 * ((fr.κ fr.ζ : E n) * (fval u)⁻¹ * (fval u)⁻¹ * Bv)
        = (fr.κ fr.ζ : E n) * Bv := by
      field_simp <;> ring
    have h2 : ((fr.κ fr.ζ : E n))⁻¹
          * μ ((fr.κ fr.ζ : E n) * (fval u)⁻¹ * (fval u)⁻¹ * Bv)
        = (μ (fval u))⁻¹ * (μ (fval u))⁻¹ * μ Bv := by
      simp only [map_mul, map_inv₀, hμc]
      field_simp <;> ring
    calc (fr.κ fr.ζ : E n) * Bv
        = (fval u) ^ 2 * ((fr.κ fr.ζ : E n) * (fval u)⁻¹ * (fval u)⁻¹ * Bv) := h1.symm
      _ = (fval u) ^ 2 * Bu := by rw [h3uv] <;> ring
      _ = ((fr.κ fr.ζ : E n))⁻¹ * μ Bu + Multiplicative.toAdd (fr.bar ω) := h4u
      _ = ((fr.κ fr.ζ : E n))⁻¹
            * μ ((fr.κ fr.ζ : E n) * (fval u)⁻¹ * (fval u)⁻¹ * Bv)
            + Multiplicative.toAdd (fr.bar ω) := by rw [h3uv] <;> ring
      _ = (μ (fval u))⁻¹ * (μ (fval u))⁻¹ * μ Bv + Multiplicative.toAdd (fr.bar ω) := by rw [h2] <;> ring
  -- `Bv ≠ 0`
  have hBv0 : Bv ≠ 0 := by
    have hsQ0 : ((sconjF fr v : ↥Q) : G) ∈ fr.Q0 := bar_fcan_step4_3_sconjF_mem_Q0 hS fr v
    have hnotQ0 : ((ω * sconjF fr v : ↥Q) : G) ∉ fr.Q0 := by
      intro h
      have hmul : ((ω * sconjF fr v : ↥Q) : G) * (((sconjF fr v : ↥Q) : G))⁻¹ ∈ fr.Q0 :=
        fr.Q0.mul_mem h (fr.Q0.inv_mem hsQ0)
      have heq : ((ω * sconjF fr v : ↥Q) : G) * (((sconjF fr v : ↥Q) : G))⁻¹ = (ω : G) := by
        rw [Subgroup.coe_mul]; group
      rw [heq] at hmul
      exact hω hmul
    have hfcan : ((fcan hS.split (ω * sconjF fr v) : ↥Q) : G) ∉ fr.Q0 :=
      fun h => hnotQ0 ((fcan_mem_Q0_iff hS fr (ω * sconjF fr v)).mp h)
    intro h
    rw [hBv] at h
    exact bar_ne_one_of_not_mem_Q0 fr hfcan (toAdd_eq_zero.mp h)
  -- (A): the relation used for the nondegeneracy
  have hA : (1 + (μ (fval u))⁻¹ * (μ (fval u))⁻¹ * (fval v) ^ 2) * μ Bv
      = ((fval v) ^ 2 + (fr.κ fr.ζ : E n)) * Multiplicative.toAdd (fr.bar ω) := by
    have h := e1
    have h2 := e2
    linear_combination (norm := (ring_nf; simp [CharTwo.two_eq_zero, CharTwo.add_self_eq_zero,
      mul_inv_cancel₀ hc0]))
      (fval v) ^ 2 * h + (fr.κ fr.ζ : E n) * h2
  have hv1 : (fval v) ^ 2 ≠ (fr.κ fr.ζ : E n)
      → 1 + (μ (fval u))⁻¹ * (μ (fval u))⁻¹ * (fval v) ^ 2 ≠ 0 := by
    intro hvne h1
    apply hvne
    have hkey : ((fval v) ^ 2 + (fr.κ fr.ζ : E n)) * Multiplicative.toAdd (fr.bar ω) = 0 := by
      rw [← hA, h1, zero_mul]
    have hsum : (fval v) ^ 2 + (fr.κ fr.ζ : E n) = 0 := (mul_eq_zero.mp hkey).resolve_right hw0
    have hneg : (fval v) ^ 2 = -(fr.κ fr.ζ : E n) := eq_neg_of_add_eq_zero_left hsum
    rwa [CharTwo.neg_eq] at hneg
  -- (9)
  have h9 : ((fval v) ^ 2 + (fr.κ fr.ζ : E n))
        * (1 + μ ((μ (fval u))⁻¹ * (μ (fval u))⁻¹) * μ ((fval v) ^ 2))
      = (μ ((μ (fval u))⁻¹ * (μ (fval u))⁻¹) + ((fr.κ fr.ζ : E n))⁻¹)
        * (1 + (μ (fval u))⁻¹ * (μ (fval u))⁻¹ * (fval v) ^ 2) :=
    step4_rel9 μ hμc hμw hc0 hw0 e1 e2
  have hτfix : σE ((μ (fval u))⁻¹ * (μ (fval u))⁻¹) = (μ (fval u))⁻¹ * (μ (fval u))⁻¹ := by
    have h1 : σE (μ (fval u)) = μ (fval u) := hμF (fval u) u.2
    simp only [map_mul, map_inv₀, h1]
  have hv2fix : σE ((fval v) ^ 2) = (fval v) ^ 2 := by rw [map_pow, v.2]
  have h10 : ((fr.κ fr.ζ : E n) + ((fr.κ fr.ζ : E n))⁻¹ + μ ((μ (fval u))⁻¹ * (μ (fval u))⁻¹))
        * ((μ (fval u))⁻¹ * (μ (fval u))⁻¹)
      = ((fr.κ fr.ζ : E n) + ((fr.κ fr.ζ : E n))⁻¹
          + μ (μ ((μ (fval u))⁻¹ * (μ (fval u))⁻¹))) * (μ ((μ (fval u))⁻¹ * (μ (fval u))⁻¹)) :=
    step4_case μ σE hμF hμc hcσ hcF hτfix hv2fix h9 hv1
  -- descend to `(fval u)^{-2}` via `μ⁻¹`
  have hμτA : μ ((fval u)⁻¹ * (fval u)⁻¹) = (μ (fval u))⁻¹ * (μ (fval u))⁻¹ := by
    simp only [map_mul, map_inv₀]
  have hsc : μ.symm (fr.κ fr.ζ : E n) = (fr.κ fr.ζ : E n) := by
    simpa only [hμc] using RingEquiv.symm_apply_apply μ (fr.κ fr.ζ : E n)
  have hst : μ.symm ((μ (fval u))⁻¹ * (μ (fval u))⁻¹) = (fval u)⁻¹ * (fval u)⁻¹ := by
    simpa only [← hμτA] using RingEquiv.symm_apply_apply μ ((fval u)⁻¹ * (fval u)⁻¹)
  have h := congrArg (fun z => μ.symm z) h10
  simp only [map_mul, map_add, map_inv₀, hsc, hst, RingEquiv.symm_apply_apply] at h
  simpa only [hμτA, map_mul, map_inv₀] using h


theorem step4_algebra {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G} {n : ℕ}
    (hS : Work.PSU3.PSU3Hyp H Q t) (fr : Work.PSU3.CoarseFrame H Q t n)
    {ω : ↥Q} (hω : (ω : G) ∉ fr.Q0) {α : ↥(Work.PSU3.StageB.FX n)}
    {η : G} (hηV : η ∈ Submission.Blueprint.centD H t)
    {μ : Work.PSU3.E n ≃+* Work.PSU3.E n}
    (hμbar : ∀ x : ↥Q, Multiplicative.toAdd (fr.bar (Work.PSU3.StageB.qconj hS.split
        (⟨η, Work.ThmF.centD_le_twoPoint (H := H) t hηV⟩ :
          ↥(Submission.Blueprint.twoPoint H t)) x)) = μ (Multiplicative.toAdd (fr.bar x)))
    (hμκ : ∀ (d e : fr.KW), (e : G) = η⁻¹ * (d : G) * η → fr.κ e = μ (fr.κ d))
    (hcentω : η * (ω : G) = (ω : G) * η) (hcentζ : η * (fr.ζ : G) = (fr.ζ : G) * η)
    (hμF : ∀ x : Work.PSU3.E n, Work.PSU3.σE x = x → Work.PSU3.σE (μ x) = μ x)
    (h4 : ∀ a : ↥(Work.PSU3.StageB.FX n),
      (Work.PSU3.StageB.fval a) ^ 2 *
        Multiplicative.toAdd (fr.bar (Work.PSU3.StageB.fcan hS.split
          (ω * Work.PSU3.StageB.sconjF fr a))) =
      ((fr.κ fr.ζ : Work.PSU3.E n))⁻¹ *
        μ (Multiplicative.toAdd (fr.bar (Work.PSU3.StageB.fcan hS.split
          (ω * Work.PSU3.StageB.sconjF fr a))))
      + Multiplicative.toAdd (fr.bar ω))
    (h3 : ∀ a b : ↥(Work.PSU3.StageB.FX n),
      Work.PSU3.StageB.fval (Work.PSU3.StageB.nmF fr b) =
        Work.PSU3.StageB.fval α + (Work.PSU3.StageB.fval (Work.PSU3.StageB.nmF fr a))⁻¹ →
      Multiplicative.toAdd (fr.bar (Work.PSU3.StageB.fcan hS.split
          (ω * Work.PSU3.StageB.sconjF fr a))) =
        (fr.κ fr.ζ : Work.PSU3.E n) *
          ((Work.PSU3.StageB.fval a)⁻¹ * (Work.PSU3.StageB.fval a)⁻¹) *
          Multiplicative.toAdd (fr.bar (Work.PSU3.StageB.fcan hS.split
            (ω * Work.PSU3.StageB.sconjF fr b)))) :
    ∀ x : Work.PSU3.E n, Work.PSU3.σE x = x → μ (μ x) = x := by
  classical
  by_cases hn0 : n = 0
  · subst hn0
    intro x _
    have hcard : Nat.card (E 0) = 2 := Work.PSU3.GaloisField.card_zero
    have hx : x = 0 ∨ x = 1 := by
      haveI : Fintype (E 0) := Fintype.ofFinite _
      have hc2 : Fintype.card (E 0) = 2 := by rw [← Nat.card_eq_fintype_card]; exact hcard
      have hsub : ({(0 : E 0), 1} : Finset (E 0)) ⊆ Finset.univ := Finset.subset_univ _
      have heq : ({(0 : E 0), 1} : Finset (E 0)) = Finset.univ := by
        refine Finset.eq_of_subset_of_card_le hsub ?_
        rw [Finset.card_univ, hc2]
        simp [zero_ne_one]
      have hxmem : x ∈ ({(0 : E 0), 1} : Finset (E 0)) := by rw [heq]; exact Finset.mem_univ x
      simpa using hxmem
    rcases hx with rfl | rfl <;> simp
  · have hn1 : 1 ≤ n := by omega
    have hα0 : (fval α)⁻¹ ≠ 0 := inv_ne_zero α.1.ne_zero
    have hαfix : σE ((fval α)⁻¹) = (fval α)⁻¹ := by rw [map_inv₀, α.2]
    let a₀ : ↥(FX n) := (nmEquiv hS fr).symm (mkFX ((fval α)⁻¹) hαfix hα0)
    have hfa₀ : fval (nmF fr a₀) = (fval α)⁻¹ := by
      show fval (nmF fr ((nmEquiv hS fr).symm (mkFX ((fval α)⁻¹) hαfix hα0))) = (fval α)⁻¹
      rw [← nmEquiv_apply hS fr ((nmEquiv hS fr).symm (mkFX ((fval α)⁻¹) hαfix hα0)),
        MulEquiv.apply_symm_apply, fval_mkFX]
    have hcardF : Nat.card {x : E n // σE x = x} = 2 ^ n :=
      Work.PSU3.GaloisField.fixedField_card n hn1
    refine step4_final hn1 μ (c := (fr.κ fr.ζ : E n)) ?_ hμF hcardF
      (b := (fval a₀)⁻¹ * (fval a₀)⁻¹) ?_
    · -- `μ c = c`
      have hζcent : (fr.ζ : G) = η⁻¹ * (fr.ζ : G) * η := by
        calc (fr.ζ : G) = η⁻¹ * (η * (fr.ζ : G)) := by group
          _ = η⁻¹ * ((fr.ζ : G) * η) := by rw [hcentζ]
          _ = η⁻¹ * (fr.ζ : G) * η := by group
      exact (hμκ fr.ζ fr.ζ hζcent).symm
    · intro X hX hXb
      by_cases hX0 : X = 0
      · subst hX0; simp
      · obtain ⟨A, hAσ, hA0, hAne, hAX⟩ := step4_param_aux hn1 hX hX0 hXb
        have huinj : Function.Injective (fval : ↥(FX n) → E n) := fun a b h => Subtype.ext (Units.ext h)
        have hnmF_inj : Function.Injective (nmF fr) := nmF_injective hS fr
        have hu : fval (nmF fr (mkFX A hAσ hA0)) ≠ (fval α)⁻¹ := by
          intro hc
          have h1 : nmF fr (mkFX A hAσ hA0) = nmF fr a₀ := by
            apply huinj
            rw [hfa₀]
            exact hc
          have h2 : mkFX A hAσ hA0 = a₀ := hnmF_inj h1
          have h3 : fval (mkFX A hAσ hA0) = fval a₀ := by rw [h2]
          rw [fval_mkFX] at h3
          exact hAne h3
        have hrel := step4_pair_aux hS fr hω (α := α) (η := η) (μ := μ) hηV hμbar hμκ hcentω hcentζ hμF h4 h3
          (mkFX A hAσ hA0) hu
        simpa only [fval_mkFX, hAX] using hrel


end Work.PSU3.StageB.NotFpfStep4
