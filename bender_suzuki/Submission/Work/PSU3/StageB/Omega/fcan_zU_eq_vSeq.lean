/-
# `Work.PSU3.StageB.Omega.fcan_zU_eq_vSeq` — Peterfalvi II Ch. VII §2 (17), sharp form

`induction_rel` (in `Omega.beta_pow_m_eq_one`) computes `f (ω · zc u_i)` up to an *unspecified*
`Q₀`-shift.  Peterfalvi's §2 (17) has the sharper content that the shift is `zc (u_i + α)`,
`vSeq α β i = uSeq β i + α`:

  `f (ω · zc u_i) = (ω · zc v_i)^{d_i}`   (`1 ≤ i ≤ N`).

The proof is the induction of `induction_rel` with the shift tracked; the extra field input is
`v_{i+1} = v_i + w_i⁻¹ u_{i+1}` (equivalent to `u_i/u_{i+1} = 1 + 1/w_i`, `Omega.uSeq_div`).
-/
import Mathlib
import Submission.Work.PSU3.StageB.Omega.beta_pow_setup
import Submission.Work.PSU3.StageB.Omega.beta_pow_m_eq_one
import Submission.Work.PSU3.StageB.Omega.fcan_step10_gen

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 4000000

open LeanEval.GroupTheory.Defs
open Submission.Blueprint
open Classical

namespace Work.PSU3.StageB.Omega

open Work.ThmF
open Work.PSU3
open Work.PSU3.StageB

variable {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G} {n : ℕ}

/-- **(13)+(14), sharpened:**  `v_{i+1} = v_i + w_i⁻¹ · u_{i+1}`. -/
lemma vSeq_succ {α0 β : E n} (hβα : β + β⁻¹ = α0) (hβ : β ≠ 0) (hα0 : α0 ≠ 0) (i : ℕ)
    (h1 : bS β i ≠ 0) (h2 : bS β (i + 1) ≠ 0) :
    vSeq α0 β (i + 1) = vSeq α0 β i + (wSeq α0 β i)⁻¹ * uSeq β (i + 1) := by
  have hi : 1 ≤ i := by
    by_contra hcon
    have h0 : i = 0 := by omega
    rw [h0, bS_zero] at h1
    exact h1 rfl
  have hdiv := uSeq_div α0 β hβα hβ hα0 hi h1 h2
  have hu : uSeq β (i + 1) ≠ 0 := uSeq_ne_zero β hβ i h1 h2
  have hmain : uSeq β i = uSeq β (i + 1) * (1 + (wSeq α0 β i)⁻¹) := by
    have h := congrArg (fun z : E n => z * uSeq β (i + 1)) hdiv
    rw [div_mul_cancel₀ _ hu] at h
    rw [show (1 + 1 / wSeq α0 β i) = 1 + (wSeq α0 β i)⁻¹ from by rw [one_div]] at h
    rw [h, mul_comm]
  rw [vSeq, vSeq, hmain]
  rw [show uSeq β (i + 1) * (1 + (wSeq α0 β i)⁻¹)
        = uSeq β (i + 1) + (wSeq α0 β i)⁻¹ * uSeq β (i + 1) from by ring]
  rw [show uSeq β (i + 1) + (wSeq α0 β i)⁻¹ * uSeq β (i + 1) + α0
        + (wSeq α0 β i)⁻¹ * uSeq β (i + 1)
      = uSeq β (i + 1) + α0
        + ((wSeq α0 β i)⁻¹ * uSeq β (i + 1) + (wSeq α0 β i)⁻¹ * uSeq β (i + 1)) from by
    ring]
  rw [CharTwo.add_self_eq_zero, add_zero]

/-- **(17), sharp form.** -/
theorem fcan_zU_eq_vSeq (hS : PSU3Hyp H Q t) (fr : CoarseFrame H Q t n)
    {ω : ↥Q} (hω : (ω : G) ∉ fr.Q0) {α : ↥(FX n)}
    (hωf : fcan hS.split ω = qconj hS.split (zetaD fr) (ω * zcQF fr α))
    {β : E n} (hβ : β ≠ 0) (hσ : σE β = β ∨ σE β = β⁻¹) (hβα : β + β⁻¹ = fval α)
    (lam : ℕ → ↥(FX n)) {N : ℕ}
    (hlam : ∀ i, 1 ≤ i → i ≤ N → fval (lam i) = wSeq (fval α) β i)
    (hN : ∀ i, 1 ≤ i → i ≤ N → bS β i ≠ 0) :
    ∀ i, 1 ≤ i → i ≤ N →
      fcan hS.split (ω * zU fr β hβ hσ i) =
        qconj hS.split
          (⟨(dSeq hS fr lam i : fr.KW), fr.KW_le (dSeq hS fr lam i).2⟩)
          (ω * zcQ fr (vSeq (fval α) β i)
            (by rw [vSeq, map_add, uSeq_fixed β hβ hσ i, α.2])) := by
  have hα0 : fval α ≠ 0 := Units.ne_zero α.1
  have hvfix : ∀ i, σE (vSeq (fval α) β i) = vSeq (fval α) β i := fun i => by
    rw [vSeq, map_add, uSeq_fixed β hβ hσ i, α.2]
  -- base case `i = 1`
  have base : (1 ≤ N) → fcan hS.split (ω * zU fr β hβ hσ 1) =
      qconj hS.split
        (⟨(dSeq hS fr lam 1 : fr.KW), fr.KW_le (dSeq hS fr lam 1).2⟩)
        (ω * zcQ fr (vSeq (fval α) β 1) (hvfix 1)) := by
    intro h1N
    have hzU1 : zU fr β hβ hσ 1 = 1 := by
      apply Subtype.ext
      simp [zU_coe, uSeq_one, zc_zero]
    have hd1 : dSeq hS fr lam 1 = fr.ζ := by
      refine dSeq_one hS fr lam ?_
      rw [hlam 1 le_rfl h1N, wSeq_one hβα hα0]
    have hq1 : (⟨(dSeq hS fr lam 1 : fr.KW), fr.KW_le (dSeq hS fr lam 1).2⟩
        : ↥(twoPoint H t)) = zetaD fr := by
      apply Subtype.ext
      show ((dSeq hS fr lam 1 : fr.KW) : G) = ((fr.ζ : fr.KW) : G)
      rw [hd1]
    have hzq1 : zcQ fr (vSeq (fval α) β 1) (hvfix 1) = zcQF fr α := by
      apply Subtype.ext
      rw [zcQ_coe, zcQF_coe, show vSeq (fval α) β 1 = fval α from by
        rw [vSeq, uSeq_one, zero_add]]
    rw [hzU1, mul_one, hq1, hzq1]
    exact hωf
  -- induction step
  have step : ∀ m, 1 ≤ m →
      ((m ≤ N) → fcan hS.split (ω * zU fr β hβ hσ m) =
        qconj hS.split
          (⟨(dSeq hS fr lam m : fr.KW), fr.KW_le (dSeq hS fr lam m).2⟩)
          (ω * zcQ fr (vSeq (fval α) β m) (hvfix m))) →
      ((m + 1 ≤ N) → fcan hS.split (ω * zU fr β hβ hσ (m + 1)) =
        qconj hS.split
          (⟨(dSeq hS fr lam (m + 1) : fr.KW), fr.KW_le (dSeq hS fr lam (m + 1)).2⟩)
          (ω * zcQ fr (vSeq (fval α) β (m + 1)) (hvfix (m + 1)))) := by
    intro m hm ih hm1N
    have hmN : m ≤ N := by omega
    have hrel := ih hmN
    have hbm : bS β m ≠ 0 := hN m hm hmN
    have hbm1 : bS β (m + 1) ≠ 0 := hN (m + 1) (by omega) hm1N
    set U : ↥(FX n) := mkFX (uSeq β (m + 1)) (uSeq_fixed β hβ hσ (m + 1))
      (uSeq_ne_zero β hβ m hbm hbm1) with hUdef
    have hU : fval U = uSeq β (m + 1) := rfl
    have h1 : ((ω * zcQF fr U : ↥Q) : G) ≠ 1 := by
      intro hc
      have hmem : (zcQF fr U : G) ∈ fr.Q0 := by rw [zcQF_coe]; exact fr.zc_mem (fval U) U.2
      have h2 : (ω : G) = ((ω * zcQF fr U : ↥Q) : G) * (zcQF fr U : G)⁻¹ := by
        rw [Subgroup.coe_mul]; group
      exact hω (by rw [h2, hc, one_mul]; exact fr.Q0.inv_mem hmem)
    have huv : uSeq β m = fval α + (fval U)⁻¹ := by
      rw [hU]
      exact (uSeq_rec_alpha (fval α) β hβα hβ hm hbm hbm1).symm
    have hgen := fcan_step10_gen hS fr hω hωf (uSeq_fixed β hβ hσ m) huv h1
    set η : E n := (fval (lam m))⁻¹ * fval U with hηdef
    have hηfix : σE η = η := by
      rw [hηdef, map_mul, map_inv₀, (lam m).2, U.2]
    -- the sharpening of the `Q₀`-shift
    have hY'z : zcQ fr (vSeq (fval α) β (m + 1)) (hvfix (m + 1))
        = zcQ fr (vSeq (fval α) β m) (hvfix m) * zcQ fr η hηfix := by
      apply Subtype.ext
      rw [Subgroup.coe_mul, zcQ_coe, zcQ_coe, zcQ_coe]
      rw [← fr.zc_add (vSeq (fval α) β m) η (hvfix m) hηfix]
      congr 1
      rw [hηdef, hU, hlam m hm hmN]
      exact vSeq_succ hβα hβ hα0 m hbm hbm1
    -- `zc η = d·zc u_{m+1}·d⁻¹`
    have hdU : (zcQ fr η hηfix : G)
        = ((dSeq hS fr lam m : fr.KW) : G) * (zcQF fr U : G)
            * ((dSeq hS fr lam m : fr.KW) : G)⁻¹ := by
      have h := dSeq_act hS fr lam m η hηfix
      have h2 : fval (lam m) * η = fval U := by
        rw [hηdef, ← mul_assoc, mul_inv_cancel₀ (Units.ne_zero (lam m).1), one_mul]
      rw [h2] at h
      rw [zcQ_coe, zcQF_coe]
      rw [← h]
      group
    have hrec_lam : fval (lam (m + 1)) = fval (lam m) * (fval U)⁻¹ * (fval U)⁻¹ := by
      rw [hlam m hm hmN, hlam (m + 1) (by omega) hm1N, hU]
      exact wSeq_rec (fval α) β hβ hα0 m hbm
    have hd' : dSeq hS fr lam (m + 1) = dSeq hS fr lam m * zetaExp hS fr U :=
      dSeq_succ hS fr lam U m hrec_lam
    have hL : ω * zU fr β hβ hσ (m + 1) = ω * zcQF fr U := by
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, zU_coe, zcQF_coe, hU]
    have hmid : (fcan hS.split (ω * zcQ fr (uSeq β m) (uSeq_fixed β hβ hσ m)) : G)
        = ((dSeq hS fr lam m : fr.KW) : G)⁻¹
            * ((ω * zcQ fr (vSeq (fval α) β m) (hvfix m) : ↥Q) : G)
            * ((dSeq hS fr lam m : fr.KW) : G) := by
      have h' := congrArg (fun z : ↥Q => (z : G)) hrel
      rw [qconj_coe] at h'
      rw [show ω * zU fr β hβ hσ m
          = ω * zcQ fr (uSeq β m) (uSeq_fixed β hβ hσ m) from rfl] at h'
      exact h'
    have hdG : ((dSeq hS fr lam (m + 1) : fr.KW) : G)
        = ((dSeq hS fr lam m : fr.KW) : G) * ((zetaExp hS fr U : fr.KW) : G) := by
      rw [hd', Subgroup.coe_mul]
    have hZcU : (zcQF fr U : G)
        = ((dSeq hS fr lam m : fr.KW) : G)⁻¹ * (zcQ fr η hηfix : G)
            * ((dSeq hS fr lam m : fr.KW) : G) := by
      rw [hdU]; group
    have hW : ((ω * zcQ fr (vSeq (fval α) β (m + 1)) (hvfix (m + 1)) : ↥Q) : G)
        = ((ω * zcQ fr (vSeq (fval α) β m) (hvfix m) : ↥Q) : G) * (zcQ fr η hηfix : G) := by
      have h1' : (ω * zcQ fr (vSeq (fval α) β (m + 1)) (hvfix (m + 1)) : ↥Q)
          = (ω * zcQ fr (vSeq (fval α) β m) (hvfix m)) * zcQ fr η hηfix := by
        rw [mul_assoc, ← hY'z]
      rw [h1', Subgroup.coe_mul]
    have hmul : ((fcan hS.split (ω * zcQ fr (uSeq β m) (uSeq_fixed β hβ hσ m))
          * zcQF fr U : ↥Q) : G)
        = (fcan hS.split (ω * zcQ fr (uSeq β m) (uSeq_fixed β hβ hσ m)) : G)
            * (zcQF fr U : G) := by
      rw [Subgroup.coe_mul]
    rw [hL]
    apply Subtype.ext
    rw [qconj_coe, hgen]
    rw [hmul, hmid, hdG, hZcU, hW]
    group
  have aux : ∀ k, 1 + k ≤ N → fcan hS.split (ω * zU fr β hβ hσ (1 + k)) =
      qconj hS.split
        (⟨(dSeq hS fr lam (1 + k) : fr.KW), fr.KW_le (dSeq hS fr lam (1 + k)).2⟩)
        (ω * zcQ fr (vSeq (fval α) β (1 + k)) (hvfix (1 + k))) := by
    intro k
    induction k with
    | zero => intro _; simpa using base (by omega : 1 ≤ N)
    | succ k ih =>
        intro hk
        have hprev : 1 + k ≤ N := by omega
        have hstep := step (1 + k) (by omega) (fun _ => ih hprev) (by omega)
        simpa only [Nat.add_assoc] using hstep
  intro i hi hiN
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hi
  exact aux k hiN

end Work.PSU3.StageB.Omega
