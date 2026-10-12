import ChallengeDeps
import Mathlib.Tactic.Have
import Mathlib.Analysis.SpecialFunctions.JapaneseBracket
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixB1.Defs
import Submission.Work.BoseKinLoc.Tprime.profHat_decay_twelve
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixR.FamForm.symA_tail_fsParams`

The **tail condition (T1)** of the kinetic-half bridge (`Submission/Work/BoseFixR/
KINETIC_HALF_DESIGN.md` §2–§3): at FS's parameters `ℓ = sideAt μ (a v)`, `d = (paramsAt μ (a v)).d`,
`s = (paramsAt μ (a v)).s`,

    `γ := (ℓ d)⁻² · symA 1 (fsKinCoeff (2s)⁻¹) 0 ≤ (1/4096) ℓ⁻²`,

i.e. `symA 1 (fsKinCoeff (2s)⁻¹) 0 ≤ d²/4096` (the `ℓ`-powers cancel).

## Why this holds, and where the exponent `4096` comes from

`symA 1 F 0 = (2π)⁻³ ∫_p F‖p‖ · profHat(p)² dp` (`symA_one_zero`), and for the FS cut-off
`F = fsKinCoeff C = [·−C]₊²` the integrand vanishes inside the ball `‖p‖ ≤ C`.  Since
`profHat` decays faster than `(1+‖p‖)^{-12}` (`Work.BoseKinLoc.Tprime.profHat_decay_twelve`,
itself `SchwartzMap.decay 12` for the bump), the exterior integral decays in `C`:

  `symA 1 (fsKinCoeff C) 0 ≤ K · C^{-17}` for every `C ≥ 1`

(§1 below: `symA_one_fsKinCoeff_decay_seventeen`; the exponent is `2·12 − 7`, `12` from the profile decay
and `7 = 4 + 3` from the volume of the `‖p‖`-shell in three dimensions).

At the cut-off `C = (2s)⁻¹` this is `K·(2s)^{17}`, and since FS's parameters satisfy `d = s⁶`
(so `d² = s^{12}`), the target reduces to `K·2^{17}·s⁵ ≤ 1/4096`, a smallness condition on the
diluteness `t = μa³` (`s = t^{1/323}`) that the existentially chosen `ε₀` enforces.  All the
bookkeeping is §2 below; the constant `4096 = 2^{12}` in the statement is the free loss of the
`d² = s^{12}`-normalisation (any O(1) constant is free — HANDOFF).
-/

namespace Work.BoseFixR.FamForm

noncomputable section

open MeasureTheory
open scoped Real Topology

set_option maxHeartbeats 800000

/-! ## 1. The sharp polynomial decay of the origin symbol at the FS cut-off

Pointwise domination of the integrand on the exterior ball, then monotone integration. -/

/-- **Pointwise domination of the cut-off integrand by the integrable weight
`C₀² C^{-17} (1+‖p‖)^{-5}`.**  Inside the ball (`‖p‖ ≤ C`) the cut-off vanishes; outside it,

    `(‖p‖−C)² profHat(p)² ≤ ‖p‖² C₀² (1+‖p‖)^{-24}
       = C₀² · ‖p‖² (1+‖p‖)^{-19} · (1+‖p‖)^{-5}
       ≤ C₀² · ‖p‖^{-17} · (1+‖p‖)^{-5}
       ≤ C₀² C^{-17} (1+‖p‖)^{-5}`,

using `1 + ‖p‖ ≥ ‖p‖` and `‖p‖ ≥ C ≥ 1`. -/
private lemma fsKinCoeff_mul_profHat_sq_le {C₀ C : ℝ} (hC : 1 ≤ C)
    (hdec : ∀ p : ℝ³, |Work.OneBodyKin.profHat p| ≤ C₀ / (1 + ‖p‖) ^ 12) (p : ℝ³) :
    Submission.BoseGases.fsKinCoeff C ‖p‖ * (Work.OneBodyKin.profHat p) ^ 2
      ≤ C₀ ^ 2 * (C ^ 17)⁻¹ * ((1 + ‖p‖) ^ 5)⁻¹ := by
  by_cases hle : ‖p‖ ≤ C
  · rw [Submission.BoseGases.fsKinCoeff_of_le hle, zero_mul]
    positivity
  · have hlt : C < ‖p‖ := not_le.mp hle
    rw [Submission.BoseGases.fsKinCoeff_of_lt (by linarith) hlt]
    have hprof2 : (Work.OneBodyKin.profHat p) ^ 2 ≤ C₀ ^ 2 * ((1 + ‖p‖) ^ 24)⁻¹ := by
      have h := pow_le_pow_left₀ (abs_nonneg (Work.OneBodyKin.profHat p)) (hdec p) 2
      rw [sq_abs, div_pow, ← pow_mul] at h
      norm_num at h
      rwa [div_eq_mul_inv] at h
    have hrC : (‖p‖ - C) ^ 2 ≤ ‖p‖ ^ 2 := by
      nlinarith [norm_nonneg p, hC]
    have hkey : ‖p‖ ^ 2 * ((1 + ‖p‖) ^ 24)⁻¹ ≤ (C ^ 17)⁻¹ * ((1 + ‖p‖) ^ 5)⁻¹ := by
      have hsplit : ((1 + ‖p‖) ^ 24)⁻¹
          = ((1 + ‖p‖) ^ 19)⁻¹ * ((1 + ‖p‖) ^ 5)⁻¹ := by
        rw [show (24 : ℕ) = 19 + 5 by norm_num, pow_add, mul_inv]
      have hbase : ‖p‖ ^ 2 * ((1 + ‖p‖) ^ 19)⁻¹ ≤ (C ^ 17)⁻¹ := by
        have hCpow : C ^ 17 ≤ ‖p‖ ^ 17 := pow_le_pow_left₀ (by linarith) (le_of_lt hlt) 17
        have h1 : ‖p‖ ^ 2 * C ^ 17 ≤ ‖p‖ ^ 19 := by
          have h := mul_le_mul_of_nonneg_left hCpow (pow_nonneg (norm_nonneg p) 2)
          calc ‖p‖ ^ 2 * C ^ 17 ≤ ‖p‖ ^ 2 * ‖p‖ ^ 17 := h
            _ = ‖p‖ ^ 19 := by ring
        have h2 : ‖p‖ ^ 19 ≤ (1 + ‖p‖) ^ 19 :=
          pow_le_pow_left₀ (norm_nonneg p) (by linarith) 19
        rw [show ‖p‖ ^ 2 * ((1 + ‖p‖) ^ 19)⁻¹ = ‖p‖ ^ 2 / (1 + ‖p‖) ^ 19 by
              rw [div_eq_mul_inv],
            show (C ^ 17)⁻¹ = 1 / C ^ 17 by rw [one_div],
            div_le_div_iff₀ (by positivity) (by positivity)]
        linarith [h1, h2]
      rw [hsplit]
      calc ‖p‖ ^ 2 * (((1 + ‖p‖) ^ 19)⁻¹ * ((1 + ‖p‖) ^ 5)⁻¹)
          = ‖p‖ ^ 2 * ((1 + ‖p‖) ^ 19)⁻¹ * ((1 + ‖p‖) ^ 5)⁻¹ := by ring
        _ ≤ (C ^ 17)⁻¹ * ((1 + ‖p‖) ^ 5)⁻¹ :=
            mul_le_mul_of_nonneg_right hbase (by positivity)
    calc (‖p‖ - C) ^ 2 * (Work.OneBodyKin.profHat p) ^ 2
        ≤ ‖p‖ ^ 2 * (C₀ ^ 2 * ((1 + ‖p‖) ^ 24)⁻¹) :=
          mul_le_mul hrC hprof2 (sq_nonneg _) (by positivity)
      _ = C₀ ^ 2 * (‖p‖ ^ 2 * ((1 + ‖p‖) ^ 24)⁻¹) := by ring
      _ ≤ C₀ ^ 2 * ((C ^ 17)⁻¹ * ((1 + ‖p‖) ^ 5)⁻¹) :=
          mul_le_mul_of_nonneg_left hkey (sq_nonneg C₀)
      _ = C₀ ^ 2 * (C ^ 17)⁻¹ * ((1 + ‖p‖) ^ 5)⁻¹ := by ring

/-- **The sharp decay of the origin value of the unprojected symbol** at the FS cut-off:
`symA 1 (fsKinCoeff C) 0 ≤ K C^{-17}` for every `C ≥ 1`, with `K` independent of `C`.

This is `Work.BoseKinLoc.Tprime.symA_zero_decay` re-run with the exponent-`12` profile decay
`profHat_decay_twelve` (the `6` there gives only `C^{-5}`; the bridge (T1) needs `≳ C^{-12}`). -/
theorem symA_one_fsKinCoeff_decay_seventeen :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ C : ℝ, 1 ≤ C →
      Work.OneBodyKin.symA 1 (Submission.BoseGases.fsKinCoeff C) 0 ≤ K / C ^ 17 := by
  obtain ⟨C₀, _hC₀, hdec⟩ := Work.BoseKinLoc.Tprime.profHat_decay_twelve
  -- the dominating weight `(1 + ‖p‖)^{-5}` is integrable in dimension `3`
  have hIint : Integrable (fun p : ℝ³ => ((1 + ‖p‖ : ℝ) ^ 5)⁻¹) := by
    have h := integrable_one_add_norm (E := ℝ³) (μ := MeasureTheory.volume) (r := 5)
      (by rw [finrank_euclideanSpace_fin]; norm_num)
    refine h.congr ?_
    filter_upwards with p
    rw [Real.rpow_neg (by positivity : (0 : ℝ) ≤ 1 + ‖p‖)]
    congr 1
    exact Real.rpow_natCast (1 + ‖p‖) 5
  refine ⟨((2 * Real.pi) ^ 3)⁻¹ * C₀ ^ 2 * ∫ p : ℝ³, ((1 + ‖p‖ : ℝ) ^ 5)⁻¹,
    by positivity, fun C hC => ?_⟩
  have key : ∫ p : ℝ³, Submission.BoseGases.fsKinCoeff C ‖p‖ * (Work.OneBodyKin.profHat p) ^ 2
      ≤ C₀ ^ 2 * (C ^ 17)⁻¹ * ∫ p : ℝ³, ((1 + ‖p‖ : ℝ) ^ 5)⁻¹ := by
    rw [← MeasureTheory.integral_const_mul]
    refine MeasureTheory.integral_mono_of_nonneg ?_ (hIint.const_mul _) ?_
    · filter_upwards with p
      exact mul_nonneg (Submission.BoseGases.fsKinCoeff_nonneg C ‖p‖) (sq_nonneg _)
    · filter_upwards with p
      exact fsKinCoeff_mul_profHat_sq_le hC hdec p
  calc Work.OneBodyKin.symA 1 (Submission.BoseGases.fsKinCoeff C) 0
      = ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : ℝ³,
          Submission.BoseGases.fsKinCoeff C ‖p‖ * (Work.OneBodyKin.profHat p) ^ 2 := by
        simp only [Work.OneBodyKin.symA, zero_add, inv_one, one_smul]
    _ ≤ ((2 * Real.pi) ^ 3)⁻¹ *
          (C₀ ^ 2 * (C ^ 17)⁻¹ * ∫ p : ℝ³, ((1 + ‖p‖ : ℝ) ^ 5)⁻¹) :=
        mul_le_mul_of_nonneg_left key (by positivity)
    _ = (((2 * Real.pi) ^ 3)⁻¹ * C₀ ^ 2 * ∫ p : ℝ³, ((1 + ‖p‖ : ℝ) ^ 5)⁻¹) / C ^ 17 := by
        rw [div_eq_mul_inv]; ring

/-! ## 2. The parameter arithmetic: (T1) from the decay -/

/-- **The tail condition (T1) from the decay of the origin symbol.**  Given
`symA 1 (fsKinCoeff C) 0 ≤ K C^{-17}` for `C ≥ 1` (with `K ≥ 0`), the conclusion of
`symA_tail_fsParams` holds.

The choice is `ε₀ := min (2^{-323}) (M^{-323/5})` with `M := 4096·2^{17}·(K+1)`: it makes the
diluteness `t = μa³ ≤ ε₀` small enough that `s = t^{1/323} ≤ M^{-1/5}`, hence
`K·(2s)^{17} = K·2^{17}s⁵·s^{12} ≤ (1/4096)s^{12} = (1/4096)d²`. -/
private lemma symA_tail_of_decay {v : EuclideanSpace ℝ (Fin 3) → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (hdec : ∀ C : ℝ, 1 ≤ C →
      Work.OneBodyKin.symA 1 (Submission.BoseGases.fsKinCoeff C) 0 ≤ K / C ^ 17) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      ((Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
          * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d) ^ 2)⁻¹
        * Work.OneBodyKin.symA 1
            (Submission.BoseGases.fsKinCoeff
              ((2 * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s)⁻¹)) 0
      ≤ (1 / 4096) * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))⁻¹ ^ 2 := by
  refine ⟨min ((1 / 2 : ℝ) ^ 323) ((4096 * (2 : ℝ) ^ 17 * (K + 1)) ^ (-(323 / 5 : ℝ))),
    lt_min (by positivity) (Real.rpow_pos_of_pos (by positivity) _), ?_⟩
  intro μ hμ
  have ha : 0 < _root_.BoseGases.a v := Work.BoseFixB1.adm_a_pos hμ
  have hs : 0 < (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s := Work.BoseFixB1.adm_s_pos hμ
  have hd : 0 < (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d := Work.BoseFixB1.adm_d_pos hμ
  have hℓ : 0 < Work.BoseBox.sideAt μ (_root_.BoseGases.a v) := Work.BoseFixB1.adm_ell_pos hμ
  set t : ℝ := μ * (_root_.BoseGases.a v) ^ 3 with ht
  have htpos : 0 < t := by rw [ht]; exact mul_pos hμ.1 (pow_pos ha 3)
  -- unfold the FS parameters as powers of the diluteness `t = μa³`
  have hs_eq : (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s = t ^ (1 / 323 : ℝ) := by
    rw [ht]
    simp [Work.BoseBox.paramsAt, Work.BoseBox.fsParams, Work.BoseBox.fsXp]
  have hd_eq : (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d
      = ((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s) ^ 6 := by
    have h1 : ((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s) ^ 6 = t ^ (6 / 323 : ℝ) := by
      rw [hs_eq, ← Real.rpow_natCast (t ^ (1 / 323 : ℝ)) 6, ← Real.rpow_mul htpos.le]
      congr 1
      norm_num
    have h2 : (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d = t ^ (6 / 323 : ℝ) := by
      rw [ht]
      simp [Work.BoseBox.paramsAt, Work.BoseBox.fsParams, Work.BoseBox.fsXp]
    linarith [h1, h2]
  -- `s ≤ 1/2`, hence the cut-off `C = (2s)⁻¹` is at least `1`
  have hs_le : (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s ≤ 1 / 2 := by
    rw [hs_eq]
    have h1 : t ^ (1 / 323 : ℝ) ≤ ((1 / 2 : ℝ) ^ 323) ^ (1 / 323 : ℝ) :=
      Real.rpow_le_rpow htpos.le (le_trans hμ.2.1 (min_le_left _ _)) (by norm_num)
    have h2 : ((1 / 2 : ℝ) ^ 323) ^ (1 / 323 : ℝ) = 1 / 2 := by
      rw [← Real.rpow_natCast (1 / 2 : ℝ) 323,
        ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 1 / 2)]
      norm_num
    linarith [h1, h2]
  have hC1 : 1 ≤ (2 * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s)⁻¹ := by
    have h2s_pos : 0 < 2 * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s := by linarith
    have h2s_le : 2 * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s ≤ 1 := by linarith
    have h := (inv_le_inv₀ (show (0 : ℝ) < 1 by norm_num) h2s_pos).mpr h2s_le
    simpa using h
  have hsymA := hdec ((2 * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s)⁻¹) hC1
  have hrew : K / ((2 * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s)⁻¹) ^ 17
      = K * (2 * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s) ^ 17 := by
    rw [div_eq_mul_inv, inv_pow, inv_inv]
  -- the smallness `s⁵ ≤ M⁻¹`
  have hs5 : ((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s) ^ 5
      ≤ (4096 * (2 : ℝ) ^ 17 * (K + 1))⁻¹ := by
    have hM : 0 < 4096 * (2 : ℝ) ^ 17 * (K + 1) := by positivity
    have h1 : ((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s) ^ 5 = t ^ (5 / 323 : ℝ) := by
      rw [hs_eq, ← Real.rpow_natCast (t ^ (1 / 323 : ℝ)) 5, ← Real.rpow_mul htpos.le]
      congr 1
      norm_num
    have h2 : t ^ (5 / 323 : ℝ)
        ≤ ((4096 * (2 : ℝ) ^ 17 * (K + 1)) ^ (-(323 / 5 : ℝ))) ^ (5 / 323 : ℝ) :=
      Real.rpow_le_rpow htpos.le (le_trans hμ.2.1 (min_le_right _ _)) (by norm_num)
    have h3 : ((4096 * (2 : ℝ) ^ 17 * (K + 1)) ^ (-(323 / 5 : ℝ))) ^ (5 / 323 : ℝ)
        = (4096 * (2 : ℝ) ^ 17 * (K + 1))⁻¹ := by
      rw [← Real.rpow_mul hM.le, show (-(323 / 5 : ℝ)) * (5 / 323 : ℝ) = -1 by norm_num,
        Real.rpow_neg_one]
    linarith [h1, h2, h3]
  -- `K·(2s)^{17} ≤ (1/4096)·s^{12}`
  have hKey : K * (2 * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s) ^ 17
      ≤ (1 / 4096) * ((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s) ^ 12 := by
    have h5' : ((K + 1) * (2 : ℝ) ^ 17)
        * ((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s) ^ 5 ≤ 1 / 4096 := by
      have h := mul_le_mul_of_nonneg_left hs5 (by positivity : (0 : ℝ) ≤ (K + 1) * (2 : ℝ) ^ 17)
      have hMeq : ((K + 1) * (2 : ℝ) ^ 17)
          * (4096 * (2 : ℝ) ^ 17 * (K + 1))⁻¹ = 1 / 4096 := by
        field_simp
      linarith [h, hMeq]
    have h5 : K * (2 : ℝ) ^ 17 * ((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s) ^ 5
        ≤ 1 / 4096 := by
      have hKle : K ≤ K + 1 := by linarith
      have hnonneg : (0 : ℝ) ≤ (2 : ℝ) ^ 17
          * ((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s) ^ 5 := by positivity
      have h := mul_le_mul_of_nonneg_right hKle hnonneg
      linarith [h, h5']
    have hmul := mul_le_mul_of_nonneg_right h5
      (pow_nonneg (le_of_lt hs) 12)
    calc K * (2 * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s) ^ 17
        = K * ((2 : ℝ) ^ 17 * ((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s) ^ 17) := by
          rw [mul_pow]
      _ = (K * (2 : ℝ) ^ 17 * ((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s) ^ 5)
            * ((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s) ^ 12 := by ring
      _ ≤ (1 / 4096) * ((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s) ^ 12 := hmul
  have hsym_d : Work.OneBodyKin.symA 1
        (Submission.BoseGases.fsKinCoeff ((2 * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s)⁻¹)) 0
      ≤ (1 / 4096) * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d ^ 2 := by
    have hstep : Work.OneBodyKin.symA 1
          (Submission.BoseGases.fsKinCoeff ((2 * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s)⁻¹)) 0
        ≤ K * (2 * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s) ^ 17 := by
      rw [← hrew]; exact hsymA
    refine le_trans hstep ?_
    have hsq : (1 / 4096) * ((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s ^ 6) ^ 2
        = (1 / 4096) * ((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s) ^ 12 := by
      rw [← pow_mul]
    rw [hd_eq, hsq]
    exact hKey
  -- divide through by the positive factor `(ℓ d)²`
  have hfac : 0 < ((Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
      * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d) ^ 2)⁻¹ := by
    rw [inv_pos]
    positivity
  calc ((Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
        * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d) ^ 2)⁻¹
      * Work.OneBodyKin.symA 1
          (Submission.BoseGases.fsKinCoeff
            ((2 * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s)⁻¹)) 0
      ≤ ((Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
          * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d) ^ 2)⁻¹
        * ((1 / 4096) * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d ^ 2) :=
        mul_le_mul_of_nonneg_left hsym_d (le_of_lt hfac)
    _ = (1 / 4096) * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))⁻¹ ^ 2 := by
        have hℓne : Work.BoseBox.sideAt μ (_root_.BoseGases.a v) ≠ 0 := ne_of_gt hℓ
        have hdne : (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d ≠ 0 := ne_of_gt hd
        rw [mul_pow, mul_inv, inv_pow]
        field_simp

/-- **The tail condition (T1)** (see the module docstring). -/
theorem symA_tail_fsParams {v : EuclideanSpace ℝ (Fin 3) → ℝ} :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      ((Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
          * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d) ^ 2)⁻¹
        * Work.OneBodyKin.symA 1
            (Submission.BoseGases.fsKinCoeff
              ((2 * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s)⁻¹)) 0
      ≤ (1 / 4096) * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))⁻¹ ^ 2 := by
  obtain ⟨K, hK, hdec⟩ := symA_one_fsKinCoeff_decay_seventeen
  exact symA_tail_of_decay hK hdec

end

end Work.BoseFixR.FamForm
