/-
# The pointwise symbol square-sum bound for the modulated height-`0` deviation

Given

* the pointwise bound `‖ballDev P N t ξ‖ ≤ Cb · min 1 (ballScale P N · |ξ|)`,
* the vanishing of `ballDev` where `ballScale P N · |ξ| ≥ 1`, and
* the reduction of the periodisation of the deviation to (at most) two translates,
  `periodize (ballDev P N t) θ = ballDev P N t (circRep θ) + ballDev P N t (circRep θ - 1)`,

the family of periodisations `n ↦ periodize (ballDev P ⌊a n⌋ t)` is controlled pointwise in the
frequency `θ` by the lacunary geometric sum of `Work.KMTPlan.A6.lacunaryGeometricSumLeENNReal`:

  `∑'_n ‖periodize (ballDev P ⌊a n⌋ t) θ‖ₑ² ≤ W²`, uniformly in the `Λ`-lacunary family `a`, in
  `t ∈ [1/2,1]` and in `θ`.

This is the pointwise symbol square-sum bound consumed by
`Work.KMTPlan.A6.tsum_eLpNorm_sq_iwConv_le`.
-/
import Mathlib
import Submission.Work.KMTPlan.A6.ballDevScaleArith
import Submission.Work.KMTPlan.A6.lacunaryGeometricSumLeENNReal

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTPlan.A6

open MeasureTheory Polynomial
open scoped ENNReal NNReal BigOperators

theorem ballDevScaleSqLe (P : Polynomial ℤ) (N : ℕ) (hN : 1 ≤ N) {δ : ℝ} (hδ : 0 ≤ δ) :
    (ballScale P N * δ) ^ 2 * (if ballScale P N * δ < 1 then 1 else 0)
      ≤ (2:ℝ) ^ (2 * P.natDegree) *
          (((N:ℝ) ^ P.natDegree * δ) ^ 2 *
            (if (N:ℝ) ^ P.natDegree * δ < (2:ℝ) ^ P.natDegree then 1 else 0)) := by
  obtain ⟨h1, h2⟩ := ballScale_le_pow_mul P N hN
  have hσnn : 0 ≤ ballScale P N := (ballScale_pos P N).le
  have h2d : (0:ℝ) < (2:ℝ)^P.natDegree := by positivity
  rcases lt_or_ge (ballScale P N * δ) 1 with hlt | hge
  · have hDδ : (N:ℝ)^P.natDegree * δ < (2:ℝ)^P.natDegree := by
      have h3 : (N:ℝ)^P.natDegree * δ ≤ (2:ℝ)^P.natDegree * (ballScale P N * δ) := by
        calc (N:ℝ)^P.natDegree * δ ≤ ((2:ℝ)^P.natDegree * ballScale P N) * δ :=
              mul_le_mul_of_nonneg_right h2 hδ
          _ = (2:ℝ)^P.natDegree * (ballScale P N * δ) := by ring
      nlinarith [h3, hlt, h2d]
    rw [if_pos hlt, if_pos hDδ, mul_one, mul_one]
    have hσδ0 : 0 ≤ ballScale P N * δ := mul_nonneg hσnn hδ
    have h4 : ballScale P N * δ ≤ (2:ℝ)^P.natDegree * ((N:ℝ)^P.natDegree * δ) := by
      calc ballScale P N * δ ≤ ((2:ℝ)^P.natDegree * (N:ℝ)^P.natDegree) * δ :=
            mul_le_mul_of_nonneg_right h1 hδ
        _ = (2:ℝ)^P.natDegree * ((N:ℝ)^P.natDegree * δ) := by ring
    calc (ballScale P N * δ)^2 ≤ ((2:ℝ)^P.natDegree * ((N:ℝ)^P.natDegree * δ))^2 :=
          pow_le_pow_left₀ hσδ0 h4 2
      _ = ((2:ℝ)^P.natDegree)^2 * ((N:ℝ)^P.natDegree * δ)^2 := by ring
      _ = (2:ℝ)^(2 * P.natDegree) * ((N:ℝ)^P.natDegree * δ)^2 := by
          rw [← pow_mul, Nat.mul_comm P.natDegree 2]
  · rw [if_neg (by linarith : ¬ (ballScale P N * δ < 1)), mul_zero]
    exact mul_nonneg (by positivity)
      (mul_nonneg (sq_nonneg _) (by split_ifs <;> norm_num))

theorem ballDevSqSum (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) (Λ : NNReal) (hΛ : 1 < Λ)
    (Cb : ℝ) (hCb : 0 < Cb)
    (hbound : ∀ (N : ℕ) (t : ℝ), t ∈ Set.Icc (1 / 2 : ℝ) 1 → ∀ ξ : ℝ,
      ‖ballDev P N t ξ‖ ≤ Cb * min 1 (ballScale P N * |ξ|))
    (hvanish : ∀ (N : ℕ) (t : ℝ) (ξ : ℝ), 1 ≤ ballScale P N * |ξ| → ballDev P N t ξ = 0)
    (hper : ∀ (N : ℕ) (t : ℝ) (θ : Work.Analysis.IonescuWainger.Circle),
      Work.Analysis.IonescuWainger.periodize (ballDev P N t) θ
        = ballDev P N t (circRep θ) + ballDev P N t (circRep θ - 1)) :
    ∃ W : NNReal, ∀ (a : ℕ → NNReal), PointwiseErgodicTheorems.Lacunary Λ a →
      (∀ n : ℕ, 1 ≤ a n) → ∀ (t : ℝ), t ∈ Set.Icc (1 / 2 : ℝ) 1 →
      ∀ θ : Work.Analysis.IonescuWainger.Circle,
        (∑' n : ℕ, ‖Work.Analysis.IonescuWainger.periodize
            (ballDev P (Nat.floor (a n)) t) θ‖ₑ ^ (2 : ℝ))
          ≤ (W : ENNReal) ^ 2 := by
  classical
  obtain ⟨Cg, hCgne, hCg⟩ := lacunaryGeometricSumLeENNReal Λ hΛ P.natDegree (by omega)
  set c : ℝ := Cg.toReal with hcdef
  have hcnn : 0 ≤ c := ENNReal.toReal_nonneg
  have hCgeq : Cg = ENNReal.ofReal c := by
    rw [hcdef]
    exact (ENNReal.ofReal_toReal hCgne).symm
  set K : ℝ := 2 * Cb^2 * (2:ℝ)^(2 * P.natDegree) with hKdef
  have hKnn : 0 ≤ K := by rw [hKdef]; positivity
  set Wr : NNReal := ⟨Real.sqrt (K * (2*c)) + 1, by positivity⟩ with hWrdef
  have hWrval : (Wr : ℝ) = Real.sqrt (K * (2*c)) + 1 := rfl
  refine ⟨Wr, ?_⟩
  intro a ha ha1 t ht θ
  set x : ℝ := |circRep θ| with hxdef
  set y : ℝ := |circRep θ - 1| with hydef
  have hxnn : 0 ≤ x := by rw [hxdef]; exact abs_nonneg _
  have hynn : 0 ≤ y := by rw [hydef]; exact abs_nonneg _
  set A : ℕ → ℝ → ℝ := fun n δ => (((Nat.floor (a n) : ℝ)) ^ P.natDegree * δ)^2 *
      (if ((Nat.floor (a n) : ℝ)) ^ P.natDegree * δ < (2:ℝ)^P.natDegree then 1 else 0) with hAdef
  have hAnn : ∀ n δ, 0 ≤ A n δ :=
    fun n δ => mul_nonneg (sq_nonneg _) (by split_ifs <;> norm_num)
  have hpt : ∀ n : ℕ, ‖Work.Analysis.IonescuWainger.periodize
        (ballDev P (Nat.floor (a n)) t) θ‖ₑ ^ (2 : ℝ)
      ≤ ENNReal.ofReal K * (ENNReal.ofReal (A n x) + ENNReal.ofReal (A n y)) := by
    intro n
    have hN1 : 1 ≤ Nat.floor (a n) := by
      have hm : Nat.floor (1 : NNReal) ≤ Nat.floor (a n) := Nat.floor_mono (ha1 n)
      simpa using hm
    have hstep1 : ∀ ξ : ℝ, ‖ballDev P (Nat.floor (a n)) t ξ‖
        ≤ Cb * ((ballScale P (Nat.floor (a n)) * |ξ|) *
            (if ballScale P (Nat.floor (a n)) * |ξ| < 1 then 1 else 0)) := by
      intro ξ
      rcases lt_or_ge (ballScale P (Nat.floor (a n)) * |ξ|) 1 with hlt | hge
      · rw [if_pos hlt]
        have hb := hbound (Nat.floor (a n)) t ht ξ
        rw [min_eq_right hlt.le] at hb
        simpa using hb
      · rw [if_neg (by linarith : ¬ (ballScale P (Nat.floor (a n)) * |ξ| < 1)), mul_zero, mul_zero]
        rw [hvanish (Nat.floor (a n)) t ξ hge, norm_zero]
    have hstep2 : ∀ ξ : ℝ, ‖ballDev P (Nat.floor (a n)) t ξ‖^2
        ≤ (Cb * (2:ℝ)^P.natDegree)^2 * A n |ξ| := by
      intro ξ
      have h1 := hstep1 ξ
      have h3 : ((ballScale P (Nat.floor (a n)) * |ξ|) *
          (if ballScale P (Nat.floor (a n)) * |ξ| < 1 then (1:ℝ) else 0))^2
          = (ballScale P (Nat.floor (a n)) * |ξ|)^2 *
            (if ballScale P (Nat.floor (a n)) * |ξ| < 1 then 1 else 0) := by
        split_ifs <;> ring
      have h4 := ballDevScaleSqLe P (Nat.floor (a n)) hN1 (abs_nonneg ξ)
      calc ‖ballDev P (Nat.floor (a n)) t ξ‖^2
          ≤ (Cb * ((ballScale P (Nat.floor (a n)) * |ξ|) *
              (if ballScale P (Nat.floor (a n)) * |ξ| < 1 then 1 else 0)))^2 :=
            pow_le_pow_left₀ (norm_nonneg _) h1 2
        _ = Cb^2 * (((ballScale P (Nat.floor (a n)) * |ξ|) *
              (if ballScale P (Nat.floor (a n)) * |ξ| < 1 then 1 else 0))^2) := by ring
        _ = Cb^2 * ((ballScale P (Nat.floor (a n)) * |ξ|)^2 *
              (if ballScale P (Nat.floor (a n)) * |ξ| < 1 then 1 else 0)) := by rw [h3]
        _ ≤ Cb^2 * ((2:ℝ)^(2 * P.natDegree) * A n |ξ|) :=
            mul_le_mul_of_nonneg_left h4 (sq_nonneg Cb)
        _ = (Cb * (2:ℝ)^P.natDegree)^2 * A n |ξ| := by
            rw [hAdef]; ring
    have hsq : ‖Work.Analysis.IonescuWainger.periodize
          (ballDev P (Nat.floor (a n)) t) θ‖^2 ≤ K * (A n x + A n y) := by
      have hp := hper (Nat.floor (a n)) t θ
      rw [hp]
      have h1 : ‖ballDev P (Nat.floor (a n)) t (circRep θ)
            + ballDev P (Nat.floor (a n)) t (circRep θ - 1)‖
          ≤ ‖ballDev P (Nat.floor (a n)) t (circRep θ)‖
            + ‖ballDev P (Nat.floor (a n)) t (circRep θ - 1)‖ := norm_add_le _ _
      have h2 : (‖ballDev P (Nat.floor (a n)) t (circRep θ)‖
            + ‖ballDev P (Nat.floor (a n)) t (circRep θ - 1)‖)^2
          ≤ 2 * (‖ballDev P (Nat.floor (a n)) t (circRep θ)‖^2
            + ‖ballDev P (Nat.floor (a n)) t (circRep θ - 1)‖^2) := by
        nlinarith [sq_nonneg (‖ballDev P (Nat.floor (a n)) t (circRep θ)‖
            - ‖ballDev P (Nat.floor (a n)) t (circRep θ - 1)‖)]
      calc ‖ballDev P (Nat.floor (a n)) t (circRep θ)
              + ballDev P (Nat.floor (a n)) t (circRep θ - 1)‖^2
          ≤ (‖ballDev P (Nat.floor (a n)) t (circRep θ)‖
            + ‖ballDev P (Nat.floor (a n)) t (circRep θ - 1)‖)^2 :=
            pow_le_pow_left₀ (norm_nonneg _) h1 2
        _ ≤ 2 * (‖ballDev P (Nat.floor (a n)) t (circRep θ)‖^2
            + ‖ballDev P (Nat.floor (a n)) t (circRep θ - 1)‖^2) := h2
        _ ≤ 2 * ((Cb * (2:ℝ)^P.natDegree)^2 * A n x
            + (Cb * (2:ℝ)^P.natDegree)^2 * A n y) := by
            gcongr
            · rw [hxdef]; exact hstep2 _
            · rw [hydef]; exact hstep2 _
        _ = K * (A n x + A n y) := by rw [hKdef]; ring
    have hen : ‖Work.Analysis.IonescuWainger.periodize
          (ballDev P (Nat.floor (a n)) t) θ‖ₑ ^ (2 : ℝ)
        = ENNReal.ofReal (‖Work.Analysis.IonescuWainger.periodize
          (ballDev P (Nat.floor (a n)) t) θ‖^2) := by
      rw [← ofReal_norm,
        ENNReal.ofReal_rpow_of_nonneg (norm_nonneg _) (by norm_num : (0:ℝ) ≤ 2)]
      congr 1
      rw [Real.rpow_two, pow_two]
    rw [hen]
    refine (ENNReal.ofReal_le_ofReal hsq).trans (le_of_eq ?_)
    rw [show K * (A n x + A n y) = K * A n x + K * A n y from by ring,
      ENNReal.ofReal_add (mul_nonneg hKnn (hAnn n x)) (mul_nonneg hKnn (hAnn n y)),
      ENNReal.ofReal_mul hKnn, ENNReal.ofReal_mul hKnn]
    ring
  calc (∑' n : ℕ, ‖Work.Analysis.IonescuWainger.periodize
        (ballDev P (Nat.floor (a n)) t) θ‖ₑ ^ (2 : ℝ))
      ≤ ∑' n : ℕ, ENNReal.ofReal K * (ENNReal.ofReal (A n x) + ENNReal.ofReal (A n y)) :=
        ENNReal.tsum_le_tsum hpt
    _ = ENNReal.ofReal K * ((∑' n : ℕ, ENNReal.ofReal (A n x))
          + (∑' n : ℕ, ENNReal.ofReal (A n y))) := by
        rw [ENNReal.tsum_mul_left, ENNReal.tsum_add]
    _ ≤ ENNReal.ofReal K * (Cg + Cg) := by
        gcongr
        · exact hCg a ha ha1 x hxnn
        · exact hCg a ha ha1 y hynn
    _ = ENNReal.ofReal (K * (2 * c)) := by
        rw [hCgeq, ← ENNReal.ofReal_add hcnn hcnn, ← ENNReal.ofReal_mul hKnn]
        congr 1
        ring
    _ ≤ (Wr : ENNReal) ^ 2 := by
        have hcoe : (Wr : ENNReal) = ENNReal.ofReal (Wr : ℝ) := ENNReal.coe_nnreal_eq Wr
        rw [hcoe, ← ENNReal.ofReal_pow (show (0:ℝ) ≤ (Wr:ℝ) by positivity) 2]
        refine ENNReal.ofReal_le_ofReal ?_
        have hs : Real.sqrt (K * (2*c)) ^ 2 = K * (2*c) :=
          Real.sq_sqrt (by positivity : (0:ℝ) ≤ K * (2*c))
        have hsn : 0 ≤ Real.sqrt (K * (2*c)) := Real.sqrt_nonneg _
        rw [hWrval]
        nlinarith


end Work.KMTPlan.A6
