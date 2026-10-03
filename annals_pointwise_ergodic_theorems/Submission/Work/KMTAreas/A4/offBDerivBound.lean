/-
# The `L¹` bound for the derivative of the middle piece `λ_k - η_{≤jj} λ_k`

This file proves `Work.KMTAreas.A4.offBDerivBound`: for `k ≤ 0`, `jj ≥ 0`, `k + jj ≥ 0` there is a
single constant `C > 0` with

  `∫ ‖ (λ_k - η_{≤jj} · λ_k)' ‖ ≤ C · 2^k · (max 2^{k+jj-1} 1)^{-N}`

where `λ_k = 𝓕⁻ η_{≤k}` (`Work.KMTAreas.A4.lam`) and `η_{≤jj}` (`Work.KMTAreas.A4.bmp`).

## The mathematics

Write `F = λ_k (1 - η_{≤jj})`.  Since `η_{≤jj} = 1` on `[-2^{jj-1}, 2^{jj-1}]`, the factor `1 - η`
vanishes on that interval, and `F' = λ_k' (1 - η) - λ_k η'`:

* the first term is dominated by `‖λ_k'‖`, which is supported on the tail
  `{|x| ≥ 2^{jj-1}}`; the derivative tail estimate `offLamTail 1 N` gives
  `∫⁻_{tail} ‖λ_k'‖ ≤ C₁ 2^k (max 2^{k+jj-1} 1)^{-N}`;
* the second term is dominated by `‖λ_k‖ · C₂ 2^{-jj}` and the (non-derivative) tail estimate
  `offLamTail 0 N` at the same scale gives `∫⁻_{tail} ‖λ_k‖ ≤ C₀ (max 2^{k+jj-1} 1)^{-N}`;
  the extra factor `2^{-jj} ≤ 2^k` (which is where `k + jj ≥ 0` is used) produces the required
  `2^k`.

Off the tail `F` is locally zero, so `F' = 0` there; this is what makes the restriction of the
two integrands to the tail legitimate.
-/
import Mathlib
import Submission.Work.KMTAreas.A4.offCutDeriv
import Submission.Work.KMTAreas.A4.offPieceMid

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTAreas.A4

open MeasureTheory Filter
open scoped ENNReal Topology

noncomputable section

/-! ## The local behaviour of the middle piece -/

/-- `η_{≤jj}` is identically `1` in a neighbourhood of every point with `|x| < 2^{jj-1}`. -/
theorem bmp_eventuallyEq_one {jj : ℤ} {x : ℝ} (hx : |x| < (2 : ℝ) ^ (jj - 1)) :
    ((bmp jj : SchwartzMap ℝ ℂ) : ℝ → ℂ) =ᶠ[𝓝 x] (fun _ => (1 : ℂ)) := by
  show ∀ᶠ y in 𝓝 x, ((bmp jj : SchwartzMap ℝ ℂ) : ℝ → ℂ) y = 1
  rw [Metric.eventually_nhds_iff]
  refine ⟨(2 : ℝ) ^ (jj - 1) - |x|, by linarith, ?_⟩
  intro y hy
  have hy' : |y - x| < (2 : ℝ) ^ (jj - 1) - |x| := by rwa [Real.dist_eq] at hy
  have h1 : |y| ≤ |x| + |y - x| := by
    have := abs_add_le x (y - x)
    rwa [show x + (y - x) = y by ring] at this
  rw [bmp_one_of_le jj (by linarith)]

/-- The middle piece `λ_k - η_{≤jj} λ_k` vanishes in a neighbourhood of every point with
`|x| < 2^{jj-1}`. -/
theorem midPiece_eventuallyEq_zero (k jj : ℤ) {x : ℝ} (hx : |x| < (2 : ℝ) ^ (jj - 1)) :
    ((lam k - mS (bmp jj) (lam k) : SchwartzMap ℝ ℂ) : ℝ → ℂ)
      =ᶠ[𝓝 x] (fun _ => (0 : ℂ)) := by
  filter_upwards [bmp_eventuallyEq_one (jj := jj) hx] with y hy
  show (lam k) y - (bmp jj) y * (lam k) y = 0
  rw [hy]; ring

/-- The derivative of the middle piece vanishes at every point with `|x| < 2^{jj-1}`. -/
theorem deriv_midPiece_eq_zero (k jj : ℤ) {x : ℝ} (hx : |x| < (2 : ℝ) ^ (jj - 1)) :
    deriv ((lam k - mS (bmp jj) (lam k) : SchwartzMap ℝ ℂ) : ℝ → ℂ) x = 0 := by
  have h := (midPiece_eventuallyEq_zero k jj hx).deriv_eq
  simpa using h

/-- The product rule for the middle piece. -/
theorem deriv_midPiece_eq (k jj : ℤ) (x : ℝ) :
    deriv ((lam k - mS (bmp jj) (lam k) : SchwartzMap ℝ ℂ) : ℝ → ℂ) x
      = deriv (⇑(lam k)) x * (1 - (bmp jj) x)
        + (lam k) x * (- deriv (⇑(bmp jj)) x) := by
  have hF : ((lam k - mS (bmp jj) (lam k) : SchwartzMap ℝ ℂ) : ℝ → ℂ)
      = fun y : ℝ => (lam k) y * (1 - (bmp jj) y) := by
    funext y
    show (lam k) y - (bmp jj) y * (lam k) y = _
    ring
  rw [hF]
  have h1 : deriv (fun y : ℝ => (lam k) y * (1 - (bmp jj) y)) x
      = deriv (fun y : ℝ => (lam k) y) x * (1 - (bmp jj) x)
        + (lam k) x * deriv (fun y : ℝ => 1 - (bmp jj) y) x := by
    rw [show (fun y : ℝ => (lam k) y * (1 - (bmp jj) y))
        = ((fun y : ℝ => (lam k) y) * (fun y : ℝ => 1 - (bmp jj) y)) from rfl]
    exact deriv_mul ((lam k).differentiable.differentiableAt)
      (((bmp jj).differentiable.differentiableAt).const_sub 1)
  rw [h1, deriv_const_sub]

/-! ## The main estimate -/

theorem offBDerivBound (N : ℕ) : ∃ C : ℝ, 0 < C ∧ ∀ (k jj : ℤ), k ≤ 0 → 0 ≤ jj → 0 ≤ k + jj → ∫ x : ℝ, ‖deriv (((Work.KMTAreas.A4.lam k - Work.KMTAreas.A4.mS (Work.KMTAreas.A4.bmp jj) (Work.KMTAreas.A4.lam k)) : SchwartzMap ℝ ℂ) : ℝ → ℂ) x‖ ≤ C * (2:ℝ)^k * (max ((2:ℝ)^(k+jj-1)) 1) ^ (-(N:ℝ)) := by
  obtain ⟨Cd, hCdpos, hCd⟩ := offCutDeriv
  obtain ⟨C₁, hC₁pos, hC₁⟩ := offLamTail 1 N
  obtain ⟨C₀, hC₀pos, hC₀⟩ := offLamTail 0 N
  refine ⟨C₁ + Cd * C₀, add_pos hC₁pos (mul_pos hCdpos hC₀pos), ?_⟩
  intro k jj hk hjj hkj
  -- abbreviations
  set R : ℝ := (2 : ℝ) ^ (jj - 1) with hR
  set T : Set ℝ := {x : ℝ | R ≤ |x|} with hT
  have hRpos : 0 < R := by rw [hR]; exact zpow_pos (by norm_num) (jj - 1)
  have hTmeas : MeasurableSet T := by
    have h := absSet_eq_Ici_union_Iic hRpos.le
    rw [hT, h]
    exact measurableSet_Ici.union measurableSet_Iic
  have hkR : (2 : ℝ) ^ k * R = (2 : ℝ) ^ (k + jj - 1) := by
    rw [hR, ← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    congr 1
    ring
  -- **the pointwise bound**
  have hpoint : ∀ x : ℝ, ‖deriv ((lam k - mS (bmp jj) (lam k) : SchwartzMap ℝ ℂ) : ℝ → ℂ) x‖
      ≤ ‖deriv (⇑(lam k)) x‖ + ‖(lam k) x‖ * (Cd * (2 : ℝ) ^ (-jj)) := by
    intro x
    by_cases hx : R ≤ |x|
    · have h1 := deriv_midPiece_eq k jj x
      have h2 : ‖1 - (bmp jj) x‖ ≤ 1 := norm_one_sub_bmp_le jj x
      have h3 : ‖deriv (⇑(bmp jj)) x‖ ≤ Cd * (2 : ℝ) ^ (-jj) := (hCd jj x).1
      calc ‖deriv ((lam k - mS (bmp jj) (lam k) : SchwartzMap ℝ ℂ) : ℝ → ℂ) x‖
          = ‖deriv (⇑(lam k)) x * (1 - (bmp jj) x)
              + (lam k) x * (- deriv (⇑(bmp jj)) x)‖ := by rw [h1]
        _ ≤ ‖deriv (⇑(lam k)) x * (1 - (bmp jj) x)‖
              + ‖(lam k) x * (- deriv (⇑(bmp jj)) x)‖ := norm_add_le _ _
        _ = ‖deriv (⇑(lam k)) x‖ * ‖1 - (bmp jj) x‖
              + ‖(lam k) x‖ * ‖deriv (⇑(bmp jj)) x‖ := by
              rw [norm_mul, norm_mul, norm_neg]
        _ ≤ ‖deriv (⇑(lam k)) x‖ * 1 + ‖(lam k) x‖ * (Cd * (2 : ℝ) ^ (-jj)) := by
              gcongr
        _ = ‖deriv (⇑(lam k)) x‖ + ‖(lam k) x‖ * (Cd * (2 : ℝ) ^ (-jj)) := by ring
    · have hx' : |x| < (2 : ℝ) ^ (jj - 1) := by rw [← hR]; exact not_le.mp hx
      rw [deriv_midPiece_eq_zero k jj hx']
      simp only [norm_zero]
      have h1 : (0 : ℝ) ≤ ‖deriv (⇑(lam k)) x‖ := norm_nonneg _
      have h2 : (0 : ℝ) ≤ ‖(lam k) x‖ := norm_nonneg _
      have h3 : (0 : ℝ) ≤ Cd * (2 : ℝ) ^ (-jj) :=
        mul_nonneg hCdpos.le (zpow_pos (by norm_num : (0 : ℝ) < 2) (-jj)).le
      linarith [h1, mul_nonneg h2 h3]
  -- **the pointwise `ENNReal` bound**
  have hpointE : ∀ x : ℝ,
      ENNReal.ofReal (‖deriv ((lam k - mS (bmp jj) (lam k) : SchwartzMap ℝ ℂ) : ℝ → ℂ) x‖)
        ≤ T.indicator (fun x => ENNReal.ofReal (‖deriv (⇑(lam k)) x‖)) x
          + ENNReal.ofReal (Cd * (2 : ℝ) ^ (-jj)) *
              T.indicator (fun x => ENNReal.ofReal (‖(lam k) x‖)) x := by
    intro x
    by_cases hx : x ∈ T
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
      have h := hpoint x
      have hCdnn : 0 ≤ Cd * (2 : ℝ) ^ (-jj) := by positivity
      calc ENNReal.ofReal (‖deriv ((lam k - mS (bmp jj) (lam k) : SchwartzMap ℝ ℂ) : ℝ → ℂ) x‖)
          ≤ ENNReal.ofReal (‖deriv (⇑(lam k)) x‖ + ‖(lam k) x‖ * (Cd * (2 : ℝ) ^ (-jj))) :=
              ENNReal.ofReal_le_ofReal h
        _ = ENNReal.ofReal (‖deriv (⇑(lam k)) x‖)
              + ENNReal.ofReal (Cd * (2 : ℝ) ^ (-jj)) * ENNReal.ofReal (‖(lam k) x‖) := by
              rw [ENNReal.ofReal_add (norm_nonneg _) (by positivity),
                ENNReal.ofReal_mul (norm_nonneg _), mul_comm]
        _ = ENNReal.ofReal (‖deriv (⇑(lam k)) x‖)
              + ENNReal.ofReal (Cd * (2 : ℝ) ^ (-jj)) * ENNReal.ofReal (‖(lam k) x‖) := rfl
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]
      have hx' : |x| < (2 : ℝ) ^ (jj - 1) := by
        simp only [hT, Set.mem_ofPred_eq] at hx
        rw [← hR]
        exact not_le.mp hx
      rw [deriv_midPiece_eq_zero k jj hx']
      simp
  -- **the two tail estimates**
  have hb1 : ∫⁻ x in T, ENNReal.ofReal (‖deriv (⇑(lam k)) x‖)
      ≤ ENNReal.ofReal (C₁ * (2 : ℝ) ^ k * (max ((2 : ℝ) ^ (k + jj - 1)) 1) ^ (-(N : ℝ))) := by
    have h1 := hC₁ k R hRpos.le
    rw [pow_one] at h1
    have hfun : (fun x : ℝ => ENNReal.ofReal (‖deriv (⇑(lam k)) x‖))
        = fun x : ℝ => ‖iteratedDeriv 1 (⇑(Work.KMTAreas.A7.etaMult_K k)) x‖ₑ := by
      funext x
      simp only [ofReal_norm, iteratedDeriv_one, lam_eq_etaMult_K]
    rw [hT, hfun, ← hkR]
    exact h1
  have hb2 : ∫⁻ x in T, ENNReal.ofReal (‖(lam k) x‖)
      ≤ ENNReal.ofReal (C₀ * (max ((2 : ℝ) ^ (k + jj - 1)) 1) ^ (-(N : ℝ))) := by
    have h1 := hC₀ k R hRpos.le
    rw [pow_zero, mul_one] at h1
    have hfun : (fun x : ℝ => ENNReal.ofReal (‖(lam k) x‖))
        = fun x : ℝ => ‖iteratedDeriv 0 (⇑(Work.KMTAreas.A7.etaMult_K k)) x‖ₑ := by
      funext x
      simp only [ofReal_norm, iteratedDeriv_zero, lam_eq_etaMult_K]
    rw [hT, hfun, ← hkR]
    exact h1
  -- **the `lintegral` chain**
  have hlin : ∫⁻ x, ENNReal.ofReal
        (‖deriv ((lam k - mS (bmp jj) (lam k) : SchwartzMap ℝ ℂ) : ℝ → ℂ) x‖)
      ≤ ENNReal.ofReal (C₁ * (2 : ℝ) ^ k * (max ((2 : ℝ) ^ (k + jj - 1)) 1) ^ (-(N : ℝ)))
        + ENNReal.ofReal (Cd * (2 : ℝ) ^ (-jj)) *
            ENNReal.ofReal (C₀ * (max ((2 : ℝ) ^ (k + jj - 1)) 1) ^ (-(N : ℝ))) := by
    have hmeasA : Measurable
        (fun x : ℝ => T.indicator (fun x => ENNReal.ofReal (‖deriv (⇑(lam k)) x‖)) x) :=
      Measurable.indicator (by fun_prop) hTmeas
    have hmeasB : Measurable (fun x : ℝ => T.indicator (fun x => ENNReal.ofReal (‖(lam k) x‖)) x) :=
      Measurable.indicator (by fun_prop) hTmeas
    calc ∫⁻ x, ENNReal.ofReal
          (‖deriv ((lam k - mS (bmp jj) (lam k) : SchwartzMap ℝ ℂ) : ℝ → ℂ) x‖)
        ≤ ∫⁻ x, (T.indicator (fun x => ENNReal.ofReal (‖deriv (⇑(lam k)) x‖)) x
            + ENNReal.ofReal (Cd * (2 : ℝ) ^ (-jj)) *
                T.indicator (fun x => ENNReal.ofReal (‖(lam k) x‖)) x) :=
            lintegral_mono hpointE
      _ = (∫⁻ x, T.indicator (fun x => ENNReal.ofReal (‖deriv (⇑(lam k)) x‖)) x)
            + ∫⁻ x, ENNReal.ofReal (Cd * (2 : ℝ) ^ (-jj)) *
                T.indicator (fun x => ENNReal.ofReal (‖(lam k) x‖)) x :=
            lintegral_add_left hmeasA _
      _ = (∫⁻ x in T, ENNReal.ofReal (‖deriv (⇑(lam k)) x‖))
            + ENNReal.ofReal (Cd * (2 : ℝ) ^ (-jj)) *
                ∫⁻ x in T, ENNReal.ofReal (‖(lam k) x‖) := by
            rw [lintegral_indicator hTmeas, lintegral_const_mul _ hmeasB, lintegral_indicator hTmeas]
      _ ≤ ENNReal.ofReal (C₁ * (2 : ℝ) ^ k * (max ((2 : ℝ) ^ (k + jj - 1)) 1) ^ (-(N : ℝ)))
            + ENNReal.ofReal (Cd * (2 : ℝ) ^ (-jj)) *
                ENNReal.ofReal (C₀ * (max ((2 : ℝ) ^ (k + jj - 1)) 1) ^ (-(N : ℝ))) := by
            gcongr
  -- **the final real arithmetic**
  have hArith : C₁ * (2 : ℝ) ^ k * (max ((2 : ℝ) ^ (k + jj - 1)) 1) ^ (-(N : ℝ))
      + Cd * (2 : ℝ) ^ (-jj) * (C₀ * (max ((2 : ℝ) ^ (k + jj - 1)) 1) ^ (-(N : ℝ)))
      ≤ (C₁ + Cd * C₀) * (2 : ℝ) ^ k * (max ((2 : ℝ) ^ (k + jj - 1)) 1) ^ (-(N : ℝ)) := by
    have hM1 : (1 : ℝ) ≤ max ((2 : ℝ) ^ (k + jj - 1)) 1 := le_max_right _ _
    have hMnn : 0 ≤ (max ((2 : ℝ) ^ (k + jj - 1)) 1) ^ (-(N : ℝ)) :=
      Real.rpow_nonneg (le_trans zero_le_one hM1) _
    have h2k : (0 : ℝ) < (2 : ℝ) ^ k := zpow_pos (by norm_num) k
    have hjj2 : (2 : ℝ) ^ (-jj) ≤ (2 : ℝ) ^ k :=
      zpow_le_zpow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (by omega)
    have hle : (2 : ℝ) ^ (-jj) * (max ((2 : ℝ) ^ (k + jj - 1)) 1) ^ (-(N : ℝ))
        ≤ (2 : ℝ) ^ k * (max ((2 : ℝ) ^ (k + jj - 1)) 1) ^ (-(N : ℝ)) :=
      mul_le_mul_of_nonneg_right hjj2 hMnn
    have hsub : Cd * (2 : ℝ) ^ (-jj) * (C₀ * (max ((2 : ℝ) ^ (k + jj - 1)) 1) ^ (-(N : ℝ)))
        ≤ Cd * C₀ * ((2 : ℝ) ^ k * (max ((2 : ℝ) ^ (k + jj - 1)) 1) ^ (-(N : ℝ))) := by
      calc Cd * (2 : ℝ) ^ (-jj) * (C₀ * (max ((2 : ℝ) ^ (k + jj - 1)) 1) ^ (-(N : ℝ)))
          = (Cd * C₀) * ((2 : ℝ) ^ (-jj) * (max ((2 : ℝ) ^ (k + jj - 1)) 1) ^ (-(N : ℝ))) := by
            ring
        _ ≤ (Cd * C₀) * ((2 : ℝ) ^ k * (max ((2 : ℝ) ^ (k + jj - 1)) 1) ^ (-(N : ℝ))) :=
            mul_le_mul_of_nonneg_left hle (mul_nonneg hCdpos.le hC₀pos.le)
    calc C₁ * (2 : ℝ) ^ k * (max ((2 : ℝ) ^ (k + jj - 1)) 1) ^ (-(N : ℝ))
        + Cd * (2 : ℝ) ^ (-jj) * (C₀ * (max ((2 : ℝ) ^ (k + jj - 1)) 1) ^ (-(N : ℝ)))
        ≤ C₁ * (2 : ℝ) ^ k * (max ((2 : ℝ) ^ (k + jj - 1)) 1) ^ (-(N : ℝ))
          + Cd * C₀ * ((2 : ℝ) ^ k * (max ((2 : ℝ) ^ (k + jj - 1)) 1) ^ (-(N : ℝ))) := by
          linarith [hsub]
      _ = (C₁ + Cd * C₀) * (2 : ℝ) ^ k
            * (max ((2 : ℝ) ^ (k + jj - 1)) 1) ^ (-(N : ℝ)) := by ring
  -- **assembly**
  have hInt : Integrable (fun x : ℝ =>
      ‖deriv ((lam k - mS (bmp jj) (lam k) : SchwartzMap ℝ ℂ) : ℝ → ℂ) x‖) volume :=
    (SchwartzMap.derivCLM ℂ ℂ (lam k - mS (bmp jj) (lam k))).integrable.norm
  have hfinal : ∫⁻ x, ENNReal.ofReal
        (‖deriv ((lam k - mS (bmp jj) (lam k) : SchwartzMap ℝ ℂ) : ℝ → ℂ) x‖)
      ≤ ENNReal.ofReal ((C₁ + Cd * C₀) * (2 : ℝ) ^ k
          * (max ((2 : ℝ) ^ (k + jj - 1)) 1) ^ (-(N : ℝ))) := by
    have hnn1 : 0 ≤ C₁ * (2 : ℝ) ^ k * (max ((2 : ℝ) ^ (k + jj - 1)) 1) ^ (-(N : ℝ)) := by
      have h1 : (1 : ℝ) ≤ max ((2 : ℝ) ^ (k + jj - 1)) 1 := le_max_right _ _
      positivity
    have hnn2 : 0 ≤ Cd * (2 : ℝ) ^ (-jj) := by positivity
    have hnn3 : 0 ≤ C₀ * (max ((2 : ℝ) ^ (k + jj - 1)) 1) ^ (-(N : ℝ)) := by
      have h1 : (1 : ℝ) ≤ max ((2 : ℝ) ^ (k + jj - 1)) 1 := le_max_right _ _
      positivity
    calc ∫⁻ x, ENNReal.ofReal
          (‖deriv ((lam k - mS (bmp jj) (lam k) : SchwartzMap ℝ ℂ) : ℝ → ℂ) x‖)
        ≤ ENNReal.ofReal (C₁ * (2 : ℝ) ^ k * (max ((2 : ℝ) ^ (k + jj - 1)) 1) ^ (-(N : ℝ)))
          + ENNReal.ofReal (Cd * (2 : ℝ) ^ (-jj)) *
              ENNReal.ofReal (C₀ * (max ((2 : ℝ) ^ (k + jj - 1)) 1) ^ (-(N : ℝ))) := hlin
      _ = ENNReal.ofReal (C₁ * (2 : ℝ) ^ k * (max ((2 : ℝ) ^ (k + jj - 1)) 1) ^ (-(N : ℝ))
            + Cd * (2 : ℝ) ^ (-jj) * (C₀ * (max ((2 : ℝ) ^ (k + jj - 1)) 1) ^ (-(N : ℝ)))) := by
            rw [← ENNReal.ofReal_mul hnn2, ← ENNReal.ofReal_add hnn1 (mul_nonneg hnn2 hnn3)]
      _ ≤ ENNReal.ofReal ((C₁ + Cd * C₀) * (2 : ℝ) ^ k
            * (max ((2 : ℝ) ^ (k + jj - 1)) 1) ^ (-(N : ℝ))) :=
            ENNReal.ofReal_le_ofReal hArith
  calc ∫ x : ℝ, ‖deriv ((lam k - mS (bmp jj) (lam k) : SchwartzMap ℝ ℂ) : ℝ → ℂ) x‖
      = (ENNReal.ofReal
          (∫ x : ℝ, ‖deriv ((lam k - mS (bmp jj) (lam k) : SchwartzMap ℝ ℂ) : ℝ → ℂ) x‖)).toReal :=
          (ENNReal.toReal_ofReal (integral_nonneg fun x => norm_nonneg _)).symm
    _ = (∫⁻ x, ENNReal.ofReal
          (‖deriv ((lam k - mS (bmp jj) (lam k) : SchwartzMap ℝ ℂ) : ℝ → ℂ) x‖)).toReal := by
          rw [ofReal_integral_eq_lintegral_ofReal hInt (Eventually.of_forall fun x => norm_nonneg _)]
    _ ≤ (ENNReal.ofReal ((C₁ + Cd * C₀) * (2 : ℝ) ^ k
          * (max ((2 : ℝ) ^ (k + jj - 1)) 1) ^ (-(N : ℝ)))).toReal :=
          ENNReal.toReal_mono ENNReal.ofReal_ne_top hfinal
    _ = (C₁ + Cd * C₀) * (2 : ℝ) ^ k * (max ((2 : ℝ) ^ (k + jj - 1)) 1) ^ (-(N : ℝ)) := by
          have h1 : (1 : ℝ) ≤ max ((2 : ℝ) ^ (k + jj - 1)) 1 := le_max_right _ _
          rw [ENNReal.toReal_ofReal (by positivity)]

end

end Work.KMTAreas.A4
