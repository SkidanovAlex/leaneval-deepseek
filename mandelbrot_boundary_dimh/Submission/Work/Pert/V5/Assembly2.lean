import Mathlib
import Submission.Work.Pert.V5.Facts
import Submission.Work.Pert.V5.Geom
import Submission.Work.Pert.V5.horiz_dev_le_clear
import Submission.Work.Pert.V5.horiz_dev_le_split
import Submission.Work.Pert.V5.horiz_dev_le_split_right

/-!
# The assembly of `Work.Pert.Phi_dev_gate_lin_v5` (split form)

Write `D w = Φm w - w`, `x = z.re`, `t = z.im`, `y₀ = z₀.im`,
`L = 1 + log (2+M)`, `r = Kp L`, `K = 1 + Ξ + 1/Ξ + 1/rr` and `c₀ = 1/150 + 1/31`.

The comparison between a band point `z` and the pin `z₀` uses the two-legged path

  `z = x + it  --(vertical at the band abscissa `x`, `dev_vert_band`)-->  x + i y₀
               --(horizontal at height `y₀`)-->  z₀`,

so `‖D z‖ ≤ ‖D z₀‖ + (1/150 + 1/31)|t - y₀| + ‖D (x+iy₀) - D z₀‖`, and the three terms are the pin
bound `r`, the vertical leg and the horizontal deviation.

The horizontal deviation is the only hard part.  The hypothesis `hcorr` isolates it: for every band
point it produces

* a number `N` of *good* sub-corridors, each of length `≤ 16 (M+2+Ξ)` and with gate margins
  `≥ √2 Rde` (so `horiz_dev_le_clear` applies, giving a logarithmic cost per piece), together with
  the counting bound `N (1 + log (2 + 16(M+2+Ξ))) ≤ 2^12 (1 + Kp) L`;
* a remainder `W`, the cost of the *low-margin* (window/band) sub-corridors, small enough that
  `W + c₀ |z.im| ≤ |z.im| / 8`, i.e. the low-margin pieces are paid out of the slack of the `|t|/8`
  slot of the target.

With those two pieces of data the target's conclusion follows with the exact constant
`(Kp + 1 + C₂) 2^40 K`.  Compare `Work.Pert.V5.gate_lin_asm`, which is the same assembly without the
subdivision (one good corridor of length `≤ 16(M+2+Ξ)`).
-/

open Set Metric Filter
open scoped Topology

namespace Work.Pert.V5

noncomputable section

set_option maxHeartbeats 4000000

/-- Vertical transport of the deviation at a band abscissa, in the `D`-notation. -/
private theorem vb {Ξ rr M : ℝ} {α σ : ℂ} {u Φm : ℂ → ℂ}
    (hF : MandelDim.FatouStatement)
    (hΞ : 0 < Ξ) (hrr : 0 < rr) (hM : 2 ^ 10 ≤ M) (hInF1 : MandelDim.InF1 α)
    (hα : ‖α‖ ≤ 1 / (32 * (M + 2 + Ξ)))
    (hQAdm : MandelDim.QAdm (some ((Ξ : ℂ) - 1 / α)) (some (-(Ξ : ℂ))))
    (hσ : σ ≠ 0) (hnorm : 1 - σ * u 0 = Complex.exp (2 * Real.pi * Complex.I * α))
    (hu : DifferentiableOn ℂ u (Metric.ball (0 : ℂ) rr))
    (hu2 : ∀ z ∈ Metric.ball (0 : ℂ) rr, 1 / 2 ≤ ‖u z‖ ∧ ‖u z‖ ≤ 2)
    (hτQ : ∀ z ∈ Work.Pert.Qm Ξ α, Work.Pert.tauC σ α z ∈ Metric.ball (0 : ℂ) rr)
    (hNT : MandelDim.NearTranslationL1 (Work.Pert.liftF u σ α) (Work.Pert.Qm Ξ α))
    (hΦm : MandelDim.IsFatouCoordOn (Work.Pert.liftF u σ α) Φm (Work.Pert.Qm Ξ α))
    {ξ s₁ s₂ : ℝ} (hξ : -(Ξ + 2 ^ 10 + 2 * M) ≤ ξ) (hξ' : ξ ≤ -(Ξ + 2 ^ 10)) :
    ‖(Φm ((ξ : ℂ) + s₁ * Complex.I) - ((ξ : ℂ) + s₁ * Complex.I))
        - (Φm ((ξ : ℂ) + s₂ * Complex.I) - ((ξ : ℂ) + s₂ * Complex.I))‖
      ≤ (1 / 150 + 1 / 31) * |s₂ - s₁| :=
  dev_vert_band hF hΞ hrr hM hInF1 hα hQAdm hσ hnorm hu hu2 hτQ hNT hΦm ξ s₁ s₂ hξ hξ'

/-- **The pin bounds.**  `‖z₀ + M‖ ≤ r` gives `|Re z₀ + M| ≤ r` and `|Im z₀| ≤ r`. -/
theorem pin_re_im {M Kp : ℝ} {z₀ : ℂ}
    (hpinbd : ‖z₀ + (((M : ℝ)) : ℂ)‖ ≤ Kp * (1 + Real.log (2 + M))) :
    |z₀.re + M| ≤ Kp * (1 + Real.log (2 + M)) ∧
      |z₀.im| ≤ Kp * (1 + Real.log (2 + M)) := by
  have h1 : |(z₀ + (((M : ℝ)) : ℂ)).re| ≤ ‖z₀ + (((M : ℝ)) : ℂ)‖ :=
    Complex.abs_re_le_norm _
  have h2 : |(z₀ + (((M : ℝ)) : ℂ)).im| ≤ ‖z₀ + (((M : ℝ)) : ℂ)‖ :=
    Complex.abs_im_le_norm _
  simp only [Complex.add_re, Complex.add_im, Complex.ofReal_im, Complex.ofReal_re,
    add_zero] at h1 h2
  exact ⟨le_trans h1 hpinbd, le_trans h2 hpinbd⟩

/-- `0 ≤ 1/Ξ` for `Ξ > 0`. -/
theorem inv_Xi_nonneg {Ξ : ℝ} (hΞ : 0 < Ξ) : (0:ℝ) ≤ 1 / Ξ :=
  div_nonneg zero_le_one (le_of_lt hΞ)

/-- `0 ≤ 1/rr` for `rr > 0`. -/
theorem inv_rr_nonneg {rr : ℝ} (hrr : 0 < rr) : (0:ℝ) ≤ 1 / rr :=
  div_nonneg zero_le_one (le_of_lt hrr)

/-- `(1 : ℝ) ≤ 2^40 (1 + Ξ + 1/Ξ + 1/rr)`. -/
private theorem one_le_big {Ξ rr : ℝ} (hΞ : 0 < Ξ) (hrr : 0 < rr) :
    (1 : ℝ) ≤ 2 ^ 40 * (1 + Ξ + 1 / Ξ + 1 / rr) := by
  have h1 : 0 ≤ 1 / Ξ := inv_Xi_nonneg hΞ
  have h2 : 0 ≤ 1 / rr := inv_rr_nonneg hrr
  have h3 : (1 : ℝ) ≤ 2 ^ 40 := by norm_num
  have hK : (1:ℝ) ≤ 1 + Ξ + 1 / Ξ + 1 / rr := by linarith
  calc (1:ℝ) ≤ 2 ^ 40 := h3
    _ = 2 ^ 40 * 1 := by ring
    _ ≤ 2 ^ 40 * (1 + Ξ + 1 / Ξ + 1 / rr) :=
        mul_le_mul_of_nonneg_left hK (by norm_num)

/-- `(1 + 1/rr) ≤ 1 + Ξ + 1/Ξ + 1/rr` for `Ξ > 0`. -/
theorem one_add_inv_rr_le_big {Ξ rr : ℝ} (hΞ : 0 < Ξ) :
    (1 : ℝ) + 1 / rr ≤ 1 + Ξ + 1 / Ξ + 1 / rr := by
  have h1 : 0 ≤ 1 / Ξ := inv_Xi_nonneg hΞ
  linarith

/-- `2^36 (1 + 1/rr) ≤ 2^40 (1 + Ξ + 1/Ξ + 1/rr)`. -/
theorem count_le_big {Ξ rr : ℝ} (hΞ : 0 < Ξ) (hrr : 0 < rr) :
    (2 : ℝ) ^ 36 * (1 + 1 / rr) ≤ 2 ^ 40 * (1 + Ξ + 1 / Ξ + 1 / rr) := by
  have h3 : (1 : ℝ) + 1 / rr ≤ 1 + Ξ + 1 / Ξ + 1 / rr := one_add_inv_rr_le_big hΞ
  have h4 : (0:ℝ) ≤ 1 + 1 / rr := by
    have h := inv_rr_nonneg hrr
    linarith
  have h5 : (2 : ℝ) ^ 36 ≤ 2 ^ 40 := by norm_num
  calc (2 : ℝ) ^ 36 * (1 + 1 / rr) ≤ 2 ^ 40 * (1 + 1 / rr) :=
        mul_le_mul_of_nonneg_right h5 h4
    _ ≤ 2 ^ 40 * (1 + Ξ + 1 / Ξ + 1 / rr) :=
        mul_le_mul_of_nonneg_left h3 (by norm_num)

/-- `(1 + 1/150 + 1/31) ≤ 2^40 (1 + Ξ + 1/Ξ + 1/rr)`. -/
theorem pin_slot_le_big {Ξ rr : ℝ} (hΞ : 0 < Ξ) (hrr : 0 < rr) :
    (1 : ℝ) + (1 / 150 + 1 / 31) ≤ 2 ^ 40 * (1 + Ξ + 1 / Ξ + 1 / rr) := by
  have h1 : 0 ≤ 1 / Ξ := inv_Xi_nonneg hΞ
  have h2 : 0 ≤ 1 / rr := inv_rr_nonneg hrr
  have h3 : (1 : ℝ) + (1/150 + 1/31) ≤ 2 := by norm_num
  have hK : (2:ℝ) ≤ 2 ^ 40 * (1 + Ξ + 1 / Ξ + 1 / rr) := by
    have h4 : (1:ℝ) ≤ 1 + Ξ + 1 / Ξ + 1 / rr := by linarith
    calc (2:ℝ) = 2 * 1 := by ring
      _ ≤ 2 * (1 + Ξ + 1 / Ξ + 1 / rr) := mul_le_mul_of_nonneg_left h4 (by norm_num)
      _ ≤ 2 ^ 40 * (1 + Ξ + 1 / Ξ + 1 / rr) := by
          have h5 : (2:ℝ) ≤ 2 ^ 40 := by norm_num
          exact mul_le_mul_of_nonneg_right h5 (by linarith)
  linarith

/-- `1 + Ξ ≤ 1 + Ξ + 1/Ξ + 1/rr` for `Ξ > 0`, `rr > 0`. -/
theorem one_add_Xi_le_big {Ξ rr : ℝ} (hΞ : 0 < Ξ) (hrr : 0 < rr) :
    (1 : ℝ) + Ξ ≤ 1 + Ξ + 1 / Ξ + 1 / rr := by
  have h1 : 0 ≤ 1 / Ξ := inv_Xi_nonneg hΞ
  have h2 : 0 ≤ 1 / rr := inv_rr_nonneg hrr
  linarith

/-- `(1/150 + 1/31) ≤ 1/8`. -/
private theorem c0_le_eighth : (1 / 150 + 1 / 31 : ℝ) ≤ 1 / 8 := by norm_num

/-- **The assembly.**  Under the horizontal-corridor data `hcorr` the target's conclusion holds. -/
theorem gate_lin_asm_gen {Ξ rr M Kp Rde C₂ : ℝ} {α σ : ℂ} {u Φm : ℂ → ℂ} {z₀ : ℂ}
    (hF : MandelDim.FatouStatement)
    (hΞ : 0 < Ξ) (hrr : 0 < rr) (hM : 2 ^ 10 ≤ M) (hKp : 0 ≤ Kp)
    (hRde : 0 < Rde) (hC₂ : 0 < C₂)
    (hInF1 : MandelDim.InF1 α) (hα : ‖α‖ ≤ 1 / (32 * (M + 2 + Ξ)))
    (hQAdm : MandelDim.QAdm (some ((Ξ : ℂ) - 1 / α)) (some (-(Ξ : ℂ))))
    (hσ : σ ≠ 0) (hnorm : 1 - σ * u 0 = Complex.exp (2 * Real.pi * Complex.I * α))
    (hu : DifferentiableOn ℂ u (Metric.ball (0 : ℂ) rr))
    (hu2 : ∀ z ∈ Metric.ball (0 : ℂ) rr, 1 / 2 ≤ ‖u z‖ ∧ ‖u z‖ ≤ 2)
    (hτQ : ∀ z ∈ Work.Pert.Qm Ξ α, Work.Pert.tauC σ α z ∈ Metric.ball (0 : ℂ) rr)
    (hNT : MandelDim.NearTranslationL1 (Work.Pert.liftF u σ α) (Work.Pert.Qm Ξ α))
    (hΦm : MandelDim.IsFatouCoordOn (Work.Pert.liftF u σ α) Φm (Work.Pert.Qm Ξ α))
    (hz₀ : z₀ ∈ Work.Pert.Qm Ξ α)
    (hpin : Φm z₀ = (((-M : ℝ)) : ℂ))
    (hpinbd : ‖z₀ + (((M : ℝ)) : ℂ)‖ ≤ Kp * (1 + Real.log (2 + M)))
    (hcorr : ∀ z ∈ Work.Pert.Qm Ξ α, -(Ξ + 2 ^ 10 + 2 * M) ≤ z.re → z.re ≤ -(Ξ + 2 ^ 10) →
      4 * Rde ≤ |z.im| → ∃ (N : ℕ) (W : ℝ),
        W + (1 / 150 + 1 / 31) * |z.im|
          ≤ |z.im| / 8 + Kp * 2 ^ 36 * (1 + Ξ + 1 / Ξ + 1 / rr) * (1 + Real.log (2 + M)) ∧
        (N : ℝ) * (C₂ * 2 ^ 6 * (1 + Ξ) * (1 + Real.log (2 + M))
              + 2 ^ 24 * (1 + 1 / rr) * (1 + Real.log (2 + 16 * (M + 2 + Ξ))))
          ≤ C₂ * 2 ^ 40 * (1 + Ξ + 1 / Ξ + 1 / rr) * (1 + Real.log (2 + M))
            + 2 ^ 40 * (1 + Ξ + 1 / Ξ + 1 / rr) * (1 + Real.log (2 + M))
            + Kp * 2 ^ 38 * (1 + Ξ + 1 / Ξ + 1 / rr) * (1 + Real.log (2 + M)) ∧
        ‖(Φm ((z.re : ℂ) + (z₀.im : ℂ) * Complex.I) - ((z.re : ℂ) + (z₀.im : ℂ) * Complex.I))
            - (Φm z₀ - z₀)‖
          ≤ W + (N : ℝ) * (C₂ * 2 ^ 6 * (1 + Ξ) * (1 + Real.log (2 + M))
              + 2 ^ 24 * (1 + 1 / rr) * (1 + Real.log (2 + 16 * (M + 2 + Ξ))))) :
    ∃ C : ℝ, 0 < C ∧ C ≤ (Kp + 1 + C₂) * 2 ^ 40 * (1 + Ξ + 1 / Ξ + 1 / rr) ∧
      ∀ z ∈ Work.Pert.Qm Ξ α, -(Ξ + 2 ^ 10 + 2 * M) ≤ z.re → z.re ≤ -(Ξ + 2 ^ 10) →
        4 * Rde ≤ |z.im| →
          ‖Φm z - z‖ ≤ C * (1 + Real.log (2 + M)) + |z.im| / 8 := by
  refine ⟨(Kp + 1 + C₂) * 2 ^ 40 * (1 + Ξ + 1 / Ξ + 1 / rr), ?_, le_rfl, ?_⟩
  · have hK : (0:ℝ) < 1 + Ξ + 1 / Ξ + 1 / rr := by
      have h1 : 0 ≤ 1 / Ξ := inv_Xi_nonneg hΞ
      have h2 : 0 ≤ 1 / rr := inv_rr_nonneg hrr
      linarith
    have hKp1 : (0:ℝ) < Kp + 1 + C₂ := by linarith
    have h2 : (0:ℝ) < 2 ^ 40 := by norm_num
    exact mul_pos (mul_pos hKp1 h2) hK
  · intro z hz hzlo hzhi ht
    -- abbreviations
    set L : ℝ := 1 + Real.log (2 + M) with hLdef
    set Lg : ℝ := 1 + Real.log (2 + 16 * (M + 2 + Ξ)) with hLgdef
    set K : ℝ := 1 + Ξ + 1 / Ξ + 1 / rr with hKdef
    have hc₀nn : (0:ℝ) ≤ 1 / 150 + 1 / 31 := by norm_num
    have hLpos : 0 < L := by
      rw [hLdef]
      have h2 : (1:ℝ) < 2 + M := by linarith
      have := Real.log_pos h2
      linarith
    have hLnn : (0:ℝ) ≤ L := le_of_lt hLpos
    have hLgnn : 0 ≤ Lg := by
      rw [hLgdef]
      have : (0:ℝ) ≤ Real.log (2 + 16 * (M + 2 + Ξ)) := Real.log_nonneg (by linarith)
      linarith
    have hKpos : (0:ℝ) < K := by
      rw [hKdef]
      have h1 : 0 ≤ 1 / Ξ := inv_Xi_nonneg hΞ
      have h2 : 0 ≤ 1 / rr := inv_rr_nonneg hrr
      linarith
    have hKX : (1:ℝ) + Ξ ≤ K := by rw [hKdef]; exact one_add_Xi_le_big hΞ hrr
    -- ## the pin
    obtain ⟨hpx, hpy⟩ := pin_re_im hpinbd
    have hpyL : |z₀.im| ≤ Kp * L := by rw [hLdef]; exact hpy
    have hDz₀ : ‖Φm z₀ - z₀‖ ≤ Kp * L := by rw [hLdef]; exact pin_dev_le hpin hpinbd
    -- ## the corridor data
    obtain ⟨N, W, hW, hNcount, hcorrbd⟩ := hcorr z hz hzlo hzhi ht
    have hKL_eq : Kp * 2 ^ 36 * K * L
        = Kp * 2 ^ 36 * (1 + Ξ + 1 / Ξ + 1 / rr) * (1 + Real.log (2 + M)) := by
      rw [hKdef, hLdef]
    have hKleq : Kp * 2 ^ 38 * K * L
        = Kp * 2 ^ 38 * (1 + Ξ + 1 / Ξ + 1 / rr) * (1 + Real.log (2 + M)) := by
      rw [hKdef, hLdef]
    have hK1' : (1:ℝ) ≤ K := by
      rw [hKdef]; linarith [inv_Xi_nonneg hΞ, inv_rr_nonneg hrr]
    have hNterm : (N:ℝ) * (C₂ * 2 ^ 6 * (1 + Ξ) * L + 2 ^ 24 * (1 + 1 / rr) * Lg)
        ≤ C₂ * 2 ^ 40 * K * L + 2 ^ 40 * K * L + Kp * 2 ^ 38 * K * L := by
      have h1 : (N:ℝ) * (C₂ * 2 ^ 6 * (1 + Ξ) * (1 + Real.log (2 + M))
            + 2 ^ 24 * (1 + 1 / rr) * (1 + Real.log (2 + 16 * (M + 2 + Ξ))))
          ≤ C₂ * 2 ^ 40 * (1 + Ξ + 1 / Ξ + 1 / rr) * (1 + Real.log (2 + M))
            + 2 ^ 40 * (1 + Ξ + 1 / Ξ + 1 / rr) * (1 + Real.log (2 + M))
            + Kp * 2 ^ 38 * (1 + Ξ + 1 / Ξ + 1 / rr) * (1 + Real.log (2 + M)) := hNcount
      have h2 : (N:ℝ) * (C₂ * 2 ^ 6 * (1 + Ξ) * L + 2 ^ 24 * (1 + 1 / rr) * Lg)
          = (N:ℝ) * (C₂ * 2 ^ 6 * (1 + Ξ) * (1 + Real.log (2 + M))
              + 2 ^ 24 * (1 + 1 / rr) * (1 + Real.log (2 + 16 * (M + 2 + Ξ)))) := by
        rw [hLdef, hLgdef]
      have h3 : C₂ * 2 ^ 40 * (1 + Ξ + 1 / Ξ + 1 / rr) * (1 + Real.log (2 + M))
            + 2 ^ 40 * (1 + Ξ + 1 / Ξ + 1 / rr) * (1 + Real.log (2 + M))
            + Kp * 2 ^ 38 * (1 + Ξ + 1 / Ξ + 1 / rr) * (1 + Real.log (2 + M))
          = C₂ * 2 ^ 40 * K * L + 2 ^ 40 * K * L + Kp * 2 ^ 38 * K * L := by
        rw [hKdef, hLdef]
      linarith [h1, h2.le, h2.ge, h3.le, h3.ge]
    have hW' : W + (1 / 150 + 1 / 31) * |z.im| ≤ |z.im| / 8 + Kp * 2 ^ 36 * K * L := by
      rw [hKL_eq]
      exact hW
    -- ## the vertical leg at the band abscissa
    have hvert : ‖(Φm ((z.re : ℂ) + (z.im : ℂ) * Complex.I)
          - ((z.re : ℂ) + (z.im : ℂ) * Complex.I))
        - (Φm ((z.re : ℂ) + (z₀.im : ℂ) * Complex.I)
          - ((z.re : ℂ) + (z₀.im : ℂ) * Complex.I))‖
        ≤ (1 / 150 + 1 / 31) * |z.im - z₀.im| := by
      rw [abs_sub_comm]
      exact dev_vert_band hF hΞ hrr hM hInF1 hα hQAdm hσ hnorm hu hu2 hτQ hNT hΦm
        z.re z.im z₀.im hzlo hzhi
    have hvert' : ‖(Φm ((z.re : ℂ) + (z.im : ℂ) * Complex.I)
          - ((z.re : ℂ) + (z.im : ℂ) * Complex.I))
        - (Φm ((z.re : ℂ) + (z₀.im : ℂ) * Complex.I)
          - ((z.re : ℂ) + (z₀.im : ℂ) * Complex.I))‖
        ≤ (1 / 150 + 1 / 31) * |z.im| + (1 / 150 + 1 / 31) * (Kp * L) := by
      have h1 : |z.im - z₀.im| ≤ |z.im| + |z₀.im| := by
        have h1a : z.im - z₀.im ≤ |z.im| + |z₀.im| := by
          linarith [le_abs_self z.im, neg_le_abs z₀.im]
        have h1b : z₀.im - z.im ≤ |z.im| + |z₀.im| := by
          linarith [le_abs_self z₀.im, neg_le_abs z.im]
        exact abs_sub_le_iff.mpr ⟨h1a, h1b⟩
      calc ‖_ - _‖ ≤ (1 / 150 + 1 / 31) * |z.im - z₀.im| := hvert
        _ ≤ (1 / 150 + 1 / 31) * (|z.im| + |z₀.im|) := mul_le_mul_of_nonneg_left h1 hc₀nn
        _ = (1 / 150 + 1 / 31) * |z.im| + (1 / 150 + 1 / 31) * |z₀.im| := by ring
        _ ≤ (1 / 150 + 1 / 31) * |z.im| + (1 / 150 + 1 / 31) * (Kp * L) := by
            have := mul_le_mul_of_nonneg_left hpyL hc₀nn
            linarith
    have hbd : ‖(Φm ((z.re : ℂ) + (z₀.im : ℂ) * Complex.I)
          - ((z.re : ℂ) + (z₀.im : ℂ) * Complex.I)) - (Φm z₀ - z₀)‖
        ≤ W + (N:ℝ) * (C₂ * 2 ^ 6 * (1 + Ξ) * L + 2 ^ 24 * (1 + 1 / rr) * Lg) := by
      rw [hLdef, hLgdef]
      exact hcorrbd
    -- ## the three legs
    have hDz : ‖Φm z - z‖ ≤ Kp * L
        + (W + (N:ℝ) * (C₂ * 2 ^ 6 * (1 + Ξ) * L + 2 ^ 24 * (1 + 1 / rr) * Lg))
        + ((1 / 150 + 1 / 31) * |z.im| + (1 / 150 + 1 / 31) * (Kp * L)) := by
      have hz' : ((z.re : ℂ) + (z.im : ℂ) * Complex.I) = z := Complex.re_add_im z
      have hsplit : Φm z - z = (Φm z₀ - z₀)
          + ((Φm ((z.re : ℂ) + (z₀.im : ℂ) * Complex.I)
                - ((z.re : ℂ) + (z₀.im : ℂ) * Complex.I)) - (Φm z₀ - z₀))
          + ((Φm z - z) - (Φm ((z.re : ℂ) + (z₀.im : ℂ) * Complex.I)
                - ((z.re : ℂ) + (z₀.im : ℂ) * Complex.I))) := by rw [← hz']; ring
      have h7 : ‖(Φm z - z) - (Φm ((z.re : ℂ) + (z₀.im : ℂ) * Complex.I)
            - ((z.re : ℂ) + (z₀.im : ℂ) * Complex.I))‖
          ≤ (1 / 150 + 1 / 31) * |z.im| + (1 / 150 + 1 / 31) * (Kp * L) := by
        simpa only [Complex.re_add_im] using hvert'
      rw [hsplit]
      calc ‖(Φm z₀ - z₀)
            + ((Φm ((z.re : ℂ) + (z₀.im : ℂ) * Complex.I)
                - ((z.re : ℂ) + (z₀.im : ℂ) * Complex.I)) - (Φm z₀ - z₀))
            + ((Φm z - z) - (Φm ((z.re : ℂ) + (z₀.im : ℂ) * Complex.I)
                - ((z.re : ℂ) + (z₀.im : ℂ) * Complex.I)))‖
          ≤ ‖(Φm z₀ - z₀)
              + ((Φm ((z.re : ℂ) + (z₀.im : ℂ) * Complex.I)
                  - ((z.re : ℂ) + (z₀.im : ℂ) * Complex.I)) - (Φm z₀ - z₀))‖
            + ‖(Φm z - z) - (Φm ((z.re : ℂ) + (z₀.im : ℂ) * Complex.I)
                - ((z.re : ℂ) + (z₀.im : ℂ) * Complex.I))‖ := norm_add_le _ _
        _ ≤ (‖Φm z₀ - z₀‖
              + ‖(Φm ((z.re : ℂ) + (z₀.im : ℂ) * Complex.I)
                  - ((z.re : ℂ) + (z₀.im : ℂ) * Complex.I)) - (Φm z₀ - z₀)‖)
            + ((1 / 150 + 1 / 31) * |z.im| + (1 / 150 + 1 / 31) * (Kp * L)) := by
            have h6 := norm_add_le (Φm z₀ - z₀)
              ((Φm ((z.re : ℂ) + (z₀.im : ℂ) * Complex.I)
                  - ((z.re : ℂ) + (z₀.im : ℂ) * Complex.I)) - (Φm z₀ - z₀))
            linarith [h6, h7]
        _ ≤ Kp * L
              + (W + (N:ℝ) * (C₂ * 2 ^ 6 * (1 + Ξ) * L + 2 ^ 24 * (1 + 1 / rr) * Lg))
              + ((1 / 150 + 1 / 31) * |z.im| + (1 / 150 + 1 / 31) * (Kp * L)) := by
            linarith [hDz₀, hbd]
    -- ## the counting budget
    have hKL1 : 2 ^ 36 * (1 + 1 / rr) * L ≤ 2 ^ 40 * K * L := by
      have hcb : (2:ℝ) ^ 36 * (1 + 1 / rr) ≤ 2 ^ 40 * K := by
        rw [hKdef]; exact count_le_big hΞ hrr
      exact mul_le_mul_of_nonneg_right hcb hLnn
    have hpinv : Kp * L + (1 / 150 + 1 / 31) * (Kp * L) ≤ Kp * (2 ^ 36 * K * L) := by
      have h1 : Kp * L + (1 / 150 + 1 / 31) * (Kp * L)
          = (1 + (1 / 150 + 1 / 31)) * (Kp * L) := by ring
      have hKLnn : (0:ℝ) ≤ Kp * L := mul_nonneg hKp hLnn
      have h2 : (1 + (1 / 150 + 1 / 31) : ℝ) ≤ 2 := by norm_num
      have h3 : (1 + (1 / 150 + 1 / 31)) * (Kp * L) ≤ 2 * (Kp * L) := by
        nlinarith [h2, hKLnn]
      have h7 : (2:ℝ) * L ≤ 2 ^ 36 * K * L := by
        have h8 : (2:ℝ) ≤ 2 ^ 36 * K := by
          nlinarith [hK1', (by norm_num : (2:ℝ) ≤ 2 ^ 36)]
        have h10 : 2 * L ≤ (2 ^ 36 * K) * L := mul_le_mul_of_nonneg_right h8 hLnn
        linarith [h10]
      have h5 : 2 * (Kp * L) ≤ Kp * (2 ^ 36 * K * L) := by nlinarith [hKp, h7]
      linarith [h1.le, h1.ge, h3, h5]
    -- ## assemble
    have hgoal : ‖Φm z - z‖
        ≤ C₂ * 2 ^ 40 * K * L + 2 ^ 40 * K * L + Kp * 2 ^ 40 * K * L + |z.im| / 8 := by
      have hWx : W + (1 / 150 + 1 / 31) * |z.im| ≤ |z.im| / 8 + Kp * 2 ^ 36 * K * L := hW'
      have hs : (N:ℝ) * (C₂ * 2 ^ 6 * (1 + Ξ) * L + 2 ^ 24 * (1 + 1 / rr) * Lg)
          = (N:ℝ) * (C₂ * 2 ^ 6 * (1 + Ξ) * L) + (N:ℝ) * (2 ^ 24 * (1 + 1 / rr) * Lg) := by
        ring
      have hKbig4 : Kp * 2 ^ 38 * K * L + Kp * 2 ^ 36 * K * L + Kp * 2 ^ 36 * K * L
          ≤ Kp * 2 ^ 40 * K * L := by
        have h2 : (2:ℝ) ^ 38 + 2 ^ 36 + 2 ^ 36 ≤ 2 ^ 40 := by norm_num
        have h3 : (0:ℝ) ≤ Kp * (K * L) := by positivity
        nlinarith [h2, h3]
      linarith [hDz, hNterm, hpinv, hWx, hKbig4, hs.le, hs.ge]
    calc ‖Φm z - z‖
        ≤ C₂ * 2 ^ 40 * K * L + 2 ^ 40 * K * L + Kp * 2 ^ 40 * K * L + |z.im| / 8 := hgoal
      _ = (Kp + 1 + C₂) * 2 ^ 40 * K * L + |z.im| / 8 := by ring
      _ = (Kp + 1 + C₂) * 2 ^ 40 * (1 + Ξ + 1 / Ξ + 1 / rr) * (1 + Real.log (2 + M))
            + |z.im| / 8 := by rw [hKdef, hLdef]

end

end Work.Pert.V5
