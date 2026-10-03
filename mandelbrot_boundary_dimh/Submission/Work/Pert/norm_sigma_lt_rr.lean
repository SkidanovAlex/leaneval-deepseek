import Mathlib
import Submission.Work.Pert.Setup
import Submission.Work.Pert.Basic

/-!
# PERT · `‖σ‖ < rr`

`Work.Pert.norm_sigma_lt_rr`: the size of the multiplier parameter `σ` is strictly smaller
than the radius `rr` of the disk on which the perturbation data is good.

The gate `Qm Ξ α = Qreg (Ξ - 1/α) (-Ξ)` (the lower gate of §4.2) is unbounded and contains,
for every sufficiently large `T > 0`, the point

`z_T = -T · i / α`   (i.e. `α z_T = -i T`,   `-2πi α z_T = -2π T`).

Indeed writing `c = 1/α = u + i v` (`u = Re c`, `v = Im c`) we have `Re c > |Im c|` because
`α ∈ 𝓕₁` (`|Im α| < Re α`), so `u ± v > 0`, and the two `Qreg` conditions at `z_T = T v - i T u`
read

* `Ξ < T (u - v)`   (the vertex `-Ξ` condition), and
* `Ξ < T (u + v) + (u - v)`   (the vertex `Ξ - c` condition),

both satisfiable for large `T`.

At such a point the denominator of `τ_f` is the positive real number `1 - e^{-2πT} ∈ (0,1)`, so

`‖σ‖ = ‖τ_f z_T‖ · (1 - e^{-2πT}) < rr · (1 - e^{-2πT}) < rr`,

using the hypothesis that `τ_f` maps the gate into `ball 0 rr`.
-/

namespace Work.Pert

open Complex

theorem norm_sigma_lt_rr {Ξ rr : ℝ} {α σ : ℂ} {u : ℂ → ℂ}
    (hΞ : 0 < Ξ) (hrr : 0 < rr) (hInF1 : MandelDim.InF1 α) (hα64 : ‖α‖ ≤ 1 / 64)
    (hQAdm : MandelDim.QAdm (some ((Ξ : ℂ) - 1 / α)) (some (-(Ξ : ℂ))))
    (hσ : σ ≠ 0) (hnorm : 1 - σ * u 0 = Complex.exp (2 * Real.pi * Complex.I * α))
    (hu2 : ∀ z ∈ Metric.ball (0 : ℂ) rr, 1 / 2 ≤ ‖u z‖ ∧ ‖u z‖ ≤ 2)
    (hτQ : ∀ z ∈ Work.Pert.Qm Ξ α, Work.Pert.tauC σ α z ∈ Metric.ball (0 : ℂ) rr) :
    ‖σ‖ < rr := by
  -- `α ∈ 𝓕₁`: `|Im α| < Re α`.
  have hF1 : |α.im| < α.re := hInF1
  have hre : 0 < α.re := lt_of_le_of_lt (abs_nonneg α.im) hF1
  have hαne : α ≠ 0 := by intro h; rw [h] at hre; simp at hre
  have hn2pos : 0 < ‖α‖ ^ 2 := by positivity
  -- `c = 1/α = u + iv`; express its real and imaginary parts.
  set c : ℂ := 1 / α with hcdef
  have hc_re : c.re = α.re / ‖α‖ ^ 2 := by
    rw [hcdef, one_div, Complex.inv_re, Complex.normSq_eq_norm_sq]
  have hc_im : c.im = -α.im / ‖α‖ ^ 2 := by
    rw [hcdef, one_div, Complex.inv_im, Complex.normSq_eq_norm_sq]
  have hcpos : 0 < c.re := by rw [hc_re]; positivity
  -- `c.re ± c.im > 0` (equivalently `c.re > |c.im|`), the content of `InF1`.
  have hp : 0 < c.re + c.im := by
    rw [hc_re, hc_im]
    rw [show α.re / ‖α‖ ^ 2 + -α.im / ‖α‖ ^ 2 = (α.re - α.im) / ‖α‖ ^ 2 by ring]
    exact div_pos (by have := (abs_lt.mp hF1).2; linarith) hn2pos
  have hm : 0 < c.re - c.im := by
    rw [hc_re, hc_im]
    rw [show α.re / ‖α‖ ^ 2 - -α.im / ‖α‖ ^ 2 = (α.re + α.im) / ‖α‖ ^ 2 by ring]
    exact div_pos (by have := (abs_lt.mp hF1).1; linarith) hn2pos
  have habs : |c.im| < c.re := by
    rw [abs_lt]; exact ⟨by linarith, by linarith⟩
  -- Choose `T = M` large: `Ξ < M (c.re - c.im)` and `Ξ < M (c.re + c.im) + (c.re - c.im)`.
  obtain ⟨M, hMpos, hMge1, hM1, hM2⟩ : ∃ M : ℝ, 0 < M ∧ 1 ≤ M ∧
      Ξ < M * (c.re - c.im) ∧ Ξ < M * (c.re + c.im) + (c.re - c.im) := by
    set K : ℝ := max Ξ (Ξ - (c.re - c.im)) + 1 with hKdef
    have hKΞ : Ξ < K := by rw [hKdef]; linarith [le_max_left Ξ (Ξ - (c.re - c.im))]
    have hKm : Ξ - (c.re - c.im) < K := by
      rw [hKdef]; linarith [le_max_right Ξ (Ξ - (c.re - c.im))]
    have hKpos : 0 < K := lt_trans hΞ hKΞ
    have hminpos : 0 < min (c.re - c.im) (c.re + c.im) := lt_min hm hp
    refine ⟨K / min (c.re - c.im) (c.re + c.im) + 1, ?_, ?_, ?_, ?_⟩
    · exact add_pos_of_nonneg_of_pos (div_nonneg hKpos.le hminpos.le) one_pos
    · exact le_add_of_nonneg_left (div_nonneg hKpos.le hminpos.le)
    · have hne : min (c.re - c.im) (c.re + c.im) ≠ 0 := ne_of_gt hminpos
      have hh : (K / min (c.re - c.im) (c.re + c.im) + 1) * min (c.re - c.im) (c.re + c.im)
          = K + min (c.re - c.im) (c.re + c.im) := by
        rw [add_mul, one_mul, div_mul_cancel₀ K hne]
      have hle : (K / min (c.re - c.im) (c.re + c.im) + 1) * min (c.re - c.im) (c.re + c.im)
          ≤ (K / min (c.re - c.im) (c.re + c.im) + 1) * (c.re - c.im) :=
        mul_le_mul_of_nonneg_left (min_le_left _ _)
          (add_nonneg (div_nonneg hKpos.le hminpos.le) zero_le_one)
      rw [hh] at hle; linarith
    · have hne : min (c.re - c.im) (c.re + c.im) ≠ 0 := ne_of_gt hminpos
      have hh : (K / min (c.re - c.im) (c.re + c.im) + 1) * min (c.re - c.im) (c.re + c.im)
          = K + min (c.re - c.im) (c.re + c.im) := by
        rw [add_mul, one_mul, div_mul_cancel₀ K hne]
      have hle : (K / min (c.re - c.im) (c.re + c.im) + 1) * min (c.re - c.im) (c.re + c.im)
          ≤ (K / min (c.re - c.im) (c.re + c.im) + 1) * (c.re + c.im) :=
        mul_le_mul_of_nonneg_left (min_le_right _ _)
          (add_nonneg (div_nonneg hKpos.le hminpos.le) zero_le_one)
      rw [hh] at hle; linarith
  -- The witness `z = -i M c` (so that `α z = -i M` and `-2πi α z = -2π M`).
  set z : ℂ := -Complex.I * (M : ℂ) * c with hzdef
  have hzre : z.re = M * c.im := by
    rw [hzdef, show -Complex.I * (M : ℂ) * c = (-Complex.I) * ((M : ℂ) * c) by ring]
    simp [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
  have hzim : z.im = -(M * c.re) := by
    rw [hzdef, show -Complex.I * (M : ℂ) * c = (-Complex.I) * ((M : ℂ) * c) by ring]
    simp [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
  -- `z` lies in the lower gate `Qm Ξ α`.
  have hzQ : z ∈ Work.Pert.Qm Ξ α := by
    unfold Work.Pert.Qm MandelDim.Qreg
    rw [← hcdef]
    constructor
    · intro b hb
      simp only [Option.mem_some_iff] at hb
      subst hb
      have h1re : (z - ((Ξ : ℂ) - c)).re = M * c.im - Ξ + c.re := by
        rw [Complex.sub_re, Complex.sub_re, Complex.ofReal_re, hzre]; ring
      have h1im : (z - ((Ξ : ℂ) - c)).im = -(M * c.re) + c.im := by
        rw [Complex.sub_im, Complex.sub_im, Complex.ofReal_im, hzim]; ring
      rw [h1re, h1im]
      have hle : -(M * c.re) + c.im ≤ 0 := by
        have h2 : c.re ≤ M * c.re := le_mul_of_one_le_left hcpos.le hMge1
        have h3 : c.im < c.re := lt_of_le_of_lt (le_abs_self c.im) habs
        linarith
      rw [abs_of_nonpos hle]
      linarith [hM2]
    · intro b hb
      simp only [Option.mem_some_iff] at hb
      subst hb
      have h2re : (z - -(Ξ : ℂ)).re = M * c.im + Ξ := by
        rw [Complex.sub_re, Complex.neg_re, Complex.ofReal_re, hzre]; ring
      have h2im : (z - -(Ξ : ℂ)).im = -(M * c.re) := by
        rw [Complex.sub_im, Complex.neg_im, Complex.ofReal_im, hzim]; ring
      rw [h2re, h2im]
      have hA : |-(M * c.re)| = M * c.re := by
        rw [abs_neg, abs_of_pos]; positivity
      rw [hA]
      linarith [hM1]
  -- The exponential at `z` is the positive real number `e^{-2πM}`.
  have hαz : α * z = -(Complex.I * (M : ℂ)) := by
    rw [hzdef]
    have hαc : α * c = 1 := by rw [hcdef, one_div, mul_inv_cancel₀ hαne]
    calc α * (-Complex.I * (M : ℂ) * c) = (-Complex.I * (M : ℂ)) * (α * c) := by ring
      _ = -(Complex.I * (M : ℂ)) := by rw [hαc, mul_one]; ring
  have harg : -(2 * ↑Real.pi * Complex.I * α * z) = ((-(2 * Real.pi * M) : ℝ) : ℂ) := by
    rw [show (2 : ℂ) * ↑Real.pi * Complex.I * α * z
          = (2 * ↑Real.pi * Complex.I) * (α * z) by ring]
    rw [hαz]
    rw [show -((2 : ℂ) * ↑Real.pi * Complex.I * -(Complex.I * ↑M))
          = (2 : ℂ) * ↑Real.pi * Complex.I * (Complex.I * ↑M) by ring]
    rw [show (2 : ℂ) * ↑Real.pi * Complex.I * (Complex.I * ↑M)
          = (2 * ↑Real.pi) * ((Complex.I * Complex.I) * ↑M) by ring]
    rw [Complex.I_mul_I]
    push_cast
    ring
  have hw : Complex.exp (-(2 * Real.pi * Complex.I * α * z))
      = ((Real.exp (-(2 * Real.pi * M))) : ℂ) := by
    rw [harg, ← Complex.ofReal_exp]
  have hden : (1 : ℂ) - Complex.exp (-(2 * Real.pi * Complex.I * α * z))
      = ((1 - Real.exp (-(2 * Real.pi * M))) : ℂ) := by
    rw [hw, ← Complex.ofReal_one, ← Complex.ofReal_sub]
  have hdenpos : 0 < 1 - Real.exp (-(2 * Real.pi * M)) := by
    have h1 : Real.exp (-(2 * Real.pi * M)) < 1 :=
      Real.exp_lt_one_iff.mpr (by nlinarith [Real.pi_pos, hMpos])
    linarith
  have htau : Work.Pert.tauC σ α z = σ / ((1 - Real.exp (-(2 * Real.pi * M))) : ℂ) := by
    rw [Work.Pert.tauC, hden]
  have hmem := hτQ z hzQ
  have hnorm_tau : ‖Work.Pert.tauC σ α z‖ = ‖σ‖ / (1 - Real.exp (-(2 * Real.pi * M))) := by
    rw [htau, norm_div]
    rw [show ‖(1 : ℂ) - ↑(Real.exp (-(2 * Real.pi * M)))‖ = 1 - Real.exp (-(2 * Real.pi * M)) from by
          rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
            abs_of_pos hdenpos]]
  simp only [Metric.mem_ball, dist_eq_norm, sub_zero] at hmem
  rw [hnorm_tau] at hmem
  have hmain : ‖σ‖ < rr * (1 - Real.exp (-(2 * Real.pi * M))) := (div_lt_iff₀ hdenpos).mp hmem
  calc ‖σ‖ < rr * (1 - Real.exp (-(2 * Real.pi * M))) := hmain
    _ < rr * 1 := mul_lt_mul_of_pos_left (by linarith [Real.exp_pos (-(2 * Real.pi * M))]) hrr
    _ = rr := mul_one rr

end Work.Pert
