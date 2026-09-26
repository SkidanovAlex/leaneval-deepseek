import Mathlib
import Submission.Work.Asymptotics.funnelTailBasic
import Submission.Work.Asymptotics.KfunAuxDefs
import Submission.Work.Asymptotics.KPlus_eight_decomposition
import Submission.Work.Asymptotics.continuous_AfunFun
import Submission.Work.Asymptotics.mdiff_eta
import Submission.Work.Asymptotics.KaxisMid.exists_local_bound_coincidence
import Submission.Work.Residues.AfunPlus_neg_one
import Submission.Work.Residues.AfunMinus_neg_one
import Submission.Work.Analysis.ThreeZeros.three_zeros_bound_ball
import Submission.Work.Asymptotics.SpikeCircle.SpikeDefs
import Submission.Work.Asymptotics.SpikeCircle.DeltaFunBoundsHalf
import Submission.Work.Asymptotics.SpikeCircle.divisorLowerDisc
import Submission.Work.Asymptotics.SpikeCircle.jInvariantFun_eq_iff_disc
import Submission.Work.Asymptotics.SpikeCircle.Wlift_id
import Submission.Work.Asymptotics.SpikeCircle.Wlift_bound

set_option maxHeartbeats 8000000

/-
# The CKMRV "spike" bound on the disc `‖z - τ‖ ≤ 29/20`  (completed assembly)

The statement `funnelKernelSpike_core` is the quantitative "spike" estimate: on the funnel
`τ ∈ 𝒟`, `2 ≤ Im τ`, and for `z` in the disc of radius `29/20` about `τ` (excluding the three
points `τ, τ±1`), the CKMRV kernel `K^{(d)} = (K₊^{(d)} + K₋^{(d)})/2` differs from its two
translate-principal-parts `(1/(2π))/(z-(τ-1)) - (1/(2π))/(z-(τ+1))` by at most
`C · (scale τ)^N · (1 + ‖z‖)^M`, with `C, N, M` independent of `τ` and `z`.

The proof below is a *reduction*, resting on the following analytic inputs, all of which are
proved elsewhere in this development:

* `Work.Asymptotics.SpikeCircle.spikeCircleBound` (CKMRV Lemma 4.12): on the spike circle
  `‖ζ - τ‖ = 29/20`, `‖Kfun ℓ d τ ζ‖ ≤ C (scale τ)^N`.
* `Work.Asymptotics.SpikeCircle.Wlift_bound`: the bound
  `‖Wlift ℓ d τ (z:ℂ)‖ ≤ C (scale τ)^N e^{-2π Im τ} ‖z-τ‖‖z-(τ+1)‖‖z-(τ-1)‖`
  in the disc (from the maximum modulus principle + the three-zero principle for the
  auxiliary function `Wlift ℓ d τ w = Δ(τ)Δ(w)(AfunFun ℓ d τ w - Tleft τ w)`, whose three zeros
  `τ, τ±1` encode the residue cancellation).
* `Work.Asymptotics.SpikeCircle.Wlift_id` (the master identity):
  `Wlift ℓ d τ (ζ:ℂ) = Δ(τ)Δ(ζ)(jτ - jζ)(Kfun ℓ d τ ζ - PP τ ζ)` for `jτ ≠ jζ`.
* `Work.Asymptotics.SpikeCircle.DeltaFunBoundsHalf`: `‖Δ w‖ ≍ e^{-2π Im w}` for `Im w ≥ 1/2`.
* `Work.Asymptotics.SpikeCircle.divisorLowerDisc`: `‖jτ - jζ‖ ≳ e^{2π Im τ}‖D̃(ζ)‖` on the disc,
  where `D̃(ζ) = (ζ-τ)(ζ-(τ-1))(ζ-(τ+1))`.
* `Work.Asymptotics.SpikeCircle.jInvariantFun_eq_iff_disc`: on the disc, `jτ = jζ` forces
  `ζ ∈ {τ, τ±1}`.

The final assembly (below) cancels the triple product `‖D̃‖`, the two `Δ`-factors and the
exponentials, and bounds the surviving `e^{2π(z.im - τ.im)}` by `e^{2π·29/20}`, giving
`C = (C_w/(c_Δ² c_d))·e^{2π·29/20}`, `N = N_w`, `M = 0`.
-/

namespace Work.Asymptotics

/-- Exponential identity used in the assembly. -/
lemma exp_neg_neg_pos (a b : ℝ) :
    Real.exp (-a) * Real.exp (-b) * Real.exp a = Real.exp (-b) := by
  rw [← Real.exp_add, ← Real.exp_add, show -a + -b + a = -b from by ring]

lemma im_ge_of_disc_spike {τ ζ : UpperHalfPlane}
    (h : ‖(ζ : ℂ) - (τ : ℂ)‖ ≤ 29 / 20) : τ.im - 29 / 20 ≤ ζ.im := by
  have h1 : |(((ζ : ℂ) - (τ : ℂ)).im)| ≤ ‖(ζ : ℂ) - (τ : ℂ)‖ := Complex.abs_im_le_norm _
  have h2 : (((ζ : ℂ) - (τ : ℂ)).im) = ζ.im - τ.im := by
    rw [Complex.sub_im, UpperHalfPlane.coe_im, UpperHalfPlane.coe_im]
  rw [h2] at h1
  have := abs_le.mp (le_trans h1 h)
  linarith [this.1]

lemma im_le_of_disc_spike {τ ζ : UpperHalfPlane}
    (h : ‖(ζ : ℂ) - (τ : ℂ)‖ ≤ 29 / 20) : ζ.im ≤ τ.im + 29 / 20 := by
  have h1 : |(((ζ : ℂ) - (τ : ℂ)).im)| ≤ ‖(ζ : ℂ) - (τ : ℂ)‖ := Complex.abs_im_le_norm _
  have h2 : (((ζ : ℂ) - (τ : ℂ)).im) = ζ.im - τ.im := by
    rw [Complex.sub_im, UpperHalfPlane.coe_im, UpperHalfPlane.coe_im]
  rw [h2] at h1
  have := abs_le.mp (le_trans h1 h)
  linarith [this.2]

/-- In the disc, off the three special points, there is no coincidence `j τ = j ζ`. -/
lemma jne_of_disc_spike {τ ζ : UpperHalfPlane} (hτ : Work.Asymptotics.Funnel τ)
    (hζ : ‖(ζ : ℂ) - (τ : ℂ)‖ ≤ 29 / 20) (h1 : ζ ≠ τ) (h2 : ζ ≠ (1:ℝ) +ᵥ τ)
    (h3 : ζ ≠ (-1:ℝ) +ᵥ τ) :
    Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun ζ := by
  intro h
  rcases (SpikeCircle.jInvariantFun_eq_iff_disc hτ hζ).mp h with h' | h' | h'
  exacts [h1 h', h2 h', h3 h']

theorem funnelKernelSpike_core (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) :
    ∃ C N M : ℝ, 0 < C ∧ 0 ≤ N ∧ 0 ≤ M ∧
      ∀ (τ z : UpperHalfPlane), Work.Asymptotics.Funnel τ → ‖(z : ℂ) - (τ : ℂ)‖ ≤ 29 / 20 →
        z ≠ τ → z ≠ (1 : ℝ) +ᵥ τ → z ≠ (-1 : ℝ) +ᵥ τ →
        ‖Work.Kernels.Kfun ℓ d τ z -
          ((1 / (2 * Real.pi) : ℂ) / ((z : ℂ) - ((τ : ℂ) - 1)) +
            (-(1 / (2 * Real.pi)) : ℂ) / ((z : ℂ) - ((τ : ℂ) + 1)))‖
          ≤ C * (Work.Kernels.scale τ) ^ N * (1 + ‖(z : ℂ)‖) ^ M := by
  obtain ⟨Cw, Nw, hCw, hNw, hb⟩ := SpikeCircle.Wlift_bound ℓ d hd
  obtain ⟨cd, hcd, hdiv⟩ := SpikeCircle.divisorLowerDisc
  obtain ⟨cD, CD, hcD, hCD, hDelta⟩ := SpikeCircle.DeltaFunBoundsHalf
  refine ⟨Cw / (cD ^ 2 * cd) * Real.exp (2 * Real.pi * (29/20)), Nw, 0, ?_, hNw, le_rfl, ?_⟩
  · exact mul_pos (div_pos hCw (mul_pos (pow_pos hcD 2) hcd)) (Real.exp_pos _)
  intro τ z hτ hz hne1 hne2 hne3
  have hhalfτ : (1/2:ℝ) ≤ τ.im := by linarith [hτ.2]
  have hhalfz : (1/2:ℝ) ≤ z.im := by
    have h := im_ge_of_disc_spike (τ := τ) (ζ := z) hz
    linarith [hτ.2]
  have hzg : τ.im - 29/20 ≤ z.im := im_ge_of_disc_spike (τ := τ) (ζ := z) hz
  have hzu : z.im ≤ τ.im + 29/20 := im_le_of_disc_spike (τ := τ) (ζ := z) hz
  have hJne : Work.Kernels.jInvariantFun τ ≠ Work.Kernels.jInvariantFun z :=
    jne_of_disc_spike hτ hz hne1 hne2 hne3
  -- positivity of the three divisor factors
  have hJ1raw : 0 < ‖(z : ℂ) - (τ : ℂ)‖ :=
    norm_pos_iff.mpr (sub_ne_zero.mpr (fun h => hne1 (UpperHalfPlane.ext h)))
  have hJ2raw : 0 < ‖(z : ℂ) - ((τ : ℂ) + 1)‖ := by
    refine norm_pos_iff.mpr (sub_ne_zero.mpr ?_)
    intro h
    exact hne2 (UpperHalfPlane.ext (by rw [SpikeCircle.coe_one_vadd]; exact h))
  have hJ3raw : 0 < ‖(z : ℂ) - ((τ : ℂ) - 1)‖ := by
    refine norm_pos_iff.mpr (sub_ne_zero.mpr ?_)
    intro h
    exact hne3 (UpperHalfPlane.ext (by rw [SpikeCircle.coe_neg_one_vadd]; exact h))
  -- the lower bounds on `‖Δ‖`
  have hΔτ : cD * Real.exp (-(2 * Real.pi * τ.im)) ≤ ‖Work.Kernels.DeltaFun τ‖ :=
    (hDelta τ hhalfτ).1
  have hΔz : cD * Real.exp (-(2 * Real.pi * z.im)) ≤ ‖Work.Kernels.DeltaFun z‖ :=
    (hDelta z hhalfz).1
  -- instantiate the two structural inputs, before introducing the abbreviations
  have hid := SpikeCircle.Wlift_id ℓ d hd τ z hJne
  have hW0 := hb τ z hτ hz hne1 hne2 hne3
  have hdiv0 := hdiv τ z hτ hz
  -- abbreviations (all arithmetic below is on these opaque reals)
  set J1 : ℝ := ‖(z : ℂ) - (τ : ℂ)‖ with hJ1
  set J2 : ℝ := ‖(z : ℂ) - ((τ : ℂ) + 1)‖ with hJ2
  set J3 : ℝ := ‖(z : ℂ) - ((τ : ℂ) - 1)‖ with hJ3
  set A3 : ℝ := ‖Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z‖ with hA3
  set D : ℝ := J1 * J2 * J3 with hD
  set E1 : ℝ := Real.exp (-(2 * Real.pi * τ.im)) with hE1
  set E2 : ℝ := Real.exp (-(2 * Real.pi * z.im)) with hE2
  set E3 : ℝ := Real.exp (2 * Real.pi * τ.im) with hE3
  set E4 : ℝ := Real.exp (2 * Real.pi * (z.im - τ.im)) with hE4
  have hJ1pos : 0 < J1 := hJ1raw
  have hJ2pos : 0 < J2 := hJ2raw
  have hJ3pos : 0 < J3 := hJ3raw
  have hDpos : 0 < D := by rw [hD]; exact mul_pos (mul_pos hJ1pos hJ2pos) hJ3pos
  have hE2pos : 0 < E2 := by rw [hE2]; exact Real.exp_pos _
  have hE3pos : 0 < E3 := by rw [hE3]; exact Real.exp_pos _
  -- the exponential identities
  have hE123 : E1 * E2 * E3 = E2 := by
    rw [hE1, hE2, hE3]
    exact exp_neg_neg_pos (2 * Real.pi * τ.im) (2 * Real.pi * z.im)
  have hE14 : E1 = E4 * E2 := by
    rw [hE1, hE4, hE2, ← Real.exp_add]
    congr 1
    ring
  -- (1) the divisor lower bound, in the order produced by `norm_mul`
  have hJb : cd * E3 * D ≤ A3 := by
    have h := hdiv0
    rw [norm_mul, norm_mul, ← hJ1, ← hJ3, ← hJ2] at h
    have hD' : J1 * J3 * J2 = D := by rw [hD]; ring
    rwa [hD'] at h
  -- (2) the master identity, as a product identity
  have hnorm : ‖Work.Kernels.DeltaFun τ‖ * ‖Work.Kernels.DeltaFun z‖ * A3 *
      ‖Work.Kernels.Kfun ℓ d τ z - SpikeCircle.PP τ z‖ = ‖SpikeCircle.Wlift ℓ d τ (z : ℂ)‖ := by
    rw [hid, norm_mul, norm_mul, norm_mul, ← hA3]
    ring
  -- (3) the upper bound on `Wlift`
  have hW : ‖SpikeCircle.Wlift ℓ d τ (z : ℂ)‖ ≤ (Cw * (Work.Kernels.scale τ) ^ Nw * E1) * D := by
    have h := hW0
    rw [show Cw * (Work.Kernels.scale τ) ^ Nw * E1 * J1 * J2 * J3
        = (Cw * (Work.Kernels.scale τ) ^ Nw * E1) * D from by rw [hD]; ring] at h
    exact h
  -- (4) the lower bound on `‖Δ τ‖‖Δ z‖‖j τ - j z‖`
  have hlow : cD ^ 2 * cd * E2 * D ≤
      ‖Work.Kernels.DeltaFun τ‖ * ‖Work.Kernels.DeltaFun z‖ * A3 := by
    have h2 : (cD * E1) * (cD * E2) * (cd * E3 * D) ≤
        ‖Work.Kernels.DeltaFun τ‖ * ‖Work.Kernels.DeltaFun z‖ * A3 :=
      mul_le_mul (mul_le_mul hΔτ hΔz (le_of_lt (mul_pos hcD hE2pos)) (norm_nonneg _)) hJb
        (le_of_lt (mul_pos (mul_pos hcd hE3pos) hDpos))
        (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    have h3 : (cD * E1) * (cD * E2) * (cd * E3 * D) = cD ^ 2 * cd * E2 * D := by
      rw [show (cD * E1) * (cD * E2) * (cd * E3 * D)
          = cD * cD * cd * (E1 * E2 * E3) * D from by ring, hE123]
      ring
    rwa [← h3]
  -- (5) multiply by `‖Kfun - PP‖`, insert the master identity and the `Wlift` bound
  have hstep : cD ^ 2 * cd * E2 * D * ‖Work.Kernels.Kfun ℓ d τ z - SpikeCircle.PP τ z‖ ≤
      (Cw * (Work.Kernels.scale τ) ^ Nw * E1) * D := by
    calc cD ^ 2 * cd * E2 * D * ‖Work.Kernels.Kfun ℓ d τ z - SpikeCircle.PP τ z‖
        ≤ (‖Work.Kernels.DeltaFun τ‖ * ‖Work.Kernels.DeltaFun z‖ * A3) *
            ‖Work.Kernels.Kfun ℓ d τ z - SpikeCircle.PP τ z‖ :=
          mul_le_mul_of_nonneg_right hlow (norm_nonneg _)
      _ = ‖SpikeCircle.Wlift ℓ d τ (z : ℂ)‖ := hnorm
      _ ≤ (Cw * (Work.Kernels.scale τ) ^ Nw * E1) * D := hW
  -- (6) cancel `D`
  have hstepD : (cD ^ 2 * cd * E2 * ‖Work.Kernels.Kfun ℓ d τ z - SpikeCircle.PP τ z‖) * D ≤
      (Cw * (Work.Kernels.scale τ) ^ Nw * E1) * D := by
    have h1 : (cD ^ 2 * cd * E2 * D) * ‖Work.Kernels.Kfun ℓ d τ z - SpikeCircle.PP τ z‖
        = (cD ^ 2 * cd * E2 * ‖Work.Kernels.Kfun ℓ d τ z - SpikeCircle.PP τ z‖) * D := by
      ring
    rwa [h1] at hstep
  have hstep' : cD ^ 2 * cd * E2 * ‖Work.Kernels.Kfun ℓ d τ z - SpikeCircle.PP τ z‖ ≤
      Cw * (Work.Kernels.scale τ) ^ Nw * E1 := le_of_mul_le_mul_right hstepD hDpos
  -- (7) divide by `cD^2 cd e^{-2π Im z}`
  have hden : 0 < cD ^ 2 * cd * E2 := mul_pos (mul_pos (pow_pos hcD 2) hcd) hE2pos
  have hkey' : ‖Work.Kernels.Kfun ℓ d τ z - SpikeCircle.PP τ z‖ ≤
      (Cw * (Work.Kernels.scale τ) ^ Nw * E1) / (cD ^ 2 * cd * E2) := by
    rw [le_div_iff₀ hden]
    have h1 : ‖Work.Kernels.Kfun ℓ d τ z - SpikeCircle.PP τ z‖ * (cD ^ 2 * cd * E2)
        = cD ^ 2 * cd * E2 * ‖Work.Kernels.Kfun ℓ d τ z - SpikeCircle.PP τ z‖ := by ring
    rwa [h1]
  -- (8) rewrite the exponential quotient
  have hkey : ‖Work.Kernels.Kfun ℓ d τ z - SpikeCircle.PP τ z‖ ≤
      Cw / (cD ^ 2 * cd) * (Work.Kernels.scale τ) ^ Nw * E4 := by
    have hconv : (Cw * (Work.Kernels.scale τ) ^ Nw * E1) / (cD ^ 2 * cd * E2)
        = Cw / (cD ^ 2 * cd) * (Work.Kernels.scale τ) ^ Nw * E4 := by
      rw [hE14]
      field_simp
    exact le_of_le_of_eq hkey' hconv
  -- (9) conclude
  have hE4le : E4 ≤ Real.exp (2 * Real.pi * (29/20)) := by
    rw [hE4, Real.exp_le_exp]
    nlinarith [hzu, Real.pi_pos]
  have hPP : (1 / (2 * Real.pi) : ℂ) / ((z : ℂ) - ((τ : ℂ) - 1)) +
      (-(1 / (2 * Real.pi)) : ℂ) / ((z : ℂ) - ((τ : ℂ) + 1)) = SpikeCircle.PP τ z := by
    rw [SpikeCircle.PP]; push_cast; ring
  rw [hPP]
  calc ‖Work.Kernels.Kfun ℓ d τ z - SpikeCircle.PP τ z‖
      ≤ Cw / (cD ^ 2 * cd) * (Work.Kernels.scale τ) ^ Nw * E4 := hkey
    _ ≤ Cw / (cD ^ 2 * cd) * (Work.Kernels.scale τ) ^ Nw *
          Real.exp (2 * Real.pi * (29/20)) :=
        mul_le_mul_of_nonneg_left hE4le
          (mul_nonneg (div_nonneg hCw.le (le_of_lt (mul_pos (pow_pos hcD 2) hcd)))
            (Real.rpow_nonneg (Work.Kernels.scale_pos τ).le _))
    _ = Cw / (cD ^ 2 * cd) * Real.exp (2 * Real.pi * (29/20)) *
          (Work.Kernels.scale τ) ^ Nw * (1 + ‖(z : ℂ)‖) ^ (0 : ℝ) := by
        rw [Real.rpow_zero, mul_one]; ring

end Work.Asymptotics
