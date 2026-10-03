/-
# `Submission.Work.FIArea6Hecke.R.LamRightHalf.thetaDualM_decay`

Exponential decay at `∞` of the weight-`m` dual theta series.  For `m ≥ 1` the `ξ = 0` summand
vanishes automatically (`0^m = 0`); for `m = 0` one needs the vanishing of the first Fourier
coefficient `ĝ(0) = gaussSum d χ 0 = 0`.  Generalises `R/thetaDual_decay`; the extra monomial
factor `(ξ₁+iξ₂)^m` is harmless because `|ξ|² ≥ 1` on the nonzero lattice points, so that
`e^{-π|ξ|²w} ≤ e^π e^{-πw} e^{-π|ξ|²}` and the resulting majorant is summable.
-/
import Mathlib
import Submission.Work.FIArea6Hecke.R.LamRightHalf.Defs
import Submission.Work.FIArea6Hecke.R.LamRightHalf.thetaDualM_continuous
import Submission.Work.FIArea6Hecke.R.thetaDual_decay

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.FIArea6Hecke.R

open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

theorem thetaDualM_decay (d : ℕ) (hd : 1 ≤ d) {chi : GaussianInt → ℂ}
    (hchi : ∀ z : GaussianInt, ‖chi z‖ ≤ 1) (m : ℕ)
    (h0 : m = 0 → Work.FIArea5.S16Hecke.gaussSum d chi 0 = 0) :
    ∃ C : ℝ, ∀ w : ℝ, 1 ≤ w →
      ‖thetaDualM d chi m w‖ ≤ C * Real.exp (-Real.pi * w) := by
  set F : ℤ × ℤ → ℝ := fun p => (1 + ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2)) ^ m *
      Real.exp (-(Real.pi * ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2))) with hF
  have hsumm : Summable F := by
    rw [hF]
    refine (summable_poly_gauss m one_pos).congr (fun p => ?_)
    rw [mul_one]
  set S : ℝ := ∑' p : ℤ × ℤ, F p with hS
  refine ⟨(((4 * d : ℕ) : ℝ) ^ 2 * Real.exp Real.pi) * S, ?_⟩
  intro w hw
  set maj : ℤ × ℤ → ℝ := fun p =>
    (((4 * d : ℕ) : ℝ) ^ 2 * Real.exp Real.pi) * (Real.exp (-Real.pi * w) * F p) with hmajdef
  have hmaj : Summable maj := by
    rw [hmajdef]
    exact (hsumm.mul_left (Real.exp (-Real.pi * w))).mul_left
      (((4 * d : ℕ) : ℝ) ^ 2 * Real.exp Real.pi)
  have hbound : ∀ p : ℤ × ℤ,
      ‖Work.FIArea5.S16Hecke.gaussSum d chi ⟨p.1, p.2⟩ *
        (((p.1 : ℂ) + Complex.I * (p.2 : ℂ)) ^ m) *
        Complex.exp (((-(Real.pi * (((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2) * w)) : ℝ) : ℂ))‖ ≤ maj p := by
    intro p
    by_cases hp : p = 0
    · have hp1 : p.1 = 0 := by rw [hp]; rfl
      have hp2 : p.2 = 0 := by rw [hp]; rfl
      have hzero : Work.FIArea5.S16Hecke.gaussSum d chi ⟨p.1, p.2⟩ *
          (((p.1 : ℂ) + Complex.I * (p.2 : ℂ)) ^ m) *
          Complex.exp (((-(Real.pi * (((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2) * w)) : ℝ) : ℂ)) = 0 := by
        by_cases hm0 : m = 0
        · subst hm0
          have hg : Work.FIArea5.S16Hecke.gaussSum d chi ⟨p.1, p.2⟩ = 0 := by
            rw [show (⟨p.1, p.2⟩ : GaussianInt) = 0 by rw [hp1, hp2]; rfl]
            exact h0 rfl
          rw [hg, zero_mul, zero_mul]
        · have hz : ((p.1 : ℂ) + Complex.I * (p.2 : ℂ)) = 0 := by rw [hp1, hp2]; ring
          rw [hz, zero_pow hm0, mul_zero, zero_mul]
      rw [hzero, norm_zero, hmajdef]
      positivity
    · rw [norm_mul, norm_mul, Complex.norm_exp_ofReal]
      have hs : (1 : ℝ) ≤ (p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2 := one_le_sq_add_sq hp
      have hexp := exp_neg_mul_le_exp_pi_mul ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2) w hs hw
      have hexp' : Real.exp (-(Real.pi * (((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2) * w)))
          ≤ Real.exp Real.pi * Real.exp (-Real.pi * w) *
            Real.exp (-Real.pi * ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2)) := by
        simpa only [neg_mul] using hexp
      simp only [hmajdef, hF]
      calc ‖Work.FIArea5.S16Hecke.gaussSum d chi ⟨p.1, p.2⟩‖ *
              ‖(((p.1 : ℂ) + Complex.I * (p.2 : ℂ)) ^ m)‖ *
                Real.exp (-(Real.pi * (((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2) * w)))
          ≤ ((4 * d : ℕ) : ℝ) ^ 2 * (1 + ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2)) ^ m *
                Real.exp (-(Real.pi * (((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2) * w))) := by
            refine mul_le_mul (mul_le_mul (thetaDualGaussBound_aux d hchi _)
              (norm_pow_le_one_add_gnorm p m) (norm_nonneg _) (by positivity))
              le_rfl (Real.exp_pos _).le (by positivity)
        _ ≤ ((4 * d : ℕ) : ℝ) ^ 2 * (1 + ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2)) ^ m *
              (Real.exp Real.pi * Real.exp (-Real.pi * w) *
                Real.exp (-Real.pi * ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2))) :=
            mul_le_mul_of_nonneg_left hexp' (by positivity)
        _ = (((4 * d : ℕ) : ℝ) ^ 2 * Real.exp Real.pi) * (Real.exp (-Real.pi * w) *
              ((1 + ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2)) ^ m *
                Real.exp (-(Real.pi * ((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2))))) := by ring_nf
  have hFsum : Summable (fun p : ℤ × ℤ => Work.FIArea5.S16Hecke.gaussSum d chi ⟨p.1, p.2⟩ *
      (((p.1 : ℂ) + Complex.I * (p.2 : ℂ)) ^ m) *
      Complex.exp (((-(Real.pi * (((p.1 : ℝ) ^ 2 + (p.2 : ℝ) ^ 2) * w)) : ℝ) : ℂ))) :=
    Summable.of_norm_bounded hmaj hbound
  have htsum_eq : (∑' p : ℤ × ℤ, maj p)
      = (((4 * d : ℕ) : ℝ) ^ 2 * Real.exp Real.pi) * (Real.exp (-Real.pi * w) * S) := by
    simp only [hmajdef]
    rw [tsum_mul_left, tsum_mul_left, ← hS]
  rw [thetaDualM]
  refine le_trans (norm_tsum_le_tsum_norm hFsum.norm) ?_
  refine le_trans (Summable.tsum_le_tsum hbound hFsum.norm hmaj) ?_
  rw [htsum_eq]
  rw [mul_comm (Real.exp (-Real.pi * w)) S, ← mul_assoc]

end

end Work.FIArea6Hecke.R
