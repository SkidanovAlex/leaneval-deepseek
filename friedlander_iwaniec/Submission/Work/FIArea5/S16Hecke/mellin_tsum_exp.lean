import Mathlib

namespace Work.FIArea5.S16Hecke

open MeasureTheory

/-- **Mellin transform of a Dirichlet-type exponential series.**

For a sequence `w : ℕ → ℂ` with `w 0 = 0`, `c > 0` and `Re s > 0`, the Mellin transform of
`u ↦ ∑' n, w n * exp (-(c * u * n))` factors as
`Γ(s) * c ^ (-s)` times the Dirichlet series `∑' n, w n * n ^ (-s)`:

`mellin (fun u => ∑' n, w n * exp (-(c * u * n))) s = Γ s * c ^ (-s) * ∑' n, w n * n ^ (-s)`.

The two summability hypotheses are exactly what is needed for the interchange of the integral
with the series: `hpoint` gives almost-everywhere summability of the integrands (pointwise in `u`
it is the summability of the exponential series), and `hsum` gives summability of the resulting
series of integrals `‖w n‖ * Gamma s.re / (c * n) ^ s.re`. -/
theorem mellin_tsum_exp (w : ℕ → ℂ) (c : ℝ) (hc : 0 < c) (hw0 : w 0 = 0) {s : ℂ}
    (hs : 0 < s.re)
    (hpoint : ∀ u : ℝ, 0 < u →
      Summable (fun n : ℕ => ‖w n‖ * Real.exp (-(c * u * (n : ℝ)))))
    (hsum : Summable (fun n : ℕ => ‖w n‖ * (n : ℝ) ^ (-s.re))) :
    mellin (fun u : ℝ => ∑' n : ℕ, w n * Complex.exp (-(c * u * (n : ℝ)))) s
      = Complex.Gamma s * (c : ℂ) ^ (-s) * ∑' n : ℕ, w n * (n : ℂ) ^ (-s) := by
  classical
  set F : ℝ → ℂ := fun u => ∑' n : ℕ, w n * Complex.exp (-(c * u * (n : ℝ))) with hFdef
  have hp : ∀ n : ℕ, w n = 0 ∨ 0 < c * n := by
    intro n
    rcases Nat.eq_zero_or_pos n with h | h
    · left
      rw [h]
      exact hw0
    · right
      have hn : (0:ℝ) < (n:ℝ) := by exact_mod_cast h
      exact mul_pos hc hn
  -- pointwise `HasSum` representation of `F`
  have hHas : ∀ t ∈ Set.Ioi (0:ℝ),
      HasSum (fun n : ℕ => w n * (Real.exp (-(c * n) * t) : ℂ)) (F t) := by
    intro t ht
    have ht0 : 0 < t := ht
    have hsm : Summable (fun n : ℕ => w n * (Real.exp (-(c * n) * t) : ℂ)) := by
      refine Summable.of_norm ?_
      refine (hpoint t ht0).congr (fun n => ?_)
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      congr 1
      ring_nf
    have hfeq : (∑' n : ℕ, w n * (Real.exp (-(c * n) * t) : ℂ)) = F t := by
      rw [hFdef]
      refine tsum_congr (fun n => ?_)
      rw [Complex.ofReal_exp]
      congr 1
      push_cast
      ring_nf
    have h2 := hsm.hasSum
    rwa [hfeq] at h2
  -- summability of `‖w n‖ / (c * n) ^ s.re`
  have h_sum : Summable (fun n : ℕ => ‖w n‖ / (c * n) ^ s.re) := by
    have key : ∀ n : ℕ,
        c ^ (-s.re) * (‖w n‖ * (n:ℝ) ^ (-s.re)) = ‖w n‖ / (c * n) ^ s.re := by
      intro n
      have hn : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
      rw [div_eq_mul_inv, Real.mul_rpow hc.le hn, mul_inv, Real.rpow_neg hc.le, Real.rpow_neg hn]
      ring_nf
    exact (hsum.mul_left (c ^ (-s.re))).congr key
  -- Mellin transform of the exponential series as a Dirichlet series
  have hHasSum : HasSum (fun n : ℕ => Complex.Gamma s * w n / ((c * n : ℝ) : ℂ) ^ s)
      (mellin F s) := hasSum_mellin hp hs hHas h_sum
  -- the termwise identification `Γ s * w n / (c n) ^ s = Γ s * c ^ (-s) * (w n * n ^ (-s))`
  have hterm : ∀ n : ℕ, Complex.Gamma s * w n / ((c * n : ℝ) : ℂ) ^ s
      = (Complex.Gamma s * (c:ℂ) ^ (-s)) * (w n * (n:ℂ) ^ (-s)) := by
    intro n
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; rw [hw0]; simp
    · have hn : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
      have hcast : ((c * n : ℝ) : ℂ) = (c:ℂ) * ((n:ℝ):ℂ) := by push_cast; ring
      rw [div_eq_mul_inv, ← Complex.cpow_neg, hcast,
        Complex.mul_cpow_ofReal_nonneg hc.le hn (-s), Complex.ofReal_natCast]
      ring_nf
  rw [← hHasSum.tsum_eq, tsum_congr hterm, tsum_mul_left]

end Work.FIArea5.S16Hecke
