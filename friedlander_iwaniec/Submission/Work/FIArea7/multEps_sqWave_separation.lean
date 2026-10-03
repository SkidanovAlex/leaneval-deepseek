import Mathlib
import Submission.Work.FIArea7.sign_re_separation
import Submission.Work.FIArea7.multEps_separation

namespace Work.FIArea7

/-- For a non-zero integer `n`, the cast of its sign to `ℂ` is the indicator of positivity. -/
lemma int_sign_cast_eq_c {n : ℤ} (hn : n ≠ 0) :
    ((Int.sign n : ℤ) : ℂ) = if (0 : ℝ) < (n : ℝ) then 1 else -1 := by
  rcases lt_trichotomy n 0 with h | h | h
  · rw [Int.sign_eq_neg_one_of_neg h,
      if_neg (by exact_mod_cast (not_lt.mpr h.le) : ¬ (0 : ℝ) < (n : ℝ))]
    norm_num
  · exact absurd h hn
  · rw [Int.sign_eq_one_of_pos h, if_pos (by exact_mod_cast h)]
    norm_num

/-- **FI (20.15) + (20.19): the multiplier sign `ε(w,z)` is separated in `w` and `z`.**
`2·ε(w,z)·(u,v)_∞ = 1 + sign(vr) − (sign v − sign r)·sign(Re wz)` ((20.15)), and the last factor
is expanded by (20.19) as `Σ_k ĉ_k (w/|w|)^k (z/|z|)^k`.  Here `w = u + iv`, `z = r + is`;
`v = w.im` and `r = z.re` must be non-zero (they are the entries of the Hilbert symbols in
(20.13)/(20.14)), and `(w*z).re = ur − vs ≠ 0`.  The hypothesis `‖w‖‖z‖ ≤ R·|Re(wz)|` is the
"room" condition of (20.18), i.e. `wz` is `1/R` away from the imaginary axis. -/
theorem multEps_sqWave_separation :
    ∃ C : ℝ, 0 < C ∧ ∀ R : ℕ, 2 ≤ R → ∃ ĉ : ℤ → ℂ,
      (∀ s : Finset ℤ, ∑ k ∈ s, ‖ĉ k‖ ≤ C * Real.log (2 * (R : ℝ))) ∧
      ∀ (w z : GaussianInt), w.im ≠ 0 → z.re ≠ 0 → (w * z).re ≠ 0 →
        ‖w.toComplex‖ * ‖z.toComplex‖ ≤ (R : ℝ) * |(((w * z).re : ℤ) : ℝ)| →
        (2 * (MultEps w z : ℂ) * (HilbertInf w.re w.im : ℂ))
          = 1 + (Int.sign (w.im * z.re) : ℂ)
            - ((Int.sign w.im - Int.sign z.re : ℤ) : ℂ)
              * (∑' k : ℤ, ĉ k * ((w.toComplex / (‖w.toComplex‖ : ℂ)) ^ k
                                   * (z.toComplex / (‖z.toComplex‖ : ℂ)) ^ k)) := by
  -- the separated square-wave expansion of the sign of `Re(wz)` (FI (20.19))
  obtain ⟨C, hC0, hC⟩ := sign_re_separation
  refine ⟨C, hC0, fun R hR => ?_⟩
  obtain ⟨ĉ, hcoeff, hsum⟩ := hC R hR
  refine ⟨ĉ, hcoeff, ?_⟩
  intro w z hv hr hre hroom
  -- the two Gaussian integers are non-zero complex numbers
  have hwne : w.toComplex ≠ 0 := by
    intro h0
    have h1 : ((w.im : ℤ) : ℝ) = 0 := by rw [GaussianInt.intCast_im, h0]; simp
    exact hv (by exact_mod_cast h1)
  have hzne : z.toComplex ≠ 0 := by
    intro h0
    have h1 : ((z.re : ℤ) : ℝ) = 0 := by rw [GaussianInt.intCast_re, h0]; simp
    exact hr (by exact_mod_cast h1)
  -- the "room" condition transfers: `Re(w̄z)` in `ℂ` is `Re(wz)` in `ℤ[i]`
  have hroom' : ‖w.toComplex‖ * ‖z.toComplex‖
      ≤ (R : ℝ) * |(w.toComplex * z.toComplex).re| := by
    rw [← GaussianInt.toComplex_mul, ← GaussianInt.intCast_re]
    exact hroom
  have hHS := hsum w.toComplex z.toComplex hwne hzne hroom'
  -- the series sums to `sign(Re(wz))`, i.e. to the cast of the integer sign
  have hsgn : (if 0 < (w.toComplex * z.toComplex).re then (1 : ℂ) else -1)
      = ((Int.sign ((w * z).re) : ℤ) : ℂ) := by
    rw [← GaussianInt.toComplex_mul, ← GaussianInt.intCast_re]
    exact (int_sign_cast_eq_c hre).symm
  have hval : (∑' k : ℤ, ĉ k * ((w.toComplex / (‖w.toComplex‖ : ℂ)) ^ k
        * (z.toComplex / (‖z.toComplex‖ : ℂ)) ^ k)) = ((Int.sign ((w * z).re) : ℤ) : ℂ) :=
    hHS.tsum_eq.trans hsgn
  -- the multiplier identity (20.15), cast to `ℂ`
  have hkey : w.re * z.re - w.im * z.im ≠ 0 := by rw [← re_mul]; exact hre
  have hme' : 2 * (MultEps w z : ℂ) * (HilbertInf w.re w.im : ℂ)
      = 1 + (Int.sign (w.im * z.re) : ℂ) - ((Int.sign w.im - Int.sign z.re : ℤ) : ℂ)
          * (Int.sign ((w * z).re) : ℂ) := by
    have h := multEps_separation w.re w.im z.re z.im hv hr hkey
    have h2 := congrArg (fun n : ℤ => (n : ℂ)) h
    push_cast at h2
    rw [re_mul w z]
    simpa using h2
  rw [hval]
  exact hme'

end Work.FIArea7
