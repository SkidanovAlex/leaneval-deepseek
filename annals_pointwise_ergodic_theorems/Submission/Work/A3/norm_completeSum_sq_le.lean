import Mathlib
import Submission.Work.A3.Circle
import Submission.Commons.Analysis.ExponentialSums.norm_sum_sq_le_shift_conj

/-!
# Single-step Weyl differencing for the complete sum `completeSum`

For an integer polynomial `g`, an integer `a` and an integer `n ≥ 1`, the complete exponential
sum `completeSum g a n = ∑_{r<n} e(-2πi a g(r)/n)` satisfies

`‖completeSum g a n‖ ^ 2 ≤ ∑_{h<n} ‖∑_{r<n} e(-2πi a (g(r+h)-g(r))/n)‖`.

The point is that the phase `r ↦ e(-2πi a g(r)/n)` is **`n`-periodic** on `ℤ`, because
`n ∣ g(r+n) - g(r)` for every integer polynomial `g` (`Polynomial.sub_dvd_eval_sub`).  Hence the
shifted autocorrelation sums `∑_r e(-2πi a (g(r+h)-g(r))/n)` have the same total as `|S|^2`
(`Commons.Analysis.ExponentialSums.norm_sum_sq_le_shift_conj`), and the triangle inequality gives
the displayed bound.
-/

namespace Work.A3

open Polynomial Finset
open scoped BigOperators

/-- The conjugate of `exp (-(2πi s))` is `exp (2πi t)`; consequently the product of the two
exponentials is `exp (-(2πi (s - t)))`. -/
private lemma exp_neg_mul_conj_exp_neg (s t : ℝ) :
    Complex.exp (-(2 * Real.pi * Complex.I * (s : ℂ))) *
        (starRingEnd ℂ) (Complex.exp (-(2 * Real.pi * Complex.I * (t : ℂ))))
      = Complex.exp (-(2 * Real.pi * Complex.I * ((s - t : ℝ) : ℂ))) := by
  rw [← Complex.exp_conj]
  rw [← Complex.exp_add]
  congr 1
  have hconj : (starRingEnd ℂ) (-(2 * Real.pi * Complex.I * (t : ℂ)))
      = 2 * Real.pi * Complex.I * (t : ℂ) := by
    simp only [map_mul, map_neg, Complex.conj_ofReal, Complex.conj_I, map_ofNat]
    ring
  rw [hconj]
  push_cast
  ring

/-- `exp (-(2πi k)) = 1` for an integer `k`. -/
private lemma exp_neg_two_pi_I_mul_int (k : ℤ) :
    Complex.exp (-(2 * Real.pi * Complex.I * ((k : ℝ) : ℂ))) = 1 := by
  rw [show -(2 * Real.pi * Complex.I * ((k : ℝ) : ℂ))
      = ((-k : ℤ) : ℂ) * (2 * Real.pi * Complex.I) by push_cast; ring]
  exact Complex.exp_int_mul_two_pi_mul_I (-k)

/-- Shifting the phase by an integral amount does not change `exp (-(2πi ·))`. -/
private lemma exp_shift_int (s : ℝ) (k : ℤ) :
    Complex.exp (-(2 * Real.pi * Complex.I * (((s + (k:ℝ)) : ℝ) : ℂ)))
      = Complex.exp (-(2 * Real.pi * Complex.I * (s : ℂ))) := by
  rw [show (((s + (k:ℝ)) : ℝ) : ℂ) = (s : ℂ) + ((k:ℝ) : ℂ) by push_cast; ring]
  rw [show -(2 * Real.pi * Complex.I * ((s : ℂ) + ((k:ℝ) : ℂ)))
      = -(2 * Real.pi * Complex.I * (s : ℂ)) + -(2 * Real.pi * Complex.I * ((k:ℝ) : ℂ))
      by ring]
  rw [Complex.exp_add, exp_neg_two_pi_I_mul_int, mul_one]

theorem norm_completeSum_sq_le (g : Polynomial ℤ) (a : ℤ) {n : ℕ} (hn : 1 ≤ n) :
    ‖Work.A3.completeSum g a n‖ ^ 2
      ≤ ∑ h ∈ Finset.range n, ‖∑ r ∈ Finset.range n,
          Complex.exp (-(2 * Real.pi * Complex.I) *
            (((a * (g.eval ((r : ℤ) + (h : ℤ)) - g.eval (r : ℤ)) : ℤ) : ℝ) / (n : ℝ)))‖ := by
  have hn0 : 0 < n := hn
  have hnR : (n : ℝ) ≠ 0 := by
    have h : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn0
    exact ne_of_gt h
  -- The phase `t` of the sum, and the `n`-periodic exponential `f = exp (-(2πi t))`.
  set t : ℤ → ℝ := fun j => (a : ℝ) * ((g.eval j : ℤ) : ℝ) / (n : ℝ) with htdef
  set f : ℤ → ℂ := fun j => Complex.exp (-(2 * Real.pi * Complex.I * (t j : ℂ))) with hfdef
  -- `f` is periodic of period `n`: for an integer polynomial `n ∣ g (x+n) - g x`.
  have hper : ∀ x : ℤ, f (x + (n : ℤ)) = f x := by
    intro x
    simp only [hfdef]
    have hdvd : (n : ℤ) ∣ g.eval (x + (n : ℤ)) - g.eval x := by
      have h := Polynomial.sub_dvd_eval_sub (x + (n : ℤ)) x g
      have hsub : x + (n : ℤ) - x = (n : ℤ) := by ring
      rwa [hsub] at h
    obtain ⟨c, hc⟩ := hdvd
    have htarg : t (x + (n : ℤ)) = t x + (a * c : ℤ) := by
      simp only [htdef]
      have key : (a : ℝ) * ((g.eval (x + (n : ℤ)) : ℤ) : ℝ)
          = (a : ℝ) * ((g.eval x : ℤ) : ℝ) + (n : ℝ) * ((a * c : ℤ) : ℝ) := by
        have h1 : ((a * (g.eval (x + (n : ℤ)) - g.eval x) : ℤ) : ℝ)
            = ((n : ℤ) : ℝ) * ((a * c : ℤ) : ℝ) := by
          rw [show a * (g.eval (x + (n : ℤ)) - g.eval x) = (n : ℤ) * (a * c)
              from by rw [hc]; ring]
          push_cast; ring
        push_cast at h1 ⊢
        linarith [h1]
      rw [key]
      field_simp
    rw [htarg]
    exact exp_shift_int (t x) (a * c)
  -- `completeSum g a n` is the complete sum of `f`.
  have hcs : (∑ x ∈ Finset.range n, f (x : ℤ)) = Work.A3.completeSum g a n := by
    rw [Work.A3.completeSum]
    apply Finset.sum_congr rfl
    intro r _
    simp only [hfdef, htdef]
    push_cast
    ring_nf
  -- The differenced phase is `f (x+h) · conj (f x)`.
  have hterm : ∀ (x h : ℕ), f ((x : ℤ) + (h : ℤ)) * (starRingEnd ℂ) (f (x : ℤ))
      = Complex.exp (-(2 * Real.pi * Complex.I) *
          (((a * (g.eval ((x : ℤ) + (h : ℤ)) - g.eval (x : ℤ)) : ℤ) : ℝ) / (n : ℝ))) := by
    intro x h
    have harg : t ((x:ℤ)+(h:ℤ)) - t (x:ℤ)
        = ((a * (g.eval ((x:ℤ)+(h:ℤ)) - g.eval (x:ℤ)) : ℤ) : ℝ) / (n:ℝ) := by
      simp only [htdef]
      push_cast
      field_simp
    simp only [hfdef]
    rw [exp_neg_mul_conj_exp_neg, harg, neg_mul]
    push_cast
    ring_nf
  rw [← hcs]
  calc ‖∑ x ∈ Finset.range n, f (x : ℤ)‖ ^ 2
      ≤ ∑ h ∈ Finset.range n,
          ‖∑ x ∈ Finset.range n, f ((x : ℤ) + (h : ℤ)) * (starRingEnd ℂ) (f (x : ℤ))‖ :=
        Commons.Analysis.ExponentialSums.norm_sum_sq_le_shift_conj n hn0 f hper
    _ = ∑ h ∈ Finset.range n, ‖∑ r ∈ Finset.range n,
          Complex.exp (-(2 * Real.pi * Complex.I) *
            (((a * (g.eval ((r : ℤ) + (h : ℤ)) - g.eval (r : ℤ)) : ℤ) : ℝ) / (n : ℝ)))‖ := by
        apply Finset.sum_congr rfl
        intro h _
        congr 1
        apply Finset.sum_congr rfl
        intro r _
        exact hterm r h

end Work.A3
