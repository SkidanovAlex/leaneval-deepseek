import Mathlib

/-!
# A per-term lower bound for the Fejér weight `1 - j/(J+1)`

This file proves `Work.LinnikAreas.turanPerTermZero`.  Given the Fejér-kernel
inequality

  `-‖w‖/(1+‖w‖) ≤ ∑_{j=1}^J (1 - j/(J+1)) Re(w^j)`  for `‖w‖ ≤ 1`

and a complex number `v` of modulus `1` (i.e. `v^j` has modulus `1` for every `j`),
it shows

  `(J+1)/4 - 1 ≤ ∑_{j=1}^J (1 - j/(J+1)) Re(v^j) (1 + Re(v^j))`.

The proof applies the hypothesis twice, at `w = v` and at `w = v^2`, and combines
the two inequalities with the elementary identity `Re(z^2) = 2 (Re z)^2 - ‖z‖^2`
together with `∑_{j=1}^J (1 - j/(J+1)) = J/2`.

## Main results

* `Work.LinnikAreas.turanPerTermZero`
-/

namespace Work.LinnikAreas

open scoped BigOperators

/-- The Gauss sum `∑_{j=1}^J j = J(J+1)/2`, over the reals. -/
lemma turanPerTermZero_sumIcc (J : ℕ) :
    ∑ j ∈ Finset.Icc 1 J, (j : ℝ) = (J : ℝ) * ((J : ℝ) + 1) / 2 := by
  induction J with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega) (fun j => (j : ℝ)), ih]
    push_cast
    ring

/-- The total Fejér weight: `∑_{j=1}^J (1 - j/(J+1)) = J/2`. -/
lemma turanPerTermZero_sumW (J : ℕ) :
    ∑ j ∈ Finset.Icc 1 J, (1 - (j : ℝ) / ((J : ℝ) + 1)) = (J : ℝ) / 2 := by
  have h1 : ∑ j ∈ Finset.Icc 1 J, (1 - (j : ℝ) / ((J : ℝ) + 1))
      = (Finset.Icc 1 J).card - (∑ j ∈ Finset.Icc 1 J, (j : ℝ)) / ((J : ℝ) + 1) := by
    rw [Finset.sum_sub_distrib, Finset.sum_div, Finset.sum_const, nsmul_eq_mul, mul_one]
  rw [h1, Nat.card_Icc, turanPerTermZero_sumIcc]
  push_cast
  field_simp
  ring

/-- `Re(z^2) = 2 (Re z)^2 - ‖z‖^2`. -/
lemma turanPerTermZero_complex_sq_re (z : ℂ) :
    (z ^ 2).re = 2 * z.re ^ 2 - ‖z‖ ^ 2 := by
  rw [pow_two, Complex.mul_re, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  ring

/-- The abstract inequality: two lower bounds of Fejér type for a real sequence `a`
give a lower bound for the "quadratic" weighted sum. -/
lemma turanPerTermZero_core (J : ℕ) (a : ℕ → ℝ)
    (h1 : -(1 / 2 : ℝ) ≤
      ∑ j ∈ Finset.Icc 1 J, (1 - (j : ℝ) / ((J : ℝ) + 1)) * a j)
    (h2 : -(1 / 2 : ℝ) ≤
      ∑ j ∈ Finset.Icc 1 J, (1 - (j : ℝ) / ((J : ℝ) + 1)) * (2 * (a j) ^ 2 - 1)) :
    ((J : ℝ) + 1) / 4 - 1 ≤
      ∑ j ∈ Finset.Icc 1 J, (1 - (j : ℝ) / ((J : ℝ) + 1)) * (a j * (1 + a j)) := by
  have hA : (∑ j ∈ Finset.Icc 1 J, (1 - (j : ℝ) / ((J : ℝ) + 1)) * (2 * (a j) ^ 2 - 1))
      = 2 * (∑ j ∈ Finset.Icc 1 J, (1 - (j : ℝ) / ((J : ℝ) + 1)) * (a j) ^ 2)
        - (∑ j ∈ Finset.Icc 1 J, (1 - (j : ℝ) / ((J : ℝ) + 1))) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl; intro j hj; ring
  have hB : (∑ j ∈ Finset.Icc 1 J, (1 - (j : ℝ) / ((J : ℝ) + 1)) * (a j * (1 + a j)))
      = (∑ j ∈ Finset.Icc 1 J, (1 - (j : ℝ) / ((J : ℝ) + 1)) * a j)
        + (∑ j ∈ Finset.Icc 1 J, (1 - (j : ℝ) / ((J : ℝ) + 1)) * (a j) ^ 2) := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl; intro j hj; ring
  have h2' : -(1 / 2 : ℝ) ≤
      2 * (∑ j ∈ Finset.Icc 1 J, (1 - (j : ℝ) / ((J : ℝ) + 1)) * (a j) ^ 2)
        - (∑ j ∈ Finset.Icc 1 J, (1 - (j : ℝ) / ((J : ℝ) + 1))) := by
    rw [← hA]; exact h2
  have hW : (∑ j ∈ Finset.Icc 1 J, (1 - (j : ℝ) / ((J : ℝ) + 1))) = (J : ℝ) / 2 :=
    turanPerTermZero_sumW J
  rw [hB]
  linarith [h1, h2', hW]

theorem turanPerTermZero (J : ℕ) (hJ : 1 ≤ J)
    (hfejer : ∀ w : ℂ, ‖w‖ ≤ 1 →
      -‖w‖ / (1 + ‖w‖) ≤
        ∑ j ∈ Finset.Icc 1 J, (1 - (j : ℝ) / (J + 1)) * (w ^ j).re)
    (v : ℂ) (hv : ‖v‖ = 1) :
    ((J : ℝ) + 1) / 4 - 1 ≤
      ∑ j ∈ Finset.Icc 1 J, (1 - (j : ℝ) / (J + 1)) * ((v ^ j).re * (1 + (v ^ j).re)) := by
  have _ : (0 : ℕ) < J := hJ
  have hv2 : ‖v ^ 2‖ ≤ 1 := by rw [norm_pow, hv, one_pow]
  have h1 : -(1 / 2 : ℝ) ≤ ∑ j ∈ Finset.Icc 1 J, (1 - (j : ℝ) / (J + 1)) * (v ^ j).re := by
    have h := hfejer v (le_of_eq hv)
    rw [hv] at h
    norm_num at h
    exact h
  have hstep : ∀ j : ℕ, ((v ^ 2) ^ j).re = 2 * (v ^ j).re ^ 2 - 1 := by
    intro j
    rw [show (v ^ 2) ^ j = (v ^ j) ^ 2 by rw [← pow_mul, ← pow_mul, mul_comm]]
    rw [turanPerTermZero_complex_sq_re, norm_pow, hv]
    norm_num
  have h2 : -(1 / 2 : ℝ) ≤
      ∑ j ∈ Finset.Icc 1 J, (1 - (j : ℝ) / (J + 1)) * (2 * (v ^ j).re ^ 2 - 1) := by
    have h := hfejer (v ^ 2) hv2
    rw [norm_pow, hv, one_pow] at h
    norm_num at h
    have hsum : (∑ j ∈ Finset.Icc 1 J, (1 - (j : ℝ) / (J + 1)) * ((v ^ 2) ^ j).re)
        = ∑ j ∈ Finset.Icc 1 J, (1 - (j : ℝ) / (J + 1)) * (2 * (v ^ j).re ^ 2 - 1) := by
      apply Finset.sum_congr rfl; intro j hj
      rw [hstep j]
    rwa [hsum] at h
  exact turanPerTermZero_core J (fun j => (v ^ j).re) h1 h2

end Work.LinnikAreas
