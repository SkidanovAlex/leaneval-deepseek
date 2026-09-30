import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.mr_direct

/-! **Expansion of a weighted mean square into a double sum.**

For a finite set `N ⊆ {n : 1 ≤ n}` of integers, and sequences `c : ℕ → ℂ`, `η : Fin R → ℂ`,
`t : Fin R → ℝ`,

`Σ_{n∈N} c n ‖Σ_i η_i n^{i t_i}‖² = Σ_{i,j} η_i conj(η_j) Σ_{n∈N} c n n^{i(t_i−t_j)}`.

This is the elementary identity that converts the `Λ`-weighted quadratic form occurring in the
duality proof of the Halász inequality for primes into the double sum over the differences
`t_i − t_j`, to which the main-term estimate and the prime-sum error estimate are applied.

Route: `‖z‖² = z·conj z` (`Complex.normSq_eq_norm_sq`, `Complex.mul_conj`), push `conj` inside and
swap the order of summation; the exponent identity
`(n:ℂ)^{i t_i}·(n:ℂ)^{−i t_j} = (n:ℂ)^{i(t_i−t_j)}` is `Complex.cpow_add` with base `(n:ℂ) ≠ 0`
(hence the hypothesis `1 ≤ n`). -/

/-- Conjugation commutes with a complex power of a natural number:
`conj (n ^ w) = n ^ (conj w)`. -/
private lemma star_natCast_cpow (n : ℕ) (w : ℂ) :
    (starRingEnd ℂ) ((n : ℂ) ^ w) = (n : ℂ) ^ ((starRingEnd ℂ) w) := by
  have harg : ((n : ℂ)).arg ≠ Real.pi := by
    rw [show (n : ℂ) = ((n : ℝ) : ℂ) from by norm_num,
      Complex.arg_ofReal_of_nonneg (Nat.cast_nonneg n)]
    exact (Real.pi_pos.ne').symm
  have h := Complex.cpow_conj ((n : ℂ)) w harg
  rw [Complex.conj_natCast] at h
  exact h.symm

theorem sum_mul_normSq_eq_double {R : ℕ} (c : ℕ → ℂ) (η : Fin R → ℂ) (t : Fin R → ℝ) (N : Finset ℕ)
    (h1 : ∀ n ∈ N, 1 ≤ n) :
    (∑ n ∈ N, c n * ((‖∑ i, η i * (n : ℂ) ^ (Complex.I * (t i : ℂ))‖ ^ 2 : ℝ) : ℂ))
      = ∑ i, ∑ j, η i * (starRingEnd ℂ) (η j) *
          (∑ n ∈ N, c n * (n : ℂ) ^ (Complex.I * ((t i - t j : ℝ) : ℂ))) := by
  classical
  have hne : ∀ n ∈ N, (n : ℂ) ≠ 0 := fun n hn => by
    have hn1 : 1 ≤ n := h1 n hn
    exact_mod_cast (show n ≠ 0 by omega)
  have hstarI : ∀ j : Fin R,
      (starRingEnd ℂ) (Complex.I * (t j : ℂ)) = -(Complex.I * (t j : ℂ)) := by
    intro j
    rw [map_mul, Complex.conj_I, Complex.conj_ofReal]
    ring
  have hpow : ∀ n ∈ N, ∀ i j : Fin R,
      (n : ℂ) ^ (Complex.I * (t i : ℂ)) * (n : ℂ) ^ (-(Complex.I * (t j : ℂ)))
        = (n : ℂ) ^ (Complex.I * ((t i - t j : ℝ) : ℂ)) := by
    intro n hn i j
    rw [← Complex.cpow_add _ _ (hne n hn)]
    congr 1
    push_cast
    ring
  have hnorm : ∀ n ∈ N,
      ((‖∑ i, η i * (n : ℂ) ^ (Complex.I * (t i : ℂ))‖ ^ 2 : ℝ) : ℂ)
      = ∑ i, ∑ j, η i * (starRingEnd ℂ) (η j) *
          ((n : ℂ) ^ (Complex.I * ((t i - t j : ℝ) : ℂ))) := by
    intro n hn
    have hsq : ((‖∑ i, η i * (n : ℂ) ^ (Complex.I * (t i : ℂ))‖ ^ 2 : ℝ) : ℂ)
        = (∑ i, η i * (n : ℂ) ^ (Complex.I * (t i : ℂ))) *
          (starRingEnd ℂ) (∑ i, η i * (n : ℂ) ^ (Complex.I * (t i : ℂ))) := by
      rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj]
    rw [hsq]
    have hstar : (starRingEnd ℂ) (∑ i, η i * (n : ℂ) ^ (Complex.I * (t i : ℂ)))
        = ∑ j, (starRingEnd ℂ) (η j) * ((n : ℂ) ^ (-(Complex.I * (t j : ℂ)))) := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro j _
      rw [map_mul, star_natCast_cpow, hstarI j]
    rw [hstar, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [show (η i * (n : ℂ) ^ (Complex.I * (t i : ℂ))) *
          ((starRingEnd ℂ) (η j) * (n : ℂ) ^ (-(Complex.I * (t j : ℂ))))
        = η i * (starRingEnd ℂ) (η j) *
          ((n : ℂ) ^ (Complex.I * (t i : ℂ)) * (n : ℂ) ^ (-(Complex.I * (t j : ℂ)))) by ring]
    rw [hpow n hn i j]
  trans ∑ n ∈ N, ∑ i, ∑ j, c n * (η i * (starRingEnd ℂ) (η j) *
        ((n : ℂ) ^ (Complex.I * ((t i - t j : ℝ) : ℂ))))
  · apply Finset.sum_congr rfl
    intro n hn
    rw [hnorm n hn, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.mul_sum]
  · rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    have hfac : (∑ x ∈ N, c x * (η i * (starRingEnd ℂ) (η j) *
            ↑x ^ (Complex.I * ↑(t i - t j))))
        = ∑ x ∈ N, (η i * (starRingEnd ℂ) (η j)) *
            (c x * ↑x ^ (Complex.I * ↑(t i - t j))) :=
      Finset.sum_congr rfl (fun x _ => by ring)
    rw [hfac, Finset.mul_sum]

end Work.BMF.mr_direct
