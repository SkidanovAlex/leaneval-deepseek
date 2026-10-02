import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.SeedCertRay

/-- Difference of powers bound: if `‖z‖ ≤ M` and `‖w‖ ≤ M` with `0 ≤ M`, then
`‖z^(k+1) - w^(k+1)‖ ≤ ‖z - w‖ * (k+1) * M^k`.  (A telescoping/induction bound on the
differentiated geometric series.) -/
lemma norm_pow_sub_pow_le (z w : ℂ) {M : ℝ} (hM : 0 ≤ M) (hz : ‖z‖ ≤ M) (hw : ‖w‖ ≤ M) :
    ∀ k : ℕ, ‖z^(k+1) - w^(k+1)‖ ≤ ‖z - w‖ * ((k:ℝ)+1) * M^k := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    have h1 : z^(k+1+1) - w^(k+1+1) = z*(z^(k+1) - w^(k+1)) + (z - w)*w^(k+1) := by ring
    rw [h1]
    have step1 : ‖z * (z ^ (k + 1) - w ^ (k + 1)) + (z - w) * w ^ (k + 1)‖
        ≤ ‖z‖ * ‖z ^ (k + 1) - w ^ (k + 1)‖ + ‖z - w‖ * ‖w ^ (k + 1)‖ := by
      calc ‖z * (z^(k+1) - w^(k+1)) + (z - w)*w^(k+1)‖
          ≤ ‖z * (z^(k+1) - w^(k+1))‖ + ‖(z - w)*w^(k+1)‖ := norm_add_le _ _
        _ = ‖z‖ * ‖z^(k+1) - w^(k+1)‖ + ‖z - w‖ * ‖w^(k+1)‖ := by rw [norm_mul, norm_mul]
    refine le_trans step1 ?_
    have hA : ‖z ^ (k + 1) - w ^ (k + 1)‖ ≤ ‖z - w‖ * ((k:ℝ)+1) * M^k := ih
    have hB : ‖w^(k+1)‖ ≤ M^(k+1) := by
      rw [norm_pow]; exact pow_le_pow_left₀ (norm_nonneg w) hw (k+1)
    have hm1 : ‖z‖ * ‖z^(k+1)-w^(k+1)‖ ≤ M * (‖z-w‖ * ((k:ℝ)+1) * M^k) :=
      mul_le_mul hz hA (norm_nonneg _) hM
    have hm2 : ‖z-w‖ * ‖w^(k+1)‖ ≤ ‖z-w‖ * M^(k+1) :=
      mul_le_mul_of_nonneg_left hB (norm_nonneg _)
    refine le_trans (add_le_add hm1 hm2) ?_
    have key : M * (‖z - w‖ * ((k:ℝ)+1) * M^k) + ‖z - w‖ * M^(k+1)
        = ‖z - w‖ * (((k+1 : ℕ) : ℝ) + 1) * M^(k+1) := by
      push_cast
      ring
    exact le_of_eq key

/-- Termwise Taylor bound: for `‖z‖, ‖w‖ ≤ 53/10`, the `(k+1)`-st Taylor term of `exp`
differs by at most `‖z - w‖ * (53/10)^k / k!`. -/
lemma norm_taylor_term_le (z w : ℂ) (hz : ‖z‖ ≤ 53/10) (hw : ‖w‖ ≤ 53/10) (k : ℕ) :
    ‖(z^(k+1) - w^(k+1)) / (((k+1).factorial : ℕ) : ℂ)‖
      ≤ ‖z - w‖ * ((53/10)^k / ((k.factorial : ℝ))) := by
  have hM : (0:ℝ) ≤ 53/10 := by norm_num
  have h := norm_pow_sub_pow_le z w hM hz hw k
  rw [norm_div, Complex.norm_natCast]
  have hfac : (((k+1).factorial : ℕ) : ℝ) = ((k:ℝ)+1) * ((k.factorial : ℕ) : ℝ) := by
    rw [Nat.factorial_succ, Nat.cast_mul]
    push_cast
    ring
  rw [hfac]
  calc ‖z ^ (k + 1) - w ^ (k + 1)‖ / (((k:ℝ)+1) * ((k.factorial : ℕ) : ℝ))
      ≤ (‖z - w‖ * ((k:ℝ)+1) * (53/10)^k) / (((k:ℝ)+1) * ((k.factorial : ℕ) : ℝ)) :=
        div_le_div_of_nonneg_right h (by positivity)
    _ = ‖z - w‖ * ((53/10)^k / ((k.factorial : ℕ) : ℝ)) := by
        field_simp

/-- Partial Taylor-sum difference bound: on the disk of radius `53/10`, the first `24`
Taylor terms of `exp` are Lipschitz with constant `250`. -/
theorem norm_sum_taylor_diff_le {z w : ℂ} (hz : ‖z‖ ≤ 53/10) (hw : ‖w‖ ≤ 53/10) :
    ‖∑ k ∈ Finset.range 24, (z^k - w^k) / ((k.factorial : ℕ) : ℂ)‖ ≤ ‖z - w‖ * 250 := by
  have h1 : ‖∑ k ∈ Finset.range 24, (z^k - w^k)/((k.factorial : ℕ):ℂ)‖
      ≤ ∑ k ∈ Finset.range 23, ‖(z^(k+1) - w^(k+1)) / (((k+1).factorial : ℕ) : ℂ)‖ := by
    calc ‖∑ k ∈ Finset.range 24, (z^k - w^k)/((k.factorial:ℕ):ℂ)‖
        ≤ ∑ k ∈ Finset.range 24, ‖(z^k - w^k)/((k.factorial:ℕ):ℂ)‖ := norm_sum_le _ _
      _ = ∑ k ∈ Finset.range 23, ‖(z^(k+1) - w^(k+1))/(((k+1).factorial:ℕ):ℂ)‖
            + ‖(z^0 - w^0)/(((0).factorial:ℕ):ℂ)‖ := by rw [Finset.sum_range_succ']
      _ = ∑ k ∈ Finset.range 23, ‖(z^(k+1) - w^(k+1))/(((k+1).factorial:ℕ):ℂ)‖ := by simp
  refine le_trans h1 ?_
  have h2 : ∑ k ∈ Finset.range 23, ‖(z^(k+1) - w^(k+1))/(((k+1).factorial:ℕ):ℂ)‖
      ≤ ∑ k ∈ Finset.range 23, ‖z - w‖ * ((53/10)^k / ((k.factorial:ℕ):ℝ)) :=
    Finset.sum_le_sum (fun k _ => norm_taylor_term_le z w hz hw k)
  refine le_trans h2 ?_
  have h3 : ∑ k ∈ Finset.range 23, ‖z - w‖ * ((53/10)^k / ((k.factorial:ℕ):ℝ))
      = ‖z - w‖ * ∑ k ∈ Finset.range 23, (53/10)^k / ((k.factorial:ℕ):ℝ) := by
    rw [Finset.mul_sum]
  rw [h3]
  have h4 : (∑ k ∈ Finset.range 23, ((53:ℝ)/10)^k / ((k.factorial:ℕ):ℝ)) ≤ 250 := by norm_num
  exact mul_le_mul_of_nonneg_left h4 (norm_nonneg _)

end Work.SeedCertRay
