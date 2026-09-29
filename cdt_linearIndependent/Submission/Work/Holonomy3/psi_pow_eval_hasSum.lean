import Mathlib

namespace Work.Holonomy3

/-- If the power series `ψ` evaluates at `z` to `w` and every power series `ψ ^ d` is absolutely
summable at `z`, then the `d`-th power evaluates to `w ^ d`.  The proof is by induction on `d`,
writing `ψ ^ (d+1) = ψ ^ d * ψ` and using the Cauchy product formula for absolutely summable
series (`tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm`), together with
`PowerSeries.coeff_mul`. -/
theorem psi_pow_eval_hasSum {ψ : PowerSeries ℂ} {z w : ℂ}
    (hψ : HasSum (fun j : ℕ => PowerSeries.coeff j ψ * z ^ j) w)
    (hs : ∀ d : ℕ, Summable (fun k : ℕ => ‖PowerSeries.coeff k (ψ ^ d) * z ^ k‖)) :
    ∀ d : ℕ, HasSum (fun k : ℕ => PowerSeries.coeff k (ψ ^ d) * z ^ k) (w ^ d) := by
  intro d
  induction d with
  | zero =>
    have h0 : (fun k : ℕ => PowerSeries.coeff k ((ψ : PowerSeries ℂ) ^ 0) * z ^ k)
        = fun k : ℕ => if k = 0 then (1 : ℂ) else 0 := by
      funext k
      rw [pow_zero, PowerSeries.coeff_one]
      by_cases hk : k = 0
      · subst hk; simp
      · simp [hk]
    rw [h0, pow_zero]
    simpa using (hasSum_ite_eq (0 : ℕ) (1 : ℂ))
  | succ d ih =>
    have hbd : Summable (fun k : ℕ => ‖PowerSeries.coeff k (ψ ^ d) * z ^ k‖) := hs d
    have ha : Summable (fun k : ℕ => ‖PowerSeries.coeff k ψ * z ^ k‖) := by
      simpa using hs 1
    have hterm : ∀ k : ℕ,
        PowerSeries.coeff k (ψ ^ (d + 1)) * z ^ k
          = ∑ kl ∈ Finset.HasAntidiagonal.antidiagonal k,
              (PowerSeries.coeff kl.1 (ψ ^ d) * z ^ kl.1) * (PowerSeries.coeff kl.2 ψ * z ^ kl.2) := by
      intro k
      rw [pow_succ, PowerSeries.coeff_mul, Finset.sum_mul]
      refine Finset.sum_congr rfl (fun kl hkl => ?_)
      rw [Finset.HasAntidiagonal.mem_antidiagonal] at hkl
      rw [← hkl, pow_add]
      ring
    have hprod := tsum_mul_tsum_eq_tsum_sum_antidiagonal_of_summable_norm hbd ha
    have hb : ∑' k : ℕ, PowerSeries.coeff k (ψ ^ (d + 1)) * z ^ k = w ^ (d + 1) := by
      rw [tsum_congr hterm]
      rw [← hprod, ih.tsum_eq, hψ.tsum_eq, pow_succ]
    have hsummable : Summable (fun k : ℕ => PowerSeries.coeff k (ψ ^ (d + 1)) * z ^ k) :=
      (hs (d + 1)).of_norm
    rw [← hb]
    exact hsummable.hasSum

end Work.Holonomy3
