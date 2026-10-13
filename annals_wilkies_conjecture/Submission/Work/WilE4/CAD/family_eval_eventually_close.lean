import Mathlib

open scoped BigOperators

namespace Work.WilE4.CAD

/-- Uniform closeness of `(p x).eval ·` to `(p x₀).eval ·` on the disk `‖z‖ ≤ K`, for a family of
complex polynomials whose coefficients depend continuously on the parameter and whose degree is
eventually bounded by `d`.  The polynomials of degree `≤ d` form a finite-dimensional space, so
coefficientwise convergence at `x₀` upgrades to uniform convergence on the compact disk. -/
theorem family_eval_eventually_close {m : ℕ} (p : (Fin m → ℝ) → Polynomial ℂ) (d : ℕ)
    (hcont : ∀ k : ℕ, Continuous fun x : Fin m → ℝ => (p x).coeff k) (x₀ : Fin m → ℝ)
    (hdeg : ∀ᶠ x in nhds x₀, (p x).natDegree ≤ d)
    (K : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ x in nhds x₀, ∀ z : ℂ, ‖z‖ ≤ K → ‖(p x).eval z - (p x₀).eval z‖ ≤ ε := by
  -- A nonnegative bound `K'` for `‖z‖`, and a positive "weight" `C` dominating `‖z‖ ^ i ≤ C`
  -- for every `i ≤ d` and every `‖z‖ ≤ K`.
  set K' : ℝ := max K 0 with hK'def
  have hK'0 : 0 ≤ K' := le_max_right K 0
  set C : ℝ := (K' + 1) ^ d with hCdef
  have hCpos : 0 < C := by
    rw [hCdef]
    exact pow_pos (by linarith) d
  -- The requested bound `δ` on the coefficientwise difference.
  set δ : ℝ := ε / (((d : ℝ) + 1) * C) with hδdef
  have hδpos : 0 < δ := by
    rw [hδdef]
    exact div_pos hε (mul_pos (by positivity) hCpos)
  -- The degree bound also holds at `x₀` itself.
  have hdeg0 : (p x₀).natDegree ≤ d := hdeg.self_of_nhds
  -- Coefficients converge (indeed are continuous) at `x₀`, hence are eventually `δ`-close.
  have hcoeff : ∀ᶠ x in nhds x₀, ∀ i : Fin (d + 1),
      ‖(p x).coeff i.val - (p x₀).coeff i.val‖ ≤ δ := by
    rw [Filter.eventually_all]
    intro i
    have hci : Continuous fun x => (p x).coeff i.val - (p x₀).coeff i.val :=
      (hcont i.val).sub continuous_const
    have htend : Filter.Tendsto (fun x => (p x).coeff i.val - (p x₀).coeff i.val)
        (nhds x₀) (nhds 0) := by
      have h := hci.tendsto x₀
      rw [sub_self] at h
      exact h
    have hev := (Metric.tendsto_nhds.mp htend) δ hδpos
    filter_upwards [hev] with x hx
    rw [dist_zero_right] at hx
    exact le_of_lt hx
  filter_upwards [hdeg, hcoeff] with x hxdeg hxcoeff z hz
  -- Near `x₀` both `p x` and `p x₀` have degree at most `d`, so their difference can be written
  -- as a sum over the `d+1` low-degree coefficients.
  have hPdeg : (p x - p x₀).natDegree ≤ d :=
    (Polynomial.natDegree_sub_le _ _).trans (max_le hxdeg hdeg0)
  have hlt : (p x - p x₀).natDegree < d + 1 := Nat.lt_succ_of_le hPdeg
  have heval : (p x).eval z - (p x₀).eval z
      = (Finset.range (d + 1)).sum (fun i => ((p x).coeff i - (p x₀).coeff i) * z ^ i) := by
    rw [← Polynomial.eval_sub,
      Polynomial.eval_eq_sum_range' (p := p x - p x₀) (n := d + 1) hlt z]
    exact Finset.sum_congr rfl (fun i _ => by rw [Polynomial.coeff_sub])
  rw [heval]
  calc ‖(Finset.range (d + 1)).sum (fun i => ((p x).coeff i - (p x₀).coeff i) * z ^ i)‖
      ≤ (Finset.range (d + 1)).sum (fun i => ‖((p x).coeff i - (p x₀).coeff i) * z ^ i‖) :=
        norm_sum_le _ _
    _ ≤ (Finset.range (d + 1)).sum (fun _ => δ * C) := by
        apply Finset.sum_le_sum
        intro i hi
        rw [norm_mul, norm_pow]
        have h1 : ‖(p x).coeff i - (p x₀).coeff i‖ ≤ δ :=
          hxcoeff ⟨i, Finset.mem_range.mp hi⟩
        have hzi : ‖z‖ ^ i ≤ C := by
          have hle1 : ‖z‖ ≤ K' := le_trans hz (le_max_left K 0)
          calc ‖z‖ ^ i ≤ (K' + 1) ^ i :=
                pow_le_pow_left₀ (norm_nonneg z) (by linarith) i
            _ ≤ (K' + 1) ^ d :=
                pow_le_pow_right₀ (by linarith) (Nat.lt_succ_iff.mp (Finset.mem_range.mp hi))
            _ = C := by rw [hCdef]
        exact mul_le_mul h1 hzi (by positivity) hδpos.le
    _ = ε := by
        have hne : ((d : ℝ) + 1) * C ≠ 0 := ne_of_gt (mul_pos (by positivity) hCpos)
        rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, hδdef]
        push_cast
        field_simp

end Work.WilE4.CAD
