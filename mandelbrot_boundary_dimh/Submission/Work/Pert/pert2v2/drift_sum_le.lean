import Mathlib
import Submission.Work.Pert.pert2v2.walk_right_deep

namespace Work.Pert.pert2v2

theorem drift_sum_le {Ξ : ℝ} {α ρ : ℂ} {M κ Y : ℝ} {F Φ : ℂ → ℂ} {w : ℕ → ℂ} {N : ℕ}
    (hM : 0 ≤ M) (hρ : ‖ρ - 1‖ ≤ 1 / 32)
    (hdec : ∀ z ∈ Work.Pert.Qm Ξ α, z.im < -Y →
      ‖F z - (z + ρ)‖ ≤ M * Real.exp (κ * z.im))
    (hstep : ∀ n < N, w (n + 1) ∈ Work.Pert.Qm Ξ α ∧ F (w (n + 1)) = w n ∧
      Φ (w (n + 1)) = Φ (w n) - 1 ∧ ‖w (n + 1) - (w n - 1)‖ ≤ 1 / 32)
    (hY : ∀ n < N, (w (n + 1)).im < -Y) :
    ‖(Φ (w N) - w N / ρ) - (Φ (w 0) - w 0 / ρ)‖ ≤
      M / ‖ρ‖ * ∑ n ∈ Finset.range N, Real.exp (κ * (w (n + 1)).im) := by
  -- `‖ρ - 1‖ ≤ 1/32` forces `ρ ≠ 0`, so that the drift `Φ (w n) - w n / ρ` is well posed.
  have hρnorm : (31 : ℝ) / 32 ≤ ‖ρ‖ := by
    have h1 : |‖ρ‖ - ‖(1 : ℂ)‖| ≤ ‖ρ - 1‖ := abs_norm_sub_norm_le ρ 1
    rw [norm_one] at h1
    have h2 : -(‖ρ‖ - 1) ≤ 1 / 32 := by
      have := neg_le_abs (‖ρ‖ - 1)
      linarith
    linarith
  have hρ0 : ρ ≠ 0 := by
    intro h; rw [h] at hρnorm; norm_num at hρnorm
  -- One step: the drift difference is `-(F (w (n+1)) - (w (n+1) + ρ)) / ρ`.
  have key : ∀ n < N, ‖(Φ (w n) - w n / ρ) - (Φ (w (n + 1)) - w (n + 1) / ρ)‖
      ≤ M / ‖ρ‖ * Real.exp (κ * (w (n + 1)).im) := by
    intro n hn
    obtain ⟨hwQ, hFw, hΦw, -⟩ := hstep n hn
    have hb := hdec (w (n + 1)) hwQ (hY n hn)
    have hrew : (Φ (w n) - w n / ρ) - (Φ (w (n + 1)) - w (n + 1) / ρ)
        = -((F (w (n + 1)) - (w (n + 1) + ρ)) / ρ) := by
      rw [hFw, hΦw]
      field_simp
      ring
    rw [hrew, norm_neg, norm_div, div_eq_mul_inv, div_eq_mul_inv]
    calc ‖F (w (n + 1)) - (w (n + 1) + ρ)‖ * ‖ρ‖⁻¹
        ≤ (M * Real.exp (κ * (w (n + 1)).im)) * ‖ρ‖⁻¹ :=
          mul_le_mul_of_nonneg_right hb (by positivity)
      _ = M * ‖ρ‖⁻¹ * Real.exp (κ * (w (n + 1)).im) := by ring
  -- Telescoping of the one-step differences.
  have hsum : (∑ n ∈ Finset.range N,
        ((Φ (w n) - w n / ρ) - (Φ (w (n + 1)) - w (n + 1) / ρ)))
      = -((Φ (w N) - w N / ρ) - (Φ (w 0) - w 0 / ρ)) := by
    rw [Finset.sum_range_sub']
    ring
  calc ‖(Φ (w N) - w N / ρ) - (Φ (w 0) - w 0 / ρ)‖
      = ‖∑ n ∈ Finset.range N,
          ((Φ (w n) - w n / ρ) - (Φ (w (n + 1)) - w (n + 1) / ρ))‖ := by
        rw [hsum, norm_neg]
    _ ≤ ∑ n ∈ Finset.range N,
          ‖(Φ (w n) - w n / ρ) - (Φ (w (n + 1)) - w (n + 1) / ρ)‖ := norm_sum_le _ _
    _ ≤ ∑ n ∈ Finset.range N, M / ‖ρ‖ * Real.exp (κ * (w (n + 1)).im) :=
        Finset.sum_le_sum (fun n hn => key n (Finset.mem_range.mp hn))
    _ = M / ‖ρ‖ * ∑ n ∈ Finset.range N, Real.exp (κ * (w (n + 1)).im) := by
        rw [Finset.mul_sum]

end Work.Pert.pert2v2
