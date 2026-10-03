import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Parab.leftCoord.sum_inv_norm_le_log

namespace Work.Analysis.PertCrux

/-- `‖τ₀ z‖ = 1/‖z‖`: the `τ₀`-chart inverts the modulus. -/
private lemma norm_tau0 (z : ℂ) : ‖MandelDim.tau0 z‖ = 1 / ‖z‖ := by
  simp [MandelDim.tau0]

/-- Core log bound on a nonzero segment of a small parabolic orbit.  Let `0 < ε` with
`Kc * ε ≤ 1/2`, and suppose the `τ₀`-chart (`τ₀ z = -1/z`) is a translation by `1` up to `Kc ‖z‖`
on the disc of radius `ε`.  If `x` is an orbit of `f₀` (`x (n+1) = f₀ (x n)`) whose entries on the
whole segment `[N, L)` are nonzero and of norm `< ε`, then `∑_{j ∈ [N,L)} ‖x j‖` is bounded by
`C (1 + log (L - N + 1))` for a constant `C ≥ 0` depending only on `ε`.  (Put `w j' = τ₀ (x (N+j'))`
and apply `Work.Parab.leftCoord.sum_inv_norm_le_log` with `c = 1/2`, `R = 1/ε`: the real parts
increase by `1/2` because the orbit relation turns the chart-error hypothesis at `x (N+j')` into
the increment estimate for `w`.) -/
theorem sum_Ico_norm_le_log {f₀ : ℂ → ℂ} {ε Kc : ℝ} (hε : 0 < ε) (hKc : 0 ≤ Kc)
    (hKε : Kc * ε ≤ 1 / 2)
    (hstep : ∀ z : ℂ, 0 < ‖z‖ → ‖z‖ ≤ ε →
      ‖MandelDim.tau0 (f₀ z) - MandelDim.tau0 z - 1‖ ≤ Kc * ‖z‖) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (x : ℕ → ℂ) (N L : ℕ),
      (∀ n : ℕ, x (n + 1) = f₀ (x n)) →
      (∀ j : ℕ, N ≤ j → j < L → x j ≠ 0) →
      (∀ j : ℕ, N ≤ j → j < L → ‖x j‖ < ε) →
      ∑ j ∈ Finset.Ico N L, ‖x j‖ ≤ C * (1 + Real.log (((L - N : ℕ) : ℝ) + 1)) := by
  -- The harmonic bound for a walk whose real part increases by `1/2` and which stays outside
  -- the disc of radius `1/ε`.
  obtain ⟨C, hC0, hC⟩ := Work.Parab.leftCoord.sum_inv_norm_le_log (c := 1 / 2) (R := 1 / ε)
    (by norm_num) (one_div_pos.mpr hε)
  refine ⟨C, hC0, ?_⟩
  intro x N L hrec hne hsmall
  -- the chart image of the segment
  let w : ℕ → ℂ := fun j => MandelDim.tau0 (x (N + j))
  have hw : ∀ j : ℕ, w j = MandelDim.tau0 (x (N + j)) := fun j => rfl
  have hcard : ∀ j : ℕ, j < L - N → N + j < L := by intro j hj; omega
  -- the walk is outside the disc of radius `1/ε`
  have hnorm : ∀ j < L - N, 1 / ε ≤ ‖w j‖ := by
    intro j hj
    have hnn : N ≤ N + j := Nat.le_add_right N j
    have hz0 : 0 < ‖x (N + j)‖ := norm_pos_iff.mpr (hne (N + j) hnn (hcard j hj))
    have hzε : ‖x (N + j)‖ ≤ ε := le_of_lt (hsmall (N + j) hnn (hcard j hj))
    rw [hw j, norm_tau0]
    exact one_div_le_one_div_of_le hz0 hzε
  -- the walk moves right by at least `1/2` per step
  have hmono : ∀ j < L - N, (w j).re + 1 / 2 ≤ (w (j + 1)).re := by
    intro j hj
    have hnn : N ≤ N + j := Nat.le_add_right N j
    have hjL := hcard j hj
    have hz0 : 0 < ‖x (N + j)‖ := norm_pos_iff.mpr (hne (N + j) hnn hjL)
    have hzε : ‖x (N + j)‖ ≤ ε := le_of_lt (hsmall (N + j) hnn hjL)
    -- the chart-error hypothesis at the orbit point `x (N+j)` gives the increment of `w`
    have hb := hstep (x (N + j)) hz0 hzε
    have hw1 : w (j + 1) = MandelDim.tau0 (f₀ (x (N + j))) := by
      rw [hw (j + 1), show N + (j + 1) = N + j + 1 from by omega, hrec (N + j)]
    have hnormb : ‖w (j + 1) - w j - 1‖ ≤ Kc * ε := by
      rw [hw1, hw j]
      exact le_trans hb (mul_le_mul_of_nonneg_left hzε hKc)
    have hre : -‖w (j + 1) - w j - 1‖ ≤ (w (j + 1) - w j - 1).re := by
      have h := Complex.abs_re_le_norm (w (j + 1) - w j - 1)
      rw [abs_le] at h
      linarith [h.1]
    have hsub : (w (j + 1) - w j - 1).re = (w (j + 1)).re - (w j).re - 1 := by simp
    linarith [hre, hnormb, hKε]
  have hsum := hC w (L - N) hnorm hmono
  -- reindex the segment sum and replace `‖x (N+j)‖` by `1/‖w j‖`
  calc ∑ j ∈ Finset.Ico N L, ‖x j‖
      = ∑ j ∈ Finset.range (L - N), ‖x (N + j)‖ :=
        Finset.sum_Ico_eq_sum_range (fun j => ‖x j‖) N L
    _ = ∑ j ∈ Finset.range (L - N), 1 / ‖w j‖ := by
        apply Finset.sum_congr rfl
        intro j _
        rw [hw j, norm_tau0, one_div_one_div]
    _ ≤ C * (1 + Real.log (((L - N : ℕ) : ℝ) + 1)) := hsum

end Work.Analysis.PertCrux
