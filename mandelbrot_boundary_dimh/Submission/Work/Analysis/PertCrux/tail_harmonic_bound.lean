import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.Analysis.PertCrux.sum_Ico_norm_le_log
import Submission.Work.Analysis.PertCrux.exists_cut

namespace Work.Analysis.PertCrux

/-- Harmonic bound for the tail of a small parabolic orbit.  Let `f₀` have `f₀ 0 = 0`, let
`0 < ε` with `Kc * ε ≤ 1/2`, and suppose the `τ₀`-chart (`τ₀ z = -1/z`) is a translation by `1` up
to `Kc ‖z‖` on the disc of radius `ε`:
`∀ z, 0 < ‖z‖ → ‖z‖ ≤ ε → ‖τ₀ (f₀ z) - τ₀ z - 1‖ ≤ Kc ‖z‖`.
Let `x` be an orbit of `f₀` (`x (n+1) = f₀ (x n)`) which from time `N` on is small
(`∀ n ≥ N, ‖x n‖ < ε`).  Then
`∃ C ≥ 0, ∀ m, ∑_{j ∈ [N,m)} ‖x j‖ ≤ C (1 + log (m+1))`,
with `C` independent of the orbit `x`.  (Proved by putting `ψ j = τ₀ (x j)`, showing
`|ψ j| ≥ 1/ε` and `Re ψ (j+1) ≥ Re ψ j + 1/2` on the small part, and applying
`Work.Parab.leftCoord.sum_inv_norm_le_log` with `c = 1/2`, `R = 1/ε`; the vanishing locus of `x`
is an upper set because `f₀ 0 = 0`, which is the one case distinction needed.) -/
theorem tail_harmonic_bound {f₀ : ℂ → ℂ} {N : ℕ} {ε Kc : ℝ}
    (hε : 0 < ε) (hKc : 0 ≤ Kc) (hKε : Kc * ε ≤ 1 / 2) (hf0 : f₀ 0 = 0)
    (hstep : ∀ z : ℂ, 0 < ‖z‖ → ‖z‖ ≤ ε →
      ‖MandelDim.tau0 (f₀ z) - MandelDim.tau0 z - 1‖ ≤ Kc * ‖z‖) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (x : ℕ → ℂ),
      (∀ n : ℕ, x (n + 1) = f₀ (x n)) →
      (∀ n : ℕ, N ≤ n → ‖x n‖ < ε) →
      ∀ m : ℕ, ∑ j ∈ Finset.Ico N m, ‖x j‖ ≤ C * (1 + Real.log ((m : ℝ) + 1)) := by
  -- The chart estimate gives a logarithmic bound on every nonzero initial segment of an orbit.
  obtain ⟨C₀, hC₀nn, hC₀⟩ := sum_Ico_norm_le_log (f₀ := f₀) hε hKc hKε hstep
  refine ⟨C₀, hC₀nn, ?_⟩
  intro x hx hsmall m
  rcases lt_or_ge m N with hmN | hNm
  · -- No indices at all: the sum is empty.
    have hempty : Finset.Ico N m = ∅ := Finset.Ico_eq_empty (not_lt.mpr (le_of_lt hmN))
    rw [hempty, Finset.sum_empty]
    refine mul_nonneg hC₀nn ?_
    have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
    have := Real.log_nonneg (show (1 : ℝ) ≤ (m : ℝ) + 1 by linarith)
    linarith
  · by_cases hex : ∃ j : ℕ, N ≤ j ∧ x j = 0
    · -- The orbit vanishes at some time `≥ N`: cut at the first such time.
      obtain ⟨L, _hNL, hLm, hnz, hsum⟩ := exists_cut hf0 hx hNm hex
      rw [hsum]
      refine (hC₀ x N L hx hnz (fun j hNj _ => hsmall j hNj)).trans ?_
      apply mul_le_mul_of_nonneg_left _ hC₀nn
      have hle : ((L - N : ℕ) : ℝ) + 1 ≤ (m : ℝ) + 1 := by
        have h : ((L - N : ℕ) : ℝ) ≤ (m : ℝ) := by
          have h' : L - N ≤ m := le_trans (Nat.sub_le L N) hLm
          exact_mod_cast h'
        linarith
      have hpos : (0 : ℝ) < ((L - N : ℕ) : ℝ) + 1 := by positivity
      linarith [Real.log_le_log hpos hle]
    · -- The orbit never vanishes on `[N, ∞)`: the whole segment `[N, m)` is nonzero.
      have hnz : ∀ j : ℕ, N ≤ j → j < m → x j ≠ 0 := fun j hNj hjm hxj => hex ⟨j, hNj, hxj⟩
      refine (hC₀ x N m hx hnz (fun j hNj _ => hsmall j hNj)).trans ?_
      apply mul_le_mul_of_nonneg_left _ hC₀nn
      have hle : ((m - N : ℕ) : ℝ) + 1 ≤ (m : ℝ) + 1 := by
        have h' : m - N ≤ m := Nat.sub_le m N
        exact_mod_cast Nat.add_le_add_right h' 1
      have hpos : (0 : ℝ) < ((m - N : ℕ) : ℝ) + 1 := by positivity
      linarith [Real.log_le_log hpos hle]

end Work.Analysis.PertCrux
