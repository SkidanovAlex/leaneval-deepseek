import Mathlib
import Submission.Work.TMC16Core.Defs

namespace Work.Assembly

/-- **Logarithmic bound on the Diophantine denominators.**

Assume `α` satisfies the Diophantine condition `DiophBelow α b₀`, i.e. for all large `k`
one has `exp(-(b₀ k)) ≤ fracDist (k α)`, and let `q` be a strictly increasing sequence of
positive naturals whose fractional distances `Δ i = fracDist (q i α)` beat the next
denominator, `Δ i < 1 / q (i+1)`.  Then eventually `log (q n) < b₀ * q (n-1)`.

Indeed, for large `n` we may evaluate the Diophantine bound at `k = q (n-1)`:
`exp (-(b₀ * q (n-1))) ≤ fracDist (q (n-1) α) = Δ (n-1) < 1 / q n`, hence
`q n < exp (b₀ * q (n-1))` and taking logarithms gives the claim. -/
theorem nr_log_qn_bound {α b₀ : ℝ} {q : ℕ → ℕ} {Δ : ℕ → ℝ}
    (hb₀ : 0 < b₀) (hDioph : Work.TMC16Core.DiophBelow α b₀) (hmono : StrictMono q)
    (hqpos : ∀ i, 0 < q i)
    (hΔeq : ∀ i, Δ i = Work.TMC16Core.fracDist ((q i : ℝ) * α))
    (hΔup : ∀ i, Δ i < 1 / ((q (i + 1) : ℝ))) :
    ∃ N : ℕ, ∀ n ≥ N, Real.log (q n : ℝ) < b₀ * (q (n - 1) : ℝ) := by
  -- unfold the "eventually" Diophantine condition into a threshold `K`
  unfold Work.TMC16Core.DiophBelow at hDioph
  obtain ⟨K, hK⟩ := Filter.eventually_atTop.mp hDioph
  refine ⟨K + 1, ?_⟩
  intro n hn
  have hnpos : 0 < n := by omega
  -- `q` is strictly increasing on `ℕ`, hence dominates the identity
  have hid : ∀ m, m ≤ q m := fun m => StrictMono.id_le hmono m
  have hqge : K ≤ q (n - 1) := by
    have h1 : K ≤ n - 1 := by omega
    have h2 : n - 1 ≤ q (n - 1) := hid (n - 1)
    omega
  -- evaluate the Diophantine bound at `k = q (n-1)`
  have hstep1 : Real.exp (-(b₀ * (q (n - 1) : ℝ))) ≤ Δ (n - 1) := by
    rw [hΔeq (n - 1)]
    exact hK (q (n - 1)) hqge
  -- the fractional distance is smaller than the reciprocal of the next denominator
  have hstep2 : Δ (n - 1) < 1 / (q n : ℝ) := by
    have hpred : n - 1 + 1 = n := by omega
    have := hΔup (n - 1)
    rwa [hpred] at this
  have hlt : Real.exp (-(b₀ * (q (n - 1) : ℝ))) < 1 / (q n : ℝ) :=
    lt_of_le_of_lt hstep1 hstep2
  have hqposn : (0 : ℝ) < (q n : ℝ) := by exact_mod_cast hqpos n
  -- convert `exp (-x) < 1/y` into `y < exp x`
  have hexp : (q n : ℝ) < Real.exp (b₀ * (q (n - 1) : ℝ)) := by
    rw [one_div, Real.exp_neg] at hlt
    exact (inv_lt_inv₀ (Real.exp_pos _) hqposn).mp hlt
  -- take logarithms
  exact (Real.log_lt_iff_lt_exp hqposn).mpr hexp

end Work.Assembly
