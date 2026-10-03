import Mathlib
import Submission.Work.FIRed6Axis.Statement
import Submission.Work.FITop4.Red5.piecesSetup

namespace Work.FIRed6Axis

/-- **`NearMassBound` applied to a subset of the primary annulus.**  Let `hmass` be the body of
`Work.FIRed6Axis.NearMassBound` after unfolding (the mass bound with constant `Cmass`).  If `T` is a
finite set of Gaussian integers each lying in `primAnn (2N)` and satisfying
`N < |z|²`, `Squarefree (|z|²)` and `nearArg (4ϑ) z`, then

  `Σ_{z∈T} τ(|z|²) ≤ Cmass·(ϑN + √N + N^{5/6} + N^{2/3} + 1)·(log(2+N))^{20}`.

This is immediate from `hmass`: `z ∈ primAnn (2N)` gives `|z|² ≤ 2N`, and the three extra clauses
are hypotheses; the only work is the cast `(|z|² : ℝ) ≤ 2·(N:ℝ)` and instantiating `hmass` at the
real `N := (N:ℝ)`. -/
lemma nearMass_tau_sum_le
    {Cmass : ℝ}
    (hmass : ∀ (N ϑ : ℝ) (T : Finset GaussianInt),
      1 ≤ N → 0 < ϑ → ϑ ≤ 1 →
      (∀ z ∈ T, N < (Work.FIPlan.gnorm z : ℝ) ∧ (Work.FIPlan.gnorm z : ℝ) ≤ 2 * N ∧
        Squarefree (Work.FIPlan.gnorm z) ∧ nearArg (4 * ϑ) z) →
      ∑ z ∈ T, (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ)
        ≤ Cmass * (ϑ * N + Real.sqrt N + N ^ ((5 : ℝ) / 6) + N ^ ((2 : ℝ) / 3) + 1)
            * (Real.log (2 + N)) ^ (20 : ℕ))
    {N : ℕ} {ϑ : ℝ} (hN : 1 ≤ N) (hϑ0 : 0 < ϑ) (hϑ1 : ϑ ≤ 1) (T : Finset GaussianInt)
    (hT : ∀ z ∈ T, z ∈ Work.FITop4.Red5.primAnn (2 * N) ∧ N < Work.FIPlan.gnorm z ∧
      Squarefree (Work.FIPlan.gnorm z) ∧ nearArg (4 * ϑ) z) :
    ∑ z ∈ T, (((Work.FIPlan.gnorm z).divisors.card : ℕ) : ℝ)
      ≤ Cmass * (ϑ * (N : ℝ) + Real.sqrt (N : ℝ) + (N : ℝ) ^ ((5 : ℝ) / 6)
          + (N : ℝ) ^ ((2 : ℝ) / 3) + 1) * (Real.log (2 + (N : ℝ))) ^ (20 : ℕ) := by
  classical
  refine hmass (N : ℝ) ϑ T ?_ hϑ0 hϑ1 ?_
  · exact_mod_cast hN
  · intro z hz
    obtain ⟨hann, hlt, hsq, hnear⟩ := hT z hz
    -- `z ∈ primAnn (2 N)` gives `|z|² ≤ 2N` as a natural number
    have hle_nat : Work.FIPlan.gnorm z ≤ 2 * N := by
      have h1 : z ∈ (Work.FIPlan.gBox (((2 * N : ℕ) : ℤ))).filter
          (fun z => 1 ≤ Work.FIPlan.gnorm z ∧ Work.FIPlan.gnorm z ≤ 2 * N) :=
        (Finset.mem_filter.mp hann).1
      exact (Finset.mem_filter.mp h1).2.2
    exact ⟨by exact_mod_cast hlt, by exact_mod_cast hle_nat, hsq, hnear⟩

end Work.FIRed6Axis
