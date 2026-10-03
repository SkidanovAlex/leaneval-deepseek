import Mathlib
import Submission.Work.A3.Weil.norm_sum_exp_affine_le_geomBound
import Submission.Work.A3.Weil.iterCorr_phaseSeq_eq_sum_Icc

/-!
# The geometric bound for the `k`-fold correlation of a phase sequence

Let `φ : ℤ → ℝ` be a phase whose `k`-fold difference along the shifts `l : Fin k → ℤ` is
*affine*, `iterDiff k l φ n = λ·n + c`, and let `u = phaseSeq φ N` be the zero-extended
phase sequence `n ↦ e(φ n)` on `wRange N = [0,N)`.  Then the `k`-fold autocorrelation sum

  `Σ_{n ∈ wRange N} iterCorr k l u n`

is bounded by the geometric (first-derivative-test) quantity `geomBound N λ`.

**Why.**  Expanding the recursive definition, `iterCorr k l u n` is a signed product of the
values `u (n + s)` over the `2^k` subset sums `s = Σ_{i∈A} l i` of the shifts.  Hence it
vanishes unless *all* the points `n + s` lie in `wRange N`, i.e. unless `n` lies in the
intersection of the `2^k` integer intervals `wRange N - s`; that intersection is an interval
`Icc a b ⊆ wRange N`, and on it the signed product telescopes to `e (iterDiff k l φ n)`
(`e(2πi·x) = exp ((2πi x))`, and `conj (e x) = e (-x)` since `‖e x‖ = 1`).  Summing the
affine phase `λ·n + c` over an interval of at most `N` points is the classical geometric-sum
estimate `min (M, 1/(2·intDist λ)) ≤ 1/max (intDist λ, 1/N) = geomBound N λ`.

The two halves of this argument are proved separately:

* `Work.A3.Weil.iterCorr_phaseSeq_eq_sum_Icc` (the structural half), and
* `Work.A3.Weil.norm_sum_exp_affine_le_geomBound` (the geometric half),

and this file assembles them.
-/

set_option autoImplicit false

namespace Work.A3.Weil

/-- **Geometric bound for the phase autocorrelation.**  If the `k`-fold difference of `φ`
along `l` is the affine function `n ↦ λ·n + c`, then the `k`-fold autocorrelation of the
zero-extended phase sequence `phaseSeq φ N`, summed over `wRange N`, is bounded by
`geomBound N λ`. -/
theorem norm_iterCorr_phase_le (k : ℕ) (l : Fin k → ℤ) (φ : ℤ → ℝ) (N : ℕ) (lam : ℝ)
    (haff : ∃ c : ℝ, ∀ n : ℤ, Work.A3.Weil.iterDiff k l φ n = lam * (n : ℝ) + c) :
    ‖∑ n ∈ Work.A3.Weil.wRange N, Work.A3.Weil.iterCorr k l (Work.A3.Weil.phaseSeq φ N) n‖ ≤ Work.A3.Weil.geomBound N lam := by
  classical
  obtain ⟨c, hc⟩ := haff
  -- The structural half: the correlation sum collapses onto an interval on which the
  -- summand is the exponential of the `k`-fold difference of `φ`.
  obtain ⟨a, b, hsub, heq⟩ := iterCorr_phaseSeq_eq_sum_Icc k l φ N
  rw [heq]
  -- On that interval the phase is affine by hypothesis.
  have hcongr : ∑ n ∈ Finset.Icc a b,
        Complex.exp (((2 * Real.pi * iterDiff k l φ n : ℝ) : ℂ) * Complex.I)
      = ∑ n ∈ Finset.Icc a b,
        Complex.exp (((2 * Real.pi * (lam * (n : ℝ) + c) : ℝ) : ℂ) * Complex.I) := by
    refine Finset.sum_congr rfl (fun n _ => ?_)
    rw [hc n]
  rw [hcongr]
  -- The geometric half.
  exact norm_sum_exp_affine_le_geomBound lam c N a b hsub

end Work.A3.Weil
