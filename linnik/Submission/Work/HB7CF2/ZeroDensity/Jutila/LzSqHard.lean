import Mathlib
import Submission.Work.ZeroDensity.Jutila.bvDefs
import Submission.Work.ZeroDensity.Jutila.LzSqIntBad
import Submission.Work.LinnikAreas2.bz_sq_hard_via_s3h

/-!
# The sharp `Λ²` (Selberg) second moment in the hard range `N < z²`

For `z : ℕ`, `Lz z n = Λ_z(n) = Σ_{d ∣ n, d ≤ z} μ(d)·log(z/d)` is the truncated von Mangoldt
sum (`bvDefs.lean`), and `Work.LinnikAreas.Density4.Bz z n = Σ_{z < d ∣ n} μ(d)·log(d/z)` is its
Möbius correction, so that `Λ_z(n) = Λ(n) + B_z(n)` for `n ≥ 2` (`LamRDefs.lean`).

The target `LzSqHard` is the **sharp Selberg `Λ²`-sieve evaluation**

  `Σ_{n ≤ N} Λ_z(n)² ≤ N·log z + C·N`   (`2 ≤ z ≤ N < z²`),

the hard range `N < z²` of the second moment (the complementary range `z² ≤ N` is
`LzSqIntGood`, via the crude floor comparison `selSum_le_selQ_crude` and the sharp
Selberg-form value `selQ z ≤ log z + C`).

## The reduction

`LzSqIntBad` (already in the workspace, `sorry`-free) performs the whole reduction:
with `Λ_z = Λ + B_z` it uses the sharp evaluations

* `Σ_{n ≤ N} Λ(n)² = N log N + O(N)`  (`Density4.vonMangoldt_sq_sum_bound`), and
* `Σ_{n ≤ N} Λ(n)·B_z(n) = −N·log(N/z) + O(N)`  (`Density4.vonMangoldt_mul_Bz_sum`,
  `prime_log_gap_sum`, packaged as `MixedSumLe`),

so that everything rests on the **sharp** bound for the correction term

  `Σ_{n ≤ N} B_z(n)² ≤ N·log(N/z) + C·N`      (`BzD_sq_bound` below).

That bound is Graham's hard case (`S. Graham, An asymptotic estimate related to Selberg's sieve,
J. Number Theory 10 (1978) 83–94`; Heath-Brown (1992) §11, quoted as (11.13)): it is *not*
elementary — the crude bound `Σ B_z² ≪ N log²z` misses the sharp coefficient `1` — and it is
proved in the workspace by the exact `S₃` quadruple reindexing
(`Density4.BzS3.S3_eq_restricted`) followed by the asymptotic evaluation of its three pieces
(`LinnikAreas2.S3Hard.s3G_abel_sharp`, `LinnikAreas2.s3_hard_main_term`,
`LinnikAreas2.s3_hard_error_BC`, `LinnikAreas2.s3_hard_error_sum_bound`), assembled in
`Submission.Work.LinnikAreas2.bz_sq_hard_via_s3h`.

## The assembly

Feeding `BzD_sq_bound` into `LzSqIntBad` gives `Σ_{n ≤ N} (Lz (z:ℝ) n)² ≤ N·log z + C·N` for the
*real* cutoff `(z : ℝ)`; the statement's own summand uses the integer filter `d ≤ z` and the cast
`((z : ℝ) / (d : ℝ))`, which agrees with `Lz`'s `(d : ℝ) ≤ (z : ℝ)` filter by `Nat.cast_le`
(`Lz_natCast_eq_LambdaR` is the same comparison).  That final rewriting is the only bookkeeping.
-/

namespace Work.ZeroDensity.Jutila

open Finset

noncomputable section

/-- **Graham's sharp bound for the correction term `B_z` in the hard range `N < z²`** — the deep
input of the reduction, with the sharp coefficient `1` of the leading term.  This is exactly the
statement consumed by `LzSqIntBad` (`hB`), and it is proved in the shared `S₃` chain
`Work.LinnikAreas2.bz_sq_hard_via_s3h`. -/
private lemma BzD_sq_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (z N : ℕ), 2 ≤ z → z ≤ N → N < z * z →
      (∑ n ∈ Finset.Icc 1 N, (LinnikAreas.Density4.Bz z n) ^ 2)
        ≤ (N : ℝ) * Real.log ((N : ℝ) / (z : ℝ)) + C * (N : ℝ) :=
  Work.LinnikAreas2.bz_sq_hard_via_s3h

/-- **Linnik's sharp Selberg `Λ²`-sieve second moment in the hard range `N < z²`.**  For every
`2 ≤ z ≤ N < z·z` there is an absolute `C > 0` with
`Σ_{n ≤ N} (Σ_{d ∣ n, d ≤ z} μ(d)·log(z/d))² ≤ N·log z + C·N` — the sharp coefficient `1` on the
leading term `N log z`. -/
theorem LzSqHard : ∃ C : ℝ, 0 < C ∧ ∀ (z N : ℕ), 2 ≤ z → z ≤ N → N < z * z →
    (∑ n ∈ Finset.Icc 1 N, (∑ d ∈ n.divisors.filter (fun d => d ≤ z),
        (ArithmeticFunction.moebius d : ℝ) * Real.log ((z : ℝ) / (d : ℝ))) ^ 2)
      ≤ (N : ℝ) * Real.log (z : ℝ) + C * (N : ℝ) := by
  obtain ⟨C, hC, h⟩ := LzSqIntBad BzD_sq_bound
  refine ⟨C, hC, ?_⟩
  intro z N hz hzN hN
  have key := h z N hz hzN hN
  have hconv : (∑ n ∈ Finset.Icc 1 N, (∑ d ∈ n.divisors.filter (fun d => d ≤ z),
        (ArithmeticFunction.moebius d : ℝ) * Real.log ((z : ℝ) / (d : ℝ))) ^ 2)
      = ∑ n ∈ Finset.Icc 1 N, (Lz (z : ℝ) n) ^ 2 := by
    apply Finset.sum_congr rfl
    intro n _
    congr 1
    simp only [Lz, Nat.cast_le]
  rw [hconv]
  exact key

end

end Work.ZeroDensity.Jutila
