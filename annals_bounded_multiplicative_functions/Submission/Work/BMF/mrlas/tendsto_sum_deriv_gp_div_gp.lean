import Mathlib
import Submission.Work.BMF.halasz_series_aux
import Submission.Work.BMF.mrlas.summable_prime_log_mul_rpow_neg
import Submission.Work.BMF.mrlas.exists_norm_deriv_gp_div_gp_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.mrlas

open Finset Filter

/-- The partial sums of the logarithmic derivatives of the local Euler factors `g_p' / g_p`
over the primes below `N` converge, as `N → ∞`, to the full Euler-product log-derivative
`Ψ f s = Σ_p g_p'(s)/g_p(s)`, for `Re s > 1`.

The proof is a reindexing argument: writing `A n = g_n'(s)/g_n(s)` for `n : ℕ`, the pointwise
bound `exists_norm_deriv_gp_div_gp_le` shows that `A` restricted to the primes is summable against
the convergent majorant `log p · p^{-Re s}`, hence the function `A` supported on the primes is
summable on `ℕ`; the partial sums over `range N` then converge to the `tsum` by
`HasSum.tendsto_sum_nat`, and `Nat.primesBelow N = (range N).filter Nat.Prime` together with
`tsum_subtype` identify the two limits. -/
theorem tendsto_sum_deriv_gp_div_gp (f : ℕ → ℂ) (hf1 : f 1 = 1)
    (hb : ∀ n, ‖f n‖ ≤ 1) {s : ℂ} (hs : 1 < s.re) :
    Filter.Tendsto (fun N : ℕ => ∑ p ∈ N.primesBelow,
        deriv (Work.BMF.gp f p) s / Work.BMF.gp f p s) Filter.atTop
      (nhds (Work.BMF.Psi f s)) := by
  obtain ⟨C, _hCpos, hC⟩ := exists_norm_deriv_gp_div_gp_le f hf1 hb hs
  set A : ℕ → ℂ := fun n => deriv (Work.BMF.gp f n) s / Work.BMF.gp f n s with hA
  -- Summability of the terms, indexed by the primes.
  have hS : Summable (fun p : Nat.Primes => A (p : ℕ)) := by
    have hbase : Summable (fun p : Nat.Primes =>
        C * (Real.log (p : ℝ) * (p : ℝ) ^ (-s.re))) :=
      (summable_prime_log_mul_rpow_neg s.re hs).mul_left C
    refine Summable.of_norm_bounded hbase (fun p => ?_)
    exact hC (p : ℕ) p.2
  -- Regard `A` as a function supported on the primes, and sum it on `ℕ`.
  set t : Set ℕ := {n | n.Prime} with ht
  have hSt : Summable (fun x : t => Set.indicator t A x) := by
    refine hS.congr (fun x => ?_)
    exact (Set.indicator_of_mem x.2 A).symm
  have hSc : Summable (fun x : ↥(tᶜ) => Set.indicator t A x) := by
    have h : (fun x : ↥(tᶜ) => Set.indicator t A x) = fun _ => (0 : ℂ) := by
      funext x; exact Set.indicator_of_notMem x.2 A
    rw [h]; exact summable_zero
  have hSind : Summable (Set.indicator t A) :=
    (summable_subtype_and_compl (f := Set.indicator t A) (s := t)).mp ⟨hSt, hSc⟩
  -- Partial sums over `range N` converge to the `tsum`.
  have htend := hSind.hasSum.tendsto_sum_nat
  have hsum_eq : (fun N : ℕ => ∑ i ∈ range N, Set.indicator t A i)
      = (fun N : ℕ => ∑ i ∈ Nat.primesBelow N, A i) := by
    funext N
    rw [Nat.primesBelow_eq_filter_range, Finset.sum_filter]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hi : i.Prime
    · rw [Set.indicator_of_mem (show i ∈ t from hi), if_pos hi]
    · rw [Set.indicator_of_notMem (show i ∉ t from hi), if_neg hi]
  rw [hsum_eq] at htend
  -- Identify the two `tsum`s.
  have htsum_eq : (∑' n, Set.indicator t A n) = ∑' p : Nat.Primes, A p := by
    rw [← tsum_subtype t A]
    rfl
  rw [htsum_eq] at htend
  simpa [Work.BMF.Psi, hA] using htend

end Work.BMF.mrlas
