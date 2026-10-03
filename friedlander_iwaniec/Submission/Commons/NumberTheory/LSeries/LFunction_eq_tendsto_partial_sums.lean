import Mathlib
import Submission.Commons.NumberTheory.DirichletCharacter.LSeries_partial_sums_tendsto

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Commons.NumberTheory.LSeries

/-- **The Dirichlet series of a non-trivial Dirichlet character converges to `L(χ,s)` on
`re s > 0`**: for `χ ≠ 1` and `0 < s.re`,
`∑_{n<M} χ(n) n^{-s} → LFunction χ s` as `M → ∞`.

This is reduced to the companion statement
`Commons.NumberTheory.DirichletCharacter.LSeries_partial_sums_tendsto` (which uses the range
`1 ≤ n ≤ M` and the form `χ n · n^{-s}`) by reindexing. -/
theorem LFunction_eq_tendsto_partial_sums {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N)
    (hχ : χ ≠ 1) {s : ℂ} (hs : 0 < s.re) :
    Filter.Tendsto (fun M : ℕ => ∑ n ∈ Finset.range M, χ (n : ZMod N) / (n : ℂ) ^ s)
      Filter.atTop (nhds (DirichletCharacter.LFunction χ s)) := by
  have hsne : s ≠ 0 := fun h => by simp [h] at hs
  have hmain :=
    Commons.NumberTheory.DirichletCharacter.LSeries_partial_sums_tendsto χ hχ hs
  have hshift : Filter.Tendsto (fun M : ℕ => M - 1) Filter.atTop Filter.atTop :=
    Filter.tendsto_sub_atTop_nat 1
  refine Filter.Tendsto.congr' ?_ (hmain.comp hshift)
  filter_upwards [Filter.eventually_ge_atTop 1] with M hM
  have hrange : Finset.range M = insert 0 (Finset.Icc 1 (M - 1)) := by
    ext n
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    omega
  have h0 : χ ((0 : ℕ) : ZMod N) / (((0 : ℕ) : ℂ) ^ s) = 0 := by
    have hc : (((0 : ℕ) : ℂ)) = 0 := Nat.cast_zero
    rw [hc, Complex.zero_cpow hsne, div_zero]
  rw [hrange, Finset.sum_insert (by simp [Finset.mem_Icc]), h0, zero_add]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [div_eq_mul_inv, ← Complex.cpow_neg]

end Commons.NumberTheory.LSeries
