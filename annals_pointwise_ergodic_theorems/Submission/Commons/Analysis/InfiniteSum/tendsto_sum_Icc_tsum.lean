import Mathlib.Analysis.CStarAlgebra.Classes

namespace Commons.Analysis.InfiniteSum

open scoped BigOperators

/-- The symmetric intervals `Icc (-N) N` are cofinal in `Finset ℤ`, i.e. they tend to `atTop`
in the inclusion order on finite subsets of `ℤ`. -/
lemma tendsto_finset_Icc_int_atTop :
    Filter.Tendsto (fun N : ℕ => Finset.Icc (-(N : ℤ)) (N : ℤ)) Filter.atTop Filter.atTop := by
  rw [Filter.tendsto_atTop]
  intro s
  filter_upwards [Filter.eventually_ge_atTop (s.sup (fun z : ℤ => z.natAbs))] with N hN
  intro z hz
  have h1 : |z| ≤ (N : ℤ) := by
    rw [Int.abs_eq_natAbs]
    exact_mod_cast le_trans (Finset.le_sup (f := fun z : ℤ => z.natAbs) hz) hN
  rw [Finset.mem_Icc]
  exact abs_le.mp h1

/-- For a summable complex sequence indexed by `ℤ`, the partial sums over the symmetric
intervals `[-N, N]` converge to the full `tsum`. -/
theorem tendsto_sum_Icc_tsum (c : ℤ → ℂ) (hc : Summable c) :
    Filter.Tendsto (fun N : ℕ => ∑ m ∈ Finset.Icc (-(N : ℤ)) (N : ℤ), c m)
      Filter.atTop (nhds (∑' m, c m)) :=
  hc.hasSum.comp tendsto_finset_Icc_int_atTop

end Commons.Analysis.InfiniteSum