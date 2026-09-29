import Mathlib.Algebra.GroupWithZero.Nat
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finsupp.Defs
import Mathlib.Data.Fintype.Pi

namespace Commons.RingTheory.MvPowerSeries

theorem exists_finset_sum_eq {σ : Type*} [Fintype σ] [DecidableEq σ] (N : ℕ) :
    ∃ S : Finset (σ →₀ ℕ), ∀ s : σ →₀ ℕ, (∑ i, s i) = N → s ∈ S := by
  classical
  refine ⟨(Fintype.piFinset fun _ : σ => Finset.range (N + 1)).image
      (fun f => Finsupp.equivFunOnFinite.symm f), ?_⟩
  intro s hs
  rw [Finset.mem_image]
  refine ⟨⇑s, ?_, ?_⟩
  · rw [Fintype.mem_piFinset]
    intro i
    rw [Finset.mem_range]
    have hle : s i ≤ ∑ j, s j := by
      simpa using Finset.single_le_sum (fun j _ => Nat.zero_le (s j)) (Finset.mem_univ i)
    omega
  · exact Finsupp.equivFunOnFinite_symm_coe s

end Commons.RingTheory.MvPowerSeries