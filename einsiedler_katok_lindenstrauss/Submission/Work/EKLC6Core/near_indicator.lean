import Mathlib
import Submission.Work.EKLContract.Defs
import Submission.Work.EKLRelCross.Instances

namespace Work.EKLC6Core

open Work.EKLContract

/-- A compact subset of `SL₃(ℝ)` is `Gδ`. -/
theorem isGδ_of_isCompact {K : Set SL3} (hK : IsCompact K) : IsGδ K :=
  IsClosed.isGδ hK.isClosed

theorem near_indicator {K : Set Work.EKLContract.SL3} (hK : IsCompact K) :
    ∃ (f : ℕ → CompactlySupportedContinuousMap Work.EKLContract.SL3 ℝ) (K' : Set Work.EKLContract.SL3),
      IsCompact K' ∧ (∀ n, Function.support (fun y => f n y) ⊆ K') ∧
      (∀ n y, 0 ≤ f n y) ∧ (∀ n y, y ∈ K → f n y = 1) ∧ (∀ n y, f n y ≤ 1) ∧
      (∀ n m, n ≤ m → ∀ y, f m y ≤ f n y) ∧
      (∀ y, Filter.Tendsto (fun n => f n y) Filter.atTop (nhds ((K.indicator fun _ => (1:ℝ)) y))) := by
  obtain ⟨ψ, hψ_eq, -, hψ_supp, hψ_range⟩ :=
    exists_continuous_one_zero_of_isCompact_of_isGδ hK (isGδ_of_isCompact hK) isClosed_empty
      (Set.disjoint_empty K)
  have hψ0 : ∀ y, 0 ≤ ψ y := fun y => (hψ_range y).1
  have hψ1 : ∀ y, ψ y ≤ 1 := fun y => (hψ_range y).2
  have hψmem : ∀ y, y ∈ K ↔ ψ y = 1 := by
    intro y; rw [hψ_eq]; simp
  let f : ℕ → CompactlySupportedContinuousMap SL3 ℝ := fun n =>
    ⟨⟨fun y => ψ y ^ (n + 1), by fun_prop⟩,
      hψ_supp.mono (by
        intro y hy
        simp only [Function.mem_support] at hy ⊢
        exact fun h => hy (by rw [h, zero_pow (Nat.succ_ne_zero n)]))⟩
  have hfval : ∀ n y, f n y = ψ y ^ (n + 1) := fun n y => rfl
  refine ⟨f, tsupport (fun y => ψ y), hψ_supp, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro n
    rw [show (fun y => f n y) = fun y => ψ y ^ (n + 1) from funext (hfval n)]
    intro y hy
    simp only [Function.mem_support] at hy
    exact subset_tsupport ψ (fun h => hy (by rw [h, zero_pow (Nat.succ_ne_zero n)]))
  · intro n y; rw [hfval]; exact pow_nonneg (hψ0 y) _
  · intro n y hy; rw [hfval, (hψmem y).mp hy, one_pow]
  · intro n y; rw [hfval]; exact pow_le_one₀ (hψ0 y) (hψ1 y)
  · intro n m hnm y
    rw [hfval, hfval]
    exact pow_le_pow_of_le_one (hψ0 y) (hψ1 y) (Nat.succ_le_succ hnm)
  · intro y
    by_cases hy : y ∈ K
    · have h1 : ∀ n, f n y = 1 :=
        fun n => by rw [hfval, (hψmem y).mp hy, one_pow]
      rw [Set.indicator_of_mem hy]
      rw [show (fun n => f n y) = fun _ => (1 : ℝ) from funext h1]
      exact tendsto_const_nhds
    · have hne : ψ y ≠ 1 := fun h => hy ((hψmem y).mpr h)
      have hlt : ψ y < 1 := lt_of_le_of_ne (hψ1 y) hne
      rw [Set.indicator_of_notMem hy]
      have hbase : Filter.Tendsto (fun n : ℕ => ψ y ^ n) Filter.atTop (nhds 0) :=
        tendsto_pow_atTop_nhds_zero_of_lt_one (hψ0 y) hlt
      have hcomp : Filter.Tendsto (fun n : ℕ => ψ y ^ (n + 1)) Filter.atTop (nhds 0) := by
        simpa [pow_succ] using hbase.mul tendsto_const_nhds
      simpa only [hfval] using hcomp

end Work.EKLC6Core
