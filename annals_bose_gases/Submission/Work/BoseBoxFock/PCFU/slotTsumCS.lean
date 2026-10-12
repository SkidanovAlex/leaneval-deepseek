import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Order.Lattice
import Mathlib.Topology.Algebra.InfiniteSum.Real
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock.PCFU

theorem slotTsumCS {ι : Type*} {a b : ι → ℝ} (ha : ∀ i, 0 ≤ a i) (hb : ∀ i, 0 ≤ b i)
    (ha2 : Summable fun i => (a i) ^ 2) (hb2 : Summable fun i => (b i) ^ 2) :
    Summable (fun i => a i * b i) ∧
      ∑' i, a i * b i
        ≤ Real.sqrt (∑' i, (a i) ^ 2) * Real.sqrt (∑' i, (b i) ^ 2) := by
  have hA : 0 ≤ ∑' i, (a i) ^ 2 := tsum_nonneg fun i => sq_nonneg _
  have hB : 0 ≤ ∑' i, (b i) ^ 2 := tsum_nonneg fun i => sq_nonneg _
  -- Cauchy–Schwarz on every finite truncation, bounded uniformly by `√A * √B`
  have key : ∀ s : Finset ι, ∑ i ∈ s, a i * b i
      ≤ Real.sqrt (∑' i, (a i) ^ 2) * Real.sqrt (∑' i, (b i) ^ 2) := by
    intro s
    have h1 : ∑ i ∈ s, (a i) ^ 2 ≤ ∑' i, (a i) ^ 2 :=
      ha2.sum_le_tsum s (fun i _ => sq_nonneg _)
    have h2 : ∑ i ∈ s, (b i) ^ 2 ≤ ∑' i, (b i) ^ 2 :=
      hb2.sum_le_tsum s (fun i _ => sq_nonneg _)
    have hsq : (∑ i ∈ s, a i * b i) ^ 2 ≤ (∑' i, (a i) ^ 2) * ∑' i, (b i) ^ 2 :=
      le_trans (Finset.sum_mul_sq_le_sq_mul_sq s a b)
        (mul_le_mul h1 h2 (Finset.sum_nonneg (fun i _ => sq_nonneg _)) hA)
    calc ∑ i ∈ s, a i * b i
        ≤ Real.sqrt ((∑' i, (a i) ^ 2) * ∑' i, (b i) ^ 2) := Real.le_sqrt_of_sq_le hsq
      _ = Real.sqrt (∑' i, (a i) ^ 2) * Real.sqrt (∑' i, (b i) ^ 2) := Real.sqrt_mul hA _
  exact ⟨summable_of_sum_le (fun i => mul_nonneg (ha i) (hb i)) key,
    Real.tsum_le_of_sum_le (fun i => mul_nonneg (ha i) (hb i)) key⟩

end Work.BoseBoxFock.PCFU
