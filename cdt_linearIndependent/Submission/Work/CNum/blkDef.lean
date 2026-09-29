import Mathlib

/-!
# `Work.CNum.blkDef`

For `N > 0` the half-open interval `(0,1]` is partitioned by the `N` blocks
`blk N k = ((k:ℝ)/N, ((k:ℝ)+1)/N]`, `k : Fin N`.  This file sets up the block,
its basic measure-theoretic properties, and the partition lemma
`exists_unique_blk`.
-/

namespace Work.CNum

open MeasureTheory

/-- The `k`-th half-open block `((k:ℝ)/N, ((k:ℝ)+1)/N]` of `(0,1]`. -/
def blk (N : ℕ) (k : Fin N) : Set ℝ := Set.Ioc ((k:ℝ)/N) (((k:ℝ)+1)/N)

lemma blk_measurable (N : ℕ) (k : Fin N) : MeasurableSet (blk N k) := measurableSet_Ioc

lemma blk_subset {N : ℕ} (hN : 0 < N) (k : Fin N) : blk N k ⊆ Set.Ioc (0:ℝ) 1 := by
  have hNpos : (0:ℝ) < N := by exact_mod_cast hN
  intro x hx
  simp only [blk, Set.mem_Ioc] at hx ⊢
  refine ⟨?_, ?_⟩
  · have : (0:ℝ) ≤ (k:ℝ)/N := by positivity
    linarith [hx.1]
  · have hk1 : ((k:ℝ)+1) ≤ (N:ℝ) := by
      have : (k:ℕ) + 1 ≤ N := by omega
      exact_mod_cast this
    have hkN : ((k:ℝ)+1)/N ≤ 1 := by
      rw [div_le_one hNpos]; exact hk1
    linarith [hx.2, hkN]

lemma blk_volume {N : ℕ} (hN : 0 < N) (k : Fin N) :
    volume (blk N k) = ENNReal.ofReal (1/(N:ℝ)) := by
  have hNne : (N:ℝ) ≠ 0 := by positivity
  rw [blk, Real.volume_Ioc]
  congr 1
  field_simp
  ring

lemma blk_restrict_volume {N : ℕ} (hN : 0 < N) (k : Fin N) :
    (volume.restrict (Set.Ioc (0:ℝ) 1)) (blk N k) = ENNReal.ofReal (1/(N:ℝ)) := by
  rw [Measure.restrict_apply (blk_measurable N k)]
  rw [Set.inter_eq_left.mpr (blk_subset hN k)]
  exact blk_volume hN k

lemma exists_unique_blk {N : ℕ} (hN : 0 < N) {x : ℝ} (hx : x ∈ Set.Ioc (0:ℝ) 1) :
    ∃! k : Fin N, x ∈ blk N k := by
  have hNpos : (0:ℝ) < N := by exact_mod_cast hN
  have hrpos : 0 < x * N := mul_pos hx.1 hNpos
  have hrle : x * N ≤ (N:ℝ) := by
    have := mul_le_mul_of_nonneg_right hx.2 (le_of_lt hNpos)
    simpa using this
  set m : ℕ := Nat.ceil (x * N) with hmdef
  have hm_ge : x * N ≤ (m:ℝ) := by rw [hmdef]; exact Nat.le_ceil _
  have hm_lt : (m:ℝ) < x * N + 1 := by
    rw [hmdef]; exact Nat.ceil_lt_add_one (le_of_lt hrpos)
  have hm_le : m ≤ N := by
    rw [hmdef]; exact (Nat.ceil_le).mpr hrle
  have hm_pos : 0 < m := by
    rw [hmdef]; exact (Nat.ceil_pos).mpr hrpos
  have hmcast : ((m - 1 : ℕ) : ℝ) = (m:ℝ) - 1 := by
    rw [Nat.cast_sub (by omega : 1 ≤ m)]; norm_num
  have hA : ((m:ℝ) - 1) < x * N := by linarith [hm_lt]
  have hB : x * N ≤ (m:ℝ) := hm_ge
  refine ⟨⟨m - 1, by omega⟩, ?_, ?_⟩
  · simp only [blk, Set.mem_Ioc]
    constructor
    · rw [hmcast, div_lt_iff₀ hNpos]
      exact hA
    · have : ((m:ℝ) - 1) + 1 = (m:ℝ) := by ring
      rw [hmcast, this, le_div_iff₀ hNpos]
      exact hB
  · intro k' hk'
    simp only [blk, Set.mem_Ioc] at hk'
    have hk'1 : (k':ℝ) < x * N := (div_lt_iff₀ hNpos).mp hk'.1
    have hk'2 : x * N ≤ (k':ℝ) + 1 := (le_div_iff₀ hNpos).mp hk'.2
    have h1 : (k':ℝ) < (m:ℝ) := lt_of_lt_of_le hk'1 hm_ge
    have h2 : (m:ℝ) < (k':ℝ) + 2 := by linarith [hA, hk'2]
    have h3 : k'.val < m := by exact_mod_cast h1
    have h4 : m < k'.val + 2 := by
      have hh : (m:ℝ) < ((k'.val + 2 : ℕ) : ℝ) := by push_cast; linarith [h2]
      exact_mod_cast hh
    have h5 : k'.val = m - 1 := by omega
    exact Fin.ext (by simpa using h5)

end Work.CNum
