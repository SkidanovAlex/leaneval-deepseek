import Mathlib

namespace Commons.Combinatorics.Transference

theorem abs_prod_sub_prod_le_sum_abs_sub {ι : Type*} [DecidableEq ι] (s : Finset ι) (a b : ι → ℝ)
    (ha : ∀ i ∈ s, 0 ≤ a i) (ha1 : ∀ i ∈ s, a i ≤ 1)
    (hb : ∀ i ∈ s, 0 ≤ b i) (hb1 : ∀ i ∈ s, b i ≤ 1) :
    |∏ i ∈ s, a i - ∏ i ∈ s, b i| ≤ ∑ i ∈ s, |a i - b i| := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j t hj ih =>
      have hj_mem : j ∈ insert j t := Finset.mem_insert_self j t
      have haj : 0 ≤ a j := ha j hj_mem
      have haj1 : a j ≤ 1 := ha1 j hj_mem
      have hAt : ∀ i ∈ t, 0 ≤ a i := fun i hi => ha i (Finset.mem_insert_of_mem hi)
      have hAt1 : ∀ i ∈ t, a i ≤ 1 := fun i hi => ha1 i (Finset.mem_insert_of_mem hi)
      have hBt : ∀ i ∈ t, 0 ≤ b i := fun i hi => hb i (Finset.mem_insert_of_mem hi)
      have hBt1 : ∀ i ∈ t, b i ≤ 1 := fun i hi => hb1 i (Finset.mem_insert_of_mem hi)
      have hAnonneg : 0 ≤ ∏ i ∈ t, a i := Finset.prod_nonneg hAt
      have hBnonneg : 0 ≤ ∏ i ∈ t, b i := Finset.prod_nonneg hBt
      have hBle : ∏ i ∈ t, b i ≤ 1 := Finset.prod_le_one hBt hBt1
      have hIH : |∏ i ∈ t, a i - ∏ i ∈ t, b i| ≤ ∑ i ∈ t, |a i - b i| :=
        ih hAt hAt1 hBt hBt1
      rw [Finset.prod_insert hj, Finset.prod_insert hj, Finset.sum_insert hj]
      calc |a j * (∏ i ∈ t, a i) - b j * (∏ i ∈ t, b i)|
          = |a j * ((∏ i ∈ t, a i) - (∏ i ∈ t, b i)) + (a j - b j) * (∏ i ∈ t, b i)| := by
              ring_nf
        _ ≤ |a j * ((∏ i ∈ t, a i) - (∏ i ∈ t, b i))| + |(a j - b j) * (∏ i ∈ t, b i)| :=
              abs_add_le _ _
        _ = a j * |(∏ i ∈ t, a i) - (∏ i ∈ t, b i)| + |a j - b j| * (∏ i ∈ t, b i) := by
              rw [abs_mul, abs_mul, abs_of_nonneg haj, abs_of_nonneg hBnonneg]
        _ ≤ |(∏ i ∈ t, a i) - (∏ i ∈ t, b i)| + |a j - b j| := by
              have hle1 : a j * |(∏ i ∈ t, a i) - (∏ i ∈ t, b i)|
                  ≤ |(∏ i ∈ t, a i) - (∏ i ∈ t, b i)| := by
                simpa using mul_le_mul_of_nonneg_right haj1 (abs_nonneg _)
              have hle2 : |a j - b j| * (∏ i ∈ t, b i) ≤ |a j - b j| := by
                simpa using mul_le_mul_of_nonneg_left hBle (abs_nonneg _)
              linarith
        _ ≤ (∑ i ∈ t, |a i - b i|) + |a j - b j| := by linarith
        _ = |a j - b j| + ∑ i ∈ t, |a i - b i| := by ring
end Commons.Combinatorics.Transference
