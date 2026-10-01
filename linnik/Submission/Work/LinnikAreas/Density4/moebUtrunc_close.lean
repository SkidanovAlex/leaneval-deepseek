import Mathlib
import Submission.Work.LinnikAreas.Density4.SqfreeCoprimeDefs
import Submission.Work.LinnikAreas.Density4.tsum_inv_sq_tail_le
import Submission.Work.LinnikAreas.Density4.summable_moebius_coprime_div_sq

/-!
# The truncation `moebUtrunc K r` differs from `moebU r` by at most `1/K`

`moebU r = Σ_{m, (m,r)=1} μ(m)/m²` and `moebUtrunc K r = Σ_{m ≤ K, (m,r)=1} μ(m)/m²`
are the coprimality restricted Möbius reciprocal sum and its truncation.  Since each
summand is dominated by `1/m²` and `Σ_{m > K} 1/m² ≤ 1/K`, the truncation error is at
most `1/K`.

The tail `Σ_{m>K} 1/m²` is bounded by comparison with the telescoping series
`Σ_{i≥0} (1/(i+K) - 1/(i+K+1)) = 1/K`; this comparison is the delegated lemma
`tsum_inv_sq_tail_le`.
-/

namespace Work.LinnikAreas.Density4

open Finset

/-- The summand of the Möbius reciprocal sum: `μ(m)/m²` when `(m,r) = 1` and `0` otherwise. -/
private noncomputable def moebTerm (r m : ℕ) : ℝ :=
  if Nat.Coprime m r then (ArithmeticFunction.moebius m : ℝ) / (m : ℝ) ^ 2 else 0

private lemma moebTerm_zero (r : ℕ) : moebTerm r 0 = 0 := by
  simp [moebTerm]

private lemma moebU_eq_tsum (r : ℕ) : moebU r = ∑' m, moebTerm r m := rfl

/-- The truncation is the sum of the summands over `1 ≤ m ≤ K`, which (as `moebTerm r 0 = 0`)
is the sum over `range (K+1)`. -/
private lemma moebUtrunc_eq_sum_range (K r : ℕ) :
    moebUtrunc K r = ∑ m ∈ Finset.range (K + 1), moebTerm r m := by
  rw [moebUtrunc, Finset.sum_filter]
  have hins : Finset.range (K + 1) = insert 0 (Finset.Icc 1 K) := by
    ext m; simp [Finset.mem_Icc, Finset.mem_range]; omega
  rw [hins, Finset.sum_insert (by simp [Finset.mem_Icc]), moebTerm_zero, zero_add]
  apply Finset.sum_congr rfl
  intro m _
  rw [moebTerm]

/-- Each summand of the Möbius reciprocal sum is dominated by `1/m²`. -/
private lemma abs_moebTerm_le (r m : ℕ) : |moebTerm r m| ≤ 1 / (m : ℝ) ^ 2 := by
  by_cases hm : m = 0
  · subst hm; rw [moebTerm_zero]; simp
  · have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm
    have hmpos : (0 : ℝ) < (m : ℝ) :=
      by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hm1)
    rw [moebTerm]
    by_cases hc : Nat.Coprime m r
    · rw [if_pos hc, abs_div, abs_of_pos (by positivity : (0 : ℝ) < (m : ℝ) ^ 2)]
      refine div_le_div_of_nonneg_right ?_ (by positivity)
      have h1 : |ArithmeticFunction.moebius m| ≤ 1 := ArithmeticFunction.abs_moebius_le_one
      exact_mod_cast h1
    · rw [if_neg hc, abs_zero]
      positivity

private lemma summable_moebTerm (r : ℕ) : Summable (moebTerm r) :=
  summable_moebius_coprime_div_sq r

/-- The tail `Σ_{m > K} 1/m²` is at most `1/K` for `K ≥ 1`, in the indexing `m = i + K + 1`. -/
private lemma tsum_inv_sq_tail (K : ℕ) (hK : 1 ≤ K) :
    (∑' i : ℕ, (1 : ℝ) / (((i + (K + 1) : ℕ) : ℝ)) ^ 2) ≤ 1 / (K : ℝ) :=
  tsum_inv_sq_tail_le K hK

theorem moebUtrunc_close (K r : ℕ) (hK : 1 ≤ K) :
    |moebUtrunc K r - moebU r| ≤ 1 / (K : ℝ) := by
  have hsum : Summable (moebTerm r) := summable_moebTerm r
  -- the truncation error is exactly the tail of the sum
  have htail : moebUtrunc K r - moebU r = -(∑' i, moebTerm r (i + (K + 1))) := by
    have hdecomp := hsum.sum_add_tsum_nat_add (K + 1)
    rw [moebU_eq_tsum, moebUtrunc_eq_sum_range]
    linarith
  rw [htail, abs_neg]
  -- the tail is dominated by `Σ 1/m²`
  have hshift : Summable (fun i : ℕ => moebTerm r (i + (K + 1))) :=
    (summable_nat_add_iff (K + 1)).mpr hsum
  have habs : Summable (fun i : ℕ => |moebTerm r (i + (K + 1))|) := hshift.abs
  have hbase : Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) :=
    (Real.summable_one_div_nat_pow (p := 2)).2 (by norm_num)
  have hMajSumm : Summable (fun i : ℕ => (1 : ℝ) / (((i + (K + 1) : ℕ) : ℝ)) ^ 2) := by
    have hs := (summable_nat_add_iff (K + 1)).mpr hbase
    simpa using hs
  have hterm : ∀ i : ℕ, |moebTerm r (i + (K + 1))| ≤ (1 : ℝ) / (((i + (K + 1) : ℕ) : ℝ)) ^ 2 :=
    fun i => abs_moebTerm_le r (i + (K + 1))
  calc |∑' i, moebTerm r (i + (K + 1))|
      ≤ ∑' i, |moebTerm r (i + (K + 1))| :=
        norm_tsum_le_tsum_norm (f := fun i : ℕ => moebTerm r (i + (K + 1))) habs
    _ ≤ ∑' i, (1 : ℝ) / (((i + (K + 1) : ℕ) : ℝ)) ^ 2 :=
        Summable.tsum_le_tsum hterm habs hMajSumm
    _ ≤ 1 / (K : ℝ) := tsum_inv_sq_tail K hK

end Work.LinnikAreas.Density4
