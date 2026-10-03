import Mathlib
import Submission.Work.FIArea1.cross_helpers
import Submission.Work.FIArea2.sum_gBox_eq_sum_congruences

namespace Work.FIArea1

open Finset
open scoped BigOperators

/-- `|c| ≤ c²` for `c : ℤ`. -/
private lemma int_abs_le_sq (c : ℤ) : |c| ≤ c ^ 2 := by
  have h1 : (0 : ℤ) ≤ |c| := abs_nonneg c
  rcases eq_or_lt_of_le h1 with h | h
  · rw [← h]; positivity
  · nlinarith [h, sq_abs c, abs_nonneg c, sq_nonneg c]

/-- Every integer root of `c² = A - s·m` with `s ∈ [-R,R]` lies in the box `[-K,K]`,
`K = |A| + R|m|`. -/
private lemma root_mem_Icc (R : ℤ) (hR : 0 ≤ R) (A m : ℤ) (s : ℤ)
    (hs : s ∈ Finset.Icc (-R) R) (c : ℤ) (hc : c ^ 2 = A - s * m) :
    c ∈ Finset.Icc (-((A.natAbs + R.natAbs * m.natAbs : ℕ) : ℤ))
      ((A.natAbs + R.natAbs * m.natAbs : ℕ) : ℤ) := by
  set K : ℕ := A.natAbs + R.natAbs * m.natAbs with hKdef
  have hmabs : |(m : ℝ)| = (m.natAbs : ℝ) := by rw [Nat.cast_natAbs, Int.cast_abs]
  have hAabs : |(A : ℝ)| = (A.natAbs : ℝ) := by rw [Nat.cast_natAbs, Int.cast_abs]
  have hR0 : (0 : ℝ) ≤ (R : ℝ) := by exact_mod_cast hR
  have hRnat : ((R.natAbs : ℕ) : ℝ) = (R : ℝ) := by
    rw [Nat.cast_natAbs, Int.cast_abs, abs_of_nonneg hR0]
  have hKcast : ((K : ℕ) : ℝ) = (A.natAbs : ℝ) + (R : ℝ) * |(m : ℝ)| := by
    rw [hKdef]; push_cast; rw [hRnat, hmabs]
  have hsabs : |s| ≤ R := abs_le.mpr (Finset.mem_Icc.mp hs)
  have hsR : |(s : ℝ)| ≤ (R : ℝ) := by
    rw [← Int.cast_abs]; exact_mod_cast hsabs
  have hml : (0 : ℝ) ≤ |(m : ℝ)| := abs_nonneg _
  have hbound : |(A : ℝ) - (s : ℝ) * (m : ℝ)| ≤ (A.natAbs : ℝ) + (R : ℝ) * |(m : ℝ)| := by
    calc |(A : ℝ) - (s : ℝ) * (m : ℝ)| ≤ |(A : ℝ)| + |(s : ℝ) * (m : ℝ)| :=
          abs_sub_le_iff.mpr ⟨by linarith [le_abs_self (A : ℝ), neg_le_abs ((s : ℝ) * (m : ℝ))],
                              by linarith [neg_le_abs (A : ℝ), le_abs_self ((s : ℝ) * (m : ℝ))]⟩
      _ = |(A : ℝ)| + |(s : ℝ)| * |(m : ℝ)| := by rw [abs_mul]
      _ ≤ (A.natAbs : ℝ) + (R : ℝ) * |(m : ℝ)| := by
          rw [hAabs]
          exact add_le_add le_rfl (mul_le_mul_of_nonneg_right hsR hml)
  have hcR : (c : ℝ) ^ 2 = (A : ℝ) - (s : ℝ) * (m : ℝ) := by
    have := congrArg (fun z : ℤ => (z : ℝ)) hc
    push_cast at this
    simpa using this
  have hcabs : |(c : ℝ)| ≤ ((K : ℕ) : ℝ) := by
    have h' : ((|c| : ℤ) : ℝ) ≤ (c : ℝ) ^ 2 := by exact_mod_cast int_abs_le_sq c
    rw [Int.cast_abs] at h'
    rw [hcR] at h'
    rw [hKcast]
    linarith [hbound, le_abs_self ((A : ℝ) - (s : ℝ) * (m : ℝ))]
  rw [Finset.mem_Icc]
  have h2 := abs_le.mp hcabs
  constructor
  · have : ((-(K : ℤ) : ℤ) : ℝ) ≤ (c : ℝ) := by push_cast; linarith [h2.1]
    exact_mod_cast this
  · have : (c : ℝ) ≤ ((K : ℤ) : ℝ) := h2.2
    exact_mod_cast this

/-- **Squares in an arithmetic progression, counted with their roots.**  For `m ≠ 0` and
`R ≥ 0`, the weighted count `∑_{s ∈ [-R,R]} Zint (A - s*m)` of the square roots of the values
`A - s*m` is at most `2√(2R|m|) + 2`: the values form an arithmetic progression with difference
`m`, spanning a real interval of length `2R|m|`, and an interval of length `L` contains at most
`√L + 1` square values (two consecutive squares differing by at least `1`), each contributing at
most two roots.  (`Work.FIArea1.card_sq_interval_le` in the imported module is the abstract
"interval of length `L` contains at most `2√L+2` roots" statement that the proof can reduce to.) -/
theorem sum_Zint_ap_le (R : ℤ) (hR : 0 ≤ R) (A m : ℤ) (hm : m ≠ 0) :
    (∑ s ∈ Finset.Icc (-R) R, (Work.FIPlan.Zint (A - s * m) : ℝ))
      ≤ 2 * Real.sqrt (2 * (R : ℝ) * |(m : ℝ)|) + 2 := by
  classical
  set K : ℕ := A.natAbs + R.natAbs * m.natAbs with hKdef
  set T : Finset (ℤ × ℤ) :=
    ((Finset.Icc (-R) R).product (Finset.Icc (-(K : ℤ)) (K : ℤ))).filter
      (fun p => p.2 ^ 2 = A - p.1 * m) with hTdef
  set U : Finset ℤ := T.image Prod.snd with hUdef
  set lo : ℝ := (A : ℝ) - (R : ℝ) * |(m : ℝ)| with hlodef
  set hi : ℝ := (A : ℝ) + (R : ℝ) * |(m : ℝ)| with hidef
  -- roots of `c² = A - s·m` lie in the box `[-K,K]`
  have hroot : ∀ s ∈ Finset.Icc (-R) R, ∀ c : ℤ,
      c ^ 2 = A - s * m → c ∈ Finset.Icc (-(K : ℤ)) (K : ℤ) := by
    intro s hs c hc
    rw [hKdef]
    exact root_mem_Icc R hR A m s hs c hc
  -- the weighted sum is the cardinality of the graph `T`
  have h1 : (∑ s ∈ Finset.Icc (-R) R, (Work.FIPlan.Zint (A - s * m) : ℝ))
      = (T.card : ℝ) := by
    have hcard : (T.card : ℝ) = ∑ s ∈ Finset.Icc (-R) R,
        ∑ c ∈ Finset.Icc (-(K : ℤ)) (K : ℤ),
          (if c ^ 2 = A - s * m then (1 : ℝ) else 0) := by
      have hb : (T.card : ℝ)
          = ∑ p ∈ (Finset.Icc (-R) R).product (Finset.Icc (-(K : ℤ)) (K : ℤ)),
            (if p.2 ^ 2 = A - p.1 * m then (1 : ℝ) else 0) := by
        rw [hTdef]
        exact (Finset.sum_boole (fun p : ℤ × ℤ => p.2 ^ 2 = A - p.1 * m)
          ((Finset.Icc (-R) R).product (Finset.Icc (-(K : ℤ)) (K : ℤ)))).symm
      rw [hb]
      exact Finset.sum_product _ _ _
    rw [hcard]
    apply Finset.sum_congr rfl
    intro s hs
    rw [Work.FIArea2.Zint_eq_Cnt K (A - s * m) (fun c hc => hroot s hs c hc)]
    rfl
  -- the projection to the roots is injective on `T`
  have hinj : Set.InjOn Prod.snd (↑T : Set (ℤ × ℤ)) := by
    intro p hp q hq hpq
    rw [hTdef] at hp hq
    obtain ⟨hpS, hpe⟩ := Finset.mem_filter.mp hp
    obtain ⟨hqS, hqe⟩ := Finset.mem_filter.mp hq
    have hpq' : p.2 = q.2 := hpq
    have hmul : p.1 * m = q.1 * m := by
      have h2' : A - p.1 * m = A - q.1 * m := by rw [← hpe, ← hqe, hpq']
      linarith
    exact Prod.ext (mul_right_cancel₀ hm hmul) hpq'
  have h2 : (T.card : ℝ) = (U.card : ℝ) := by
    rw [hUdef]
    rw [Finset.card_image_of_injOn hinj]
  -- the roots form a set whose squares lie in an interval of length `2R|m|`
  have hlh : lo ≤ hi := by
    have : (0 : ℝ) ≤ (R : ℝ) * |(m : ℝ)| :=
      mul_nonneg (by exact_mod_cast hR) (abs_nonneg _)
    rw [hlodef, hidef]; linarith
  have hsq : ∀ c ∈ U, lo ≤ (c : ℝ) ^ 2 ∧ (c : ℝ) ^ 2 ≤ hi := by
    intro c hc
    rw [hUdef] at hc
    obtain ⟨p, hpT, hpc⟩ := Finset.mem_image.mp hc
    rw [hTdef] at hpT
    obtain ⟨hpS, hpe⟩ := Finset.mem_filter.mp hpT
    have hs1 : p.1 ∈ Finset.Icc (-R) R := (Finset.mem_product.mp hpS).1
    have hpc' : (c : ℝ) = (p.2 : ℝ) := by rw [← hpc]
    have hsabs : |p.1| ≤ R := abs_le.mpr (Finset.mem_Icc.mp hs1)
    have hsR : |((p.1 : ℤ) : ℝ)| ≤ (R : ℝ) := by
      rw [← Int.cast_abs]; exact_mod_cast hsabs
    have hml : (0 : ℝ) ≤ |(m : ℝ)| := abs_nonneg _
    have hbound : |((p.1 : ℝ)) * (m : ℝ)| ≤ (R : ℝ) * |(m : ℝ)| := by
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_right hsR hml
    have habs := abs_le.mp hbound
    have hsqr : (c : ℝ) ^ 2 = (A : ℝ) - (p.1 : ℝ) * (m : ℝ) := by
      rw [hpc']
      have hcast := congrArg (fun z : ℤ => (z : ℝ)) hpe
      push_cast at hcast
      exact hcast
    rw [hlodef, hidef]
    constructor
    · linarith [habs.1]
    · linarith [habs.2]
  have h3 : (U.card : ℝ) ≤ 2 * Real.sqrt (hi - lo) + 2 := card_sq_interval_le hlh hsq
  have h4 : hi - lo = 2 * (R : ℝ) * |(m : ℝ)| := by rw [hlodef, hidef]; ring
  calc (∑ s ∈ Finset.Icc (-R) R, (Work.FIPlan.Zint (A - s * m) : ℝ))
      = (T.card : ℝ) := h1
    _ = (U.card : ℝ) := h2
    _ ≤ 2 * Real.sqrt (hi - lo) + 2 := h3
    _ = 2 * Real.sqrt (2 * (R : ℝ) * |(m : ℝ)|) + 2 := by rw [h4]

end Work.FIArea1
