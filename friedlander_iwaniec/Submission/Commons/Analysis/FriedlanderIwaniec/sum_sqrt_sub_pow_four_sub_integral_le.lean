import Mathlib.Analysis.SumIntegralComparisons

open scoped BigOperators
open MeasureTheory intervalIntegral

namespace Commons.Analysis.FriedlanderIwaniec

lemma sum_sqrt_sub_pow_four_sub_integral_le {y : ℝ} (hy : 1 ≤ y) :
    |(∑ c ∈ Finset.range (⌊y⌋₊ + 1), Real.sqrt (y ^ 4 - (c:ℝ) ^ 4)) -
      (∫ t in (0)..y, Real.sqrt (y ^ 4 - t ^ 4))| ≤ y ^ 2 := by
  set n : ℕ := ⌊y⌋₊ with hn
  set f : ℝ → ℝ := fun t => Real.sqrt (y ^ 4 - t ^ 4) with hf
  have hy0 : 0 ≤ y := by linarith
  have h0n_nat : 0 ≤ n := Nat.zero_le n
  have hny : (n:ℝ) ≤ y := by rw [hn]; exact Nat.floor_le hy0
  have hylt : y < (n:ℝ) + 1 := by rw [hn]; exact Nat.lt_floor_add_one y
  have hfnn : ∀ t, 0 ≤ f t := by intro t; simp only [hf]; exact Real.sqrt_nonneg _
  have hf0 : f 0 = y ^ 2 := by
    simp only [hf]
    rw [show y ^ 4 - (0:ℝ) ^ 4 = (y ^ 2) ^ 2 by ring, Real.sqrt_sq (by positivity)]
  have hfle : ∀ t, f t ≤ y ^ 2 := by
    intro t
    simp only [hf]
    have h : Real.sqrt (y ^ 4 - t ^ 4) ≤ Real.sqrt (y ^ 4) := by
      apply Real.sqrt_le_sqrt
      have : (0:ℝ) ≤ t ^ 4 := by positivity
      linarith
    rwa [show Real.sqrt (y ^ 4) = y ^ 2 by
      rw [show (y:ℝ) ^ 4 = (y ^ 2) ^ 2 by ring, Real.sqrt_sq (by positivity)]] at h
  have hanti : AntitoneOn f (Set.Ici (0:ℝ)) := by
    intro a ha b hb hab
    rw [Set.mem_Ici] at ha hb
    simp only [hf]
    apply Real.sqrt_le_sqrt
    have h4 : a ^ 4 ≤ b ^ 4 := pow_le_pow_left₀ ha hab 4
    linarith
  have hant0 : AntitoneOn f (Set.Icc ((0:ℕ):ℝ) (n:ℝ)) :=
    hanti.mono (fun x hx => by
      rw [Set.mem_Icc] at hx
      rw [Set.mem_Ici]
      simpa using hx.1)
  have hcont : Continuous f := by rw [hf]; fun_prop
  have hi0n : IntervalIntegrable f volume (0:ℝ) n := hcont.intervalIntegrable _ _
  have hiny : IntervalIntegrable f volume (n:ℝ) y := hcont.intervalIntegrable _ _
  have hI : (∫ t in (0)..y, f t) = (∫ t in (0)..n, f t) + (∫ t in (n)..y, f t) :=
    (integral_add_adjacent_intervals hi0n hiny).symm
  have hupper : (∑ c ∈ Finset.range n, f ((c:ℝ)+1)) ≤ ∫ t in (0)..n, f t := by
    have h := hant0.sum_le_integral_Ico (a := 0) (b := n) (Nat.zero_le n)
    show (∑ c ∈ Finset.range n, f ((c:ℝ)+1)) ≤ ∫ t in (0:ℝ)..(n:ℝ), f t
    rw [Finset.range_eq_Ico]
    simpa using h
  have hlower : (∫ t in (0)..n, f t) ≤ ∑ c ∈ Finset.range n, f (c:ℝ) := by
    have h := hant0.integral_le_sum_Ico (a := 0) (b := n) (Nat.zero_le n)
    show (∫ t in (0:ℝ)..(n:ℝ), f t) ≤ ∑ c ∈ Finset.range n, f (c:ℝ)
    rw [Finset.range_eq_Ico]
    simpa using h
  have hA_le : (∑ c ∈ Finset.range (n+1), f (c:ℝ)) - (∫ t in (0)..n, f t) ≤ y^2 := by
    have hS := Finset.sum_range_succ' (fun k : ℕ => f (k:ℝ)) n
    rw [hS]
    simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero]
    rw [hf0]
    linarith [hupper]
  have hA_ge : 0 ≤ (∑ c ∈ Finset.range (n+1), f (c:ℝ)) - (∫ t in (0)..n, f t) := by
    have hS := Finset.sum_range_succ (fun k : ℕ => f (k:ℝ)) n
    rw [hS]
    have hfn : 0 ≤ f ((n:ℕ):ℝ) := hfnn _
    linarith [hlower, hfn]
  have hB_ge : 0 ≤ ∫ t in (n)..y, f t :=
    intervalIntegral.integral_nonneg hny (fun u _ => hfnn u)
  have hB_le : (∫ t in (n)..y, f t) ≤ y^2 := by
    have hconst : (∫ t in (n)..y, f t) ≤ ∫ t in (n)..y, (y^2:ℝ) :=
      integral_mono_on hny hiny intervalIntegrable_const (fun u _ => hfle u)
    rw [intervalIntegral.integral_const] at hconst
    simp only [smul_eq_mul] at hconst
    have hy1 : y - (n:ℝ) ≤ 1 := by linarith [hylt]
    have hy2 : (0:ℝ) ≤ y^2 := by positivity
    have h2 : (y - (n:ℝ)) * y^2 ≤ y^2 := by
      have := mul_le_mul_of_nonneg_right hy1 hy2
      simpa using this
    linarith [hconst, h2]
  rw [hI, abs_le]
  constructor <;> linarith [hA_le, hA_ge, hB_ge, hB_le]

end Commons.Analysis.FriedlanderIwaniec