import Mathlib
import Submission.Work.ResMath.gaussSumm
import Submission.Work.ResMath.gaussPair
import Submission.Work.ResMath.gaussReduce

/-!
# The Gaussian lattice-sum bound

`Work.ResMath.gauss_lattice_le`: for `α > 0` and every real `z`,

`∑' n : ℤ, exp (-(π / α²) * (z + n)²) ≤ 1 + α`.

This is the "integral comparison for the unimodal Gaussian" underlying Lemma 4.5 of
Harvey–van der Hoeven, *Integer multiplication in time* `O(n log n)` — the estimate
`‖S‖ < 1 + α⁻¹`.

The proof follows the paper.  After reducing `z` modulo the (periodic) centre to
`η ∈ [-1/2, 1/2]`, split the `ℤ`-sum into its two tails.  The nearest term is `≤ 1`,
and each tail is bounded by the corresponding half-line Gaussian integral; the two
half-line integrals add up to the full Gaussian integral `√(π/a) = α`.
-/

namespace Work.ResMath

open Set MeasureTheory intervalIntegral Filter Finset

/-- **One-sided Gaussian tail bound.** For `a > 0` and `ξ ∈ [-1/2, 1/2]`,
`∑_{n≥0} exp (-a (ξ + n + 1)²) ≤ ∫_{x > ξ} exp (-a x²) dx`.

(We prove the sharper step `exp (-a (ξ + m + 1)²) ≤ ∫_{ξ+m}^{ξ+m+1} exp (-a x²) dx`
for every `m`, which holds because on `(ξ+m, ξ+m+1)` the point `ξ+m+1` is the farthest
from the origin — this uses `ξ ≥ -1/2`.) -/
theorem gaussTail (a : ℝ) (ha : 0 < a) (ξ : ℝ) (hξ : ξ ∈ Set.Icc (-(1/2:ℝ)) (1/2)) :
    ∑' n : ℕ, Real.exp (-a * (ξ + ((n+1:ℕ):ℝ))^2) ≤ ∫ x in Set.Ioi ξ, Real.exp (-a*x^2) := by
  have hg_anti : AntitoneOn (fun x : ℝ => Real.exp (-a * x^2)) (Set.Ici 0) := by
    intro x hx y hy hxy
    simp only [Set.mem_Ici] at hx hy
    apply Real.exp_le_exp.mpr
    have h2 : x ^ 2 ≤ y ^ 2 := by nlinarith [hx, hxy, sq_nonneg (y - x), sq_nonneg (y + x)]
    have h3 : a * x^2 ≤ a * y^2 := by nlinarith [mul_le_mul_of_nonneg_left h2 ha.le]
    linarith
  have hg_cont : Continuous (fun x : ℝ => Real.exp (-a * x^2)) := by fun_prop
  have hg_int : IntegrableOn (fun x : ℝ => Real.exp (-a*x^2)) (Set.Ioi ξ) :=
    (integrable_exp_neg_mul_sq ha).integrableOn
  have hfin : ∀ M : ℕ, ∑ i ∈ Finset.range M, Real.exp (-a*(ξ + (i:ℝ) + 1)^2)
      ≤ ∫ x in ξ..(ξ+(M:ℝ)), Real.exp (-a*x^2) := by
    intro M
    induction M with
    | zero => simp
    | succ M ih =>
      rw [Finset.sum_range_succ, show (ξ + ((M+1:ℕ):ℝ)) = (ξ+(M:ℝ)) + 1 from by push_cast; ring]
      have hstep : Real.exp (-a*(ξ + (M:ℝ) + 1)^2) ≤ ∫ x in (ξ+(M:ℝ))..(ξ+(M:ℝ)+1), Real.exp (-a*x^2) := by
        have hM0 : (0:ℝ) ≤ (M:ℝ) := Nat.cast_nonneg M
        have hle : ∀ x ∈ Set.Ioo (ξ+(M:ℝ)) (ξ+(M:ℝ)+1), Real.exp (-a*(ξ+(M:ℝ)+1)^2) ≤ Real.exp (-a*x^2) := by
          intro x hx
          rw [Set.mem_Ioo] at hx
          apply Real.exp_le_exp.mpr
          have hx2 : x^2 ≤ (ξ+(M:ℝ)+1)^2 := by nlinarith [hx.1, hx.2, hξ.1]
          nlinarith [mul_le_mul_of_nonneg_left hx2 ha.le]
        have hfi : IntervalIntegrable (fun _ : ℝ => Real.exp (-a*(ξ+(M:ℝ)+1)^2)) volume (ξ+(M:ℝ)) (ξ+(M:ℝ)+1) := intervalIntegrable_const
        have hgi : IntervalIntegrable (fun x : ℝ => Real.exp (-a*x^2)) volume (ξ+(M:ℝ)) (ξ+(M:ℝ)+1) := hg_cont.intervalIntegrable _ _
        have hi := integral_mono_on_of_le_Ioo (f := fun _ => Real.exp (-a*(ξ+(M:ℝ)+1)^2))
          (g := fun x => Real.exp (-a*x^2)) (by linarith) hfi hgi hle
        simpa using hi
      calc ∑ i ∈ Finset.range M, Real.exp (-a*(ξ+(i:ℝ)+1)^2) + Real.exp (-a*(ξ+(M:ℝ)+1)^2)
          ≤ (∫ x in ξ..(ξ+(M:ℝ)), Real.exp (-a*x^2)) + ∫ x in (ξ+(M:ℝ))..(ξ+(M:ℝ)+1), Real.exp (-a*x^2) := add_le_add ih hstep
        _ = ∫ x in ξ..((ξ+(M:ℝ))+1), Real.exp (-a*x^2) := by
              exact integral_add_adjacent_intervals (hg_cont.intervalIntegrable _ _) (hg_cont.intervalIntegrable _ _)
  have hbound : ∀ s : Finset ℕ, ∑ i ∈ s, Real.exp (-a*(ξ + ((i+1 : ℕ):ℝ))^2) ≤ ∫ x in Set.Ioi ξ, Real.exp (-a*x^2) := by
    intro s
    set M := s.sup id + 1 with hM
    have hs : s ⊆ Finset.range M := by
      intro i hi
      rw [Finset.mem_range]
      have : i ≤ s.sup id := Finset.le_sup (f := id) hi
      omega
    calc ∑ i ∈ s, Real.exp (-a*(ξ + ((i+1:ℕ):ℝ))^2)
        ≤ ∑ i ∈ Finset.range M, Real.exp (-a*(ξ + ((i+1:ℕ):ℝ))^2) :=
          sum_le_sum_of_subset_of_nonneg hs (fun i _ _ => Real.exp_nonneg _)
      _ = ∑ i ∈ Finset.range M, Real.exp (-a*(ξ + (i:ℝ) + 1)^2) := by
          apply Finset.sum_congr rfl; intro i _; congr 2; push_cast; ring
      _ ≤ ∫ x in ξ..(ξ+(M:ℝ)), Real.exp (-a*x^2) := hfin M
      _ ≤ ∫ x in Set.Ioi ξ, Real.exp (-a*x^2) := by
          rw [integral_of_le (le_add_of_nonneg_right (Nat.cast_nonneg M))]
          apply setIntegral_mono_set hg_int (Eventually.of_forall (fun x => Real.exp_nonneg _))
          exact Eventually.of_forall (fun x hx => (Set.mem_Ioc.mp hx).1)
  exact tsum_le_of_sum_le' (setIntegral_nonneg measurableSet_Ioi (fun x _ => Real.exp_nonneg _)) hbound

/-- **The Gaussian lattice sum.** For `a > 0` and every real `z`,
`∑' n : ℤ, exp (-a (z + n)²) ≤ 1 + √(π/a)`. -/
theorem gaussSumBound (a : ℝ) (ha : 0 < a) (z : ℝ) :
    ∑' n : ℤ, Real.exp (-a*(z+(n:ℝ))^2) ≤ 1 + Real.sqrt (Real.pi / a) := by
  obtain ⟨η, hη, hred⟩ := gaussReduce a ha z
  rw [hred]
  set g : ℤ → ℝ := fun n => Real.exp (-a*(η+(n:ℝ))^2) with hg
  have hsum : Summable g := gaussSumm a ha η
  have hsumNat : Summable (fun n : ℕ => g n) := hsum.comp_injective Nat.cast_injective
  have hsumNeg : Summable (fun n : ℕ => g (-(↑n+1))) :=
    hsum.comp_injective (fun m n h => by simp only [neg_inj] at h; omega)
  have hpos : (∑' n : ℕ, g (↑(n+1))) = ∑' n : ℕ, Real.exp (-a*(η+((n+1:ℕ):ℝ))^2) := by
    apply tsum_congr; intro n
    simp only [hg, Int.cast_natCast]
  have hneg : (∑' n : ℕ, g (-(↑n+1))) = ∑' n : ℕ, Real.exp (-a*((-η)+((n+1:ℕ):ℝ))^2) := by
    apply tsum_congr; intro n
    simp only [hg]
    congr 1
    push_cast
    ring
  rw [tsum_of_nat_of_neg_add_one hsumNat hsumNeg, Summable.tsum_eq_zero_add hsumNat, hpos, hneg]
  have h0 : g 0 ≤ 1 := by
    simp only [hg, Int.cast_zero, add_zero]
    rw [Real.exp_le_one_iff]
    nlinarith [sq_nonneg η]
  have ht := gaussTail a ha η hη
  have htn := gaussTail a ha (-η) (by constructor <;> linarith [hη.1, hη.2])
  have hp := gaussPair a ha η
  linarith [h0, ht, htn, hp]

theorem gauss_lattice_le (α : ℝ) (hα : 0 < α) (z : ℝ) :
    ∑' n : ℤ, Real.exp (-(Real.pi / α ^ 2) * (z + (n : ℝ)) ^ 2) ≤ 1 + α := by
  have ha : 0 < Real.pi / α^2 := div_pos Real.pi_pos (pow_pos hα 2)
  have h := gaussSumBound (Real.pi / α^2) ha z
  have hsqrt : Real.sqrt (Real.pi / (Real.pi / α^2)) = α := by
    rw [show Real.pi / (Real.pi / α^2) = α^2 by field_simp]
    exact Real.sqrt_sq hα.le
  rwa [hsqrt] at h

end Work.ResMath
