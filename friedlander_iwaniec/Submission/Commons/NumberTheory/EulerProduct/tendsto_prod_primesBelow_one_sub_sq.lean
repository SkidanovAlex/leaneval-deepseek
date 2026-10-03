import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Mathlib.NumberTheory.PrimeCounting

namespace Commons.NumberTheory.EulerProduct

open Filter Finset
open scoped BigOperators Topology

theorem tendsto_prod_primesBelow_one_sub_sq {g : ℕ → ℝ} {C : ℝ} (hC : 0 < C)
    (hbd : ∀ p : ℕ, p.Prime → |g (p ^ 2)| ≤ C / (p : ℝ) ^ 2) :
    Filter.Tendsto (fun N : ℕ => ∏ p ∈ Nat.primesBelow N, (1 - g (p ^ 2)))
      Filter.atTop (nhds (∏' p : {p : ℕ // p.Prime}, (1 - g ((p : ℕ) ^ 2)))) := by
  classical
  have hsumC : Summable (fun n : ℕ => C / (n : ℝ) ^ 2) := by
    have h1 : Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) :=
      (Real.summable_one_div_nat_pow (p := 2)).mpr (by norm_num)
    simpa [one_div, div_eq_mul_inv] using h1.mul_left C
  set z : ℕ → ℝ := fun n => -(if n.Prime then g (n ^ 2) else 0) with hz
  set F : ℕ → ℝ := fun n => if n.Prime then 1 - g (n ^ 2) else 1 with hF
  have hzF : ∀ n, 1 + z n = F n := by
    intro n; rw [hz, hF]; by_cases h : n.Prime <;> simp [h, sub_eq_add_neg]
  have hbound : ∀ n : ℕ, ‖z n‖ ≤ C / (n : ℝ) ^ 2 := by
    intro n
    by_cases h : n.Prime
    · have : z n = -g (n ^ 2) := by rw [hz]; simp [h]
      rw [this, norm_neg, Real.norm_eq_abs]
      exact hbd n h
    · have : z n = 0 := by rw [hz]; simp [h]
      rw [this, norm_zero]
      exact div_nonneg hC.le (pow_two_nonneg _)
  have hsumz : Summable (fun n : ℕ => ‖z n‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hbound hsumC
  have hmult : Multipliable (fun n : ℕ => 1 + z n) :=
    multipliable_one_add_of_summable hsumz
  have hmultF : Multipliable F := hmult.congr hzF
  have htend := hmultF.tendsto_prod_tprod_nat
  have hFprod : ∀ N : ℕ, ∏ i ∈ range N, F i = ∏ p ∈ Nat.primesBelow N, (1 - g (p ^ 2)) := by
    intro N
    rw [Nat.primesBelow_eq_filter_range, Finset.prod_filter]
  have htprod : ∏' i : ℕ, F i = ∏' p : {p : ℕ // p.Prime}, (1 - g ((p : ℕ) ^ 2)) := by
    have h1 : ∏' p : {p : ℕ // p.Prime}, (1 - g ((p : ℕ) ^ 2))
        = ∏' i : ℕ, {n : ℕ | n.Prime}.mulIndicator (fun n => 1 - g (n ^ 2)) i :=
      tprod_subtype {n : ℕ | n.Prime} (fun n => 1 - g (n ^ 2))
    rw [h1]
    apply tprod_congr
    intro n
    rw [hF]
    by_cases h : n.Prime
    · rw [Set.mulIndicator_of_mem (show n ∈ {n : ℕ | n.Prime} from h)]; simp [h]
    · rw [Set.mulIndicator_of_notMem (show n ∉ {n : ℕ | n.Prime} from h)]; simp [h]
  rw [show (fun N : ℕ => ∏ p ∈ Nat.primesBelow N, (1 - g (p ^ 2)))
        = fun N : ℕ => ∏ i ∈ range N, F i from funext (fun N => (hFprod N).symm), ← htprod]
  exact htend

end Commons.NumberTheory.EulerProduct