import Mathlib
import Submission.Work.BMF.n4_mv_defs
import Submission.Work.BMF.tuple_setup

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF

open Finset

/-- Each product `∏ i, χ (v i)` of Dirichlet-character values along a tuple has norm at most `1`. -/
lemma n4_norm_prod_char_le_one {q m : ℕ} (χ : DirichletCharacter ℂ q) (v : Fin m → ℕ) :
    ‖∏ i, χ ((v i : ℕ) : ZMod q)‖ ≤ 1 := by
  rw [norm_prod]
  exact Finset.prod_le_one₀ (fun i _ => norm_nonneg _) (fun i _ => χ.norm_le_one _)

/-- The grouped coefficient at `n` is bounded in norm by the number of tuples with product `n`. -/
lemma n4_norm_mvCoeff_le_card {P : ℝ} {q m : ℕ} (χ : DirichletCharacter ℂ q) (n : ℕ) :
    ‖mvCoeff P q χ m n‖ ≤ (((tup P q m).filter (fun v => tprod v = n)).card : ℝ) := by
  rw [mvCoeff_apply]
  calc ‖∑ v ∈ (tup P q m).filter (fun v => tprod v = n), ∏ i, χ ((v i : ℕ) : ZMod q)‖
      ≤ ∑ v ∈ (tup P q m).filter (fun v => tprod v = n),
          ‖∏ i, χ ((v i : ℕ) : ZMod q)‖ := norm_sum_le _ _
    _ ≤ ∑ _v ∈ (tup P q m).filter (fun v => tprod v = n), (1 : ℝ) :=
        Finset.sum_le_sum (fun v _ => n4_norm_prod_char_le_one χ v)
    _ = (((tup P q m).filter (fun v => tprod v = n)).card : ℝ) := by simp

/-- Every fibre of `tprod` over `tup P q m` has at most `(m+1)^m` elements. -/
private lemma n4_fiber_card_le {P : ℝ} {q m : ℕ} (hm : 1 ≤ m) (hP : 1 ≤ P)
    (h2l : (2:ℝ)^m ≤ P) (n : ℕ) :
    ((tup P q m).filter (fun v => tprod v = n)).card ≤ (m+1)^m := by
  classical
  by_cases h : ((tup P q m).filter (fun v => tprod v = n)).Nonempty
  · obtain ⟨v, hv⟩ := h
    rw [Finset.mem_filter] at hv
    have heq : (tup P q m).filter (fun w => tprod w = n) =
        (tup P q m).filter (fun w => tprod w = tprod v) := by
      apply Finset.filter_congr
      intro w _
      rw [hv.2]
    rw [heq]
    exact fiber_card_le hm hP h2l v hv.1
  · rw [Finset.not_nonempty_iff_eq_empty] at h
    rw [h]
    simp

/-- Summing the fibre cardinalities over `n ∈ [0,N]` recovers the cardinality of `tup`,
provided every tuple product is at most `N`. -/
lemma n4_sum_card_fiber {P : ℝ} {q m N : ℕ}
    (hN : ∀ v ∈ tup P q m, tprod v ≤ N) :
    ∑ n ∈ Finset.range (N + 1), (((tup P q m).filter (fun v => tprod v = n)).card : ℝ)
      = ((tup P q m).card : ℝ) := by
  classical
  have hnat : ∑ n ∈ Finset.range (N + 1),
      ((tup P q m).filter (fun v => tprod v = n)).card = (tup P q m).card := by
    rw [Finset.sum_card_fiberwise_eq_card_filter]
    have hf : (tup P q m).filter (fun v => tprod v ∈ Finset.range (N + 1)) = tup P q m :=
      Finset.filter_true_of_mem (fun v hv => by
        rw [Finset.mem_range]; exact Nat.lt_succ_of_le (hN v hv))
    rw [hf]
  have := congrArg (fun k : ℕ => (k : ℝ)) hnat
  simpa using this

/-- **The `ℓ²` bound for the grouped coefficients.** -/
lemma n4_sum_normSq_mvCoeff_le {P : ℝ} {q m N : ℕ} (hP : 1 ≤ P) (hm : 1 ≤ m)
    (h2l : (2:ℝ)^m ≤ P) (χ : DirichletCharacter ℂ q)
    (hN : ∀ v ∈ tup P q m, tprod v ≤ N) :
    ∑ n ∈ Finset.range (N + 1), ‖mvCoeff P q χ m n‖ ^ 2
      ≤ (((m+1)^m : ℕ) : ℝ) * ((tup P q m).card : ℝ) := by
  classical
  set K : ℝ := (((m+1)^m : ℕ) : ℝ) with hKdef
  have hsumcard := n4_sum_card_fiber (P := P) (q := q) (m := m) (N := N) hN
  calc ∑ n ∈ Finset.range (N + 1), ‖mvCoeff P q χ m n‖ ^ 2
      ≤ ∑ n ∈ Finset.range (N + 1),
          K * (((tup P q m).filter (fun v => tprod v = n)).card : ℝ) := by
        apply Finset.sum_le_sum
        intro n _
        have h1 : ‖mvCoeff P q χ m n‖ ≤
            (((tup P q m).filter (fun v => tprod v = n)).card : ℝ) :=
          n4_norm_mvCoeff_le_card χ n
        have h2 : (((tup P q m).filter (fun v => tprod v = n)).card : ℝ) ≤ K := by
          rw [hKdef]; exact_mod_cast n4_fiber_card_le hm hP h2l n
        have hc : (0 : ℝ) ≤ (((tup P q m).filter (fun v => tprod v = n)).card : ℝ) :=
          Nat.cast_nonneg _
        calc ‖mvCoeff P q χ m n‖ ^ 2
            ≤ (((tup P q m).filter (fun v => tprod v = n)).card : ℝ) ^ 2 :=
              pow_le_pow_left₀ (norm_nonneg _) h1 2
          _ = (((tup P q m).filter (fun v => tprod v = n)).card : ℝ)
                * (((tup P q m).filter (fun v => tprod v = n)).card : ℝ) := by rw [sq]
          _ ≤ K * (((tup P q m).filter (fun v => tprod v = n)).card : ℝ) :=
              mul_le_mul_of_nonneg_right h2 hc
    _ = K * ∑ n ∈ Finset.range (N + 1),
          (((tup P q m).filter (fun v => tprod v = n)).card : ℝ) := by
        rw [Finset.mul_sum]
    _ = K * ((tup P q m).card : ℝ) := by rw [hsumcard]
    _ = (((m+1)^m : ℕ) : ℝ) * ((tup P q m).card : ℝ) := by rw [hKdef]

end Work.BMF
