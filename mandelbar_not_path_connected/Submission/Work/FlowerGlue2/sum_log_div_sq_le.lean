import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.FlowerGlue2

/-- Pointwise telescoping estimate: for `t ≥ 1`, the `n`-th tail term of the sum is bounded
by the difference of `B t = (2 + log t)/t` at consecutive integers. -/
lemma telescope_ineq (t : ℝ) (ht : 1 ≤ t) :
    (1 + Real.log (t + 1)) / (t + 1) ^ 2 ≤
      (2 + Real.log t) / t - (2 + Real.log (t + 1)) / (t + 1) := by
  have ht0 : (0:ℝ) < t := by linarith
  have hinv : (0:ℝ) < 1 + 1/t := by positivity
  have hlog : Real.log (t + 1) = Real.log t + Real.log (1 + 1/t) := by
    have h : t + 1 = t * (1 + 1/t) := by field_simp
    rw [h, Real.log_mul (ne_of_gt ht0) (ne_of_gt hinv)]
  have hstep : Real.log (1 + 1/t) ≤ 1/t := by
    have := Real.log_le_sub_one_of_pos hinv
    linarith
  have hkey : t * Real.log (1 + 1/t) ≤ 1 := by
    have h1 : t * Real.log (1 + 1/t) ≤ t * (1/t) :=
      mul_le_mul_of_nonneg_left hstep (le_of_lt ht0)
    have h2 : t * (1/t) = 1 := by field_simp
    rw [h2] at h1; exact h1
  have hkey2 : t * (t + 2) * Real.log (1 + 1/t) ≤ (t + 2) := by
    have h3 : t * Real.log (1+1/t) * (t+2) ≤ 1 * (t+2) :=
      mul_le_mul_of_nonneg_right hkey (by linarith)
    linarith [h3]
  have hlogt : (0:ℝ) ≤ Real.log t := Real.log_nonneg ht
  have heq : (2 + Real.log t) / t - (2 + Real.log (t + 1)) / (t + 1) -
      (1 + Real.log (t + 1)) / (t + 1) ^ 2
      = ((t + 2) + Real.log t - t * (t + 2) * Real.log (1 + 1/t)) / (t * (t + 1) ^ 2) := by
    rw [hlog]; field_simp; ring
  have hnum : (0:ℝ) ≤ (t + 2) + Real.log t - t * (t + 2) * Real.log (1 + 1/t) := by
    linarith [hkey2, hlogt]
  have hden : (0:ℝ) < t * (t + 1) ^ 2 := by positivity
  have : 0 ≤ (2 + Real.log t) / t - (2 + Real.log (t + 1)) / (t + 1) -
      (1 + Real.log (t + 1)) / (t + 1) ^ 2 := by
    rw [heq]; exact div_nonneg hnum (le_of_lt hden)
  linarith

theorem sum_log_div_sq_le (v : ℝ) (hv : 1 ≤ v) :
    Summable (fun n : ℕ => (1 + Real.log (v + (n : ℝ))) / (v + (n : ℝ)) ^ 2) ∧
      ∑' n : ℕ, (1 + Real.log (v + (n : ℝ))) / (v + (n : ℝ)) ^ 2 ≤
        8 * (1 + Real.log v) / v := by
  have hv0 : (0:ℝ) < v := by linarith
  set f : ℕ → ℝ := fun n : ℕ => (1 + Real.log (v + (n : ℝ))) / (v + (n : ℝ)) ^ 2 with hf
  set g : ℕ → ℝ := fun n : ℕ => (2 + Real.log (v + (n : ℝ))) / (v + (n : ℝ)) with hg
  have hfnn : ∀ n, 0 ≤ f n := by
    intro n
    have hn : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
    have hpos : (0:ℝ) < v + (n:ℝ) := by linarith
    have hlog : (0:ℝ) ≤ Real.log (v + (n:ℝ)) := Real.log_nonneg (by linarith)
    simp only [hf]
    exact div_nonneg (by linarith) (by positivity)
  have hgnn : ∀ n, 0 ≤ g n := by
    intro n
    have hn : (0:ℝ) ≤ (n:ℝ) := Nat.cast_nonneg n
    have hpos : (0:ℝ) < v + (n:ℝ) := by linarith
    have hlog : (0:ℝ) ≤ Real.log (v + (n:ℝ)) := Real.log_nonneg (by linarith)
    simp only [hg]
    exact div_nonneg (by linarith) (by positivity)
  have htel : ∀ i, f (i+1) ≤ g i - g (i+1) := by
    intro i
    have h1 : (1:ℝ) ≤ v + (i:ℝ) := by
      have : (0:ℝ) ≤ (i:ℝ) := Nat.cast_nonneg i
      linarith
    have hcast : v + ((i+1 : ℕ) : ℝ) = (v + (i:ℝ)) + 1 := by push_cast; ring
    have key := telescope_ineq (v + (i:ℝ)) h1
    simp only [hf, hg, hcast]
    exact key
  have hbound : ∀ N, ∑ i ∈ Finset.range N, f i ≤ f 0 + g 0 := by
    intro N
    cases N with
    | zero => simp only [Finset.range_zero, Finset.sum_empty]; linarith [hfnn 0, hgnn 0]
    | succ M =>
      rw [Finset.sum_range_succ']
      have h1 : ∑ i ∈ Finset.range M, f (i+1) ≤ ∑ i ∈ Finset.range M, (g i - g (i+1)) :=
        Finset.sum_le_sum (fun i _ => htel i)
      rw [Finset.sum_range_sub'] at h1
      linarith [h1, hgnn M]
  have hf0 : f 0 = (1 + Real.log v)/v^2 := by simp [hf]
  have hg0 : g 0 = (2 + Real.log v)/v := by simp [hg]
  have hmain : f 0 + g 0 ≤ 8*(1+Real.log v)/v := by
    rw [hf0, hg0]
    have hL : (0:ℝ) ≤ Real.log v := Real.log_nonneg hv
    have hsub : 8*(1 + Real.log v)/v - ((1 + Real.log v)/v^2 + (2 + Real.log v)/v)
        = (7*v*Real.log v + 6*v - 1 - Real.log v)/v^2 := by
      field_simp; ring
    have hnum : 0 ≤ 7*v*Real.log v + 6*v - 1 - Real.log v := by
      have hprod : 0 ≤ Real.log v * (7*v - 1) := mul_nonneg hL (by linarith)
      nlinarith [hprod, hv]
    have : 0 ≤ 8*(1 + Real.log v)/v - ((1 + Real.log v)/v^2 + (2 + Real.log v)/v) := by
      rw [hsub]; exact div_nonneg hnum (by positivity)
    linarith
  have hC : ∀ N, ∑ i ∈ Finset.range N, f i ≤ 8*(1+Real.log v)/v :=
    fun N => le_trans (hbound N) hmain
  constructor
  · exact summable_of_sum_range_le hfnn hC
  · exact Real.tsum_le_of_sum_range_le hfnn hC

end Work.FlowerGlue2
