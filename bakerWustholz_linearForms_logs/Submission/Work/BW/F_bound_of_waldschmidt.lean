import Mathlib
import Submission.Work.BW.aligned_defs
import Submission.Work.BW.F_bound_arith
import Submission.Work.BW.sum_mul_prod_erase

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The `F`-bound obtained from Waldschmidt's relation bound

BW §6 reduces the lower bound for a linear form in logarithms to a bound on the weighted
`ℓ¹`-norm `F c y = ∑ᵢ |yᵢ| cᵢ` of an integer relation `y`, with weights `cᵢ = d · h'(αᵢ, ℓᵢ)`
where `d = [K : ℚ]` and `h'` is the modified height `Defs.hmod`.

Waldschmidt's bound controls each *coordinate* of `y` separately:

  `|y_k| ≤ (9 (m-1) d³)^{m-1} · ∏_{j ≠ k} h'(α_j, ℓ_j)`,

(`y` is a rational relation whose *proper* subfamilies are independent, so `y` is determined up to
a scalar; the coordinate bounds are the input) and this file turns that coordinatewise statement
into the statement about `F`.

The mathematics is elementary.  Multiply the bound for `|t_k|` by the nonnegative weight
`d · h'(α_k, ℓ_k) ≥ 0` and sum over `k`: each summand is the same number,

  `d h_k · C · ∏_{j ≠ k} h_j = d · C · ∏_j h_j`  since  `h_k · ∏_{j ≠ k} h_j = ∏_j h_j`,

so the weighted sum is `m d C ∏_j h_j`.  The remaining scalar inequality
`m d (9(m-1)d³)^{m-1} ≤ (9 m d³)^m` (valid for `d ≥ 1`, and for `m = 0` as well) is
`Work.BW.F_bound_arith`; the product identity used is `Work.BW.sum_mul_prod_erase`.
-/

namespace Work.BW

open Complex

/-- The modified height `h'(α, ℓ) = max(h(α)/d, ‖ℓ‖/d, 1/d)` is nonnegative: it dominates the
last term `1/d ≥ 0`. -/
lemma hmod_nonneg_of_field {K : Type*} [Field K] [NumberField K] (β : K) (ℓ : ℂ) :
    0 ≤ hmod β ℓ := by
  have hd : (0 : ℝ) ≤ (Module.finrank ℚ K : ℝ) := Nat.cast_nonneg _
  have h : (0 : ℝ) ≤ 1 / (Module.finrank ℚ K : ℝ) := by
    rw [one_div_nonneg]
    exact hd
  unfold hmod
  exact le_trans h (le_trans (le_max_right _ _) (le_max_right _ _))

/-- **The `F`-bound from Waldschmidt's relation bound.**  If every coordinate `t k` of an
integer vector `t : Fin m → ℤ` satisfies
`|t k| ≤ (9 (m-1) d³)^{m-1} ∏_{j ≠ k} h'(α_j, ℓ_j)`, then the weighted `ℓ¹`-norm with weights
`d · h'(αᵢ, ℓᵢ)` is at most `(9 m d³)^m ∏ᵢ h'(αᵢ, ℓᵢ)`, where `d = [K : ℚ]`. -/
theorem F_bound_of_waldschmidt {K : Type*} [Field K] [NumberField K] {m : ℕ} (α : Fin m → K)
    (ℓ : Fin m → ℂ) (t : Fin m → ℤ)
    (ht : ∀ k : Fin m, |((t k : ℤ) : ℝ)| ≤
      (9 * ((m : ℝ) - 1) * (Module.finrank ℚ K : ℝ) ^ 3) ^ (m - 1) *
        ∏ j ∈ Finset.univ.erase k, hmod (α j) (ℓ j)) :
    wn (fun i => (Module.finrank ℚ K : ℝ) * hmod (α i) (ℓ i)) t ≤
      (9 * (m : ℝ) * (Module.finrank ℚ K : ℝ) ^ 3) ^ m * ∏ i, hmod (α i) (ℓ i) := by
  classical
  -- `d = [K : ℚ] ≥ 1`: `K` is a nontrivial field, so it is not the zero-dimensional `ℚ`-space.
  have hd1 : (1 : ℝ) ≤ (Module.finrank ℚ K : ℝ) := by
    have h : 0 < Module.finrank ℚ K := Module.finrank_pos
    exact_mod_cast h
  have hmod0 : ∀ i, 0 ≤ hmod (α i) (ℓ i) := fun i => hmod_nonneg_of_field (α i) (ℓ i)
  rw [wn]
  set d : ℝ := (Module.finrank ℚ K : ℝ) with hddef
  set C : ℝ := (9 * ((m : ℝ) - 1) * d ^ 3) ^ (m - 1) with hCdef
  set Pr : ℝ := ∏ i, hmod (α i) (ℓ i) with hPrdef
  have hd0 : (0 : ℝ) ≤ d := by rw [hddef]; exact Nat.cast_nonneg _
  have hd1' : (1 : ℝ) ≤ d := by rw [hddef]; exact hd1
  have hP0 : 0 ≤ Pr := by
    rw [hPrdef]
    exact Finset.prod_nonneg fun i _ => hmod0 i
  -- the one-omitted products sum to `m · ∏ h`
  have hsum : ∑ i, hmod (α i) (ℓ i) * ∏ j ∈ Finset.univ.erase i, hmod (α j) (ℓ j)
      = (m : ℝ) * Pr := by
    rw [sum_mul_prod_erase, ← hPrdef]
  calc ∑ i, |((t i : ℤ) : ℝ)| * (d * hmod (α i) (ℓ i))
      ≤ ∑ i, (C * ∏ j ∈ Finset.univ.erase i, hmod (α j) (ℓ j)) *
          (d * hmod (α i) (ℓ i)) := by
        -- multiply the coordinatewise Waldschmidt bound by the nonnegative weight `d · h'`
        apply Finset.sum_le_sum
        intro i _
        exact mul_le_mul_of_nonneg_right (ht i) (mul_nonneg hd0 (hmod0 i))
    _ = (C * d) * ((m : ℝ) * Pr) := by
        -- every summand equals `(C * d) * ∏ h`
        rw [← hsum, Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring
    _ = (m : ℝ) * ((C * d) * Pr) := by ring
    _ ≤ (9 * (m : ℝ) * d ^ 3) ^ m * Pr := by
        have harith : (m : ℝ) * d * C ≤ (9 * (m : ℝ) * d ^ 3) ^ m := by
          rw [hCdef]
          exact F_bound_arith m hd1'
        calc (m : ℝ) * ((C * d) * Pr) = ((m : ℝ) * d * C) * Pr := by ring
          _ ≤ (9 * (m : ℝ) * d ^ 3) ^ m * Pr := mul_le_mul_of_nonneg_right harith hP0

end Work.BW
