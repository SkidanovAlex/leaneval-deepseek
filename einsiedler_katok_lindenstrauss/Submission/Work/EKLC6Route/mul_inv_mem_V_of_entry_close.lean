import Mathlib
import Submission.Work.EKLComp.inv_mem_V

/-!
# `Work.EKLC6Route.mul_inv_mem_V_of_entry_close`

If `k` lies in the displacement neighbourhood `V ρ` (`ρ ≤ 1/10`) and `k'` is entrywise within
`K` of `k`, then `k' * k⁻¹` lies in `V (3 K (1 + 10 ρ))`.

This is the "`k'` and `k` code the same cell of the grid" step: `k'` is a grid cell representative
close to the element `k` attached to the point, and one needs the correction `k' k⁻¹` to be small
in the same `V`-sense that the whole space uses.

The estimate is entrywise.  Write `A = k`, `B = k'`, `C = k⁻¹` as matrices.  Since `A C = 1`,

  `B C - 1 = (B - A) C = (B - A) + (B - A) (C - 1)`

and the two summands are bounded by `K` and by `3 · K · 10ρ` respectively: the entries of `B - A`
are `≤ K` by hypothesis, and the entries of `C - 1` are `≤ 10ρ` by
`Work.EKLComp.inv_mem_V` applied to `k ∈ V ρ` (`ρ ≤ 1/10 ≤ 1`).  Hence

  `|(B C - 1) i j| ≤ K + 30 K ρ < 3 K + 30 K ρ = 3 K (1 + 10 ρ)`,

the strictness coming from `K > 0` (this is where the extra factor `3` in the conclusion is spent).
-/

namespace Work.EKLC6Route

open Work.EKLContract

/-- Entrywise bound for a `3 × 3` product along a fixed row and column: if the entries of `M` in
row `i` are bounded by `b ≥ 0` and the entries of `N` in column `j` by `d`, then the `(i,j)` entry
of `M * N` is bounded by `3 (b d)` (three terms, each at most `b d`). -/
lemma abs_sum_mul_three {M N : Matrix (Fin 3) (Fin 3) ℝ} {b d : ℝ} (hb : 0 ≤ b) (i j : Fin 3)
    (hA : ∀ l : Fin 3, |M i l| ≤ b) (hB : ∀ l : Fin 3, |N l j| ≤ d) :
    |(M * N) i j| ≤ 3 * (b * d) := by
  rw [Matrix.mul_apply]
  calc |∑ k, M i k * N k j| ≤ ∑ k, |M i k * N k j| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ k, |M i k| * |N k j| := by simp [abs_mul]
    _ ≤ ∑ _k : Fin 3, b * d :=
        Finset.sum_le_sum (fun k _ => mul_le_mul (hA k) (hB k) (abs_nonneg _) hb)
    _ = 3 * (b * d) := by rw [Fin.sum_univ_three]; ring

theorem mul_inv_mem_V_of_entry_close {ρ K : ℝ} (hρ : 0 < ρ) (hρ1 : ρ ≤ 1 / 10) (hK : 0 < K) {k k' : Work.EKLContract.SL3} (hk : k ∈ Work.EKLContract.V ρ) (hclose : ∀ i j, |(k' : Matrix (Fin 3) (Fin 3) ℝ) i j - (k : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ K) : k' * k⁻¹ ∈ Work.EKLContract.V (3 * K * (1 + 10 * ρ)) := by
  -- `k⁻¹` is entrywise `10 ρ`-close to the identity
  have hρ1' : ρ ≤ 1 := by linarith
  have hinv : k⁻¹ ∈ V (10 * ρ) := Work.EKLComp.inv_mem_V hρ hρ1' hk
  have hC : ∀ l j : Fin 3,
      |((k⁻¹ : SL3) : Matrix (Fin 3) (Fin 3) ℝ) l j - (1 : Matrix (Fin 3) (Fin 3) ℝ) l j|
        < 10 * ρ := fun l j => hinv l j
  intro i j
  -- `(k : M) * (k⁻¹ : M) = 1`
  have h1 : (k : Matrix (Fin 3) (Fin 3) ℝ) * ((k⁻¹ : SL3) : Matrix (Fin 3) (Fin 3) ℝ) = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one]
  -- reduce the target to the entry of `(k' - k) * k⁻¹`
  have heq : |((k' * k⁻¹ : SL3) : Matrix (Fin 3) (Fin 3) ℝ) i j
        - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j|
      = |(((k' : Matrix (Fin 3) (Fin 3) ℝ) - (k : Matrix (Fin 3) (Fin 3) ℝ))
          * ((k⁻¹ : SL3) : Matrix (Fin 3) (Fin 3) ℝ)) i j| := by
    rw [Matrix.SpecialLinearGroup.coe_mul, ← Matrix.sub_apply, Matrix.sub_mul, h1]
  rw [heq]
  -- the two entrywise bounds
  have hE : ∀ l : Fin 3,
      |((k' : Matrix (Fin 3) (Fin 3) ℝ) - (k : Matrix (Fin 3) (Fin 3) ℝ)) i l| ≤ K := by
    intro l; rw [Matrix.sub_apply]; exact hclose i l
  have hC' : ∀ l j : Fin 3,
      |((((k⁻¹ : SL3) : Matrix (Fin 3) (Fin 3) ℝ)) - 1) l j| ≤ 10 * ρ := by
    intro l j; rw [Matrix.sub_apply]; exact le_of_lt (hC l j)
  have h2 : |(((k' : Matrix (Fin 3) (Fin 3) ℝ) - (k : Matrix (Fin 3) (Fin 3) ℝ))
      * (((k⁻¹ : SL3) : Matrix (Fin 3) (Fin 3) ℝ) - 1)) i j| ≤ 3 * (K * (10 * ρ)) :=
    abs_sum_mul_three (le_of_lt hK) i j hE (fun l => hC' l j)
  -- `(B - A) C = (B - A) + (B - A)(C - 1)`
  have hsplit : (((k' : Matrix (Fin 3) (Fin 3) ℝ) - (k : Matrix (Fin 3) (Fin 3) ℝ))
      * ((k⁻¹ : SL3) : Matrix (Fin 3) (Fin 3) ℝ)) i j
      = ((k' : Matrix (Fin 3) (Fin 3) ℝ) - (k : Matrix (Fin 3) (Fin 3) ℝ)) i j
        + (((k' : Matrix (Fin 3) (Fin 3) ℝ) - (k : Matrix (Fin 3) (Fin 3) ℝ))
          * (((k⁻¹ : SL3) : Matrix (Fin 3) (Fin 3) ℝ) - 1)) i j := by
    have hC1 : ((k⁻¹ : SL3) : Matrix (Fin 3) (Fin 3) ℝ)
        = 1 + (((k⁻¹ : SL3) : Matrix (Fin 3) (Fin 3) ℝ) - 1) := by abel
    conv_lhs => rw [hC1]
    rw [Matrix.mul_add, Matrix.mul_one, Matrix.add_apply]
  have hfinal : |(((k' : Matrix (Fin 3) (Fin 3) ℝ) - (k : Matrix (Fin 3) (Fin 3) ℝ))
      * ((k⁻¹ : SL3) : Matrix (Fin 3) (Fin 3) ℝ)) i j| ≤ K + 3 * (K * (10 * ρ)) := by
    rw [hsplit]
    exact le_trans (abs_add_le _ _) (add_le_add (hE j) h2)
  -- `K + 30 K ρ < 3 K (1 + 10 ρ)`
  have harith : K + 3 * (K * (10 * ρ)) < 3 * K * (1 + 10 * ρ) := by nlinarith [hK, hρ]
  linarith [hfinal, harith]

end Work.EKLC6Route
