import Mathlib
import Submission.Work.EKLC6Core.Basic
import Submission.Work.EKLC6Core.adjugate_entry_bound_abs

/-!
# `Work.EKLC6Core.V_mul_inv_bound`

The displacement neighbourhoods `V δ = {g : SL₃(ℝ) | ∀ i j, |g i j - 1 i j| < δ}` are bounded
in the following sense: the "distance" `b · a⁻¹` between two elements of `V ρ` stays in a
fixed neighbourhood `V R` of the identity.

The proof is the elementary entrywise estimate.  If `a, b ∈ V ρ` with `ρ > 0`, then

* every entry of `a` and of `b` is bounded in absolute value by `1 + ρ`;
* `det a = 1`, so `a⁻¹` is the adjugate of `a`, whose entries are `2 × 2` minors of `a` and hence
  bounded in absolute value by `2 (1 + ρ)²`;
* consequently every entry of `b · a⁻¹` is bounded by `3 · (1 + ρ) · 2 (1 + ρ)² = 6 (1 + ρ)³`,
  and every entry of `b · a⁻¹ - 1` is bounded by `6 (1 + ρ)³ + 1 < 6 (1 + ρ)³ + 2`.

Hence `R = 6 (1 + ρ)³ + 2` works.
-/

namespace Work.EKLC6Core

open Work.EKLContract

/-- Any `g ∈ V δ` has every entry bounded in absolute value by `1 + δ`. -/
lemma entry_abs_le_of_mem_V {δ : ℝ} {g : Work.EKLContract.SL3}
    (hg : g ∈ Work.EKLContract.V δ) :
    ∀ i j : Fin 3, |(g : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ 1 + δ := by
  intro i j
  have h1 : |(1 : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ 1 := by
    rw [Matrix.one_apply]; split <;> simp
  calc |(g : Matrix (Fin 3) (Fin 3) ℝ) i j|
      = |((g : Matrix (Fin 3) (Fin 3) ℝ) i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j)
          + (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| := by ring_nf
    _ ≤ |(g : Matrix (Fin 3) (Fin 3) ℝ) i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j|
          + |(1 : Matrix (Fin 3) (Fin 3) ℝ) i j| := abs_add_le _ _
    _ ≤ δ + 1 := add_le_add (le_of_lt (hg i j)) h1
    _ = 1 + δ := by ring

theorem V_mul_inv_bound (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ R : ℝ, ∀ a b : Work.EKLContract.SL3, a ∈ Work.EKLContract.V ρ →
      b ∈ Work.EKLContract.V ρ → b * a⁻¹ ∈ Work.EKLContract.V R := by
  refine ⟨6 * (1 + ρ) ^ 3 + 2, ?_⟩
  intro a b ha hb i j
  have ha_bd := entry_abs_le_of_mem_V ha
  have hb_bd := entry_abs_le_of_mem_V hb
  have hM : (0 : ℝ) ≤ 1 + ρ := by linarith
  have hadj : ∀ k j : Fin 3,
      |(a : Matrix (Fin 3) (Fin 3) ℝ).adjugate k j| ≤ 2 * (1 + ρ) ^ 2 :=
    adjugate_entry_bound_abs _ hM ha_bd
  -- `↑(b * a⁻¹) = ↑b * (↑a).adjugate`
  have hcoe : ((b * a⁻¹ : Work.EKLContract.SL3) : Matrix (Fin 3) (Fin 3) ℝ)
      = (b : Matrix (Fin 3) (Fin 3) ℝ) * (a : Matrix (Fin 3) (Fin 3) ℝ).adjugate := by
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv]
  rw [hcoe]
  -- entrywise bound on the product `↑b * (↑a).adjugate`
  have hsum : |((b : Matrix (Fin 3) (Fin 3) ℝ)
        * (a : Matrix (Fin 3) (Fin 3) ℝ).adjugate) i j| ≤ 6 * (1 + ρ) ^ 3 := by
    rw [Matrix.mul_apply]
    calc |∑ k : Fin 3, (b : Matrix (Fin 3) (Fin 3) ℝ) i k
            * (a : Matrix (Fin 3) (Fin 3) ℝ).adjugate k j|
        ≤ ∑ k : Fin 3, |(b : Matrix (Fin 3) (Fin 3) ℝ) i k
            * (a : Matrix (Fin 3) (Fin 3) ℝ).adjugate k j| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _k : Fin 3, (1 + ρ) * (2 * (1 + ρ) ^ 2) := by
          apply Finset.sum_le_sum
          intro k _
          rw [abs_mul]
          exact mul_le_mul (hb_bd i k) (hadj k j) (abs_nonneg _) hM
      _ = 6 * (1 + ρ) ^ 3 := by rw [Fin.sum_univ_three]; ring
  have hone : |(1 : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ 1 := by
    rw [Matrix.one_apply]; split <;> simp
  calc |((b : Matrix (Fin 3) (Fin 3) ℝ) * (a : Matrix (Fin 3) (Fin 3) ℝ).adjugate) i j
        - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j|
      ≤ |((b : Matrix (Fin 3) (Fin 3) ℝ) * (a : Matrix (Fin 3) (Fin 3) ℝ).adjugate) i j|
          + |(1 : Matrix (Fin 3) (Fin 3) ℝ) i j| := by
          rw [sub_eq_add_neg]
          have h := abs_add_le
            (((b : Matrix (Fin 3) (Fin 3) ℝ) * (a : Matrix (Fin 3) (Fin 3) ℝ).adjugate) i j)
            (-((1 : Matrix (Fin 3) (Fin 3) ℝ) i j))
          rw [abs_neg] at h
          exact h
    _ ≤ 6 * (1 + ρ) ^ 3 + 1 := add_le_add hsum hone
    _ < 6 * (1 + ρ) ^ 3 + 2 := by linarith

end Work.EKLC6Core
