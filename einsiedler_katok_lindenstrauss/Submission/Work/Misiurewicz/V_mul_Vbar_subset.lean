import Mathlib
import Submission.Work.EKLComp.Misiurewicz.Defs

/-!
# `V ε · Vbar r ⊆ V r'` for `0 < r < r'`

`Work.EKLContract.V δ = {g | ∀ i j, |g i j - 1 i j| < δ}` is the entrywise `δ`-ball around the
identity in `SL₃(ℝ)` and `Work.EKLComp.Vbar r` is the corresponding closed entrywise box.  This
file proves the elementary product estimate: for `0 < r < r'` there is `ε > 0` with

`V ε · Vbar r ⊆ V r'`.

Writing `A = 1 + a`, `B = 1 + b` the identity

`A * B - 1 = a * b + a + b`

(for matrices; note `1 * B = B` and `A * 1 = A`) gives the entrywise expansion

`(A * B) i j - 1 i j = (A i j - 1 i j) + (B i j - 1 i j) + ∑ k, (A i k - 1 i k) * (B k j - 1 k j)`,

so `|(A * B) i j - 1 i j| ≤ ε + r + 3 ε r`, which is `< r'` for `ε = (r' - r) / (2 (1 + 3 r))`.
-/

namespace Work.Misiurewicz

open Work.EKLContract

/-- Entrywise size of a product of matrices close to the identity.

If every entry of `A` is within `ε` of the identity and every entry of `B` is within `r ≥ 0` of
the identity, then every entry of `A * B` is within `ε + r + 3 ε r` of the identity. -/
lemma matrix_mul_entry_bound {ε r r' : ℝ} (hε : 0 < ε)
    (hbound : ε + r + 3 * ε * r < r') {A B : Matrix (Fin 3) (Fin 3) ℝ}
    (hA : ∀ i j, |A i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| < ε)
    (hB : ∀ i j, |B i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| ≤ r) :
    ∀ i j, |(A * B) i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j| < r' := by
  intro i j
  have hexp : (A * B) i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j
      = (A i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j)
        + (B i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j)
        + ∑ k, (A i k - (1 : Matrix (Fin 3) (Fin 3) ℝ) i k)
               * (B k j - (1 : Matrix (Fin 3) (Fin 3) ℝ) k j) := by
    have h1 : A * B - 1 = (A - 1) * (B - 1) + (A - 1) + (B - 1) := by noncomm_ring
    have h2 := congrFun (congrFun h1 i) j
    simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.mul_apply] at h2
    rw [Matrix.mul_apply]
    linarith [h2]
  rw [hexp]
  have hsum : |∑ k : Fin 3, (A i k - (1 : Matrix (Fin 3) (Fin 3) ℝ) i k)
      * (B k j - (1 : Matrix (Fin 3) (Fin 3) ℝ) k j)| ≤ 3 * (ε * r) := by
    calc |∑ k : Fin 3, (A i k - (1 : Matrix (Fin 3) (Fin 3) ℝ) i k)
            * (B k j - (1 : Matrix (Fin 3) (Fin 3) ℝ) k j)|
        ≤ ∑ k : Fin 3, |(A i k - (1 : Matrix (Fin 3) (Fin 3) ℝ) i k)
            * (B k j - (1 : Matrix (Fin 3) (Fin 3) ℝ) k j)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ = ∑ k : Fin 3, |A i k - (1 : Matrix (Fin 3) (Fin 3) ℝ) i k|
            * |B k j - (1 : Matrix (Fin 3) (Fin 3) ℝ) k j| := by
          exact Finset.sum_congr rfl fun k _ => abs_mul _ _
      _ ≤ ∑ _k : Fin 3, ε * r := by
          apply Finset.sum_le_sum
          intro k _
          exact mul_le_mul (le_of_lt (hA i k)) (hB k j) (abs_nonneg _) (le_of_lt hε)
      _ = 3 * (ε * r) := by simp
  have htri : |(A i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j)
        + (B i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j)
        + ∑ k, (A i k - (1 : Matrix (Fin 3) (Fin 3) ℝ) i k)
               * (B k j - (1 : Matrix (Fin 3) (Fin 3) ℝ) k j)|
      ≤ |A i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j|
        + |B i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j|
        + |∑ k, (A i k - (1 : Matrix (Fin 3) (Fin 3) ℝ) i k)
               * (B k j - (1 : Matrix (Fin 3) (Fin 3) ℝ) k j)| := by
    calc |(A i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j)
            + (B i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j)
            + ∑ k, (A i k - (1 : Matrix (Fin 3) (Fin 3) ℝ) i k)
               * (B k j - (1 : Matrix (Fin 3) (Fin 3) ℝ) k j)|
        ≤ |(A i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j)
            + (B i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j)|
          + |∑ k, (A i k - (1 : Matrix (Fin 3) (Fin 3) ℝ) i k)
               * (B k j - (1 : Matrix (Fin 3) (Fin 3) ℝ) k j)| := abs_add_le _ _
      _ ≤ |A i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j|
          + |B i j - (1 : Matrix (Fin 3) (Fin 3) ℝ) i j|
          + |∑ k, (A i k - (1 : Matrix (Fin 3) (Fin 3) ℝ) i k)
               * (B k j - (1 : Matrix (Fin 3) (Fin 3) ℝ) k j)| := by
          gcongr
          exact abs_add_le _ _
  linarith [htri, hsum, hA i j, hB i j, hbound]

theorem V_mul_Vbar_subset {r r' : ℝ} (hr : 0 < r) (hrr' : r < r') :
    ∃ ε > 0, ∀ g : Work.EKLContract.SL3, g ∈ Work.EKLContract.V ε →
      ∀ h : Work.EKLContract.SL3, h ∈ Work.EKLComp.Vbar r → g * h ∈ Work.EKLContract.V r' := by
  have hr0 : (0 : ℝ) ≤ r := le_of_lt hr
  have hd : (0 : ℝ) < r' - r := by linarith
  have hden : (0 : ℝ) < 2 * (1 + 3 * r) := by linarith
  have hεpos : (0 : ℝ) < (r' - r) / (2 * (1 + 3 * r)) := div_pos hd hden
  have hkey : (r' - r) / (2 * (1 + 3 * r)) * (1 + 3 * r) = (r' - r) / 2 := by
    field_simp
  have hbound :
      (r' - r) / (2 * (1 + 3 * r)) + r + 3 * ((r' - r) / (2 * (1 + 3 * r))) * r < r' := by
    have h3 : (r' - r) / (2 * (1 + 3 * r)) + 3 * ((r' - r) / (2 * (1 + 3 * r))) * r
        = (r' - r) / (2 * (1 + 3 * r)) * (1 + 3 * r) := by ring
    rw [show (r' - r) / (2 * (1 + 3 * r)) + r + 3 * ((r' - r) / (2 * (1 + 3 * r))) * r
          = ((r' - r) / (2 * (1 + 3 * r))
              + 3 * ((r' - r) / (2 * (1 + 3 * r))) * r) + r by ring, h3, hkey]
    linarith
  refine ⟨(r' - r) / (2 * (1 + 3 * r)), hεpos, ?_⟩
  intro g hg h hh i j
  rw [Matrix.SpecialLinearGroup.coe_mul]
  exact matrix_mul_entry_bound hεpos hbound hg hh i j

end Work.Misiurewicz
