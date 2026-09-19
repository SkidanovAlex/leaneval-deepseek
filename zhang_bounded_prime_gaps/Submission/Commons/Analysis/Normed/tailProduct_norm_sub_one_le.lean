import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Log.Summable
import Submission.Commons.Analysis.Complex.norm_ratio_sub_one_le

namespace Commons.Analysis.Normed

open scoped BigOperators

/-- Telescoping bound for the sum of inverse squares over a finite set of
naturals all exceeding `w ≥ 1`: `∑_{p ∈ S} 1/p² ≤ 1/w`.

This is the elementary estimate behind `∏_{p > w}(1 + O(p⁻²)) = 1 + o(1)`:
every `p ∈ S` lies in `Ioc w M` for `M = max S`, and
`∑_{w < n ≤ M} 1/n² ≤ 1/w - 1/M ≤ 1/w`. -/
lemma sum_inv_sq_le_inv {S : Finset ℕ} {w : ℕ} (hw : 1 ≤ w)
    (hS : ∀ p ∈ S, w < p) :
    ∑ p ∈ S, ((p : ℝ) ^ 2)⁻¹ ≤ (w : ℝ)⁻¹ := by
  classical
  rcases S.eq_empty_or_nonempty with rfl | hne
  · simp
  · obtain ⟨M, hMmem, hMmax⟩ := S.exists_max_image id hne
    have hwM : w ≤ M := le_of_lt (hS M hMmem)
    have hsub : S ⊆ Finset.Ioc w M := by
      intro p hp
      exact Finset.mem_Ioc.mpr ⟨hS p hp, hMmax p hp⟩
    calc
      ∑ p ∈ S, ((p : ℝ) ^ 2)⁻¹
          ≤ ∑ p ∈ Finset.Ioc w M, ((p : ℝ) ^ 2)⁻¹ :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => by positivity)
      _ ≤ (w : ℝ)⁻¹ - (M : ℝ)⁻¹ :=
            sum_Ioc_inv_sq_le_sub (k := w) (n := M) (by omega) hwM
      _ ≤ (w : ℝ)⁻¹ := by
            have hM : 0 ≤ (M : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg M)
            linarith

theorem tailProduct_norm_sub_one_le {C : ℝ} (hC : 0 ≤ C) {w : ℕ} (hw : 1 ≤ w)
    {S : Finset ℕ} (hS : ∀ p ∈ S, w < p) {z : ℕ → ℂ}
    (hz : ∀ p ∈ S, ‖z p‖ ≤ C / (p : ℝ) ^ 2) :
    ‖∏ p ∈ S, (1 + z p) - 1‖ ≤ Real.exp (C / (w : ℝ)) - 1 := by
  refine (Finset.norm_prod_one_add_sub_one_le S z).trans ?_
  have hsum : ∑ p ∈ S, ‖z p‖ ≤ C / (w : ℝ) := by
    calc
      ∑ p ∈ S, ‖z p‖ ≤ ∑ p ∈ S, C / (p : ℝ) ^ 2 := Finset.sum_le_sum hz
      _ = C * ∑ p ∈ S, ((p : ℝ) ^ 2)⁻¹ := by
            rw [Finset.mul_sum]
            exact Finset.sum_congr rfl (fun p _ => by rw [div_eq_mul_inv])
      _ ≤ C * (w : ℝ)⁻¹ :=
            mul_le_mul_of_nonneg_left (sum_inv_sq_le_inv hw hS) hC
      _ = C / (w : ℝ) := by rw [div_eq_mul_inv]
  exact sub_le_sub_right (Real.exp_le_exp.mpr hsum) 1

end Commons.Analysis.Normed