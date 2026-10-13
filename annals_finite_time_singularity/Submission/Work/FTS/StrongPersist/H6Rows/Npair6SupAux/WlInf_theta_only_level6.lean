import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.PhiStar.Psi0Est.WlInf_theta_only_six
import Submission.Work.FTS.PhiStar.Psi0Est.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongPersist.H6Rows.Npair6SupAux

open scoped Real Topology ContDiff
open MeasureTheory Set Filter

/-!
# The `𝒲^{6,∞}`-bound for a function of `θ` alone

This is the level-`6` analogue of `Work.FTS.PhiStar.Psi0Est.WlInf_theta_only_six` (which is
the level-`5` statement).  For `F = fun _ θ => g θ` (a function of the angular variable
alone) all the radial derivatives `pzIter k F` vanish for `k ≥ 1`
(`pzIter_theta_only_succ`) and `DthIter j F = fun _ θ => dthU^[j] g θ` (`DthIter_theta_only`),
so in `WlInf α 6 F` only the slots with `k = 0` survive:

* the radial slot `k = 0` contributes `supAbs (fun _ θ => g θ) ≤ C`;
* the six angular slots `k = 0`, `1 ≤ j ≤ 6` contribute
  `supAbs (fun _ θ => dthU^[j] g θ · sin(2θ)^{-α/5}/(α + sin(2θ))) ≤ C` each;
* every slot with `k ≥ 1` is the supremum of the zero function.

Total `C + 6C = 7C`.
-/

/-- `∂_z^k` of a function of `θ` alone vanishes for `k ≥ 1`. -/
private lemma pzIter_theta_eq_zero (g : ℝ → ℝ) {k : ℕ} (hk : 1 ≤ k) :
    Work.Spaces.pzIter k (fun _ θ => g θ) = fun _ _ => (0 : ℝ) := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  exact Work.FTS.PhiStar.Psi0Est.pzIter_theta_only_succ g k'

/-- `∂_z^k D_θ^j` of a function of `θ` alone vanishes for `k ≥ 1`. -/
private lemma pzIter_DthIter_theta_eq_zero (g : ℝ → ℝ) (j : ℕ) {k : ℕ} (hk : 1 ≤ k) :
    Work.Spaces.pzIter k (Work.Spaces.DthIter j (fun _ θ => g θ)) = fun _ _ => (0 : ℝ) := by
  rw [Work.FTS.PhiStar.Psi0Est.DthIter_theta_only]
  exact pzIter_theta_eq_zero (Work.Spaces.dthU^[j] g) hk

/-- `|a·s/d| = |a|·s/d` for `s, d ≥ 0`. -/
private lemma abs_mul_div_of_nonneg {a s d : ℝ} (hs : 0 ≤ s) (hd : 0 ≤ d) :
    |a * s / d| = |a| * s / d := by
  rw [abs_div, abs_mul, abs_of_nonneg hs, abs_of_nonneg hd]

/-- The angular slot with `k = 0` and order `1 ≤ j ≤ 6` is bounded by `C`. -/
private lemma angSlot_zero_le (α C : ℝ) (hα : 0 < α) (g : ℝ → ℝ)
    (hw : ∀ j : ℕ, 1 ≤ j → j ≤ 6 → ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.dthU^[j] g θ| * (Real.sin (2 * θ)) ^ (-(α / 5))
        / (α + Real.sin (2 * θ)) ≤ C)
    {j : ℕ} (hj1 : 1 ≤ j) (hj6 : j ≤ 6) :
    Work.Spaces.supAbs (fun z θ => (z + 1) ^ 0
        * Work.Spaces.pzIter 0 (Work.Spaces.DthIter j (fun _ θ => g θ)) z θ
        * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ))) ≤ C := by
  refine Work.Spaces.supAbs_le (fun z _ θ hθ => ?_)
  have hs : 0 ≤ Real.sin (2 * θ) :=
    Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2]⟩
  have hd : 0 ≤ α + Real.sin (2 * θ) := by linarith
  rw [Work.Spaces.pzIter_zero, Work.FTS.PhiStar.Psi0Est.DthIter_theta_only]
  simp only [pow_zero, one_mul]
  rw [abs_mul_div_of_nonneg (Real.rpow_nonneg hs _) hd]
  exact hw j hj1 hj6 θ hθ

private lemma sum7_ite_eq (C : ℝ) :
    (∑ k ∈ Finset.range 7, (if k = 0 then C else (0 : ℝ))) = C := by
  rw [Finset.sum_eq_single 0]
  · simp
  · intro b _ hbne
    rw [ite_eq_right hbne]
  · intro h
    exact absurd (Finset.mem_range.mpr (by norm_num : 0 < 7)) h

private lemma sum77_ite_eq (C : ℝ) :
    (∑ j ∈ Finset.range 7, ∑ k ∈ Finset.range 7,
      (if k = 0 ∧ 1 ≤ j ∧ j ≤ 6 then C else (0 : ℝ))) = 6 * C := by
  have hinner : ∀ j : ℕ, (∑ k ∈ Finset.range 7,
      (if k = 0 ∧ 1 ≤ j ∧ j ≤ 6 then C else (0 : ℝ)))
      = (if 1 ≤ j ∧ j ≤ 6 then C else (0 : ℝ)) := by
    intro j
    rw [Finset.sum_eq_single 0]
    · simp
    · intro b _ hbne
      rw [ite_eq_right (fun h => hbne h.1)]
    · intro h
      exact absurd (Finset.mem_range.mpr (by norm_num : 0 < 7)) h
  rw [Finset.sum_congr rfl (fun j _ => hinner j)]
  rw [Finset.sum_range_succ' (fun j => if 1 ≤ j ∧ j ≤ 6 then C else (0 : ℝ)) 6]
  have h0 : (if 1 ≤ (0 : ℕ) ∧ (0 : ℕ) ≤ 6 then C else (0 : ℝ)) = 0 := by norm_num
  rw [h0, add_zero]
  have hone : ∀ j ∈ Finset.range 6,
      (if 1 ≤ j + 1 ∧ j + 1 ≤ 6 then C else (0 : ℝ)) = C := by
    intro j hj
    have hj6 : j < 6 := Finset.mem_range.mp hj
    rw [ite_eq_left (by omega : 1 ≤ j + 1 ∧ j + 1 ≤ 6)]
  rw [Finset.sum_congr rfl hone, Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  norm_num

/-- Sharp `𝒲^{6,∞}`-reduction for a function of `θ` alone. -/
theorem WlInf_theta_only_level6 (α C : ℝ) (hα : 0 < α) (hC : 0 < C) (g : ℝ → ℝ)
    (hg : ∀ θ ∈ Work.Spaces.Iθ, |g θ| ≤ C)
    (hw : ∀ j : ℕ, 1 ≤ j → j ≤ 6 → ∀ θ ∈ Work.Spaces.Iθ,
      |Work.Spaces.dthU^[j] g θ| * (Real.sin (2 * θ)) ^ (-(α / 5))
        / (α + Real.sin (2 * θ)) ≤ C) :
    Work.Spaces.WlInfMem α 6 (fun _ θ => g θ) ∧
      Work.Spaces.WlInf α 6 (fun _ θ => g θ) ≤ 7 * C := by
  have hC0 : 0 ≤ C := le_of_lt hC
  have hs2 : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ Real.sin (2 * θ) := fun θ hθ =>
    Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2]⟩
  constructor
  · constructor
    · intro k hk
      by_cases hk0 : k = 0
      · subst hk0
        refine Work.Spaces.supFinite_of_pointwise (C := C) (fun z _ θ hθ => ?_)
        simpa using hg θ hθ
      · have hk1 : 1 ≤ k := by omega
        refine Work.Spaces.supFinite_of_pointwise (C := C) (fun z _ θ _ => ?_)
        have hz : Work.Spaces.pzIter k (fun _ θ => g θ) z θ = 0 := by
          rw [pzIter_theta_eq_zero g hk1]
        rw [hz]
        simp only [mul_zero, abs_zero]
        exact hC0
    · intro j _ k _ hj1 hjk
      by_cases hk0 : k = 0
      · subst hk0
        refine Work.Spaces.supFinite_of_pointwise (C := C) (fun z _ θ hθ => ?_)
        have hd : 0 ≤ α + Real.sin (2 * θ) := by linarith [hs2 θ hθ]
        rw [Work.Spaces.pzIter_zero, Work.FTS.PhiStar.Psi0Est.DthIter_theta_only]
        simp only [pow_zero, one_mul]
        rw [abs_mul_div_of_nonneg (Real.rpow_nonneg (hs2 θ hθ) _) hd]
        exact hw j hj1 (by omega) θ hθ
      · have hk1 : 1 ≤ k := by omega
        refine Work.Spaces.supFinite_of_pointwise (C := C) (fun z _ θ _ => ?_)
        have hz : Work.Spaces.pzIter k (Work.Spaces.DthIter j (fun _ θ => g θ)) z θ = 0 := by
          rw [pzIter_DthIter_theta_eq_zero g j hk1]
        rw [hz]
        simp only [mul_zero, zero_mul, zero_div, abs_zero]
        exact hC0
  · rw [Work.Spaces.WlInf]
    have hS1 : (∑ k ∈ Finset.range (6 + 1), Work.Spaces.supAbs (fun z θ =>
        (z + 1) ^ k * Work.Spaces.pzIter k (fun _ θ => g θ) z θ)) ≤ C := by
      refine le_trans (Finset.sum_le_sum (fun k hk => ?_)) (le_of_eq (sum7_ite_eq C))
      by_cases hk0 : k = 0
      · subst hk0
        rw [ite_eq_left rfl]
        refine Work.Spaces.supAbs_le (fun z _ θ hθ => ?_)
        simpa using hg θ hθ
      · have hk1 : 1 ≤ k := by omega
        rw [ite_eq_right hk0]
        refine Work.Spaces.supAbs_le (fun z _ θ _ => ?_)
        have hz : Work.Spaces.pzIter k (fun _ θ => g θ) z θ = 0 := by
          rw [pzIter_theta_eq_zero g hk1]
        rw [hz]
        simp
    have hS2 : (∑ j ∈ Finset.range (6 + 1), ∑ k ∈ Finset.range (6 + 1),
        if 1 ≤ j ∧ k + j ≤ 6 then Work.Spaces.supAbs (fun z θ =>
          (z + 1) ^ k * Work.Spaces.pzIter k (Work.Spaces.DthIter j (fun _ θ => g θ)) z θ
            * (Real.sin (2 * θ)) ^ (-(α / 5)) / (α + Real.sin (2 * θ)))
        else 0) ≤ 6 * C := by
      refine le_trans (Finset.sum_le_sum (fun j _ => Finset.sum_le_sum (fun k _ => ?_)))
        (le_of_eq (sum77_ite_eq C))
      by_cases h : 1 ≤ j ∧ k + j ≤ 6
      · rw [ite_eq_left h]
        have hj1 : 1 ≤ j := h.1
        have hj6 : j ≤ 6 := by omega
        by_cases hk0 : k = 0
        · subst hk0
          rw [ite_eq_left ⟨rfl, hj1, hj6⟩]
          exact angSlot_zero_le α C hα g hw hj1 hj6
        · have hk1 : 1 ≤ k := by omega
          rw [ite_eq_right (fun hh => hk0 hh.1)]
          refine Work.Spaces.supAbs_le (fun z _ θ _ => ?_)
          have hz : Work.Spaces.pzIter k (Work.Spaces.DthIter j (fun _ θ => g θ)) z θ = 0 := by
            rw [pzIter_DthIter_theta_eq_zero g j hk1]
          rw [hz]
          simp
      · rw [ite_eq_right h]
        split_ifs with hh
        · exact hC0
        · exact le_refl 0
    linarith

end Work.FTS.StrongPersist.H6Rows.Npair6SupAux
