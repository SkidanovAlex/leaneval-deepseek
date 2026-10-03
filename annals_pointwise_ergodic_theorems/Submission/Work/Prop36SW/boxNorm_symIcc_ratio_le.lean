import Mathlib
import Submission.Work.Peluse.Basic

/-!
# The window-ratio inequality for the Gowers box norm

The box sum `Work.Peluse.boxSumPow t Q S f` sums its shift variable `x` over all of `ℤ`, so the
ambient window `S` enters only through the normalising factor `|S|⁻¹`:

    boxNormPow t Q (symIcc N') f = (|symIcc N| / |symIcc N'|) * boxNormPow t Q (symIcc N) f .

Taking the `1/2^t`-th root — an exponent lying in `[0,1]` — turns the ratio, which is `≤ 1` for
nested windows `N ≤ N'`, into something that only *increases*:

    (|symIcc N| / |symIcc N'|) * boxNorm t Q (symIcc N) f ≤ boxNorm t Q (symIcc N') f .

This is the per-term (per direction family) inequality behind the ambient monotonicity of the
`Prop36SW` state: enlarging the support window can only help.
-/

namespace Work.Prop36SW

open scoped BigOperators

noncomputable section

open Work.Peluse

/-! ## The window of a box sum is only a normalisation -/

/-- The cube sum is `|S|⁻¹` times a factor independent of the ambient set `S`. -/
private lemma boxSumPow_eq_inv_mul_common {t : ℕ} (Q : Fin t → Finset ℤ) (f : ℤ → ℂ) :
    ∃ A : ℂ, ∀ S : Finset ℤ, boxSumPow t Q S f = ((S.card : ℂ))⁻¹ * A := by
  refine ⟨(∏ i : Fin t, (((Q i).card : ℂ))⁻¹) * (∏ i : Fin t, (((Q i).card : ℂ))⁻¹) *
      ∑ h : (i : Fin t) → {x : ℤ // x ∈ Q i}, ∑ h' : (i : Fin t) → {x : ℤ // x ∈ Q i},
        ∑' x : ℤ, ∏ ω : Fin t → Bool,
          (star^[weight ω]) (f (x + cornerShift (fun i => (h i).1) (fun i => (h' i).1) ω)), ?_⟩
  intro S
  simp only [boxSumPow, prodCubeSum_eq]
  ring

/-- Changing the ambient set rescales the box-norm power by the ratio of the cardinalities
(here written for the two symmetric windows). -/
private lemma boxNormPow_symIcc_ratio {t : ℕ} (Q : Fin t → Finset ℤ) (N N' : ℕ) (f : ℤ → ℂ) :
    boxNormPow t Q (symIcc N') f
      = (((symIcc N).card : ℝ) / ((symIcc N').card : ℝ)) *
          boxNormPow t Q (symIcc N) f := by
  obtain ⟨A, hA⟩ := boxSumPow_eq_inv_mul_common Q f
  have h1 : boxSumPow t Q (symIcc N') f = (((symIcc N').card : ℂ))⁻¹ * A := hA _
  have h2 : boxSumPow t Q (symIcc N) f = (((symIcc N).card : ℂ))⁻¹ * A := hA _
  have hmem' : (0 : ℤ) ∈ symIcc N' := by simp [symIcc]
  have hmem : (0 : ℤ) ∈ symIcc N := by simp [symIcc]
  have ha : (((symIcc N').card : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Finset.card_pos.mpr ⟨0, hmem'⟩))
  have hb : (((symIcc N).card : ℕ) : ℝ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Finset.card_pos.mpr ⟨0, hmem⟩))
  rw [boxNormPow, boxNormPow, h1, h2, norm_mul, norm_mul, norm_inv, norm_inv,
    Complex.norm_natCast, Complex.norm_natCast]
  field_simp
  try ring

/-! ## Two elementary real-variable facts -/

/-- For `0 < x ≤ 1` and `z ≤ 1` one has `x ≤ x^z`. -/
private lemma self_le_rpow_of_le_one {x z : ℝ} (hx0 : 0 < x) (hx1 : x ≤ 1) (hz1 : z ≤ 1) :
    x ≤ x ^ z := by
  have h : x ^ (1 : ℝ) ≤ x ^ z := Real.rpow_le_rpow_of_exponent_ge hx0 hx1 hz1
  simpa using h

/-- `1 / 2^t ≤ 1`. -/
private lemma one_div_two_pow_le_one (t : ℕ) : (1 : ℝ) / (2 : ℝ) ^ t ≤ 1 :=
  (div_le_one (by positivity)).mpr (one_le_pow₀ (by norm_num))

/-! ## The main inequality -/

theorem boxNorm_symIcc_ratio_le {t : ℕ} (Q : Fin t → Finset ℤ) {N N' : ℕ} (hNN' : N ≤ N') (f : ℤ → ℂ) :
    (((Work.Peluse.symIcc N).card : ℝ) / ((Work.Peluse.symIcc N').card : ℝ))
        * Work.Peluse.boxNorm t Q (Work.Peluse.symIcc N) f
      ≤ Work.Peluse.boxNorm t Q (Work.Peluse.symIcc N') f := by
  -- the windows are nested, hence the cardinality ratio lies in `(0,1]`
  have hsub : symIcc N ⊆ symIcc N' := by
    rw [symIcc, symIcc]
    refine Finset.Icc_subset_Icc ?_ ?_
    · have hc : (N : ℤ) ≤ (N' : ℤ) := by exact_mod_cast hNN'
      exact neg_le_neg hc
    · exact_mod_cast hNN'
  have hcard_le : (symIcc N).card ≤ (symIcc N').card := Finset.card_le_card hsub
  have hposN : (0 : ℝ) < ((symIcc N).card : ℝ) := by
    have h : 0 < (symIcc N).card := Finset.card_pos.mpr ⟨0, by simp [symIcc]⟩
    exact_mod_cast h
  have hposN' : (0 : ℝ) < ((symIcc N').card : ℝ) := by
    have h : 0 < (symIcc N').card := Finset.card_pos.mpr ⟨0, by simp [symIcc]⟩
    exact_mod_cast h
  set c : ℝ := ((Work.Peluse.symIcc N).card : ℝ) / ((Work.Peluse.symIcc N').card : ℝ) with hcdef
  have hcpos : 0 < c := by rw [hcdef]; exact div_pos hposN hposN'
  have hcle : c ≤ 1 := by
    rw [hcdef]
    exact div_le_one_of_le₀ (by exact_mod_cast hcard_le) (le_of_lt hposN')
  -- the exact scaling identity for the box-norm power
  have hratio : boxNormPow t Q (symIcc N') f = c * boxNormPow t Q (symIcc N) f := by
    rw [hcdef]
    exact boxNormPow_symIcc_ratio Q N N' f
  -- the exponent `1/2^t` lies in `(0,1]`, so raising the ratio `≤ 1` to it increases it
  have hY0 : (0 : ℝ) ≤ boxNormPow t Q (symIcc N) f := norm_nonneg _
  have hp1 : (1 : ℝ) / (2 : ℝ) ^ t ≤ 1 := one_div_two_pow_le_one t
  have hcp : c ≤ c ^ (1 / (2 : ℝ) ^ t) := self_le_rpow_of_le_one hcpos hcle hp1
  have hmain : c * (boxNormPow t Q (symIcc N) f) ^ (1 / (2 : ℝ) ^ t)
      ≤ (c * boxNormPow t Q (symIcc N) f) ^ (1 / (2 : ℝ) ^ t) := by
    rw [Real.mul_rpow (le_of_lt hcpos) hY0]
    exact mul_le_mul_of_nonneg_right hcp (Real.rpow_nonneg hY0 _)
  simp only [Work.Peluse.boxNorm]
  rw [hratio]
  exact hmain

end

end Work.Prop36SW
