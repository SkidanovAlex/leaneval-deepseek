import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Submission.Commons.Analysis.Fourier.nested_indicator_l2_bound

open MeasureTheory Finset
open scoped ENNReal BigOperators

namespace Commons.Analysis.Fourier

/-!
### Auxiliary lemmas about finite sup of nonnegative reals

The target lemma compares a Lebesgue integral in `ℝ≥0∞` with the `ofReal` of an ordinary
Lebesgue integral in `ℝ`.  The bridge is the pointwise identity

`(⨆ i ∈ J, ‖f i x‖ₑ) = ENNReal.ofReal (⨆ i ∈ J, ‖f i x‖)`,

which is the `ofReal`-commutation with finite nonnegative suprema proved below.
-/

/-- For a finite set of indices, the indexed supremum in `ℝ` of a nonnegative function agrees
with the `sSup` of its image.  (For `ℝ` the `⨆`-notation is a `csSup`, so it is convenient to
convert it into the set-theoretic `sSup`.) -/
private lemma sSup_finset_eq_ciSup_of_nonneg {ι : Type*} (J : Finset ι) (a : ι → ℝ)
    (ha : ∀ i, 0 ≤ a i) :
    (⨆ i ∈ J, a i) = sSup (a '' (↑J : Set ι)) := by
  rcases J.eq_empty_or_nonempty with hJ | hne
  · subst hJ; simp [Real.sSup_empty]
  · obtain ⟨j, hj⟩ := hne
    have hne' : J.Nonempty := ⟨j, hj⟩
    rw [Finset.ciSup_eq_max'_image a ⟨j, hj, by rw [Real.sSup_empty]; exact ha j⟩
      (Finset.Nonempty.image hne' a)]
    rw [← Finset.coe_image, Finset.Nonempty.csSup_eq_max' (Finset.Nonempty.image hne' a)]

/-- A finite indexed supremum of nonnegative reals is nonnegative. -/
private lemma ciSup_finset_nonneg {ι : Type*} (J : Finset ι) (a : ι → ℝ)
    (ha : ∀ i, 0 ≤ a i) :
    0 ≤ (⨆ i ∈ J, a i) := by
  rcases J.eq_empty_or_nonempty with hJ | hne
  · subst hJ; simp
  · obtain ⟨j, hj⟩ := hne
    rw [sSup_finset_eq_ciSup_of_nonneg J a ha]
    exact le_trans (ha j) (le_csSup (J.finite_toSet.image a).bddAbove (Set.mem_image_of_mem a hj))

/-- `ENNReal.ofReal` commutes with a finite indexed supremum of nonnegative reals. -/
private lemma ciSup_finset_ofReal_eq_of_nonneg {ι : Type*} (J : Finset ι) (a : ι → ℝ)
    (ha : ∀ i, 0 ≤ a i) :
    (⨆ i ∈ J, ENNReal.ofReal (a i)) = ENNReal.ofReal (⨆ i ∈ J, a i) := by
  rcases J.eq_empty_or_nonempty with hJ | hne
  · subst hJ; simp
  · obtain ⟨j, hj⟩ := hne
    have hne' : J.Nonempty := ⟨j, hj⟩
    have h1 := sSup_finset_eq_ciSup_of_nonneg J a ha
    have h2 : (⨆ i ∈ J, ENNReal.ofReal (a i))
        = sSup ((fun i => ENNReal.ofReal (a i)) '' (↑J : Set ι)) := by
      rw [Finset.ciSup_eq_max'_image (fun i => ENNReal.ofReal (a i))
        ⟨j, hj, by simp⟩ (Finset.Nonempty.image hne' (fun i => ENNReal.ofReal (a i)))]
      rw [← Finset.coe_image]
      rw [Finset.Nonempty.csSup_eq_max' (Finset.Nonempty.image hne' (fun i => ENNReal.ofReal (a i)))]
    rw [h2, h1]
    rw [Set.Finite.map_sSup_of_monotone ENNReal.ofReal_mono
      ⟨a j, Set.mem_image_of_mem a hj⟩ (J.finite_toSet.image a)]
    rw [← Set.image_comp]
    rfl

/-- **`∫⁻ (⨆ ‖f i·‖)^2 = ofReal (∫ (⨆ ‖f i·‖)^2)`.**

For a finite family `f i : ℝ → ℂ` whose (pointwise) finite sup of norms is in `L²`, the Lebesgue
integral of the square of the `ℝ≥0∞`-valued finite sup of `enorm`s equals the `ofReal` of the
ordinary Lebesgue integral of the square of the finite sup of norms. -/
theorem lintegral_iSup_finset_enorm_eq_ofReal {ι : Type*} (J : Finset ι) (f : ι → ℝ → ℂ)
    (h : MeasureTheory.MemLp (fun x : ℝ => ⨆ i ∈ J, ‖f i x‖) 2 MeasureTheory.volume) :
    ∫⁻ x : ℝ, (⨆ i ∈ J, ‖f i x‖ₑ) ^ (2:ℝ) ∂MeasureTheory.volume
      = ENNReal.ofReal (∫ x : ℝ, (⨆ i ∈ J, ‖f i x‖) ^ (2:ℝ)) := by
  have hnn : ∀ x, 0 ≤ (⨆ i ∈ J, ‖f i x‖) := fun x =>
    ciSup_finset_nonneg J _ (fun i => norm_nonneg _)
  have hGg : ∀ x, (⨆ i ∈ J, ‖f i x‖ₑ) = ENNReal.ofReal (⨆ i ∈ J, ‖f i x‖) := fun x => by
    simpa only [ofReal_norm] using
      ciSup_finset_ofReal_eq_of_nonneg J (fun i => ‖f i x‖) (fun i => norm_nonneg _)
  have hint : Integrable (fun x : ℝ => (⨆ i ∈ J, ‖f i x‖) ^ (2:ℝ)) volume := by
    have hb := h.integrable_norm_rpow (by norm_num) (by norm_num)
    refine hb.congr (Filter.Eventually.of_forall (fun x => ?_))
    simp only [ENNReal.toReal_ofNat]
    rw [Real.norm_of_nonneg (hnn x)]
  have key : ∫⁻ x : ℝ, (⨆ i ∈ J, ‖f i x‖ₑ) ^ (2:ℝ) ∂volume
      = ∫⁻ x : ℝ, ENNReal.ofReal ((⨆ i ∈ J, ‖f i x‖) ^ (2:ℝ)) ∂volume := by
    apply lintegral_congr
    intro x
    rw [hGg x, ENNReal.ofReal_rpow_of_nonneg (hnn x) (by norm_num)]
  rw [key]
  exact (ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall (fun x => Real.rpow_nonneg (hnn x) 2))).symm

end Commons.Analysis.Fourier