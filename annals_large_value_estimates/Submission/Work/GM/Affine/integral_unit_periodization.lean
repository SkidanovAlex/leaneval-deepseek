import Mathlib

namespace Work.GM.Affine

open MeasureTheory
open scoped BigOperators ENNReal

/-- The half-open unit intervals `(n, n+1]`, `n : ℤ`, are pairwise disjoint. -/
private lemma disjoint_Ioc_intCast (m n : ℤ) (h : m ≠ n) :
    Disjoint (Set.Ioc (m : ℝ) ((m : ℝ) + 1)) (Set.Ioc (n : ℝ) ((n : ℝ) + 1)) := by
  rw [Set.disjoint_left]
  intro x hmx hnx
  rcases lt_or_gt_of_ne h with hlt | hgt
  · have hcast : (m : ℝ) + 1 ≤ (n : ℝ) := by
      have : m + 1 ≤ n := by omega
      exact_mod_cast this
    have hx1 : x ≤ (m : ℝ) + 1 := hmx.2
    have hx2 : (n : ℝ) < x := hnx.1
    linarith
  · have hcast : (n : ℝ) + 1 ≤ (m : ℝ) := by
      have : n + 1 ≤ m := by omega
      exact_mod_cast this
    have hx1 : x ≤ (n : ℝ) + 1 := hnx.2
    have hx2 : (m : ℝ) < x := hmx.1
    linarith

/-- Translation invariance of the set Lebesgue integral: `∫⁻_{[0,1]} f (a + u) du = ∫⁻_{[a,a+1]} f`. -/
private lemma setLIntegral_comp_add_left_Ioc (f : ℝ → ℝ≥0∞) (a : ℝ) :
    ∫⁻ u in Set.Ioc (0 : ℝ) 1, f (a + u) = ∫⁻ x in Set.Ioc a (a + 1), f x := by
  have h := MeasurePreserving.setLIntegral_comp_emb (measurePreserving_add_left volume a)
      (Homeomorph.addLeft a).measurableEmbedding f (Set.Ioc (0 : ℝ) 1)
  rw [Set.image_const_add_Ioc] at h
  simpa using h

/-- Translation invariance of the set Bochner integral: `∫_{[0,1]} F (a + u) du = ∫_{[a,a+1]} F`. -/
private lemma setIntegral_comp_add_left_Ioc {F : ℝ → ℝ} (a : ℝ) :
    ∫ u in Set.Ioc (0 : ℝ) 1, F (a + u) = ∫ x in Set.Ioc a (a + 1), F x := by
  have h := (MeasurePreserving.setIntegral_image_emb (measurePreserving_add_left volume a)
      (Homeomorph.addLeft a).measurableEmbedding F (Set.Ioc (0 : ℝ) 1)).symm
  rw [Set.image_const_add_Ioc] at h
  simpa using h

/-- The Lebesgue integral over `ℝ` as the sum of the integrals over the unit intervals `(n, n+1]`. -/
private lemma lintegral_intCast_Ioc_tsum (g : ℝ → ℝ≥0∞) :
    ∫⁻ x, g x = ∑' n : ℤ, ∫⁻ x in Set.Ioc (n : ℝ) ((n : ℝ) + 1), g x := by
  have hd : Pairwise (Function.onFun Disjoint (fun n : ℤ => Set.Ioc (n : ℝ) ((n : ℝ) + 1))) :=
    fun m n hmn => disjoint_Ioc_intCast m n hmn
  have h := lintegral_iUnion (μ := volume) (s := fun n : ℤ => Set.Ioc (n : ℝ) ((n : ℝ) + 1))
      (fun n => measurableSet_Ioc) hd g
  rw [iUnion_Ioc_intCast ℝ, Measure.restrict_univ] at h
  exact h

/-- The Bochner integral over `ℝ` as the sum of the integrals over the unit intervals `(n, n+1]`. -/
private lemma integral_intCast_Ioc_tsum {F : ℝ → ℝ} (hint : Integrable F) :
    ∫ x, F x = ∑' n : ℤ, ∫ x in Set.Ioc (n : ℝ) ((n : ℝ) + 1), F x := by
  have hd : Pairwise (Function.onFun Disjoint (fun n : ℤ => Set.Ioc (n : ℝ) ((n : ℝ) + 1))) :=
    fun m n hmn => disjoint_Ioc_intCast m n hmn
  have hintU : IntegrableOn F (⋃ n : ℤ, Set.Ioc (n : ℝ) ((n : ℝ) + 1)) volume := by
    rw [iUnion_Ioc_intCast ℝ]
    exact integrableOn_univ.mpr hint
  have h := integral_iUnion (s := fun n : ℤ => Set.Ioc (n : ℝ) ((n : ℝ) + 1))
      (f := F) (fun n => measurableSet_Ioc) hd hintU
  rw [iUnion_Ioc_intCast ℝ, Measure.restrict_univ] at h
  exact h

theorem integral_unit_periodization {F : ℝ → ℝ} (hF : Continuous F) (hnn : ∀ x, 0 ≤ F x)
    (hint : Integrable F) :
    ∫ u in (0 : ℝ)..1, (∑' ℓ : ℤ, F ((ℓ : ℝ) + u)) = ∫ x, F x := by
  have hmeas : ∀ ℓ : ℤ, AEStronglyMeasurable (fun u : ℝ => F ((ℓ : ℝ) + u))
      (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
    intro ℓ
    exact ((hF.comp (continuous_const.add continuous_id)).measurable).aestronglyMeasurable
  have hfin : (∑' ℓ : ℤ, ∫⁻ u in Set.Ioc (0 : ℝ) 1, ‖F ((ℓ : ℝ) + u)‖ₑ) ≠ ⊤ := by
    have hstep : ∀ ℓ : ℤ, ∫⁻ u in Set.Ioc (0 : ℝ) 1, ‖F ((ℓ : ℝ) + u)‖ₑ
        = ∫⁻ x in Set.Ioc (ℓ : ℝ) ((ℓ : ℝ) + 1), ‖F x‖ₑ :=
      fun ℓ => setLIntegral_comp_add_left_Ioc (fun x => ‖F x‖ₑ) (ℓ : ℝ)
    rw [tsum_congr hstep]
    rw [← lintegral_intCast_Ioc_tsum (fun x => ‖F x‖ₑ)]
    rw [show (∫⁻ x, ‖F x‖ₑ) = ∫⁻ x, ENNReal.ofReal (F x) from
      lintegral_congr (fun x => Real.enorm_of_nonneg (hnn x))]
    rw [← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall hnn)]
    exact ENNReal.ofReal_ne_top
  calc
    ∫ u in (0 : ℝ)..1, (∑' ℓ : ℤ, F ((ℓ : ℝ) + u))
        = ∫ u in Set.Ioc (0 : ℝ) 1, (∑' ℓ : ℤ, F ((ℓ : ℝ) + u)) :=
          intervalIntegral.integral_of_le (by norm_num)
    _ = ∑' ℓ : ℤ, ∫ u in Set.Ioc (0 : ℝ) 1, F ((ℓ : ℝ) + u) :=
          integral_tsum hmeas hfin
    _ = ∑' ℓ : ℤ, ∫ x in Set.Ioc (ℓ : ℝ) ((ℓ : ℝ) + 1), F x :=
          tsum_congr (fun ℓ => setIntegral_comp_add_left_Ioc (ℓ : ℝ))
    _ = ∫ x, F x := (integral_intCast_Ioc_tsum hint).symm

end Work.GM.Affine
