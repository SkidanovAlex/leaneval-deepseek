import Mathlib
import Submission.Work.BoseDict.Defs2
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.boxAnnOf_norm_sq_le` — the operator bound for the superposed
box annihilation

`Work.BoseDict.boxAnnOf e w d Θ` is the box (first-quantised) annihilation of the superposed
one-particle function `η_w = Σ_l w_l e_l`, acting on `(d+1)`-particle functions:

`(boxAnnOf e w d Θ)(y) = √(d+1) ∫_z conj(η_w z) Θ(z, y)`.

The theorem below is the elementary "Bessel/operator" bound

`‖boxAnnOf e w d Θ‖²_{L²(Xn d)} ≤ (d+1) ‖η_w‖²_{L²(Sp)} ‖Θ‖²_{L²(Xn d+1)}`,

which is exactly Cauchy–Schwarz in the `z`-variable performed for almost every `y`, followed by
Fubini (the identification `Xn (d+1) ≃ Sp × Xn d`, `x ↦ (x 0, x ∘ succ)`, is measure preserving).

## The pieces

* `boxPeel` — the measure preserving measurable equivalence
  `Sp × Xn d ≃ᵐ Xn (d+1)`, `(z,y) ↦ Fin.cons z y` (the inverse of
  `MeasurableEquiv.piFinSuccAbove` at the index `0`); `boxPeel_apply` computes it and
  `boxPeel_measurePreserving` records that it preserves `volume`;
* `slice_cauchySchwarz` — the pointwise (in `y`) Cauchy–Schwarz bound, for a.e. `y`, obtained
  from Hölder with conjugate exponents `2, 2` (`integral_mul_norm_le_Lp_mul_Lq`);
* the a.e. `L²`-membership of the slices `z ↦ Θ (Fin.cons z y)` comes from the joint `MemLp`
  of `Θ ∘ boxPeel` (`MemLp.comp_measurePreserving`) via the Fubini lemmas
  `AEStronglyMeasurable.prodMk_right` and `Integrable.prod_left_ae`;
* Fubini (`integral_prod`, `integral_integral_swap`) identifies
  `∫_y ∫_z ‖Θ (Fin.cons z y)‖²` with `∫_x ‖Θ x‖²`.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Work.BoseBoxFock

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## 1. The measure preserving peel of the first coordinate -/

/-- The measurable equivalence `(z, y) ↦ Fin.cons z y` between `Sp × Xn d` and `Xn (d+1)`:
the inverse of `MeasurableEquiv.piFinSuccAbove` at the index `0`. -/
def boxPeel (d : ℕ) : Work.BoseDict.Sp × Work.BoseDict.Xn d ≃ᵐ Work.BoseDict.Xn (d + 1) :=
  (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (d + 1) => Work.BoseDict.Sp) 0).symm

@[simp]
lemma boxPeel_apply (d : ℕ) (p : Work.BoseDict.Sp × Work.BoseDict.Xn d) :
    boxPeel d p = Fin.cons p.1 p.2 := by
  simp [boxPeel, MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]

lemma boxPeel_measurePreserving (d : ℕ) :
    MeasureTheory.MeasurePreserving (boxPeel d)
      ((MeasureTheory.volume : MeasureTheory.Measure Work.BoseDict.Sp).prod
        (MeasureTheory.volume : MeasureTheory.Measure (Work.BoseDict.Xn d)))
      (MeasureTheory.volume : MeasureTheory.Measure (Work.BoseDict.Xn (d + 1))) :=
  (MeasureTheory.volume_preserving_piFinSuccAbove
    (fun _ : Fin (d + 1) => Work.BoseDict.Sp) 0).symm

/-! ## 2. The pointwise Cauchy–Schwarz bound -/

/-- For a fixed `y`, Cauchy–Schwarz in `z` bounds the square of the (unsquared) box
annihilation integrand by the product of the two `L²` masses. -/
lemma slice_cauchySchwarz {d : ℕ} {η : Work.BoseDict.Sp → ℂ}
    {Θ : Work.BoseDict.Xn (d + 1) → ℂ} (y : Work.BoseDict.Xn d)
    (hη : MeasureTheory.MemLp η 2 (MeasureTheory.volume : MeasureTheory.Measure Work.BoseDict.Sp))
    (hΘy : MeasureTheory.MemLp (fun z : Work.BoseDict.Sp => Θ (Fin.cons z y)) 2
      (MeasureTheory.volume : MeasureTheory.Measure Work.BoseDict.Sp)) :
    ‖∫ z : Work.BoseDict.Sp, (starRingEnd ℂ) (η z) * Θ (Fin.cons z y)‖ ^ 2
      ≤ (∫ z : Work.BoseDict.Sp, ‖η z‖ ^ 2)
        * ∫ z : Work.BoseDict.Sp, ‖Θ (Fin.cons z y)‖ ^ 2 := by
  have hη2 : MeasureTheory.Integrable (fun z : Work.BoseDict.Sp => ‖η z‖ ^ 2)
      (MeasureTheory.volume : MeasureTheory.Measure Work.BoseDict.Sp) :=
    (MeasureTheory.memLp_two_iff_integrable_sq_norm hη.aestronglyMeasurable).mp hη
  -- the conjugate is `L²`
  have hconj : MeasureTheory.MemLp (fun z : Work.BoseDict.Sp => (starRingEnd ℂ) (η z)) 2
      (MeasureTheory.volume : MeasureTheory.Measure Work.BoseDict.Sp) := by
    refine (MeasureTheory.memLp_two_iff_integrable_sq_norm hη.aestronglyMeasurable.star).mpr ?_
    refine hη2.congr (Filter.Eventually.of_forall fun z => ?_)
    simp only [Pi.star_apply, norm_star]
  -- Hölder with conjugate exponents `2, 2`
  have hH := MeasureTheory.integral_mul_norm_le_Lp_mul_Lq
    (μ := (MeasureTheory.volume : MeasureTheory.Measure Work.BoseDict.Sp))
    (f := fun z : Work.BoseDict.Sp => (starRingEnd ℂ) (η z))
    (g := fun z : Work.BoseDict.Sp => Θ (Fin.cons z y))
    Real.HolderConjugate.two_two
    (by rw [show ENNReal.ofReal (2 : ℝ) = 2 from by norm_num]; exact hconj)
    (by rw [show ENNReal.ofReal (2 : ℝ) = 2 from by norm_num]; exact hΘy)
  have h2 : (∫ z : Work.BoseDict.Sp, ‖(starRingEnd ℂ) (η z)‖ ^ (2 : ℝ))
      = ∫ z : Work.BoseDict.Sp, ‖η z‖ ^ 2 := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    simp only [starRingEnd_apply, norm_star, Real.rpow_two]
  have h3 : (∫ z : Work.BoseDict.Sp, ‖Θ (Fin.cons z y)‖ ^ (2 : ℝ))
      = ∫ z : Work.BoseDict.Sp, ‖Θ (Fin.cons z y)‖ ^ 2 := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    simp only [Real.rpow_two]
  have hH' : ∫ z : Work.BoseDict.Sp, ‖(starRingEnd ℂ) (η z)‖ * ‖Θ (Fin.cons z y)‖
      ≤ Real.sqrt (∫ z : Work.BoseDict.Sp, ‖η z‖ ^ 2)
        * Real.sqrt (∫ z : Work.BoseDict.Sp, ‖Θ (Fin.cons z y)‖ ^ 2) := by
    have hh := hH
    rw [h2, h3, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow] at hh
    exact hh
  have h1 : ‖∫ z : Work.BoseDict.Sp, (starRingEnd ℂ) (η z) * Θ (Fin.cons z y)‖
      ≤ ∫ z : Work.BoseDict.Sp, ‖(starRingEnd ℂ) (η z)‖ * ‖Θ (Fin.cons z y)‖ :=
    (MeasureTheory.norm_integral_le_integral_norm _).trans_eq
      (MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z => norm_mul _ _))
  have hA_nn : 0 ≤ ∫ z : Work.BoseDict.Sp, ‖η z‖ ^ 2 :=
    MeasureTheory.integral_nonneg fun z => sq_nonneg _
  have hB_nn : 0 ≤ ∫ z : Work.BoseDict.Sp, ‖Θ (Fin.cons z y)‖ ^ 2 :=
    MeasureTheory.integral_nonneg fun z => sq_nonneg _
  have hle : ‖∫ z : Work.BoseDict.Sp, (starRingEnd ℂ) (η z) * Θ (Fin.cons z y)‖
      ≤ Real.sqrt (∫ z : Work.BoseDict.Sp, ‖η z‖ ^ 2)
        * Real.sqrt (∫ z : Work.BoseDict.Sp, ‖Θ (Fin.cons z y)‖ ^ 2) :=
    h1.trans hH'
  calc ‖∫ z : Work.BoseDict.Sp, (starRingEnd ℂ) (η z) * Θ (Fin.cons z y)‖ ^ 2
      ≤ (Real.sqrt (∫ z : Work.BoseDict.Sp, ‖η z‖ ^ 2)
          * Real.sqrt (∫ z : Work.BoseDict.Sp, ‖Θ (Fin.cons z y)‖ ^ 2)) ^ 2 :=
        sq_le_sq' (le_trans
          (neg_nonpos.mpr (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)))
          (norm_nonneg _)) hle
    _ = (∫ z : Work.BoseDict.Sp, ‖η z‖ ^ 2)
        * ∫ z : Work.BoseDict.Sp, ‖Θ (Fin.cons z y)‖ ^ 2 := by
        rw [mul_pow, Real.sq_sqrt hA_nn, Real.sq_sqrt hB_nn]

/-! ## 3. The theorem -/

theorem boxAnnOf_norm_sq_le {m d : ℕ} {e : Fin m → Work.BoseDict.Sp → ℂ} (w : Fin m → ℝ)
    (hη : MeasureTheory.MemLp (Work.BoseDict.etaOf e w) 2
      (MeasureTheory.volume : MeasureTheory.Measure Work.BoseDict.Sp))
    {Θ : Work.BoseDict.Xn (d + 1) → ℂ}
    (hΘ : MeasureTheory.MemLp Θ 2
      (MeasureTheory.volume : MeasureTheory.Measure (Work.BoseDict.Xn (d + 1)))) :
    ∫ y : Work.BoseDict.Xn d, ‖Work.BoseDict.boxAnnOf e w d Θ y‖ ^ 2
      ≤ ((d : ℝ) + 1) * (∫ z : Work.BoseDict.Sp, ‖Work.BoseDict.etaOf e w z‖ ^ 2)
          * ∫ x : Work.BoseDict.Xn (d + 1), ‖Θ x‖ ^ 2 := by
  classical
  -- the peel: joint `L²`-membership and integrability of `Θ ∘ boxPeel`
  have hEmp := boxPeel_measurePreserving d
  have hΘE : MeasureTheory.MemLp
      (fun p : Work.BoseDict.Sp × Work.BoseDict.Xn d => Θ (boxPeel d p)) 2
      ((MeasureTheory.volume : MeasureTheory.Measure Work.BoseDict.Sp).prod
        (MeasureTheory.volume : MeasureTheory.Measure (Work.BoseDict.Xn d))) :=
    hΘ.comp_measurePreserving hEmp
  have hΘE2 : MeasureTheory.Integrable
      (fun p : Work.BoseDict.Sp × Work.BoseDict.Xn d => ‖Θ (boxPeel d p)‖ ^ 2)
      ((MeasureTheory.volume : MeasureTheory.Measure Work.BoseDict.Sp).prod
        (MeasureTheory.volume : MeasureTheory.Measure (Work.BoseDict.Xn d))) :=
    (MeasureTheory.memLp_two_iff_integrable_sq_norm hΘE.aestronglyMeasurable).mp hΘE
  -- integrability of `y ↦ ∫_z ‖Θ (z,y)‖²`
  have hBint : MeasureTheory.Integrable
      (fun y : Work.BoseDict.Xn d => ∫ z : Work.BoseDict.Sp, ‖Θ (Fin.cons z y)‖ ^ 2)
      (MeasureTheory.volume : MeasureTheory.Measure (Work.BoseDict.Xn d)) := by
    have h1 : MeasureTheory.Integrable
        (fun y : Work.BoseDict.Xn d => ∫ z : Work.BoseDict.Sp, ‖Θ (boxPeel d (z, y))‖ ^ 2)
        (MeasureTheory.volume : MeasureTheory.Measure (Work.BoseDict.Xn d)) := by
      refine hΘE2.integral_norm_prod_right.congr (Filter.Eventually.of_forall fun y => ?_)
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
      simp only [Real.norm_of_nonneg (sq_nonneg (‖Θ (boxPeel d (z, y))‖))]
    refine h1.congr (Filter.Eventually.of_forall fun y => ?_)
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    simp only [boxPeel_apply]
  -- a.e. `L²`-membership of the slices
  have hslice : ∀ᵐ y ∂(MeasureTheory.volume : MeasureTheory.Measure (Work.BoseDict.Xn d)),
      MeasureTheory.MemLp (fun z : Work.BoseDict.Sp => Θ (Fin.cons z y)) 2
        (MeasureTheory.volume : MeasureTheory.Measure Work.BoseDict.Sp) := by
    have h1 : ∀ᵐ y ∂(MeasureTheory.volume : MeasureTheory.Measure (Work.BoseDict.Xn d)),
        MeasureTheory.Integrable (fun z : Work.BoseDict.Sp => ‖Θ (boxPeel d (z, y))‖ ^ 2)
          (MeasureTheory.volume : MeasureTheory.Measure Work.BoseDict.Sp) :=
      hΘE2.prod_left_ae
    have h2 : ∀ᵐ y ∂(MeasureTheory.volume : MeasureTheory.Measure (Work.BoseDict.Xn d)),
        MeasureTheory.AEStronglyMeasurable (fun z : Work.BoseDict.Sp => Θ (boxPeel d (z, y)))
          (MeasureTheory.volume : MeasureTheory.Measure Work.BoseDict.Sp) :=
      hΘE.aestronglyMeasurable.prodMk_right
    filter_upwards [h1, h2] with y hy1 hy2
    have hy1' : MeasureTheory.Integrable
        (fun z : Work.BoseDict.Sp => ‖Θ (Fin.cons z y)‖ ^ 2)
        (MeasureTheory.volume : MeasureTheory.Measure Work.BoseDict.Sp) :=
      hy1.congr (Filter.Eventually.of_forall fun z => by simp only [boxPeel_apply])
    have hy2' : MeasureTheory.AEStronglyMeasurable
        (fun z : Work.BoseDict.Sp => Θ (Fin.cons z y))
        (MeasureTheory.volume : MeasureTheory.Measure Work.BoseDict.Sp) :=
      hy2.congr (Filter.Eventually.of_forall fun z => by simp only [boxPeel_apply])
    exact (MeasureTheory.memLp_two_iff_integrable_sq_norm hy2').mpr hy1'
  -- the pointwise a.e. Cauchy–Schwarz bound
  have hpt : ∀ᵐ y ∂(MeasureTheory.volume : MeasureTheory.Measure (Work.BoseDict.Xn d)),
      ‖∫ z : Work.BoseDict.Sp,
          (starRingEnd ℂ) (Work.BoseDict.etaOf e w z) * Θ (Fin.cons z y)‖ ^ 2
        ≤ (∫ z : Work.BoseDict.Sp, ‖Work.BoseDict.etaOf e w z‖ ^ 2)
          * ∫ z : Work.BoseDict.Sp, ‖Θ (Fin.cons z y)‖ ^ 2 := by
    filter_upwards [hslice] with y hy
    exact slice_cauchySchwarz y hη hy
  -- the identification of the `boxAnnOf` integrand
  have hrewrite : ∀ y : Work.BoseDict.Xn d,
      ‖Work.BoseDict.boxAnnOf e w d Θ y‖ ^ 2
        = ((d : ℝ) + 1)
          * ‖∫ z : Work.BoseDict.Sp,
              (starRingEnd ℂ) (Work.BoseDict.etaOf e w z) * Θ (Fin.cons z y)‖ ^ 2 := by
    intro y
    simp only [Work.BoseDict.boxAnnOf]
    rw [norm_mul, mul_pow, Complex.sq_norm, Complex.normSq_ofReal, ← pow_two,
      Real.sq_sqrt (by positivity)]
  -- the majorant
  have hABint : MeasureTheory.Integrable
      (fun y : Work.BoseDict.Xn d => (∫ z : Work.BoseDict.Sp, ‖Work.BoseDict.etaOf e w z‖ ^ 2)
        * ∫ z : Work.BoseDict.Sp, ‖Θ (Fin.cons z y)‖ ^ 2)
      (MeasureTheory.volume : MeasureTheory.Measure (Work.BoseDict.Xn d)) :=
    hBint.const_mul _
  -- integrability of the left hand side, from the a.e. bound
  have hLHSint : MeasureTheory.Integrable
      (fun y : Work.BoseDict.Xn d =>
        ‖∫ z : Work.BoseDict.Sp,
            (starRingEnd ℂ) (Work.BoseDict.etaOf e w z) * Θ (Fin.cons z y)‖ ^ 2)
      (MeasureTheory.volume : MeasureTheory.Measure (Work.BoseDict.Xn d)) := by
    refine hABint.mono' ?_ ?_
    · -- a.e. strong measurability of the partial integral
      have hj : MeasureTheory.AEStronglyMeasurable
          (fun p : Work.BoseDict.Sp × Work.BoseDict.Xn d =>
            (starRingEnd ℂ) (Work.BoseDict.etaOf e w p.1) * Θ (boxPeel d p))
          ((MeasureTheory.volume : MeasureTheory.Measure Work.BoseDict.Sp).prod
            (MeasureTheory.volume : MeasureTheory.Measure (Work.BoseDict.Xn d))) :=
        ((hη.aestronglyMeasurable.comp_fst).star).mul hΘE.aestronglyMeasurable
      have hj' : MeasureTheory.AEStronglyMeasurable
          (fun q : Work.BoseDict.Xn d × Work.BoseDict.Sp =>
            (starRingEnd ℂ) (Work.BoseDict.etaOf e w q.2) * Θ (boxPeel d (q.2, q.1)))
          ((MeasureTheory.volume : MeasureTheory.Measure (Work.BoseDict.Xn d)).prod
            (MeasureTheory.volume : MeasureTheory.Measure Work.BoseDict.Sp)) :=
        hj.prod_swap
      have hcongr : (fun y : Work.BoseDict.Xn d =>
            ∫ z : Work.BoseDict.Sp,
              (starRingEnd ℂ) (Work.BoseDict.etaOf e w z) * Θ (boxPeel d (z, y)))
          =ᵐ[(MeasureTheory.volume : MeasureTheory.Measure (Work.BoseDict.Xn d))]
          (fun y : Work.BoseDict.Xn d =>
            ∫ z : Work.BoseDict.Sp,
              (starRingEnd ℂ) (Work.BoseDict.etaOf e w z) * Θ (Fin.cons z y)) := by
        refine Filter.Eventually.of_forall fun y => ?_
        refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
        simp only [boxPeel_apply]
      have h1 : MeasureTheory.AEStronglyMeasurable
          (fun y : Work.BoseDict.Xn d =>
            ∫ z : Work.BoseDict.Sp,
              (starRingEnd ℂ) (Work.BoseDict.etaOf e w z) * Θ (Fin.cons z y))
          (MeasureTheory.volume : MeasureTheory.Measure (Work.BoseDict.Xn d)) :=
        (hj'.integral_prod_right').congr hcongr
      exact (h1.norm.pow 2).congr
        (Filter.Eventually.of_forall fun y => by simp only [Pi.pow_apply])
    · filter_upwards [hpt] with y hy
      rwa [Real.norm_of_nonneg (sq_nonneg _)]
  -- Fubini: the total mass of the slanted integral
  have hBsum : (∫ y : Work.BoseDict.Xn d,
        ∫ z : Work.BoseDict.Sp, ‖Θ (Fin.cons z y)‖ ^ 2)
      = ∫ x : Work.BoseDict.Xn (d + 1), ‖Θ x‖ ^ 2 := by
    have hprod : (∫ p : Work.BoseDict.Sp × Work.BoseDict.Xn d, ‖Θ (boxPeel d p)‖ ^ 2)
        = ∫ x : Work.BoseDict.Xn (d + 1), ‖Θ x‖ ^ 2 :=
      hEmp.integral_comp' (fun x => ‖Θ x‖ ^ 2)
    calc ∫ y : Work.BoseDict.Xn d, ∫ z : Work.BoseDict.Sp, ‖Θ (Fin.cons z y)‖ ^ 2
        = ∫ y : Work.BoseDict.Xn d, ∫ z : Work.BoseDict.Sp, ‖Θ (boxPeel d (z, y))‖ ^ 2 := by
          refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
          refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
          simp only [boxPeel_apply]
      _ = ∫ z : Work.BoseDict.Sp, ∫ y : Work.BoseDict.Xn d, ‖Θ (boxPeel d (z, y))‖ ^ 2 :=
          (MeasureTheory.integral_integral_swap
            (f := fun z : Work.BoseDict.Sp =>
              fun y : Work.BoseDict.Xn d => ‖Θ (boxPeel d (z, y))‖ ^ 2) hΘE2).symm
      _ = ∫ p : Work.BoseDict.Sp × Work.BoseDict.Xn d, ‖Θ (boxPeel d p)‖ ^ 2 :=
          (MeasureTheory.integral_prod _ hΘE2).symm
      _ = ∫ x : Work.BoseDict.Xn (d + 1), ‖Θ x‖ ^ 2 := hprod
  calc ∫ y : Work.BoseDict.Xn d, ‖Work.BoseDict.boxAnnOf e w d Θ y‖ ^ 2
      = ∫ y : Work.BoseDict.Xn d, ((d : ℝ) + 1)
          * ‖∫ z : Work.BoseDict.Sp,
              (starRingEnd ℂ) (Work.BoseDict.etaOf e w z) * Θ (Fin.cons z y)‖ ^ 2 :=
        MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hrewrite)
    _ = ((d : ℝ) + 1) * ∫ y : Work.BoseDict.Xn d,
          ‖∫ z : Work.BoseDict.Sp,
              (starRingEnd ℂ) (Work.BoseDict.etaOf e w z) * Θ (Fin.cons z y)‖ ^ 2 := by
        rw [MeasureTheory.integral_const_mul]
    _ ≤ ((d : ℝ) + 1) * ∫ y : Work.BoseDict.Xn d,
          (∫ z : Work.BoseDict.Sp, ‖Work.BoseDict.etaOf e w z‖ ^ 2)
            * ∫ z : Work.BoseDict.Sp, ‖Θ (Fin.cons z y)‖ ^ 2 :=
        mul_le_mul_of_nonneg_left (MeasureTheory.integral_mono_ae hLHSint hABint hpt)
          (by positivity)
    _ = ((d : ℝ) + 1) * ((∫ z : Work.BoseDict.Sp, ‖Work.BoseDict.etaOf e w z‖ ^ 2)
          * ∫ y : Work.BoseDict.Xn d, ∫ z : Work.BoseDict.Sp, ‖Θ (Fin.cons z y)‖ ^ 2) := by
        rw [MeasureTheory.integral_const_mul]
    _ = ((d : ℝ) + 1) * (∫ z : Work.BoseDict.Sp, ‖Work.BoseDict.etaOf e w z‖ ^ 2)
          * ∫ x : Work.BoseDict.Xn (d + 1), ‖Θ x‖ ^ 2 := by
        rw [hBsum]; ring

end Work.BoseBoxFock
