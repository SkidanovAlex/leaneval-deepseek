/-
# Measure-theoretic plumbing for the `D_θ`-coercivity estimate

This file collects the elementary measure-theoretic facts used by the finite-`z`-interval
("box") coercivity estimate for the angular derivative `D_θ f`:

* the open and the closed interval (and the open and the closed box) carry the same
  restricted Lebesgue measure;
* a function continuous on an open interval and bounded there is integrable on the
  closed interval (and the analogous statement for a box);
* the Fubini bridge between the iterated integral over an open box and the integral
  over the box with respect to the product measure.
-/
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.Coercivity.thetaAux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.Coercivity

set_option autoImplicit false

/-! ## Almost-everywhere equal sets -/

/-- The open interval and the closed interval are almost everywhere equal. -/
theorem ae_eq_Ioo_Icc (a b : ℝ) : Set.Ioo a b =ᵐ[(volume : Measure ℝ)] Set.Icc a b := by
  rw [MeasureTheory.ae_eq_set]
  constructor
  · rw [Set.sdiff_eq_empty.mpr Set.Ioo_subset_Icc_self, MeasureTheory.measure_empty]
  · refine MeasureTheory.measure_mono_null (fun x hx => ?_)
      (((Set.finite_singleton b).insert a).measure_zero volume)
    rw [Set.mem_sdiff, Set.mem_Icc, Set.mem_Ioo] at hx
    obtain ⟨⟨h1, h2⟩, h3⟩ := hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    rcases not_and_or.mp h3 with h | h
    · exact Or.inl (le_antisymm (not_lt.mp h) h1)
    · exact Or.inr (le_antisymm h2 (not_lt.mp h))

/-- The open box `(0,R) × (0,π/2)` and the closed box `[0,R] × [0,π/2]` carry the same
restricted Lebesgue measure. -/
theorem restrict_box_eq (R : ℝ) :
    (volume : Measure (ℝ × ℝ)).restrict (Set.Ioo 0 R ×ˢ Set.Ioo 0 (π / 2))
      = (volume : Measure (ℝ × ℝ)).restrict (Set.Icc 0 R ×ˢ Spaces.Iθ) := by
  have h1 : (volume : Measure (ℝ × ℝ)) = (volume : Measure ℝ).prod (volume : Measure ℝ) :=
    MeasureTheory.Measure.volume_eq_prod ℝ ℝ
  rw [h1]
  rw [← MeasureTheory.Measure.prod_restrict, ← MeasureTheory.Measure.prod_restrict]
  rw [MeasureTheory.Measure.restrict_congr_set (ae_eq_Ioo_Icc 0 R),
    MeasureTheory.Measure.restrict_congr_set (ae_eq_Ioo_Icc 0 (π / 2))]
  rfl

/-- The closed interval integral equals the open interval integral. -/
theorem integral_Icc_eq_Ioo (f : ℝ → ℝ) (a b : ℝ) :
    (∫ x in Set.Icc a b, f x) = ∫ x in Set.Ioo a b, f x :=
  MeasureTheory.setIntegral_congr_set (ae_eq_Ioo_Icc a b).symm

/-! ## Integrability on an interval or a box -/

/-- A function which is continuous on the open interval and bounded there is integrable
on the closed interval. -/
theorem integrableOn_Icc_of_continuousOn_Ioo {g : ℝ → ℝ} {a b K : ℝ}
    (hg : ContinuousOn g (Set.Ioo a b)) (hb : ∀ x ∈ Set.Ioo a b, ‖g x‖ ≤ K) :
    MeasureTheory.IntegrableOn g (Set.Icc a b) := by
  have hfin : volume (Set.Ioo a b) < ⊤ := by
    rw [Real.volume_Ioo]; exact ENNReal.ofReal_lt_top
  have hInt : MeasureTheory.IntegrableOn g (Set.Ioo a b) := by
    refine MeasureTheory.IntegrableOn.of_bound hfin
      (hg.aestronglyMeasurable measurableSet_Ioo) K ?_
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioo]
    exact Eventually.of_forall (fun x hx => hb x hx)
  exact hInt.congr_set_ae (ae_eq_Ioo_Icc a b).symm

/-- A function which is continuous on the open rectangle and bounded there is integrable
on that rectangle. -/
theorem integrableOn_Ioo_prod_of_continuousOn {F : ℝ × ℝ → ℝ} {R K : ℝ}
    (hF : ContinuousOn F (Set.Ioo 0 R ×ˢ Set.Ioo 0 (π / 2)))
    (hb : ∀ p ∈ Set.Ioo 0 R ×ˢ Set.Ioo 0 (π / 2), ‖F p‖ ≤ K) :
    MeasureTheory.IntegrableOn F (Set.Ioo 0 R ×ˢ Set.Ioo 0 (π / 2)) := by
  have hfin : volume (Set.Ioo 0 R ×ˢ Set.Ioo 0 (π / 2)) < ⊤ := by
    rw [MeasureTheory.Measure.volume_eq_prod, MeasureTheory.Measure.prod_prod,
      Real.volume_Ioo, Real.volume_Ioo]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top ENNReal.ofReal_lt_top
  refine MeasureTheory.IntegrableOn.of_bound hfin
    (hF.aestronglyMeasurable (measurableSet_Ioo.prod measurableSet_Ioo)) K ?_
  rw [MeasureTheory.ae_restrict_iff' (measurableSet_Ioo.prod measurableSet_Ioo)]
  exact Eventually.of_forall (fun x hx => hb x hx)

/-- The `θ`-slice of a function continuous on the open box is continuous on `(0,π/2)`. -/
theorem continuousOn_slice_right {F : ℝ × ℝ → ℝ} {R z : ℝ} (hz : z ∈ Set.Ioo 0 R)
    (hF : ContinuousOn F (Set.Ioo 0 R ×ˢ Set.Ioo 0 (π / 2))) :
    ContinuousOn (fun θ => F (z, θ)) (Set.Ioo 0 (π / 2)) :=
  hF.comp (continuousOn_const.prodMk continuousOn_id) (fun θ hθ => ⟨hz, hθ⟩)

/-- The `z`-slice of a function continuous on the open box is continuous on `(0,R)`. -/
theorem continuousOn_slice_left {F : ℝ × ℝ → ℝ} {R θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2))
    (hF : ContinuousOn F (Set.Ioo 0 R ×ˢ Set.Ioo 0 (π / 2))) :
    ContinuousOn (fun z => F (z, θ)) (Set.Ioo 0 R) :=
  hF.comp (continuousOn_id.prodMk continuousOn_const) (fun z hz => ⟨hz, hθ⟩)

/-! ## The Fubini bridge -/

/-- The Fubini bridge between the iterated integral over an open box and the integral
over that box with respect to the product measure. -/
theorem iterated_eq_prod_integral {F : ℝ → ℝ → ℝ} {R : ℝ}
    (hF : MeasureTheory.IntegrableOn (Function.uncurry F)
      (Set.Ioo 0 R ×ˢ Set.Ioo 0 (π / 2))) :
    (∫ z in Set.Ioo 0 R, ∫ θ in Set.Ioo 0 (π / 2), F z θ)
      = ∫ p in Set.Ioo 0 R ×ˢ Set.Ioo 0 (π / 2), F p.1 p.2 := by
  have h := MeasureTheory.setIntegral_prod (μ := (volume : Measure ℝ)) (ν := (volume : Measure ℝ))
    (s := Set.Ioo 0 R) (t := Set.Ioo 0 (π / 2)) (Function.uncurry F) hF
  rw [← MeasureTheory.Measure.volume_eq_prod] at h
  exact h.symm

/-- Fubini for the iterated integral over an open box in the opposite order. -/
theorem iterated_swap {F : ℝ → ℝ → ℝ} {R : ℝ}
    (hF : MeasureTheory.IntegrableOn (Function.uncurry F)
      (Set.Ioo 0 R ×ˢ Set.Ioo 0 (π / 2))) :
    (∫ z in Set.Ioo 0 R, ∫ θ in Set.Ioo 0 (π / 2), F z θ)
      = ∫ θ in Set.Ioo 0 (π / 2), ∫ z in Set.Ioo 0 R, F z θ := by
  have h : MeasureTheory.Integrable (Function.uncurry F)
      ((volume.restrict (Set.Ioo 0 R)).prod (volume.restrict (Set.Ioo 0 (π / 2)))) := by
    rw [MeasureTheory.Measure.prod_restrict]
    exact hF
  exact MeasureTheory.integral_integral_swap h

end Work.Coercivity
