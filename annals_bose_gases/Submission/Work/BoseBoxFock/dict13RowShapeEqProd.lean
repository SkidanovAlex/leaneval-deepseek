import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseBoxFock.dict13Aux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.dict13RowShapeEqProd`

`rowShape13 Θ A B K p` is defined (`pairRowS2Row.lean`) as the **iterated** integral over the
*full* volumes
`∫ x, ∫ y, ∫ u, star (Θ x) * A (x p.1) * K (x p.2) y * star (B u) * Θ (x[p.1↦y][p.2↦u])`,
whereas the dictionary's `L¹`-arguments (`dict13_L1`, `dict13Aux`) state their integrability
hypotheses for the **product** measure `(volume ↾ abox n ℓ).prod (volume.prod volume)` on
`X n × (E3 × E3)` (via `rowProd`).  This file bridges the two:

* `integral_iterated_eq_integral_prod` — the threefold iterated integral of an integrable
  function equals its integral against the product measure (`MeasureTheory.integral_prod`
  twice);
* `integral_prod_restrict_eq_integral` — if the integrand vanishes off `s ×ˢ univ`, restricting
  the first variable to `s` does not change the integral (no integrability needed);
* `integrable_prod_restrict_iff` — the corresponding integrability transfer.

The target `dict13RowShapeEqProd` is then immediate: `Function.support Θ ⊆ abox n ℓ` makes
`rowProd Θ A B K p` vanish whenever the configuration coordinate leaves the box.

Everything here is `sorry`-free.
-/

noncomputable section

open MeasureTheory

namespace Work.BoseBoxFock

set_option autoImplicit false

/-- **Fubini, threefold.**  For an integrable `ℂ`-valued function on `α × (β × γ)`, the iterated
Bochner integral over the three coordinates equals the Bochner integral against the product
measure.  (`MeasureTheory.integral_prod` at the outer pair, then at the inner pair, the latter
a.e. — integrability of the inner slices is `Integrable.prod_right_ae`.) -/
theorem integral_iterated_eq_integral_prod {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] (μ : Measure α) (ν : Measure β) (ρ : Measure γ)
    [SFinite μ] [SFinite ν] [SFinite ρ]
    {f : α × (β × γ) → ℂ} (hf : Integrable f (μ.prod (ν.prod ρ))) :
    (∫ x, ∫ y, ∫ u, f (x, (y, u)) ∂ρ ∂ν ∂μ) = ∫ z, f z ∂(μ.prod (ν.prod ρ)) := by
  rw [MeasureTheory.integral_prod f hf]
  refine integral_congr_ae ?_
  filter_upwards [hf.prod_right_ae] with x hx
  exact (MeasureTheory.integral_prod (fun w : β × γ => f (x, w)) hx).symm

/-- If `f` vanishes whenever its first coordinate is outside `s`, then integrating the first
coordinate against `μ.restrict s` gives the same value as integrating against `μ`.  Only
measurability of `s` is used (no integrability: the two integrals are compared through
`MeasureTheory.integral_indicator` and `MeasureTheory.integral_congr_ae`, and both sides are
integrals against the same measure `μ.prod (ν.prod ρ)`). -/
theorem integral_prod_restrict_eq_integral {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] (μ : Measure α) (ν : Measure β) (ρ : Measure γ)
    [SFinite μ] [SFinite ν] [SFinite ρ] (s : Set α) (hs : MeasurableSet s)
    {f : α × (β × γ) → ℂ} (hvan : ∀ z, z.1 ∉ s → f z = 0) :
    ∫ z, f z ∂((μ.restrict s).prod (ν.prod ρ)) = ∫ z, f z ∂(μ.prod (ν.prod ρ)) := by
  have hmeas : (μ.restrict s).prod (ν.prod ρ)
      = (μ.prod (ν.prod ρ)).restrict (s ×ˢ (Set.univ : Set (β × γ))) := by
    have := Measure.prod_restrict (μ := μ) (ν := ν.prod ρ) s (Set.univ : Set (β × γ))
    rwa [Measure.restrict_univ] at this
  rw [hmeas, ← integral_indicator (hs.prod MeasurableSet.univ)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
  by_cases hz : z ∈ s ×ˢ (Set.univ : Set (β × γ))
  · rw [Set.indicator_of_mem hz]
  · rw [Set.indicator_of_notMem hz]
    exact (hvan z fun h => hz ⟨h, Set.mem_univ _⟩).symm

/-- Integrability transfers between `(μ.restrict s).prod (ν.prod ρ)` and `μ.prod (ν.prod ρ)`
when `f` vanishes off `s ×ˢ univ` (so that `f` is its own indicator on that set). -/
theorem integrable_prod_restrict_iff {α β γ : Type*} [MeasurableSpace α] [MeasurableSpace β]
    [MeasurableSpace γ] (μ : Measure α) (ν : Measure β) (ρ : Measure γ)
    [SFinite μ] [SFinite ν] [SFinite ρ] (s : Set α) (hs : MeasurableSet s)
    {f : α × (β × γ) → ℂ} (hvan : ∀ z, z.1 ∉ s → f z = 0) :
    Integrable f ((μ.restrict s).prod (ν.prod ρ)) ↔ Integrable f (μ.prod (ν.prod ρ)) := by
  have hmeas : (μ.restrict s).prod (ν.prod ρ)
      = (μ.prod (ν.prod ρ)).restrict (s ×ˢ (Set.univ : Set (β × γ))) := by
    have := Measure.prod_restrict (μ := μ) (ν := ν.prod ρ) s (Set.univ : Set (β × γ))
    rwa [Measure.restrict_univ] at this
  have hfun : (s ×ˢ (Set.univ : Set (β × γ))).indicator f = f := by
    funext z
    by_cases hz : z ∈ s ×ˢ (Set.univ : Set (β × γ))
    · rw [Set.indicator_of_mem hz]
    · rw [Set.indicator_of_notMem hz]
      exact (hvan z fun h => hz ⟨h, Set.mem_univ _⟩).symm
  rw [hmeas,
    show Integrable f ((μ.prod (ν.prod ρ)).restrict (s ×ˢ (Set.univ : Set (β × γ))))
      ↔ IntegrableOn f (s ×ˢ (Set.univ : Set (β × γ))) (μ.prod (ν.prod ρ)) from Iff.rfl,
    ← integrable_indicator_iff (hs.prod MeasurableSet.univ), hfun]

theorem dict13RowShapeEqProd {n : ℕ} {ℓ : ℝ} {Θ : Submission.BoseGases.X n → ℂ}
    {A B : EuclideanSpace ℝ (Fin 3) → ℂ}
    {K : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℂ}
    {p : Fin n × Fin n} (hΘs : Function.support Θ ⊆ Submission.BoseGases.abox n ℓ)
    (hI : Integrable (Work.BoseBoxFock.rowProd Θ A B K p)
      (((volume : Measure (Submission.BoseGases.X n)).restrict (Submission.BoseGases.abox n ℓ)).prod
        ((volume : Measure (EuclideanSpace ℝ (Fin 3))).prod (volume : Measure (EuclideanSpace ℝ (Fin 3)))))) :
    Work.BoseBoxFock.rowShape13 Θ A B K p
      = ∫ z, Work.BoseBoxFock.rowProd Θ A B K p z
          ∂(((volume : Measure (Submission.BoseGases.X n)).restrict (Submission.BoseGases.abox n ℓ)).prod
              ((volume : Measure (EuclideanSpace ℝ (Fin 3))).prod (volume : Measure (EuclideanSpace ℝ (Fin 3))))) := by
  -- the integrand vanishes as soon as the configuration leaves the box
  have hvan : ∀ z : Submission.BoseGases.X n ×
      (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)),
      z.1 ∉ Submission.BoseGases.abox n ℓ → rowProd Θ A B K p z = 0 := by
    rintro ⟨x, y, u⟩ hx
    have hΘ0 : Θ x = 0 := by
      by_contra h
      exact hx (hΘs (Function.mem_support.mpr h))
    simp [rowProd, rowInt, hΘ0]
  -- hence integrability against the full product volume
  have hI_full : Integrable (rowProd Θ A B K p)
      ((volume : Measure (Submission.BoseGases.X n)).prod
        ((volume : Measure (EuclideanSpace ℝ (Fin 3))).prod
          (volume : Measure (EuclideanSpace ℝ (Fin 3))))) :=
    (integrable_prod_restrict_iff (volume : Measure (Submission.BoseGases.X n))
      (volume : Measure (EuclideanSpace ℝ (Fin 3)))
      (volume : Measure (EuclideanSpace ℝ (Fin 3))) (Submission.BoseGases.abox n ℓ)
      (Submission.BoseGases.abox_measurable n ℓ) hvan).mp hI
  rw [rowShape13_eq_integral]
  exact (integral_iterated_eq_integral_prod (volume : Measure (Submission.BoseGases.X n))
      (volume : Measure (EuclideanSpace ℝ (Fin 3)))
      (volume : Measure (EuclideanSpace ℝ (Fin 3))) (f := rowProd Θ A B K p) hI_full).trans
    (integral_prod_restrict_eq_integral (volume : Measure (Submission.BoseGases.X n))
      (volume : Measure (EuclideanSpace ℝ (Fin 3)))
      (volume : Measure (EuclideanSpace ℝ (Fin 3))) (Submission.BoseGases.abox n ℓ)
      (Submission.BoseGases.abox_measurable n ℓ) hvan).symm

end Work.BoseBoxFock
