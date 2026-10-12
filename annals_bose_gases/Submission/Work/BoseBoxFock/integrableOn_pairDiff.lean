import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Submission.Work.BoseBoxFock.imagesAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.integrableOn_pairDiff`

`S ↦ (p ↦ S (p.1 - p.2 + c))` preserves `L¹` on the product of the centred box
`Λ(ℓ) × Λ(ℓ)`, for every integrable `S : ℝ³ → ℝ` and every shift `c`.

This is the measure-theoretic substrate for every "pair term" estimate of the box analysis: the
two-body kernels are functions of the *difference* `xᵢ - xⱼ` of two box slots, and to speak of
their integral over `Λ(ℓ) × Λ(ℓ)` one needs the composition with the difference map to be
integrable there.  Note that `S` is only assumed a.e. strongly measurable (not Borel
measurable), so some care is needed; the two halves of `Integrable` are handled separately:

* *a.e. strong measurability*: the difference map
  `(x,y) ↦ x - y + c` is quasi-measure-preserving for Lebesgue measure
  (`quasiMeasurePreserving_sub_of_right_invariant`, composed with the translation), and
  quasi-measure-preservation restricts to the box via `QuasiMeasurePreserving.mono_left`
  (a restricted measure is absolutely continuous w.r.t. the ambient one).  Alternatively stated:
  the push-forward of `Λ(ℓ) × Λ(ℓ)` by the difference map has density `≤ ℓ³` w.r.t. Lebesgue
  measure (Fubini: the fibre of the difference map over a point `z` has volume `≤ ℓ³`).

* *finiteness of `∫⁻ ‖·‖ₑ`*: Tonelli in the `≤` form (`lintegral_prod_le`, which needs no
  measurability at all) reduces the double integral to the iterated one; for fixed `x` the inner
  integral over the box is at most the integral over all of `ℝ³` (monotone set integral), and the
  latter equals `∫⁻ ‖S‖ₑ` by the measure-preservation of the reflection `y ↦ (x+c) - y`
  (`lintegral_sub_left_eq_self`).  The outer integral is then
  `(∫⁻ ‖S‖ₑ)·volume (Λ(ℓ)) = (∫⁻ ‖S‖ₑ)·ℓ³ < ∞`.

Everything here is `sorry`-free.
-/

noncomputable section

open MeasureTheory

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## The difference map is quasi-measure-preserving -/

/-- The difference map `(x,y) ↦ x - y` on `ℝ³ × ℝ³` is quasi-measure-preserving for Lebesgue
measure (Lebesgue measure is translation invariant). -/
private lemma qmp_sub_prod :
    Measure.QuasiMeasurePreserving (fun p : E3 × E3 => p.1 - p.2)
      ((MeasureTheory.volume : Measure E3).prod (MeasureTheory.volume : Measure E3))
      (MeasureTheory.volume : Measure E3) :=
  quasiMeasurePreserving_sub_of_right_invariant _ _

/-- Translation `z ↦ z + c` is quasi-measure-preserving for Lebesgue measure. -/
private lemma qmp_add_right (c : E3) :
    Measure.QuasiMeasurePreserving (fun z : E3 => z + c)
      (MeasureTheory.volume : Measure E3) (MeasureTheory.volume : Measure E3) :=
  quasiMeasurePreserving_add_right _ c

/-- The shifted difference map `(x,y) ↦ x - y + c` is quasi-measure-preserving for Lebesgue
measure. -/
lemma qmp_pairDiff (c : E3) :
    Measure.QuasiMeasurePreserving (fun p : E3 × E3 => p.1 - p.2 + c)
      ((MeasureTheory.volume : Measure E3).prod (MeasureTheory.volume : Measure E3))
      (MeasureTheory.volume : Measure E3) :=
  (qmp_add_right c).comp qmp_sub_prod

/-- On the box product, the restricted measure is dominated by the ambient product Lebesgue
measure (hence absolutely continuous w.r.t. it). -/
private lemma prod_restrict_le (ℓ : ℝ) :
    ((MeasureTheory.volume : Measure E3).restrict (Submission.BoseGases.acube ℓ)).prod
        ((MeasureTheory.volume : Measure E3).restrict (Submission.BoseGases.acube ℓ))
      ≤ (MeasureTheory.volume : Measure E3).prod (MeasureTheory.volume : Measure E3) := by
  rw [Measure.prod_restrict]
  exact Measure.restrict_le_self

/-- **A.e. strong measurability** of the composed difference kernel on the box product. -/
lemma aestronglyMeasurable_pairDiff {ℓ : ℝ} {S : E3 → ℝ}
    (hS : MeasureTheory.Integrable S) (c : E3) :
    MeasureTheory.AEStronglyMeasurable (fun p : E3 × E3 => S (p.1 - p.2 + c))
      (((MeasureTheory.volume : Measure E3).restrict (Submission.BoseGases.acube ℓ)).prod
        ((MeasureTheory.volume : Measure E3).restrict (Submission.BoseGases.acube ℓ))) :=
  hS.aestronglyMeasurable.comp_quasiMeasurePreserving
    ((qmp_pairDiff c).mono_left (Measure.absolutelyContinuous_of_le (prod_restrict_le ℓ)))

/-- **Finiteness of the `L¹`-norm** of the composed difference kernel on the box product. -/
lemma hasFiniteIntegral_pairDiff {ℓ : ℝ} (hℓ : 0 < ℓ) {S : E3 → ℝ}
    (hS : MeasureTheory.Integrable S) (c : E3) :
    MeasureTheory.HasFiniteIntegral (fun p : E3 × E3 => S (p.1 - p.2 + c))
      (((MeasureTheory.volume : Measure E3).restrict (Submission.BoseGases.acube ℓ)).prod
        ((MeasureTheory.volume : Measure E3).restrict (Submission.BoseGases.acube ℓ))) := by
  rw [MeasureTheory.hasFiniteIntegral_iff_enorm]
  have hSfin : ∫⁻ z, ‖S z‖ₑ ∂(MeasureTheory.volume : Measure E3) < ⊤ :=
    (MeasureTheory.hasFiniteIntegral_iff_enorm (f := S) (μ := MeasureTheory.volume)).mp hS.2
  -- for fixed `x`, the inner integral over the box is at most the full integral of `‖S‖ₑ`
  have hinner : ∀ x : E3,
      ∫⁻ y, ‖S (x - y + c)‖ₑ ∂((MeasureTheory.volume : Measure E3).restrict
          (Submission.BoseGases.acube ℓ))
        ≤ ∫⁻ y, ‖S y‖ₑ ∂(MeasureTheory.volume : Measure E3) := by
    intro x
    calc ∫⁻ y, ‖S (x - y + c)‖ₑ ∂((MeasureTheory.volume : Measure E3).restrict
            (Submission.BoseGases.acube ℓ))
        = ∫⁻ y in Submission.BoseGases.acube ℓ, ‖S (x - y + c)‖ₑ
            ∂(MeasureTheory.volume : Measure E3) :=
          rfl
      _ ≤ ∫⁻ y in (Set.univ : Set E3), ‖S (x - y + c)‖ₑ ∂(MeasureTheory.volume : Measure E3) :=
          MeasureTheory.lintegral_mono_set (Set.subset_univ _)
      _ = ∫⁻ y, ‖S (x - y + c)‖ₑ ∂(MeasureTheory.volume : Measure E3) := by simp
      _ = ∫⁻ y, (fun w => ‖S w‖ₑ) ((x + c) - y) ∂(MeasureTheory.volume : Measure E3) := by
          refine MeasureTheory.lintegral_congr (fun y => ?_)
          have h : x - y + c = (x + c) - y := by abel
          rw [h]
      _ = ∫⁻ w, (fun w => ‖S w‖ₑ) w ∂(MeasureTheory.volume : Measure E3) :=
          MeasureTheory.lintegral_sub_left_eq_self (fun w => ‖S w‖ₑ) (x + c)
  calc ∫⁻ p, ‖S (p.1 - p.2 + c)‖ₑ ∂(((MeasureTheory.volume : Measure E3).restrict
          (Submission.BoseGases.acube ℓ)).prod
          ((MeasureTheory.volume : Measure E3).restrict (Submission.BoseGases.acube ℓ)))
      ≤ ∫⁻ x, ∫⁻ y, ‖S (x - y + c)‖ₑ ∂((MeasureTheory.volume : Measure E3).restrict
            (Submission.BoseGases.acube ℓ))
          ∂((MeasureTheory.volume : Measure E3).restrict (Submission.BoseGases.acube ℓ)) :=
        MeasureTheory.lintegral_prod_le _
    _ ≤ ∫⁻ _x, ∫⁻ y, ‖S y‖ₑ ∂(MeasureTheory.volume : Measure E3)
          ∂((MeasureTheory.volume : Measure E3).restrict (Submission.BoseGases.acube ℓ)) := by
        apply MeasureTheory.lintegral_mono
        intro x
        exact hinner x
    _ = (∫⁻ y, ‖S y‖ₑ ∂(MeasureTheory.volume : Measure E3)) *
          ((MeasureTheory.volume : Measure E3).restrict (Submission.BoseGases.acube ℓ)) Set.univ :=
        MeasureTheory.lintegral_const _
    _ = (∫⁻ y, ‖S y‖ₑ ∂(MeasureTheory.volume : Measure E3)) *
          ENNReal.ofReal (ℓ ^ 3) := by
        rw [Measure.restrict_apply_univ, Submission.BoseGases.acube_volume ℓ hℓ.le]
    _ < ⊤ := ENNReal.mul_lt_top hSfin ENNReal.ofReal_lt_top

/-- **The requested lemma.**  If `S` is integrable on `ℝ³` then the two-body kernel
`(x,y) ↦ S (x - y + c)` is integrable on the box product `Λ(ℓ) × Λ(ℓ)`. -/
theorem integrableOn_pairDiff {ℓ : ℝ} (hℓ : 0 < ℓ)
    {S : EuclideanSpace ℝ (Fin 3) → ℝ} (hS : MeasureTheory.Integrable S)
    (c : EuclideanSpace ℝ (Fin 3)) :
    MeasureTheory.IntegrableOn (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
      S (p.1 - p.2 + c)) (Submission.BoseGases.acube ℓ ×ˢ Submission.BoseGases.acube ℓ) := by
  change MeasureTheory.Integrable (fun p : E3 × E3 => S (p.1 - p.2 + c))
    ((MeasureTheory.volume : Measure (E3 × E3)).restrict
      (Submission.BoseGases.acube ℓ ×ˢ Submission.BoseGases.acube ℓ))
  rw [show ((MeasureTheory.volume : Measure (E3 × E3)).restrict
        (Submission.BoseGases.acube ℓ ×ˢ Submission.BoseGases.acube ℓ))
      = ((MeasureTheory.volume : Measure E3).restrict (Submission.BoseGases.acube ℓ)).prod
        ((MeasureTheory.volume : Measure E3).restrict (Submission.BoseGases.acube ℓ)) from by
    rw [show (MeasureTheory.volume : Measure (E3 × E3))
        = (MeasureTheory.volume : Measure E3).prod (MeasureTheory.volume : Measure E3) from rfl]
    exact (Measure.prod_restrict _ _).symm]
  exact ⟨aestronglyMeasurable_pairDiff hS c, hasFiniteIntegral_pairDiff hℓ hS c⟩

end Work.BoseBoxFock
