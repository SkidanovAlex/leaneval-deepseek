import Mathlib.Tactic.Have
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixGlue.Pot.aestronglyMeasurable_potWordU_weight
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB2.Pot.aemeasurable_wPairC_prod`

A.e. strong measurability of the localized two-body kernel
`wPairC ℓ h (x,y) = χ_ℓ(x) · h(x−y)/(χ⋆χ)_ℓ(x−y) · χ_ℓ(y)`
on the product `ℝ³ × ℝ³`, for a numerator `h` which is only *a.e.* strongly
measurable (this is exactly the situation in the corpus, where `h` is one of the
scattering kernels `v`, `g₀`, `g₂` known only a.e.).

The three ingredients are elementary:

* `(x,y) ↦ h (x − y)`: `h` composed with the difference map, which is
  quasi-measure-preserving on `(ℝ³ × ℝ³, volume.prod volume)`
  (`quasiMeasurePreserving_sub_of_right_invariant`), so `AEStronglyMeasurable`
  transfers (`AEStronglyMeasurable.comp_quasiMeasurePreserving`);
* `(x,y) ↦ ((χ⋆χ)_ℓ(x−y))⁻¹`: measurable, being the inverse of a continuous
  function (`convScale_continuous` composed with the continuous difference map);
* `(x,y) ↦ χ_ℓ(x)` and `(x,y) ↦ χ_ℓ(y)`: continuous (`chiScale_continuous`).

The result is closed under pointwise products.
-/

noncomputable section

open MeasureTheory

namespace Work.BoseFixB2.Pot

set_option autoImplicit false

/-- The difference map `(x,y) ↦ x − y` on `ℝ³ × ℝ³` is quasi-measure-preserving
for Lebesgue measure (which is translation invariant). -/
lemma qmp_sub_prod :
    Measure.QuasiMeasurePreserving (fun p : ℝ³ × ℝ³ => p.1 - p.2)
      ((MeasureTheory.volume : Measure ℝ³).prod (MeasureTheory.volume : Measure ℝ³))
      (MeasureTheory.volume : Measure ℝ³) :=
  quasiMeasurePreserving_sub_of_right_invariant _ _

/-- Composition of an a.e. strongly measurable function with the difference map. -/
lemma aestronglyMeasurable_comp_sub {h : ℝ³ → ℝ}
    (hh : MeasureTheory.AEStronglyMeasurable h (MeasureTheory.volume : Measure ℝ³)) :
    MeasureTheory.AEStronglyMeasurable (fun p : ℝ³ × ℝ³ => h (p.1 - p.2))
      ((MeasureTheory.volume : Measure ℝ³).prod (MeasureTheory.volume : Measure ℝ³)) :=
  hh.comp_quasiMeasurePreserving qmp_sub_prod

/-- `(x,y) ↦ ((χ⋆χ)_ℓ(x−y))⁻¹` is measurable. -/
lemma measurable_convScale_sub_inv (ℓ : ℝ) :
    Measurable (fun p : ℝ³ × ℝ³ => (Submission.BoseGases.convScale ℓ (p.1 - p.2))⁻¹) :=
  measurable_inv.comp
    ((Submission.BoseGases.convScale_continuous ℓ)
      |>.comp (by fun_prop : Continuous fun p : ℝ³ × ℝ³ => p.1 - p.2) |>.measurable)

/-- `wPairC ℓ h` is a.e. strongly measurable on the product `ℝ³ × ℝ³` whenever the
numerator `h` is a.e. strongly measurable with respect to Lebesgue measure. -/
theorem aemeasurable_wPairC_prod {h : EuclideanSpace ℝ (Fin 3) → ℝ} {ℓ : ℝ}
    (hh : MeasureTheory.AEStronglyMeasurable h (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3)))) :
    MeasureTheory.AEStronglyMeasurable (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
        Submission.BoseGases.wPairC ℓ h p.1 p.2)
      ((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).prod
        (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3)))) := by
  have hsub : MeasureTheory.AEStronglyMeasurable (fun p : ℝ³ × ℝ³ => h (p.1 - p.2))
      ((MeasureTheory.volume : Measure ℝ³).prod (MeasureTheory.volume : Measure ℝ³)) :=
    aestronglyMeasurable_comp_sub hh
  have hinv : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ³ × ℝ³ => (Submission.BoseGases.convScale ℓ (p.1 - p.2))⁻¹)
      ((MeasureTheory.volume : Measure ℝ³).prod (MeasureTheory.volume : Measure ℝ³)) :=
    (measurable_convScale_sub_inv ℓ).aestronglyMeasurable
  have hchi1 : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ³ × ℝ³ => Submission.BoseGases.chiScale ℓ p.1)
      ((MeasureTheory.volume : Measure ℝ³).prod (MeasureTheory.volume : Measure ℝ³)) :=
    ((Submission.BoseGases.chiScale_continuous ℓ).comp
      (by fun_prop : Continuous fun p : ℝ³ × ℝ³ => p.1) |>.measurable).aestronglyMeasurable
  have hchi2 : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ³ × ℝ³ => Submission.BoseGases.chiScale ℓ p.2)
      ((MeasureTheory.volume : Measure ℝ³).prod (MeasureTheory.volume : Measure ℝ³)) :=
    ((Submission.BoseGases.chiScale_continuous ℓ).comp
      (by fun_prop : Continuous fun p : ℝ³ × ℝ³ => p.2) |>.measurable).aestronglyMeasurable
  have hmain := (hchi1.mul (hsub.mul hinv)).mul hchi2
  refine hmain.congr ?_
  exact Filter.Eventually.of_forall (fun p => by
    simp [Submission.BoseGases.wPairC, Submission.BoseGases.wPair, Submission.BoseGases.wScaled,
      Pi.mul_apply, div_eq_mul_inv])

end Work.BoseFixB2.Pot
