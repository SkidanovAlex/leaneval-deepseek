import ChallengeDeps
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.BoseB1Cube.NomDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `aestronglyMeasurable_nomBoxInner` — measurability of FS's nominal per-box `F`-weight in `u`

FS's `thm:aprioriHLambda` integrates the per-box weight

    u ↦ ∫_{Λ} Φ² F( n(u)/|B(u)| )

against `u` (the sliding parameter).  This module supplies the measurability of that function of
`u`, i.e. that `Work.BoseB1Cube.nomBoxInner h μ Φ` is `AEStronglyMeasurable` for arbitrary
`Φ : BoxState n ℓ` (no smallness, positivity or support hypothesis on `Φ` is needed: only that `Φ`
is a smooth function, hence continuous, on the configuration space).

The proof is the parametric-integral theorem `AEStronglyMeasurable.integral_prod_right'`: the
integrand `(u, x) ↦ Φ x² · psiWeight 1 μ (nomCnt ℓ d u x / boxMass ℓ d u)` is jointly Borel
measurable, being built from
* `Φ ·` (continuous, so measurable),
* `psiWeight 1 μ` (a continuous function of `t`),
* the count `nomCnt ℓ d u x = Σᵢ 1_{xᵢ ∈ dlBox ℓ d u}` (a finite sum of indicators of measurable
  sets of the product),
* the box volume `boxMass ℓ d u` (the `u`-section of a measurable set of the product),
and division in `ℝ`.

Note that no domination/integrability hypothesis is needed: the section-integral theorem used
(`MeasureTheory.AEStronglyMeasurable.integral_prod_right'`) requires only the joint
a.e.-strong-measurability of the integrand.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseB1Cube

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "X" => Submission.BoseGases.X

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **Joint measurability of the box volume.**  `u ↦ boxMass ℓ d u` is Borel measurable for
*arbitrary* `ℓ, d` (no positivity of `ℓ` is needed): `boxMass ℓ d u = (volume.real) (dlBox ℓ d u)`
is the `u`-section of a measurable subset of `E3 × E3`, and sections of measurable sets have
measurable measure (`measurable_measure_prodMk_left`), followed by `ENNReal.toReal`. -/
lemma measurable_boxMass_cube (ℓ d : ℝ) :
    Measurable fun u : E3 => Work.SmallBoxSliding.boxMass ℓ d u := by
  have h1 : Measurable (fun u : E3 =>
      (volume : Measure E3) (Prod.mk u ⁻¹' {p : E3 × E3 |
        p.2 ∈ Submission.BoseGases.dlBox ℓ d p.1})) :=
    measurable_measure_prodMk_left (Work.SmallBoxSliding.measurableSet_boxIndSet ℓ d)
  have h2 : Measurable (fun u : E3 =>
      ((volume : Measure E3) (Submission.BoseGases.dlBox ℓ d u)).toReal) := h1.ennreal_toReal
  simpa [Work.SmallBoxSliding.boxMass_eq_measureReal, Measure.real_def] using h2

/-- **Joint measurability of the nominal count** `(u, x) ↦ nomCnt ℓ d u x`: a finite sum of
indicators of the sets `{(u,x) | xᵢ ∈ dlBox ℓ d u}`, which are preimages of the measurable set
`{p : E3 × E3 | p.2 ∈ dlBox ℓ d p.1}` under the measurable maps `p ↦ (p.1, p.2 i)`. -/
lemma measurable_nomCnt_joint (ℓ d : ℝ) (n : ℕ) :
    Measurable fun p : E3 × X n => Work.BoseB1Cube.nomCnt ℓ d p.1 p.2 := by
  unfold Work.BoseB1Cube.nomCnt
  refine Finset.measurable_sum _ (fun i _ => ?_)
  have hset : MeasurableSet {p : E3 × X n | p.2 i ∈ Submission.BoseGases.dlBox ℓ d p.1} := by
    have hmap : Measurable (fun p : E3 × X n => (p.1, p.2 i)) :=
      measurable_fst.prodMk ((measurable_pi_apply i).comp measurable_snd)
    exact hmap (Work.SmallBoxSliding.measurableSet_boxIndSet ℓ d)
  rw [show (fun p : E3 × X n => Work.SmallBoxSliding.boxInd ℓ d p.1 (p.2 i))
      = {p : E3 × X n | p.2 i ∈ Submission.BoseGases.dlBox ℓ d p.1}.indicator
          (fun _ => (1 : ℝ)) from rfl]
  exact measurable_const.indicator hset

/-- **Measurability of the `F`-weight as a function of the density**: `psiWeight c μ` is a
rational function of `t`, hence Borel measurable (division in `ℝ` is measurable with no
nonvanishing hypothesis). -/
lemma measurable_psiWeight_cube (c μ : ℝ) :
    Measurable fun t : ℝ => Work.SmallBoxSliding.psiWeight c μ t := by
  unfold Work.SmallBoxSliding.psiWeight
  fun_prop

/-- **The per-box nominal `F`-weight is a.e. strongly measurable in the sliding parameter `u`.**

This is the measurability that lets FS's `eq:appsliding` be integrated over `u`.  Note that the
statement carries no hypothesis at all beyond `Φ` being a smooth box state: in particular no
positivity of `μ`, no smallness of the diluteness and no support condition on `Φ` is used. -/
theorem aestronglyMeasurable_nomBoxInner {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v} {μ : ℝ} {n : ℕ}
    (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))) :
    MeasureTheory.AEStronglyMeasurable (fun u : EuclideanSpace ℝ (Fin 3) =>
      Work.BoseB1Cube.nomBoxInner h μ (Φ : Submission.BoseGases.X n → ℝ) u)
      (volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))) := by
  -- abbreviations for the two geometric parameters of the sliding box
  have hboxMass : Measurable (fun u : E3 =>
      Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) :=
    measurable_boxMass_cube _ _
  have hcnt : Measurable (fun p : E3 × X n =>
      Work.BoseB1Cube.nomCnt (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d p.1 p.2) :=
    measurable_nomCnt_joint _ _ n
  have hψ : Measurable (fun t : ℝ => Work.SmallBoxSliding.psiWeight 1 μ t) :=
    measurable_psiWeight_cube 1 μ
  have hΦ : Measurable (fun p : E3 × X n => (Φ : X n → ℝ) p.2 ^ 2) :=
    ((Φ.contDiff.continuous.measurable).comp measurable_snd).pow_const 2
  have hint : Measurable (fun p : E3 × X n => (Φ : X n → ℝ) p.2 ^ 2 *
      Work.SmallBoxSliding.psiWeight 1 μ
        (Work.BoseB1Cube.nomCnt (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d p.1 p.2 /
         Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d p.1)) :=
    hΦ.mul (hψ.comp (hcnt.div (hboxMass.comp measurable_fst)))
  have hAESM : MeasureTheory.AEStronglyMeasurable (fun p : E3 × X n => (Φ : X n → ℝ) p.2 ^ 2 *
      Work.SmallBoxSliding.psiWeight 1 μ
        (Work.BoseB1Cube.nomCnt (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d p.1 p.2 /
         Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d p.1))
      ((volume : Measure E3).prod
        ((volume : Measure (X n)).restrict
          (Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))))) :=
    (hint.aemeasurable).aestronglyMeasurable
  have hres := MeasureTheory.AEStronglyMeasurable.integral_prod_right'
      (μ := (volume : Measure E3))
      (ν := (volume : Measure (X n)).restrict
              (Submission.BoseGases.abox n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))))
      hAESM
  unfold Work.BoseB1Cube.nomBoxInner
  exact hres

end Work.BoseB1Cube
