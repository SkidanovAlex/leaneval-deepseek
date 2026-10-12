import ChallengeDeps
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Submission.Work.BoseFixB1.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1B.MeasurabilityGlobal`

A **taint-free** supply of the three measurability facts on the *full* product measure that
`Work.BoseFixB1.aestronglyMeasurable_w1MassB` needs (its global kernel statement
`Work.BoseFixB1.aestronglyMeasurable_wSmall1Pair_global` is still a dispatched `sorry`):

* `aemeasurable_g0_sub_full` — a.e.-measurability of `((u,a),y) ↦ g₀(a − y)` on
  `(volume ⊗ volume) ⊗ volume` for an a.e.-measurable `g₀` (measurable representative +
  null-preimage along the measure-preserving shift `y ↦ a − y`; the same argument as
  `Work.UBBInputs7.Finding.aemeasurable_comp_sub_coord₂`, but with the *unrestricted* third
  coordinate, which is what the marginal `u ↦ ∬ w_{1,B(u)}` needs);
* `aeStronglyMeasurable_wSmall1Pair_global` — a.e.-strong measurability of the three-variable
  localised kernel on the full `(volume ⊗ volume) ⊗ volume` (the same argument as the proved
  `Work.SmallBoxSliding.aestronglyMeasurable_wSmall1Pair_jointProd`, with the restricted
  `acube`-coordinates replaced by `volume`; the `mono_measure` step is then unnecessary);
* `aeStronglyMeasurable_w1MassB_global` — a.e.-strong measurability of `u ↦ ∬w_{1,B(u)}`
  (two applications of the parametric-integral lemma `integral_prod_right'`, plus the
  degenerate `M = 0` case in which `chiSmall 0` is constant and `w1MassB` does not depend on
  `u`).

All three are `sorry`-free and rest only on the corpus's proved kernel/`g₀` facts.
-/

noncomputable section

open MeasureTheory Metric

namespace Work.BoseFixB1B

open Submission.BoseGases

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-! ## 1. The `g₀(x−y)` numerator on the full triple product -/

/-- **A.e.-measurability of `((u,a),y) ↦ g (a − y)`** on
`(volume ⊗ volume) ⊗ volume`, for an a.e.-measurable `g : EuclideanSpace ℝ (Fin 3) → ℝ`.

Measurable representative `w` of `g`; the difference set is contained in the pullback of a
measurable null set `T ⊇ {g ≠ w}` along the difference map, and that pullback is null by
Tonelli, every fibre `y ↦ a − y` being measure-preserving. -/
theorem aemeasurable_g0_sub_full {g : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hg : AEMeasurable g (volume : Measure (EuclideanSpace ℝ (Fin 3)))) :
    AEMeasurable (fun p : (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) × EuclideanSpace ℝ (Fin 3) => g (p.1.2 - p.2))
      (((volume : Measure (EuclideanSpace ℝ (Fin 3))).prod (volume : Measure (EuclideanSpace ℝ (Fin 3)))).prod (volume : Measure (EuclideanSpace ℝ (Fin 3)))) := by
  set w : EuclideanSpace ℝ (Fin 3) → ℝ := hg.mk g with hwdef
  have hw : Measurable w := by rw [hwdef]; exact hg.measurable_mk
  have hgw : g =ᵐ[(volume : Measure (EuclideanSpace ℝ (Fin 3)))] w := by rw [hwdef]; exact hg.ae_eq_mk
  have hφ : Measurable (fun p : (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) × EuclideanSpace ℝ (Fin 3) => p.1.2 - p.2) := by fun_prop
  refine ((hw.comp hφ).aemeasurable).congr ?_
  have hT0 : (volume : Measure (EuclideanSpace ℝ (Fin 3))) {y | g y ≠ w y} = 0 := by
    simpa using MeasureTheory.ae_iff.mp hgw
  obtain ⟨T, hTsub, hTmeas, hTnull⟩ := MeasureTheory.exists_measurable_superset_of_null hT0
  set S : Set ((EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) × EuclideanSpace ℝ (Fin 3)) := {p | p.1.2 - p.2 ∈ T} with hSdef
  have hSmeas : MeasurableSet S := hTmeas.preimage hφ
  have hSnull : (((volume : Measure (EuclideanSpace ℝ (Fin 3))).prod (volume : Measure (EuclideanSpace ℝ (Fin 3)))).prod (volume : Measure (EuclideanSpace ℝ (Fin 3)))) S
      = 0 := by
    rw [Measure.prod_apply hSmeas]
    have hfib : ∀ q : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3), (volume : Measure (EuclideanSpace ℝ (Fin 3))) (Prod.mk q ⁻¹' S) = 0 := by
      intro q
      have hset : Prod.mk q ⁻¹' S = (fun y : EuclideanSpace ℝ (Fin 3) => q.2 - y) ⁻¹' T := by
        rw [hSdef]; ext y; simp
      rw [hset]
      have hpmp : MeasurePreserving (fun y : EuclideanSpace ℝ (Fin 3) => q.2 - y)
          (volume : Measure (EuclideanSpace ℝ (Fin 3))) (volume : Measure (EuclideanSpace ℝ (Fin 3))) := by
        convert (Measure.measurePreserving_neg (volume : Measure (EuclideanSpace ℝ (Fin 3)))).comp
          (measurePreserving_sub_right (volume : Measure (EuclideanSpace ℝ (Fin 3))) q.2) using 1
        ext y
        simp [Function.comp, neg_sub]
      rw [hpmp.measure_preimage hTmeas.nullMeasurableSet, hTnull]
    simp only [hfib, lintegral_zero]
  have hsub : {p : (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) × EuclideanSpace ℝ (Fin 3) | w (p.1.2 - p.2) ≠ g (p.1.2 - p.2)} ⊆ S := by
    intro p hp
    rw [hSdef]
    by_contra hmem
    exact hp (not_not.mp (fun h => hmem (hTsub h))).symm
  have hdiff : (((volume : Measure (EuclideanSpace ℝ (Fin 3))).prod (volume : Measure (EuclideanSpace ℝ (Fin 3)))).prod (volume : Measure (EuclideanSpace ℝ (Fin 3))))
      {p | w (p.1.2 - p.2) ≠ g (p.1.2 - p.2)} = 0 :=
    MeasureTheory.measure_mono_null hsub hSnull
  exact MeasureTheory.ae_iff.mpr hdiff

/-! ## 2. The localised kernel on the full triple product -/

/-- **A.e.-strong measurability of `((u,x),y) ↦ w_{1,B(u)}(x,y)`** for the product measure
`(volume ⊗ volume) ⊗ volume`.

The two `chiSmallB` factors and the two renormalisation denominators are continuous
(`chiScale_continuous`, `chiSmall_continuous`, `convScale_continuous`,
`conv3Small_continuous`), and the only a.e.-measurable ingredient is the numerator
`g₀ v h (x − y)` (from `g₀_integrable` through `aemeasurable_g0_sub_full`); quotients and
products of (a.e.-)measurable functions are a.e.-measurable, and an a.e.-measurable
real-valued function is a.e.-strongly-measurable. -/
theorem aeStronglyMeasurable_wSmall1Pair_global {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v} {M : ℕ}
    (hM : 1 ≤ M) {ℓ d : ℝ} {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R) :
    MeasureTheory.AEStronglyMeasurable
      (fun p : (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) × EuclideanSpace ℝ (Fin 3) => wSmall1Pair h M ℓ d p.1.1 p.1.2 p.2)
      (((volume : Measure (EuclideanSpace ℝ (Fin 3))).prod (volume : Measure (EuclideanSpace ℝ (Fin 3)))).prod (volume : Measure (EuclideanSpace ℝ (Fin 3)))) := by
  have hg0 : MeasureTheory.Integrable (g0 v h) (volume : Measure (EuclideanSpace ℝ (Fin 3))) :=
    g0_integrable hR hv_supp h
  have hnum : AEMeasurable (fun p : (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) × EuclideanSpace ℝ (Fin 3) => g0 v h (p.1.2 - p.2))
      (((volume : Measure (EuclideanSpace ℝ (Fin 3))).prod (volume : Measure (EuclideanSpace ℝ (Fin 3)))).prod (volume : Measure (EuclideanSpace ℝ (Fin 3)))) :=
    aemeasurable_g0_sub_full hg0.aemeasurable
  have hden : Continuous (fun p : (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) × EuclideanSpace ℝ (Fin 3) => convScaleSmall M (ℓ * d) (p.1.2 - p.2)) := by
    have h1 : Continuous (fun p : (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) × EuclideanSpace ℝ (Fin 3) => (ℓ * d)⁻¹ • (p.1.2 - p.2)) := by fun_prop
    exact (conv3Small_continuous hM).comp h1
  have hW0 : AEMeasurable (fun p : (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) × EuclideanSpace ℝ (Fin 3) =>
      wSmallScaled M (ℓ * d) (g0 v h) (p.1.2 - p.2))
      (((volume : Measure (EuclideanSpace ℝ (Fin 3))).prod (volume : Measure (EuclideanSpace ℝ (Fin 3)))).prod (volume : Measure (EuclideanSpace ℝ (Fin 3)))) :=
    hnum.div hden.aemeasurable
  have hvc : AEMeasurable (fun p : (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) × EuclideanSpace ℝ (Fin 3) => convScale ℓ (p.1.2 - p.2))
      (((volume : Measure (EuclideanSpace ℝ (Fin 3))).prod (volume : Measure (EuclideanSpace ℝ (Fin 3)))).prod (volume : Measure (EuclideanSpace ℝ (Fin 3)))) :=
    ((convScale_continuous ℓ).comp (by fun_prop)).aemeasurable
  have hW : AEMeasurable (fun p : (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) × EuclideanSpace ℝ (Fin 3) =>
      wSmallScaled M (ℓ * d) (g0 v h) (p.1.2 - p.2) / convScale ℓ (p.1.2 - p.2))
      (((volume : Measure (EuclideanSpace ℝ (Fin 3))).prod (volume : Measure (EuclideanSpace ℝ (Fin 3)))).prod (volume : Measure (EuclideanSpace ℝ (Fin 3)))) :=
    hW0.div hvc
  have hA : AEMeasurable (fun p : (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) × EuclideanSpace ℝ (Fin 3) => chiSmallB M ℓ d p.1.1 p.1.2)
      (((volume : Measure (EuclideanSpace ℝ (Fin 3))).prod (volume : Measure (EuclideanSpace ℝ (Fin 3)))).prod (volume : Measure (EuclideanSpace ℝ (Fin 3)))) := by
    have h1 : Continuous (fun p : (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) × EuclideanSpace ℝ (Fin 3) => chiScale ℓ p.1.2) :=
      (chiScale_continuous ℓ).comp (by fun_prop)
    have h2 : Continuous (fun p : (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) × EuclideanSpace ℝ (Fin 3) =>
        chiSmall M ((ℓ * d)⁻¹ • p.1.2 - p.1.1)) :=
      (chiSmall_continuous hM).comp (by fun_prop)
    exact (h1.mul h2).aemeasurable
  have hC : AEMeasurable (fun p : (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) × EuclideanSpace ℝ (Fin 3) => chiSmallB M ℓ d p.1.1 p.2)
      (((volume : Measure (EuclideanSpace ℝ (Fin 3))).prod (volume : Measure (EuclideanSpace ℝ (Fin 3)))).prod (volume : Measure (EuclideanSpace ℝ (Fin 3)))) := by
    have h1 : Continuous (fun p : (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) × EuclideanSpace ℝ (Fin 3) => chiScale ℓ p.2) :=
      (chiScale_continuous ℓ).comp (by fun_prop)
    have h2 : Continuous (fun p : (EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3)) × EuclideanSpace ℝ (Fin 3) =>
        chiSmall M ((ℓ * d)⁻¹ • p.2 - p.1.1)) :=
      (chiSmall_continuous hM).comp (by fun_prop)
    exact (h1.mul h2).aemeasurable
  exact ((hA.mul hW).mul hC).aestronglyMeasurable

/-! ## 3. The `u`-marginal `∬w_{1,B(u)}` -/

/-- **A.e.-strong measurability of `u ↦ ∬w_{1,B(u)}`** (the full double integral). -/
theorem aeStronglyMeasurable_w1MassB_global {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R) {M : ℕ} {ℓ d : ℝ}
    (hℓ : 0 < ℓ) (hd : 0 < d) :
    MeasureTheory.AEStronglyMeasurable
      (fun u : EuclideanSpace ℝ (Fin 3) => Work.BoseFixB1.w1MassB h M ℓ d u)
      (volume : Measure (EuclideanSpace ℝ (Fin 3))) := by
  -- `chiSmall 0` is constant, so for `M = 0` the mass does not depend on `u`
  have hchi0 : chiSmall 0 = fun _ : EuclideanSpace ℝ (Fin 3) => (Real.sqrt (chiSmallNormSq 0))⁻¹ := by
    funext z
    simp [chiSmall, chiSmallBase]
  by_cases hM0 : M = 0
  · rw [hM0]
    have hconst : ∀ u : EuclideanSpace ℝ (Fin 3), Work.BoseFixB1.w1MassB h 0 ℓ d u = Work.BoseFixB1.w1MassB h 0 ℓ d 0 := by
      intro u
      simp only [Work.BoseFixB1.w1MassB, wSmall1Pair, wSmallPair, chiSmallB, hchi0]
    rw [show (fun u : EuclideanSpace ℝ (Fin 3) => Work.BoseFixB1.w1MassB h 0 ℓ d u)
        = (fun _ : EuclideanSpace ℝ (Fin 3) => Work.BoseFixB1.w1MassB h 0 ℓ d 0) from funext hconst]
    exact aestronglyMeasurable_const
  · have hM : 1 ≤ M := Nat.one_le_iff_ne_zero.mpr hM0
    have hj := aeStronglyMeasurable_wSmall1Pair_global (v := v) (h := h) (M := M) (ℓ := ℓ) (d := d)
      hM hR hv_supp
    have h1 : AEStronglyMeasurable
        (fun q : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) => ∫ y : EuclideanSpace ℝ (Fin 3), wSmall1Pair h M ℓ d q.1 q.2 y)
        ((volume : Measure (EuclideanSpace ℝ (Fin 3))).prod (volume : Measure (EuclideanSpace ℝ (Fin 3)))) :=
      AEStronglyMeasurable.integral_prod_right' (ν := (volume : Measure (EuclideanSpace ℝ (Fin 3)))) hj
    have h2 : AEStronglyMeasurable
        (fun u : EuclideanSpace ℝ (Fin 3) => ∫ x : EuclideanSpace ℝ (Fin 3), ∫ y : EuclideanSpace ℝ (Fin 3), wSmall1Pair h M ℓ d u x y)
        (volume : Measure (EuclideanSpace ℝ (Fin 3))) :=
      AEStronglyMeasurable.integral_prod_right' (ν := (volume : Measure (EuclideanSpace ℝ (Fin 3)))) h1
    exact h2

end Work.BoseFixB1B
