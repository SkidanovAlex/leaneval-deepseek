import ChallengeDeps
import Mathlib.Tactic.Have
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.BoseFixB1.WB.Lead
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.WB.wbU_aemeasurable`

A.e. strong measurability of the two window-vocabulary objects of `WB.Defs`:

* `wbMass v h μ u = ∬ w_{1,B(u)}` — the localised one-body mass, a *double* Bochner
  integral of the localised kernel `Submission.BoseGases.wSmall1Pair h M ℓ d u x y`;
* `wbU v h μ z = ∫_{I₋} (wbMass u / chiMass u)·χ_{B(u)}(z)² du` — FS's `U`.

Both follow from the two Fubini-measurability steps of
`MeasureTheory.AEStronglyMeasurable.integral_prod_right'`, applied to the joint
a.e. strong measurability of the kernel on the `(u,x,y)`-space.  That joint fact is
the only non-trivial input:

* the two `χ_{B(u)}` factors are *continuous* in `(u,x)` resp. `(u,y)`
  (`chiScale_continuous`, `chiSmall_continuous`), hence a.e. strongly measurable;
* the denominators `convScaleSmall M (ℓd) (x−y)`, `convScale ℓ (x−y)` are continuous
  in `(x,y)` (`conv3Small_continuous`, `convScale_continuous`);
* the numerator `g₀ v h = v(1−w₀)` is only a.e. strongly measurable, since the
  `ScatSol` data supplies it only through `LocallyIntegrable (v·(1−w₀))`
  (`IsScatteringSolution.rhs_integrable`); its transport along the difference map is
  handled by quasi-measure-preservation of `(u,x,y) ↦ x−y`, which the additive
  `QuasiMeasurePreserving.prod_of_left` reduces to the measure-preserving slice
  `y ↦ x−y`.

The `χ`-mass factor in the definition of `wbU` is measurable for the same reason
(`chiMass M ℓ d u = ∫_x χ_{B(u)}(u,x)²` is an integral of a jointly continuous
function).
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.BoseFixB1.WB

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## 1. The difference map on `(ℝ³ × ℝ³) × ℝ³` is quasi-measure-preserving -/

/-- The map `q ↦ q.1.2 − q.2` (the difference of the *second* and *third* coordinates of
`(ℝ³ × ℝ³) × ℝ³`) is quasi-measure-preserving for Lebesgue measure: every slice
`p ↦ p.2 − z` is a measure-preserving bijection of `ℝ³`. -/
lemma quasiMeasurePreserving_sub_coord₂ :
    Measure.QuasiMeasurePreserving (fun q : (ℝ³ × ℝ³) × ℝ³ => q.1.2 - q.2)
      (((MeasureTheory.volume : MeasureTheory.Measure ℝ³).prod MeasureTheory.volume).prod
        MeasureTheory.volume)
      (MeasureTheory.volume : MeasureTheory.Measure ℝ³) := by
  refine MeasureTheory.QuasiMeasurePreserving.prod_of_left (by fun_prop) ?_
  filter_upwards with z
  exact ((measurePreserving_sub_right (MeasureTheory.volume : MeasureTheory.Measure ℝ³) z)
      |>.quasiMeasurePreserving).comp Measure.quasiMeasurePreserving_snd

/-! ## 2. `g₀` and the `χ`-mass are a.e. strongly measurable -/

/-- `g₀ v h = v·(1−w₀)` is a.e. strongly measurable: the scattering-solution data
supplies it as a locally integrable (hence a.e. strongly measurable) function. -/
lemma aestronglyMeasurable_g0 {v : ℝ³ → ℝ} {h : Work.UBB.ScatSol v} :
    MeasureTheory.AEStronglyMeasurable (Submission.BoseGases.g0 v h) := by
  have hli : MeasureTheory.LocallyIntegrable (Submission.BoseGases.g0 v h) := by
    have h2 := (Classical.choose_spec h).2.rhs_integrable
    have hfun : (v * (1 - Classical.choose h) : ℝ³ → ℝ) = Submission.BoseGases.g0 v h := by
      funext x; simp [Submission.BoseGases.g0, Pi.mul_apply, Pi.sub_apply]
    rwa [hfun] at h2
  exact hli.aestronglyMeasurable

/-- `u ↦ chiMass M ℓ d u` is measurable (it is the Bochner integral of the jointly continuous
function `(u,x) ↦ χ_{B(u)}(u,x)²`). -/
lemma measurable_chiMass (M : ℕ) (hM : 1 ≤ M) (ℓ d : ℝ) :
    Measurable (fun u : ℝ³ => Work.SmallBoxSliding.chiMass M ℓ d u) := by
  have hcont : Continuous (fun p : ℝ³ × ℝ³ =>
      (Submission.BoseGases.chiSmallB M ℓ d p.1 p.2) ^ 2) := by
    have h1 : Continuous (fun p : ℝ³ × ℝ³ => Submission.BoseGases.chiScale ℓ p.2) :=
      (Submission.BoseGases.chiScale_continuous ℓ).comp continuous_snd
    have h2 : Continuous (fun p : ℝ³ × ℝ³ =>
        Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • p.2 - p.1)) :=
      (Submission.BoseGases.chiSmall_continuous hM).comp (by fun_prop)
    exact (h1.mul h2).pow 2
  have hstrong : StronglyMeasurable
      (fun u : ℝ³ => ∫ x, (Submission.BoseGases.chiSmallB M ℓ d u x) ^ 2) :=
    StronglyMeasurable.integral_prod_right
      (f := fun u x => (Submission.BoseGases.chiSmallB M ℓ d u x) ^ 2) hcont.stronglyMeasurable
  exact hstrong.measurable

/-! ## 3. Joint a.e. strong measurability of the localised kernel on `(u,x,y)` -/

/-- The localised one-body kernel `(u,x,y) ↦ wSmall1Pair h M ℓ d u x y` is a.e. strongly
measurable for the triple product of Lebesgue measures. -/
lemma aestronglyMeasurable_wSmall1Pair_vol {v : ℝ³ → ℝ} {h : Work.UBB.ScatSol v}
    {M : ℕ} (hM : 1 ≤ M) (ℓ d : ℝ) :
    MeasureTheory.AEStronglyMeasurable
      (fun q : (ℝ³ × ℝ³) × ℝ³ => Submission.BoseGases.wSmall1Pair h M ℓ d q.1.1 q.1.2 q.2)
      (((MeasureTheory.volume : MeasureTheory.Measure ℝ³).prod MeasureTheory.volume).prod
        MeasureTheory.volume) := by
  have hnum : AEMeasurable
      (fun q : (ℝ³ × ℝ³) × ℝ³ => Submission.BoseGases.g0 v h (q.1.2 - q.2))
      (((MeasureTheory.volume : MeasureTheory.Measure ℝ³).prod MeasureTheory.volume).prod
        MeasureTheory.volume) :=
    ((aestronglyMeasurable_g0 (v := v) (h := h)).comp_quasiMeasurePreserving
      quasiMeasurePreserving_sub_coord₂).aemeasurable
  have hden : AEMeasurable
      (fun q : (ℝ³ × ℝ³) × ℝ³ => Submission.BoseGases.convScaleSmall M (ℓ * d) (q.1.2 - q.2))
      (((MeasureTheory.volume : MeasureTheory.Measure ℝ³).prod MeasureTheory.volume).prod
        MeasureTheory.volume) := by
    have hcont : Continuous (fun q : (ℝ³ × ℝ³) × ℝ³ =>
        Submission.BoseGases.conv3Small M ((ℓ * d)⁻¹ • (q.1.2 - q.2))) :=
      (Submission.BoseGases.conv3Small_continuous hM).comp (by fun_prop)
    exact hcont.aemeasurable
  have hvc : AEMeasurable
      (fun q : (ℝ³ × ℝ³) × ℝ³ => Submission.BoseGases.convScale ℓ (q.1.2 - q.2))
      (((MeasureTheory.volume : MeasureTheory.Measure ℝ³).prod MeasureTheory.volume).prod
        MeasureTheory.volume) :=
    ((Submission.BoseGases.convScale_continuous ℓ).comp
      (by fun_prop : Continuous fun q : (ℝ³ × ℝ³) × ℝ³ => q.1.2 - q.2)).aemeasurable
  have hW0 : AEMeasurable
      (fun q : (ℝ³ × ℝ³) × ℝ³ =>
        Submission.BoseGases.wSmallScaled M (ℓ * d) (Submission.BoseGases.g0 v h) (q.1.2 - q.2))
      (((MeasureTheory.volume : MeasureTheory.Measure ℝ³).prod MeasureTheory.volume).prod
        MeasureTheory.volume) := hnum.div hden
  have hW : AEMeasurable
      (fun q : (ℝ³ × ℝ³) × ℝ³ =>
        Submission.BoseGases.wSmallScaled M (ℓ * d) (Submission.BoseGases.g0 v h) (q.1.2 - q.2)
          / Submission.BoseGases.convScale ℓ (q.1.2 - q.2))
      (((MeasureTheory.volume : MeasureTheory.Measure ℝ³).prod MeasureTheory.volume).prod
        MeasureTheory.volume) := hW0.div hvc
  have hA : AEMeasurable
      (fun q : (ℝ³ × ℝ³) × ℝ³ => Submission.BoseGases.chiSmallB M ℓ d q.1.1 q.1.2)
      (((MeasureTheory.volume : MeasureTheory.Measure ℝ³).prod MeasureTheory.volume).prod
        MeasureTheory.volume) := by
    have h1 : Continuous (fun q : (ℝ³ × ℝ³) × ℝ³ => Submission.BoseGases.chiScale ℓ q.1.2) :=
      (Submission.BoseGases.chiScale_continuous ℓ).comp (by fun_prop)
    have h2 : Continuous (fun q : (ℝ³ × ℝ³) × ℝ³ =>
        Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • q.1.2 - q.1.1)) :=
      (Submission.BoseGases.chiSmall_continuous hM).comp (by fun_prop)
    exact (h1.mul h2).aemeasurable
  have hC : AEMeasurable
      (fun q : (ℝ³ × ℝ³) × ℝ³ => Submission.BoseGases.chiSmallB M ℓ d q.1.1 q.2)
      (((MeasureTheory.volume : MeasureTheory.Measure ℝ³).prod MeasureTheory.volume).prod
        MeasureTheory.volume) := by
    have h1 : Continuous (fun q : (ℝ³ × ℝ³) × ℝ³ => Submission.BoseGases.chiScale ℓ q.2) :=
      (Submission.BoseGases.chiScale_continuous ℓ).comp (by fun_prop)
    have h2 : Continuous (fun q : (ℝ³ × ℝ³) × ℝ³ =>
        Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • q.2 - q.1.1)) :=
      (Submission.BoseGases.chiSmall_continuous hM).comp (by fun_prop)
    exact (h1.mul h2).aemeasurable
  exact ((hA.mul hW).mul hC).aestronglyMeasurable

/-! ## 4. The two objects -/

theorem wbU_aemeasurable {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v} {R0 : ℝ}
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R0) (hR0 : 0 < R0)
    {μ : ℝ} (hM : 1 ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M)
    (hℓ : 0 < Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
    (hd : 0 < (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d) :
    MeasureTheory.AEStronglyMeasurable
        (fun z : EuclideanSpace ℝ (Fin 3) => Work.BoseFixB1.wbU v h μ z) MeasureTheory.volume
      ∧ MeasureTheory.AEStronglyMeasurable
        (fun u : EuclideanSpace ℝ (Fin 3) => Work.BoseFixB1.wbMass v h μ u) MeasureTheory.volume := by
  unfold Work.BoseFixB1.wbU Work.BoseFixB1.wbMass Work.BoseFixB1.w1MassB
  set M := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M with hMdef
  set ℓ := Work.BoseBox.sideAt μ (_root_.BoseGases.a v) with hℓdef
  set dd := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d with hddef
  -- the joint kernel, and the two Fubini steps for `wbMass`
  have hK := aestronglyMeasurable_wSmall1Pair_vol (v := v) (h := h) (M := M) hM ℓ dd
  have hinner := MeasureTheory.AEStronglyMeasurable.integral_prod_right' hK
  have houter := MeasureTheory.AEStronglyMeasurable.integral_prod_right' hinner
  -- the same joint kernel, now as a function of `(z,u)`
  have hmassSnd : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ³ × ℝ³ => ∫ x, ∫ y, Submission.BoseGases.wSmall1Pair h M ℓ dd p.2 x y)
      ((MeasureTheory.volume : MeasureTheory.Measure ℝ³).prod MeasureTheory.volume) :=
    houter.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd
  have hchiMassInv : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ³ × ℝ³ => (Work.SmallBoxSliding.chiMass M ℓ dd p.2)⁻¹)
      ((MeasureTheory.volume : MeasureTheory.Measure ℝ³).prod MeasureTheory.volume) :=
    (measurable_inv.comp ((measurable_chiMass M hM ℓ dd).comp measurable_snd)).aestronglyMeasurable
  have hchiSq : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ³ × ℝ³ => (Submission.BoseGases.chiSmallB M ℓ dd p.2 p.1) ^ 2)
      ((MeasureTheory.volume : MeasureTheory.Measure ℝ³).prod MeasureTheory.volume) := by
    have hcont : Continuous (fun p : ℝ³ × ℝ³ =>
        Submission.BoseGases.chiSmallB M ℓ dd p.2 p.1) := by
      have h1 : Continuous (fun p : ℝ³ × ℝ³ => Submission.BoseGases.chiScale ℓ p.1) :=
        (Submission.BoseGases.chiScale_continuous ℓ).comp continuous_fst
      have h2 : Continuous (fun p : ℝ³ × ℝ³ =>
          Submission.BoseGases.chiSmall M ((ℓ * dd)⁻¹ • p.1 - p.2)) :=
        (Submission.BoseGases.chiSmall_continuous hM).comp (by fun_prop)
      exact h1.mul h2
    exact (hcont.pow 2).aestronglyMeasurable
  have hG : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ³ × ℝ³ => (∫ x, ∫ y, Submission.BoseGases.wSmall1Pair h M ℓ dd p.2 x y)
        / Work.SmallBoxSliding.chiMass M ℓ dd p.2
        * (Submission.BoseGases.chiSmallB M ℓ dd p.2 p.1) ^ 2)
      ((MeasureTheory.volume : MeasureTheory.Measure ℝ³).prod MeasureTheory.volume) :=
    (hmassSnd.mul hchiMassInv).mul hchiSq
  -- integrate over `u` against `volume.restrict I₋` (the set integral is *defined* as the
  -- integral against the restricted measure)
  have hle : ((MeasureTheory.volume : MeasureTheory.Measure ℝ³).prod
        ((MeasureTheory.volume : MeasureTheory.Measure ℝ³).restrict
          (Work.SmallBoxSliding.interiorSet ℓ dd μ)))
      ≤ ((MeasureTheory.volume : MeasureTheory.Measure ℝ³).prod
          (MeasureTheory.volume : MeasureTheory.Measure ℝ³)) :=
    Measure.prod_mono le_rfl Measure.restrict_le_self
  have hInt : MeasureTheory.AEStronglyMeasurable
      (fun z : ℝ³ => ∫ u in Work.SmallBoxSliding.interiorSet ℓ dd μ,
        (∫ x, ∫ y, Submission.BoseGases.wSmall1Pair h M ℓ dd u x y)
        / Work.SmallBoxSliding.chiMass M ℓ dd u
        * (Submission.BoseGases.chiSmallB M ℓ dd u z) ^ 2) MeasureTheory.volume :=
    MeasureTheory.AEStronglyMeasurable.integral_prod_right'
      (hG.mono_measure hle)
  exact ⟨hInt, houter⟩

end Work.BoseFixB1.WB
