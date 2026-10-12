import ChallengeDeps
import Mathlib.MeasureTheory.Measure.Haar.Unique
import Submission.Work.BoseFixB1.WB.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.WB.aestronglyMeasurable_wbMass`

A.e. strong measurability of the localised one-body mass
`wbMass v h μ = ∬ w_{1,B(u)}` as a function of the sliding variable
`u ∈ ℝ³` (FS's `∫_{I₋} wmass`, the ingredient `∈ L¹` of the Jensen/Cauchy–Schwarz
step of FS's `thm:aprioriHLambda`).

## The mathematics

By definition (`WB.Defs`, `Submission.Work.BoseFixB1.Defs`)

  `wbMass v h μ u = w1MassB h M ℓ d u = ∫ x, ∫ y, wSmall1Pair h M ℓ d u x y`

with the *frozen* parameters `M = (paramsAt μ (a v)).M = 48`, `ℓ = sideAt μ (a v)`,
`d = (paramsAt μ (a v)).d`, and (`DLSmallKernels`)

  `wSmall1Pair h M ℓ d u x y
     = χ_{B(u)}(x) · (g₀(x−y) / (χ_M⋆χ_M)((x−y)/(ℓd)) / (χ⋆χ)((x−y)/ℓ))
         · χ_{B(u)}(y)`,

  `χ_{B(u)}(x) = χ(x/ℓ)·χ_M(x/(ℓd) − u)`.

So the only `u`-dependence sits in the two cutoff factors `χ_{B(u)}(x)`,
`χ_{B(u)}(y)`, which are *jointly continuous* in `(u,x)`, and the two-fold
integral is exactly the iterated Bochner integral whose kernel carries the
difference map `(x,y) ↦ x − y`.

The proof therefore proceeds as follows.

*  The kernel `(u,x,y) ↦ wSmall1Pair h M ℓ d u x y` is a.e. strongly measurable
   on `(ℝ³ × ℝ³) × ℝ³`: the two cutoff factors and both normalisation
   denominators are continuous, while the numerator `g₀(x−y)` is pulled back
   along the **difference map**, which is quasi-measure-preserving for Lebesgue
   measure (`QuasiMeasurePreserving.prod_of_right`, using translation
   invariance); `g₀ v h = v(1−w₀)` is only a.e. strongly measurable, the
   hypotheses on `v` being weak (`ScatSol v` gives exactly that
   `v(1−w₀) ∈ L¹_loc`).
*  `AEStronglyMeasurable.integral_prod_right'` (a Fubini-measurability lemma
   that needs *no* integrability hypothesis, so it applies to the a.e.-
   measurable kernel and does not require the small box to have finite measure)
   integrates out the `y`-variable, and then the `x`-variable.

No positivity, integrability or consistency hypothesis on `(μ, v)` is used: the
statement is unconditional.
-/

noncomputable section

open MeasureTheory

namespace Work.BoseFixB1.WB

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem aestronglyMeasurable_wbMass {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {μ : ℝ} :
    MeasureTheory.AEStronglyMeasurable
      (fun u : EuclideanSpace ℝ (Fin 3) => Work.BoseFixB1.wbMass v h μ u)
      (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))) := by
  -- the numerator `g₀ v h = v(1−w₀)` is a.e. strongly measurable, since it is
  -- locally integrable by the scattering-solution axioms.
  have hg0 : AEStronglyMeasurable (Submission.BoseGases.g0 v h) (volume : Measure E3) :=
    (h.choose_spec.2.rhs_integrable).aestronglyMeasurable
  -- the difference map on the triple `(u,x,y) ↦ x − y` is quasi-measure-preserving
  -- (translation invariance of Lebesgue measure), so a.e. strong measurability is
  -- pulled back along it.
  have hqmp : Measure.QuasiMeasurePreserving (fun q : (E3 × E3) × E3 => q.1.2 - q.2)
      (((volume : Measure E3).prod (volume : Measure E3)).prod (volume : Measure E3))
      (volume : Measure E3) := by
    refine MeasureTheory.QuasiMeasurePreserving.prod_of_right ?_ ?_
    · fun_prop
    · filter_upwards with a
      have h : (fun b : E3 => a.2 - b) = (fun b => -(b - a.2)) := by
        funext b
        abel
      rw [h]
      exact ((Measure.measurePreserving_neg (volume : Measure E3)).comp
        (measurePreserving_sub_right (volume : Measure E3) a.2)).quasiMeasurePreserving
  have hg0p : AEStronglyMeasurable
      (fun q : (E3 × E3) × E3 => Submission.BoseGases.g0 v h (q.1.2 - q.2))
      (((volume : Measure E3).prod (volume : Measure E3)).prod (volume : Measure E3)) :=
    hg0.comp_quasiMeasurePreserving hqmp
  clear hg0 hqmp
  -- the main computation, for the frozen parameters `(M, ℓ, d)`
  have key : ∀ (M : ℕ) (_hM : 1 ≤ M) (ℓ d : ℝ),
      AEStronglyMeasurable (fun u : E3 => ∫ x : E3, ∫ y : E3,
        Submission.BoseGases.wSmall1Pair h M ℓ d u x y) (volume : Measure E3) := by
    intro M hM ℓ d
    have hchiSM : Continuous (fun z : E3 => Submission.BoseGases.chiSmall M z) :=
      Submission.BoseGases.chiSmall_continuous hM
    -- the two cutoff factors are jointly continuous in `(u, x)`
    have hchi1 : Continuous (fun q : (E3 × E3) × E3 =>
        Submission.BoseGases.chiSmallB M ℓ d q.1.1 q.1.2) := by
      have heq : (fun q : (E3 × E3) × E3 => Submission.BoseGases.chiSmallB M ℓ d q.1.1 q.1.2)
          = fun q => Submission.BoseGases.chiScale ℓ q.1.2 *
              Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • q.1.2 - q.1.1) := rfl
      rw [heq]
      exact ((Submission.BoseGases.chiScale_continuous ℓ).comp (by fun_prop)).mul
        (hchiSM.comp (by fun_prop))
    have hchi2 : Continuous (fun q : (E3 × E3) × E3 =>
        Submission.BoseGases.chiSmallB M ℓ d q.1.1 q.2) := by
      have heq : (fun q : (E3 × E3) × E3 => Submission.BoseGases.chiSmallB M ℓ d q.1.1 q.2)
          = fun q => Submission.BoseGases.chiScale ℓ q.2 *
              Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • q.2 - q.1.1) := rfl
      rw [heq]
      exact ((Submission.BoseGases.chiScale_continuous ℓ).comp (by fun_prop)).mul
        (hchiSM.comp (by fun_prop))
    -- the two normalisation denominators are continuous, too
    have hcs : Continuous (fun q : (E3 × E3) × E3 =>
        Submission.BoseGases.convScaleSmall M (ℓ * d) (q.1.2 - q.2)) := by
      have heq : (fun q : (E3 × E3) × E3 =>
            Submission.BoseGases.convScaleSmall M (ℓ * d) (q.1.2 - q.2))
          = fun q => Submission.BoseGases.conv3Small M ((ℓ * d)⁻¹ • (q.1.2 - q.2)) := rfl
      rw [heq]
      exact (Submission.BoseGases.conv3Small_continuous hM).comp (by fun_prop)
    have hcl : Continuous (fun q : (E3 × E3) × E3 =>
        Submission.BoseGases.convScale ℓ (q.1.2 - q.2)) :=
      (Submission.BoseGases.convScale_continuous ℓ).comp (by fun_prop)
    have hkerAe : AEMeasurable
        (fun q : (E3 × E3) × E3 =>
          Submission.BoseGases.chiSmallB M ℓ d q.1.1 q.1.2 *
            (Submission.BoseGases.g0 v h (q.1.2 - q.2) /
              Submission.BoseGases.convScaleSmall M (ℓ * d) (q.1.2 - q.2) /
                Submission.BoseGases.convScale ℓ (q.1.2 - q.2)) *
          Submission.BoseGases.chiSmallB M ℓ d q.1.1 q.2)
        (((volume : Measure E3).prod (volume : Measure E3)).prod (volume : Measure E3)) :=
      ((hchi1.aemeasurable.mul
        ((hg0p.aemeasurable.div hcs.aemeasurable).div hcl.aemeasurable)).mul hchi2.aemeasurable)
    have hkern : AEStronglyMeasurable
        (fun q : (E3 × E3) × E3 =>
          Submission.BoseGases.wSmall1Pair h M ℓ d q.1.1 q.1.2 q.2)
        (((volume : Measure E3).prod (volume : Measure E3)).prod (volume : Measure E3)) := by
      refine hkerAe.aestronglyMeasurable.congr ?_
      filter_upwards with q
      simp only [Submission.BoseGases.wSmall1Pair, Submission.BoseGases.wSmallPair,
        Submission.BoseGases.wSmallScaled]
    -- Fubini-measurability, first in `y`, then in `x`
    have hstep1 : AEStronglyMeasurable (fun p : E3 × E3 => ∫ y : E3,
        Submission.BoseGases.wSmall1Pair h M ℓ d p.1 p.2 y)
        ((volume : Measure E3).prod (volume : Measure E3)) :=
      MeasureTheory.AEStronglyMeasurable.integral_prod_right'
        (μ := (volume : Measure E3).prod (volume : Measure E3)) (ν := (volume : Measure E3)) hkern
    exact MeasureTheory.AEStronglyMeasurable.integral_prod_right'
      (μ := (volume : Measure E3)) (ν := (volume : Measure E3)) hstep1
  have hmain := key (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
    (by norm_num [Work.BoseBox.paramsAt, Work.BoseBox.fsParams, Work.BoseBox.mValue])
    (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d
  show AEStronglyMeasurable (fun u : E3 => ∫ x : E3, ∫ y : E3,
      Submission.BoseGases.wSmall1Pair h (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
        (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u x y)
      (volume : Measure E3)
  exact hmain

end Work.BoseFixB1.WB
