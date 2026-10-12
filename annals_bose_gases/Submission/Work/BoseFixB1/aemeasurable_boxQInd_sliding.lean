import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseFixB1.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.aemeasurable_boxQInd_sliding`

Joint measurability of FS's box mean-free projection `boxQInd volA A i Ψ = 1_A(x_i)·Ψ − P_{B,i}Ψ`
(`Work.UBBInputs8.boxQInd`, FS `eq:HBU`) along the *sliding* family of boxes
`B(u) = dlBox ℓ d u`, as a function of `q = (u, x) ∈ ℝ³ × X N`:

    (u, x) ↦ boxQInd (boxMass ℓ d u) (dlBox ℓ d u) i Φ x

is `AEMeasurable` for `volume.prod volume`, for every *continuous* `Φ`.

This is the measurability input of the `(u,x)`-joint integrability statements of the
FS-faithful kinetic layer (`Work.UBBInputs8.tBwordBInd`, used by
`Work.BoseFixB1.sbKin`), where the sliding centre `u` is *integrated over* `ℝ³`
(`Work.BoseFixB1.Defs`), and it parallels the fixed-`u` companion
`Work.SlotWord.measurable_boxQInd`.

## The argument

Unfolding `boxQInd`/`boxPInd`, the function is

    (u,x) ↦ 1_{x_i ∈ B(u)}·Φ(x)
             − (1/|B(u)|)·(∫_{B(u)} Φ(update x i z) dz)·1_{x_i ∈ B(u)} ,

so it suffices to know that each of the four factors is `AEMeasurable` in `q = (u,x)`.

* the box indicator: the set `{(u,x) | x_i ∈ dlBox ℓ d u}` is the preimage of the
  measurable set `Work.SmallBoxSliding.measurableSet_boxIndSet ℓ d` under the
  measurable map `(u,x) ↦ (u, x_i)`;
* `(u,x) ↦ Φ x` is continuous;
* the box volume `(u,x) ↦ boxMass ℓ d u = ∫_z boxInd ℓ d u z`: the `(u,x,z)`-integrand
  `boxInd ℓ d p.1.1 p.2` is *jointly measurable* (as the indicator of the measurable
  set `{p | p.2 ∈ dlBox ℓ d p.1.1}`, again a preimage of `measurableSet_boxIndSet`),
  so its parametric integral is strongly measurable in `p = (u,x)` by the
  parametric-integral lemma `MeasureTheory.StronglyMeasurable.integral_prod_right'`;
* the slot integral `(u,x) ↦ ∫_{B(u)} Φ(update x i z) dz`: the same parametric-integral
  lemma, applied to the jointly measurable integrand
  `1_{z ∈ B(u)}·Φ(update x i z)`, whose `(u,x,z)`-measurability comes from
  `Measurable.update'` (`measurable_update'`) for the update map and from continuity of `Φ`.

No integrability, finiteness or support hypothesis is needed: the parametric-integral
lemma is a *measurability* statement (Tonelli–Fubini for the marginal), and the trivial
value `1/0 = 0` of `boxMass` on the empty box is measurable as it stands.
-/

noncomputable section

open MeasureTheory

namespace Work.BoseFixB1

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option linter.unusedVariables false

/-- The sliding box volume `u ↦ boxMass ℓ d u`, lifted to a function of `q = (u,x)`.
Joint measurability of the `(u,x,z)`-integrand `boxInd ℓ d u z` followed by the
parametric-integral lemma. -/
lemma aemeasurable_boxMass_sliding {N : ℕ} (ℓ d : ℝ) :
    AEMeasurable (fun q : E3 × Submission.BoseGases.X N =>
      Work.SmallBoxSliding.boxMass ℓ d q.1)
      (MeasureTheory.volume.prod MeasureTheory.volume) := by
  classical
  have hset : MeasurableSet {p : (E3 × Submission.BoseGases.X N) × E3 |
      p.2 ∈ Submission.BoseGases.dlBox ℓ d p.1.1} := by
    have hmap : Measurable (fun p : (E3 × Submission.BoseGases.X N) × E3 => (p.1.1, p.2)) := by
      fun_prop
    exact (Work.SmallBoxSliding.measurableSet_boxIndSet ℓ d).preimage hmap
  have hjj : Measurable (fun p : (E3 × Submission.BoseGases.X N) × E3 =>
      Work.SmallBoxSliding.boxInd ℓ d p.1.1 p.2) := by
    have hfun : (fun p : (E3 × Submission.BoseGases.X N) × E3 =>
        Work.SmallBoxSliding.boxInd ℓ d p.1.1 p.2)
        = {p : (E3 × Submission.BoseGases.X N) × E3 |
            p.2 ∈ Submission.BoseGases.dlBox ℓ d p.1.1}.indicator (fun _ => (1 : ℝ)) := by
      funext p
      rw [Work.SmallBoxSliding.boxInd]
      by_cases h : p.2 ∈ Submission.BoseGases.dlBox ℓ d p.1.1
      · rw [Set.indicator_of_mem h, Set.indicator_of_mem (show p ∈ _ from h)]
      · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (show p ∉ _ from h)]
    rw [hfun]
    exact measurable_const.indicator hset
  have h := MeasureTheory.StronglyMeasurable.integral_prod_right'
    (ν := (MeasureTheory.volume : MeasureTheory.Measure E3)) hjj.stronglyMeasurable
  have hfun2 : (fun q : E3 × Submission.BoseGases.X N => Work.SmallBoxSliding.boxMass ℓ d q.1)
      = fun q => ∫ z : E3, Work.SmallBoxSliding.boxInd ℓ d q.1 z := by
    funext q; rw [Work.SmallBoxSliding.boxMass]
  rw [hfun2]
  exact h.aemeasurable

/-- The sliding slot integral `(u,x) ↦ ∫_{B(u)} Φ(update x i z) dz`, jointly measurable
in `q = (u,x)`. -/
lemma aemeasurable_slotIntegral_sliding {N : ℕ} (ℓ d : ℝ)
    {Φ : Submission.BoseGases.X N → ℝ} (hΦ : Continuous Φ) (i : Fin N) :
    AEMeasurable (fun q : E3 × Submission.BoseGases.X N =>
      ∫ z in Submission.BoseGases.dlBox ℓ d q.1, Φ (Function.update q.2 i z))
      (MeasureTheory.volume.prod MeasureTheory.volume) := by
  classical
  have hset : MeasurableSet {p : (E3 × Submission.BoseGases.X N) × E3 |
      p.2 ∈ Submission.BoseGases.dlBox ℓ d p.1.1} := by
    have hmap : Measurable (fun p : (E3 × Submission.BoseGases.X N) × E3 => (p.1.1, p.2)) := by
      fun_prop
    exact (Work.SmallBoxSliding.measurableSet_boxIndSet ℓ d).preimage hmap
  have hjoint : Measurable (fun p : (E3 × Submission.BoseGases.X N) × E3 =>
      (Submission.BoseGases.dlBox ℓ d p.1.1).indicator
        (fun z => Φ (Function.update p.1.2 i z)) p.2) := by
    have hcomp : Measurable (fun p : (E3 × Submission.BoseGases.X N) × E3 =>
        Φ (Function.update p.1.2 i p.2)) := by
      apply hΦ.measurable.comp
      fun_prop
    have hite : (fun p : (E3 × Submission.BoseGases.X N) × E3 =>
        (Submission.BoseGases.dlBox ℓ d p.1.1).indicator
          (fun z => Φ (Function.update p.1.2 i z)) p.2)
        = fun p => if p.2 ∈ Submission.BoseGases.dlBox ℓ d p.1.1
          then Φ (Function.update p.1.2 i p.2) else 0 := by
      funext p
      by_cases h : p.2 ∈ Submission.BoseGases.dlBox ℓ d p.1.1
      · rw [if_pos h, Set.indicator_of_mem h]
      · rw [if_neg h, Set.indicator_of_notMem h]
    rw [hite]
    exact Measurable.ite hset hcomp measurable_const
  have h := MeasureTheory.StronglyMeasurable.integral_prod_right'
    (ν := (MeasureTheory.volume : MeasureTheory.Measure E3)) hjoint.stronglyMeasurable
  refine h.aemeasurable.congr ?_
  filter_upwards with q
  rw [MeasureTheory.integral_indicator (Work.SmallBoxSliding.measurableSet_dlBox ℓ d q.1)]

theorem aemeasurable_boxQInd_sliding {N : ℕ} {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    {Φ : Submission.BoseGases.X N → ℝ} (hΦ : Continuous Φ) (i : Fin N) :
    AEMeasurable
      (fun q : EuclideanSpace ℝ (Fin 3) × Submission.BoseGases.X N =>
        Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d q.1)
          (Submission.BoseGases.dlBox ℓ d q.1) i Φ q.2)
      (MeasureTheory.volume.prod MeasureTheory.volume) := by
  classical
  -- the box indicator `q ↦ 1_{q.2 i ∈ B(q.1)}`
  have hset1 : MeasurableSet {q : E3 × Submission.BoseGases.X N |
      q.2 i ∈ Submission.BoseGases.dlBox ℓ d q.1} := by
    have hmap : Measurable (fun q : E3 × Submission.BoseGases.X N => (q.1, q.2 i)) := by
      fun_prop
    exact (Work.SmallBoxSliding.measurableSet_boxIndSet ℓ d).preimage hmap
  have hboxind : AEMeasurable
      (fun q : E3 × Submission.BoseGases.X N =>
        (Submission.BoseGases.dlBox ℓ d q.1).indicator (fun _ => (1 : ℝ)) (q.2 i))
      (MeasureTheory.volume.prod MeasureTheory.volume) := by
    have hfun : (fun q : E3 × Submission.BoseGases.X N =>
        (Submission.BoseGases.dlBox ℓ d q.1).indicator (fun _ => (1 : ℝ)) (q.2 i))
        = {q : E3 × Submission.BoseGases.X N |
            q.2 i ∈ Submission.BoseGases.dlBox ℓ d q.1}.indicator (fun _ => (1 : ℝ)) := by
      funext q
      by_cases h : q.2 i ∈ Submission.BoseGases.dlBox ℓ d q.1
      · rw [Set.indicator_of_mem h, Set.indicator_of_mem (show q ∈ _ from h)]
      · rw [Set.indicator_of_notMem h, Set.indicator_of_notMem (show q ∉ _ from h)]
    rw [hfun]
    exact (measurable_const.indicator hset1).aemeasurable
  -- the state
  have hPhi : AEMeasurable (fun q : E3 × Submission.BoseGases.X N => Φ q.2)
      (MeasureTheory.volume.prod MeasureTheory.volume) :=
    (hΦ.measurable.comp measurable_snd).aemeasurable
  -- the box volume and the slot integral
  have hboxmass : AEMeasurable (fun q : E3 × Submission.BoseGases.X N =>
      Work.SmallBoxSliding.boxMass ℓ d q.1) (MeasureTheory.volume.prod MeasureTheory.volume) :=
    aemeasurable_boxMass_sliding (N := N) ℓ d
  have hint : AEMeasurable (fun q : E3 × Submission.BoseGases.X N =>
      ∫ z in Submission.BoseGases.dlBox ℓ d q.1, Φ (Function.update q.2 i z))
      (MeasureTheory.volume.prod MeasureTheory.volume) :=
    aemeasurable_slotIntegral_sliding ℓ d hΦ i
  -- unfold `boxQInd`/`boxPInd` and combine the four factors
  have hmain : (fun q : E3 × Submission.BoseGases.X N =>
        Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d q.1)
          (Submission.BoseGases.dlBox ℓ d q.1) i Φ q.2)
      = fun q => (Submission.BoseGases.dlBox ℓ d q.1).indicator (fun _ => (1 : ℝ)) (q.2 i) * Φ q.2
          - (1 / Work.SmallBoxSliding.boxMass ℓ d q.1)
              * (∫ z in Submission.BoseGases.dlBox ℓ d q.1, Φ (Function.update q.2 i z))
            * (Submission.BoseGases.dlBox ℓ d q.1).indicator (fun _ => (1 : ℝ)) (q.2 i) := by
    funext q
    rfl
  rw [hmain]
  exact ((hboxind.mul hPhi).sub
    (((aemeasurable_const.div hboxmass).mul hint).mul hboxind))

end Work.BoseFixB1
