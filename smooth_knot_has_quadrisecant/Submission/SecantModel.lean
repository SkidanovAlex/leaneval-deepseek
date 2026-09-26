import Mathlib
import Submission.ChordParam
import Submission.SecantSpace

noncomputable section

open Complex
open ComplexConjugate

namespace LeanEval.KnotTheory.Quadrisecant

/-!
# The topological quotient descent: `OpenMobius ≃ MobiusModel`

The analytic core of the chord parametrisation (`Submission/ChordParam.lean`)
gives, for every ordered pair `(u,v)` of *distinct circle points*, the chord
data `chordDataOf u v h : ChordData` (unit normal + offset in `(-1,1)`),
flip-equivariant under the endpoint swap (`chordDataOf_swap`); and, going
back, every chord data `(n,d)` recovers its two endpoints
(`backwardOrdered`, flip-equivariant up to the swap).  This module carries
both maps through the quotients to the open Möbius band:

    forwardRep  : OrderedPairs  → MobiusModel      (continuous, swap-invariant)
    forwardModel: OpenMobius    → MobiusModel      (continuous)
    backward    : MobiusModel   → OpenMobius       (continuous)

`OrderedPairs` are the ordered pairs of distinct *parameters*; they map to
circle points through `paramCircleHomeo : AddCircle period ≃ₜ Circle`
(`Submission/Pi1Mobius.lean`).  The domain quotient is `OpenMobius`
(`Submission/SecantSpace.lean`), whose quotient map
`mobiusCover : OrderedPairs → OpenMobius` is an *open quotient map*
(`isOpenMap_mobiusCover`, `isQuotientMap_mobiusCover`), so a function out of
`OpenMobius` is continuous as soon as its composite with `mobiusCover` is
(`IsOpenQuotientMap.continuous_comp_iff`).  `forwardModel` is defined by
choosing an ordered representative of the class (the fibres of `mobiusCover`
are exactly `{p, swapOrdered p}`, and `forwardRep` is swap-invariant, so the
choice is immaterial — `forwardModel_mobiusCover`).

The backward map goes from `MobiusModel = ChordData/flip` to the unordered
circle-pair classes (`CircleUnordPairs`), landing in the off-diagonal part
`CircleOpenPairs` (the endpoints of a chord are distinct), and then back to
`OpenMobius` through the circle-pair homeomorphism
`openMobiusCircleEquiv` (`Submission/CirclePairs.lean`).  It is continuous
because the endpoint formulas are continuous on the open strip `d ∈ (-1,1)`
(`Continuous.quotient_lift` over the flip relation, using
`backwardOrdered_flip_rel`).

The two maps are mutually inverse: recovery identity (A) at class level
(`backwardCircle_chordDataOf`, `backwardModel_forwardModel_mobiusCover`,
`backward_leftInverse_forwardModel` — backward of the chord data of a pair
recovers the pair's class) and recovery identity (B) at class level
(`chordDataOf_param_self` — `φ (φ⁻¹ u) = u` cancels inside chord data,
`forwardChordData_param_symm`, `forwardModel_backwardModel_mobiusMk`,
`forward_rightInverse_backwardModel`).  Hence

    openMobiusModelEquiv : OpenMobius ≃ MobiusModel     (the bijection)
    openMobiusModelHomeo : OpenMobius ≃ₜ MobiusModel    (the homeomorphism)

The next layer: the core correspondence (`d = 0` ↔ antipodal pairs),
transporting the deformation retraction `mobius_core_retract` of
`MobiusModel` back to `OpenMobiusCoreRetract`, and then the π₁ assembly.
-/

/-- Distinct parameters map to distinct circle points under the parameter
circle homeomorphism. -/
lemma paramCircleHomeo_injective_ne {x y : AddCircle period} (h : x ≠ y) :
    paramCircleHomeo x ≠ paramCircleHomeo y :=
  paramCircleHomeo.injective.ne h

/-- Chord data of an ordered pair of distinct parameters: compute the circle
points through `paramCircleHomeo` and take their chord data. -/
noncomputable def forwardChordData (p : OrderedPairs) : ChordData :=
  chordDataOf (paramCircleHomeo p.1.1) (paramCircleHomeo p.1.2)
    (paramCircleHomeo_injective_ne p.2)

/-- `w ↦ w/‖w‖` is continuous off zero (in `ℂ`). -/
lemma continuousOn_div_norm_complex : ContinuousOn (fun w : ℂ => w / ‖w‖) {w : ℂ | w ≠ 0} := by
  intro w hw
  have hnorm : ContinuousAt (fun z : ℂ => (‖z‖ : ℂ)) w := by
    exact continuous_ofReal.continuousAt.comp continuous_norm.continuousAt
  have hval : (‖w‖ : ℂ) ≠ 0 := by
    exact_mod_cast (norm_ne_zero_iff.mpr hw)
  exact (continuous_id.continuousAt.div hnorm hval).continuousWithinAt

/-- The raw chord normal `rawCircleNormal (φ x) (φ y)` depends continuously
on the ordered pair of distinct parameters. -/
lemma continuous_rawNormal_ordered :
    Continuous (fun p : OrderedPairs => (rawCircleNormal (paramCircleHomeo p.1.1 : ℂ)
      (paramCircleHomeo p.1.2 : ℂ) : ℂ)) := by
  have hdiff : Continuous (fun p : OrderedPairs => (paramCircleHomeo p.1.2 : ℂ) -
      (paramCircleHomeo p.1.1 : ℂ)) := by
    have h1 : Continuous (fun p : OrderedPairs => (paramCircleHomeo p.1.1 : ℂ)) := by
      exact continuous_subtype_val.comp (paramCircleHomeo.continuous.comp
        (continuous_fst.comp continuous_subtype_val))
    have h2 : Continuous (fun p : OrderedPairs => (paramCircleHomeo p.1.2 : ℂ)) := by
      exact continuous_subtype_val.comp (paramCircleHomeo.continuous.comp
        (continuous_snd.comp continuous_subtype_val))
    exact h2.sub h1
  have hne : ∀ p : OrderedPairs, (paramCircleHomeo p.1.2 : ℂ) - (paramCircleHomeo p.1.1 : ℂ) ≠ 0 := by
    intro p hz
    have hz' : (paramCircleHomeo p.1.2 : ℂ) = (paramCircleHomeo p.1.1 : ℂ) := sub_eq_zero.mp hz
    have hc' : paramCircleHomeo p.1.2 = paramCircleHomeo p.1.1 := Circle.coe_injective hz'
    exact (paramCircleHomeo_injective_ne (fun h => p.2 h.symm)) hc'
  have hdiv : Continuous (fun p : OrderedPairs =>
      ((paramCircleHomeo p.1.2 : ℂ) - (paramCircleHomeo p.1.1 : ℂ)) /
        ‖(paramCircleHomeo p.1.2 : ℂ) - (paramCircleHomeo p.1.1 : ℂ)‖) :=
    ContinuousOn.comp_continuous continuousOn_div_norm_complex hdiff hne
  have hI : Continuous (fun _ : OrderedPairs => (I : ℂ)) := continuous_const
  have hmul : Continuous (fun p : OrderedPairs => I *
      (((paramCircleHomeo p.1.2 : ℂ) - (paramCircleHomeo p.1.1 : ℂ)) /
        ‖(paramCircleHomeo p.1.2 : ℂ) - (paramCircleHomeo p.1.1 : ℂ)‖)) := hI.mul hdiv
  change Continuous (fun p : OrderedPairs =>
    rawCircleNormal (paramCircleHomeo p.1.1 : ℂ) (paramCircleHomeo p.1.2 : ℂ))
  simpa [rawCircleNormal, div_eq_mul_inv, mul_assoc] using hmul

/-- The chord normal (as a circle element) depends continuously on the
ordered pair of distinct parameters. -/
lemma continuous_circleNormal_ordered :
    Continuous (fun p : OrderedPairs => (circleNormal (paramCircleHomeo p.1.1 : ℂ)
      (paramCircleHomeo p.1.2 : ℂ) (ne_symm_of_ne (paramCircleHomeo_injective_ne p.2)) : Circle)) := by
  apply Continuous.subtype_mk
  · exact continuous_rawNormal_ordered

/-- The chord offset depends continuously on the ordered pair of distinct
parameters. -/
lemma continuous_circleChordOffset_ordered :
    Continuous (fun p : OrderedPairs => circleChordOffset (paramCircleHomeo p.1.1)
      (paramCircleHomeo p.1.2) (paramCircleHomeo_injective_ne p.2)) := by
  unfold circleChordOffset chordOffset
  refine Continuous.inner ?_ ?_
  · exact continuous_subtype_val.comp (paramCircleHomeo.continuous.comp
      (continuous_fst.comp continuous_subtype_val))
  · exact continuous_subtype_val.comp continuous_circleNormal_ordered

/-- The representative chord-data map `forwardChordData` is continuous. -/
lemma continuous_forwardChordData : Continuous forwardChordData := by
  unfold forwardChordData
  refine Continuous.subtype_mk (f := fun p : OrderedPairs =>
      (circleNormal (paramCircleHomeo p.1.1 : ℂ) (paramCircleHomeo p.1.2 : ℂ)
          (ne_symm_of_ne (paramCircleHomeo_injective_ne p.2)),
        circleChordOffset (paramCircleHomeo p.1.1) (paramCircleHomeo p.1.2)
          (paramCircleHomeo_injective_ne p.2))) ?_ ?_
  · exact continuous_circleNormal_ordered.prodMk continuous_circleChordOffset_ordered

/-- The representative forward map into the model Möbius band
(`MobiusModel = ChordData/flip`). -/
noncomputable def forwardRep (p : OrderedPairs) : MobiusModel :=
  mobiusMk (forwardChordData p)

/-- `forwardRep` is continuous. -/
lemma continuous_forwardRep : Continuous forwardRep := by
  exact continuous_mobiusMk.comp continuous_forwardChordData

/-- Swapping the ordered parameters flips the chord data (the two
descriptions of the same chord). -/
lemma forwardChordData_swap (p : OrderedPairs) :
    forwardChordData (swapOrdered p) = chordFlip (forwardChordData p) := by
  unfold forwardChordData
  have hp0 : paramCircleHomeo p.1.1 ≠ paramCircleHomeo p.1.2 := paramCircleHomeo_injective_ne p.2
  have hswap := chordDataOf_swap (u := paramCircleHomeo p.1.1) (v := paramCircleHomeo p.1.2) hp0
  dsimp [swapOrdered]
  trans chordDataOf (paramCircleHomeo p.1.2) (paramCircleHomeo p.1.1) (Ne.symm hp0)
  · apply Subtype.ext
    ext <;> simp
  · exact hswap

/-- The representative forward map is invariant under swapping the two
parameters (the two orders give the same chord class). -/
lemma forwardRep_swap (p : OrderedPairs) : forwardRep (swapOrdered p) = forwardRep p := by
  unfold forwardRep
  rw [forwardChordData_swap]
  exact mobiusMk_flip (forwardChordData p)

/-- **Forward descent**: the chord data of an open (unordered) secant, i.e.
the induced map `OpenMobius → MobiusModel` (an ordered representative is
chosen; the fibres of `mobiusCover` are the swap orbits, on which
`forwardRep` is constant). -/
noncomputable def forwardModel (c : OpenMobius) : MobiusModel :=
  forwardRep (Classical.choose (mobiusCover_surjective c))

/-- Over a represented class the descended map agrees with the
representative map. -/
lemma forwardModel_mobiusCover (p : OrderedPairs) :
    forwardModel (mobiusCover p) = forwardRep p := by
  unfold forwardModel
  have hq : mobiusCover (Classical.choose (mobiusCover_surjective (mobiusCover p))) = mobiusCover p :=
    Classical.choose_spec (mobiusCover_surjective (mobiusCover p))
  have hmem0 : Classical.choose (mobiusCover_surjective (mobiusCover p)) ∈
      {q : OrderedPairs | mobiusCover q = mobiusCover p} := hq
  have hmem : Classical.choose (mobiusCover_surjective (mobiusCover p)) ∈
      ({p, swapOrdered p} : Set OrderedPairs) := by
    rw [← mobiusCover_fiber p]
    exact hmem0
  rcases hmem with h | h
  · rw [h]
  · rw [h]
    exact forwardRep_swap p

/-- **The forward induced map `OpenMobius → MobiusModel` is continuous**:
`mobiusCover` is an open quotient map, so it suffices to check continuity of
the composite with `mobiusCover`, which is the continuous `forwardRep`. -/
lemma continuous_forwardModel : Continuous forwardModel := by
  have hQ : IsOpenQuotientMap mobiusCover := IsOpenQuotientMap.of_isOpenMap_isQuotientMap
    isOpenMap_mobiusCover isQuotientMap_mobiusCover
  have heq : (fun p : OrderedPairs => forwardModel (mobiusCover p)) = forwardRep := by
    funext p
    exact forwardModel_mobiusCover p
  have hrep : Continuous (fun p : OrderedPairs => forwardModel (mobiusCover p)) := by
    rw [heq]
    exact continuous_forwardRep
  exact (IsOpenQuotientMap.continuous_comp_iff hQ (g := forwardModel)).mp hrep


/-! ## Backward: chord data → open secant -/

/-- The `+` chord endpoint depends continuously on the chord data. -/
lemma continuous_chordEndpointPlus_data :
    Continuous (fun q : ChordData => chordEndpointPlus q.1.1 q.1.2 q.2) := by
  apply Continuous.subtype_mk
  · have hn : Continuous (fun q : ChordData => (q.1.1 : ℂ)) := by
      exact continuous_subtype_val.comp (continuous_fst.comp continuous_subtype_val)
    have hd : Continuous (fun q : ChordData => (q.1.2 : ℝ)) := by
      exact continuous_snd.comp continuous_subtype_val
    have hc1 : Continuous (fun q : ChordData => (q.1.2 : ℂ)) := continuous_ofReal.comp hd
    have hsq : Continuous (fun q : ChordData => Real.sqrt (1 - q.1.2 ^ 2)) :=
      Real.continuous_sqrt.comp (continuous_const.sub (hd.pow 2))
    have hc2 : Continuous (fun q : ChordData => (Real.sqrt (1 - q.1.2 ^ 2) : ℂ)) :=
      continuous_ofReal.comp hsq
    have hI : Continuous (fun _ : ChordData => (I : ℂ)) := continuous_const
    have hsum : Continuous (fun q : ChordData => (q.1.2 : ℂ) + I * (Real.sqrt (1 - q.1.2 ^ 2) : ℂ)) :=
      hc1.add (hI.mul hc2)
    have hmul : Continuous (fun q : ChordData =>
        (q.1.1 : ℂ) * ((q.1.2 : ℂ) + I * (Real.sqrt (1 - q.1.2 ^ 2) : ℂ))) :=
      hn.mul hsum
    change Continuous (fun q : ChordData => (chordEndpointPlus q.1.1 q.1.2 q.2 : ℂ))
    simpa [chordEndpointPlus, unitCircleOf, chordHalfSpread] using hmul

/-- The `-` chord endpoint depends continuously on the chord data. -/
lemma continuous_chordEndpointMinus_data :
    Continuous (fun q : ChordData => chordEndpointMinus q.1.1 q.1.2 q.2) := by
  apply Continuous.subtype_mk
  · have hn : Continuous (fun q : ChordData => (q.1.1 : ℂ)) := by
      exact continuous_subtype_val.comp (continuous_fst.comp continuous_subtype_val)
    have hd : Continuous (fun q : ChordData => (q.1.2 : ℝ)) := by
      exact continuous_snd.comp continuous_subtype_val
    have hc1 : Continuous (fun q : ChordData => (q.1.2 : ℂ)) := continuous_ofReal.comp hd
    have hsq : Continuous (fun q : ChordData => Real.sqrt (1 - q.1.2 ^ 2)) :=
      Real.continuous_sqrt.comp (continuous_const.sub (hd.pow 2))
    have hc2 : Continuous (fun q : ChordData => (Real.sqrt (1 - q.1.2 ^ 2) : ℂ)) :=
      continuous_ofReal.comp hsq
    have hI : Continuous (fun _ : ChordData => (I : ℂ)) := continuous_const
    have hsum : Continuous (fun q : ChordData => (q.1.2 : ℂ) - I * (Real.sqrt (1 - q.1.2 ^ 2) : ℂ)) :=
      hc1.sub (hI.mul hc2)
    have hmul : Continuous (fun q : ChordData =>
        (q.1.1 : ℂ) * ((q.1.2 : ℂ) - I * (Real.sqrt (1 - q.1.2 ^ 2) : ℂ))) :=
      hn.mul hsum
    change Continuous (fun q : ChordData => (chordEndpointMinus q.1.1 q.1.2 q.2 : ℂ))
    simpa [chordEndpointMinus, unitCircleOf, chordHalfSpread] using hmul

/-- The unordered circle-pair class of the backward endpoints, as a function
of chord data. -/
noncomputable def backwardChordClass (q : ChordData) : CircleUnordPairs :=
  ⟦(backwardOrdered q).1⟧

/-- `backwardChordClass` is continuous. -/
lemma continuous_backwardChordClass : Continuous backwardChordClass := by
  unfold backwardChordClass
  exact continuous_quot_mk.comp
    (continuous_chordEndpointPlus_data.prodMk continuous_chordEndpointMinus_data)

/-- The backward endpoints depend only on the chord, not on its two ordered
descriptions (`chordRel`-invariance at class level). -/
lemma backwardChordClass_resp (a b : ChordData) (hab : a ≈ b) :
    backwardChordClass a = backwardChordClass b := by
  rcases hab with hab | hab
  · rw [hab]
  · unfold backwardChordClass
    rw [← hab]
    apply Quotient.sound
    exact circleSwapRel_symm (backwardOrdered_flip_rel a)

/-- An unordered pair of *distinct* circle points is not a diagonal class. -/
lemma circleClass_not_diag_of_ne {u v : Circle} (h : u ≠ v) :
    ¬ ∃ a : Circle, (⟦(u, v)⟧ : CircleUnordPairs) = circleDiagClass a := by
  rintro ⟨a, ha⟩
  have hs := (circleUnordMk_eq_iff (u, v) (a, a)).mp ha
  rcases hs with hs | hs
  · have hu : u = a := congrArg Prod.fst hs
    have hv : v = a := congrArg Prod.snd hs
    exact h (hu.trans hv.symm)
  · have hs' : (v, u) = (a, a) := by simpa [circleSwap] using hs
    have hv : v = a := congrArg Prod.fst hs'
    have hu : u = a := congrArg Prod.snd hs'
    exact h (hu.trans hv.symm)

/-- **Backward lift**: from a chord class to the unordered circle-pair class
of its endpoints. -/
noncomputable def backwardLift : MobiusModel → CircleUnordPairs :=
  Quotient.lift backwardChordClass backwardChordClass_resp

/-- The backward lift is continuous. -/
lemma continuous_backwardLift : Continuous backwardLift := by
  unfold backwardLift
  exact Continuous.quotient_lift continuous_backwardChordClass backwardChordClass_resp

/-- The backward lift of any chord lands in the *open* part (the endpoints
of a nondegenerate chord are distinct). -/
lemma backwardLift_not_diag (c : MobiusModel) :
    ¬ ∃ a : Circle, backwardLift c = circleDiagClass a := by
  refine Quotient.inductionOn c ?_
  intro q
  have h : backwardLift (⟦q⟧ : MobiusModel) = ⟦(backwardOrdered q).1⟧ := by
    rfl
  rw [h]
  exact circleClass_not_diag_of_ne (backwardOrdered q).2

/-- **Backward** into the open circle-pair model. -/
noncomputable def backwardCircle (c : MobiusModel) : CircleOpenPairs :=
  ⟨backwardLift c, backwardLift_not_diag c⟩

/-- `backwardCircle` is continuous. -/
lemma continuous_backwardCircle : Continuous backwardCircle := by
  exact Continuous.subtype_mk continuous_backwardLift backwardLift_not_diag

/-- **Backward descent**: chord data → open secant (through the circle-pair
homeomorphism `openMobiusCircleEquiv`). -/
noncomputable def backwardModel (c : MobiusModel) : OpenMobius :=
  openMobiusCircleEquiv.symm (backwardCircle c)

/-- **The backward induced map `MobiusModel → OpenMobius` is continuous.**
-/
lemma continuous_backwardModel : Continuous backwardModel := by
  exact openMobiusCircleEquiv.symm.continuous.comp continuous_backwardCircle

/-! ## Class-level assembly: identity (A) -/

/-- The circle image of the represented open secant `mobiusCover p` is the
circle class of the two images `(φx, φy)`. -/
lemma openMobiusCircleEquiv_mobiusCover (p : OrderedPairs) :
    openMobiusCircleEquiv (mobiusCover p) =
      ⟨⟦(paramCircleHomeo p.1.1, paramCircleHomeo p.1.2)⟧,
        circleClass_not_diag_of_ne (paramCircleHomeo.injective.ne p.2)⟩ := by
  apply Subtype.ext
  change unordParamCircleEquiv (mobiusCover p).1 =
    ⟦(paramCircleHomeo p.1.1, paramCircleHomeo p.1.2)⟧
  dsimp [mobiusCover, unordOfOrdered]
  change unordParamCircleEquiv (⟦(p.1.1, p.1.2)⟧ : UnordCirclePairs) =
    ⟦(paramCircleHomeo p.1.1, paramCircleHomeo p.1.2)⟧
  rfl

/-- Distinct circle points give distinct parameters under the inverse of the
parameter homeomorphism. -/
lemma paramCircleHomeo_symm_injective_ne (u v : Circle) (huv : u ≠ v) :
    paramCircleHomeo.symm u ≠ paramCircleHomeo.symm v :=
  paramCircleHomeo.symm.injective.ne huv

/-- The preimage of the circle class of `(u,v)` under the circle homeo is the
open secant `mobiusCover (φ⁻¹u, φ⁻¹v)`. -/
lemma openMobiusCircleEquiv_symm_mk (u v : Circle) (huv : u ≠ v) :
    openMobiusCircleEquiv.symm ⟨⟦(u, v)⟧, circleClass_not_diag_of_ne huv⟩ =
      mobiusCover ⟨(paramCircleHomeo.symm u, paramCircleHomeo.symm v),
        paramCircleHomeo_symm_injective_ne u v huv⟩ := by
  apply Subtype.ext
  change unordParamCircleEquiv.symm (⟦(u, v)⟧ : CircleUnordPairs) =
    (mobiusCover ⟨(paramCircleHomeo.symm u, paramCircleHomeo.symm v),
      paramCircleHomeo_symm_injective_ne u v huv⟩).1
  dsimp [mobiusCover, unordOfOrdered]
  rfl

/-- Equal unordered pairs give equal circle classes. -/
lemma circleUnordMk_eq_of_swapRel {x y : Circle × Circle}
    (h : circleSwapRel x y) : (⟦x⟧ : CircleUnordPairs) = ⟦y⟧ :=
  (circleUnordMk_eq_iff x y).mpr h

/-- Backward of the chord data of a pair recovers the pair's class
(recovery identity (A) at class level). -/
lemma backwardCircle_chordDataOf (u v : Circle) (h : u ≠ v) :
    backwardCircle (⟦chordDataOf u v h⟧) =
      ⟨⟦(u, v)⟧, circleClass_not_diag_of_ne h⟩ := by
  apply Subtype.ext
  change backwardLift (⟦chordDataOf u v h⟧) = ⟦(u, v)⟧
  have h1 : backwardLift (⟦chordDataOf u v h⟧) = ⟦(backwardOrdered (chordDataOf u v h)).1⟧ := by
    rfl
  rw [h1]
  exact circleUnordMk_eq_of_swapRel (backwardOrdered_of_chordDataOf_rel u v h)

/-- `backward ∘ forward` is the identity on represented open secants (the
open-quotient version of identity (A)). -/
lemma backwardModel_forwardModel_mobiusCover (p : OrderedPairs) :
    backwardModel (forwardModel (mobiusCover p)) = mobiusCover p := by
  have hfm : forwardModel (mobiusCover p) = forwardRep p := forwardModel_mobiusCover p
  unfold backwardModel
  rw [hfm]
  unfold forwardRep
  have hbc : backwardCircle (⟦forwardChordData p⟧) =
      ⟨⟦(paramCircleHomeo p.1.1, paramCircleHomeo p.1.2)⟧,
        circleClass_not_diag_of_ne (paramCircleHomeo.injective.ne p.2)⟩ := by
    simpa [forwardChordData] using
      (backwardCircle_chordDataOf (paramCircleHomeo p.1.1) (paramCircleHomeo p.1.2)
        (paramCircleHomeo.injective.ne p.2))
  rw [hbc]
  have hs := openMobiusCircleEquiv_symm_mk (paramCircleHomeo p.1.1) (paramCircleHomeo p.1.2)
    (paramCircleHomeo.injective.ne p.2)
  rw [hs]
  apply congrArg mobiusCover
  ext <;> simp [paramCircleHomeo.symm_apply_apply]

/-- **`backwardModel ∘ forwardModel = id` on the open Möbius band** (the
`OpenMobius`-level form of recovery identity (A)). -/
lemma backward_leftInverse_forwardModel (c : OpenMobius) :
    backwardModel (forwardModel c) = c := by
  rcases mobiusCover_surjective c with ⟨p, hp⟩
  rw [← hp]
  exact backwardModel_forwardModel_mobiusCover p

/-! ## Class-level assembly: identity (B) and the homeomorphism -/

/-- `φ (φ⁻¹ u) = u` cancels inside chord data (value-level equality). -/
lemma chordDataOf_param_self (u v : Circle) (h : u ≠ v) :
    chordDataOf (paramCircleHomeo (paramCircleHomeo.symm u))
        (paramCircleHomeo (paramCircleHomeo.symm v))
        (paramCircleHomeo.injective.ne (paramCircleHomeo_symm_injective_ne u v h)) =
      chordDataOf u v h := by
  apply Subtype.ext
  ext
  · simp [paramCircleHomeo.apply_symm_apply]
  · simp [paramCircleHomeo.apply_symm_apply]

/-- Forward chord data of the inverse circle pair is the chord data of the
pair itself. -/
lemma forwardChordData_param_symm (u v : Circle) (h : u ≠ v) :
    forwardChordData ⟨(paramCircleHomeo.symm u, paramCircleHomeo.symm v),
        paramCircleHomeo_symm_injective_ne u v h⟩ = chordDataOf u v h := by
  unfold forwardChordData
  exact chordDataOf_param_self u v h

/-- `forward ∘ backward` is the identity on represented chord classes (the
open-quotient version of identity (B)). -/
lemma forwardModel_backwardModel_mobiusMk (q : ChordData) :
    forwardModel (backwardModel (⟦q⟧ : MobiusModel)) = (⟦q⟧ : MobiusModel) := by
  unfold backwardModel
  have hb : backwardCircle (⟦q⟧ : MobiusModel) =
      ⟨⟦(backwardOrdered q).1⟧, backwardLift_not_diag (⟦q⟧ : MobiusModel)⟩ := by
    rfl
  rw [hb]
  have hnd : backwardLift_not_diag (⟦q⟧ : MobiusModel) =
      circleClass_not_diag_of_ne (backwardOrdered q).2 := by
    exact Subsingleton.elim _ _
  rw [hnd]
  have hs := openMobiusCircleEquiv_symm_mk (backwardOrdered q).1.1 (backwardOrdered q).1.2
    (backwardOrdered q).2
  rw [hs]
  have hfm := forwardModel_mobiusCover
    ⟨(paramCircleHomeo.symm (backwardOrdered q).1.1, paramCircleHomeo.symm (backwardOrdered q).1.2),
      paramCircleHomeo_symm_injective_ne (backwardOrdered q).1.1 (backwardOrdered q).1.2
        (backwardOrdered q).2⟩
  rw [hfm]
  unfold forwardRep
  have hcd : forwardChordData
      ⟨(paramCircleHomeo.symm (backwardOrdered q).1.1, paramCircleHomeo.symm (backwardOrdered q).1.2),
        paramCircleHomeo_symm_injective_ne (backwardOrdered q).1.1 (backwardOrdered q).1.2
          (backwardOrdered q).2⟩ =
      q := by
    rw [forwardChordData_param_symm (backwardOrdered q).1.1 (backwardOrdered q).1.2
      (backwardOrdered q).2]
    exact chordDataOf_backwardOrdered q
  rw [hcd]

/-- **`forwardModel ∘ backwardModel = id` on the model Möbius band** (the
`MobiusModel`-level form of recovery identity (B)). -/
lemma forward_rightInverse_backwardModel (m : MobiusModel) :
    forwardModel (backwardModel m) = m := by
  refine Quotient.inductionOn m ?_
  intro q
  exact forwardModel_backwardModel_mobiusMk q

/-- The equivalence between the open Möbius band of the knot secants and the
chord model (chord data up to the flip). -/
noncomputable def openMobiusModelEquiv : OpenMobius ≃ MobiusModel where
  toFun := forwardModel
  invFun := backwardModel
  left_inv := backward_leftInverse_forwardModel
  right_inv := forward_rightInverse_backwardModel

/-- **The open Möbius band is homeomorphic to the chord model**:
`OpenMobius ≃ₜ MobiusModel` (both continuous maps built above). -/
noncomputable def openMobiusModelHomeo : OpenMobius ≃ₜ MobiusModel where
  toFun := forwardModel
  invFun := backwardModel
  left_inv := backward_leftInverse_forwardModel
  right_inv := forward_rightInverse_backwardModel
  continuous_toFun := continuous_forwardModel
  continuous_invFun := continuous_backwardModel

/-! ## Core correspondence and the deformation retraction of `OpenMobius`

The homeomorphism `openMobiusModelHomeo` maps the core circle of the open
Möbius band (antipodal pairs, `range coreFactor`) onto the core circle of
the chord model (diameters, `range mobiusCore`): a parameter pair shifted by
the half period corresponds, under `paramCircleHomeo : AddCircle period ≃ₜ
Circle`, to a pair of antipodal unit points (lemma
`paramCircleHomeo_add_halfPeriod`), whose chord passes through the origin
(`circleChordOffset_neg_zero`), i.e. is a diameter
(`chordDataOf_neg_eq_coreChord`, `forwardModel_core_mem_mobiusCore`);
conversely a diameter `(n,0)` has antipodal endpoints whose inverse images
are half a period apart (`paramCircleHomeo_symm_neg`,
`backwardModel_mobiusCore_mem_core`).

Transporting `mobius_core_retract` (the slide `(n,d) ↦ (n,(1-t)d)` of
`MobiusModel`, `Submission/MobiusModel.lean`) through the homeomorphism
gives **`openMobiusCoreRetract`** — the deformation retraction of the open
Möbius band onto its core circle (the target statement formulated in
`Submission/Pi1Mobius.lean`).
-/

/-! ### The parameter homeomorphism and the half period -/

/-- `Circle.exp π = -1`. -/
lemma Circle_exp_pi_neg_one : Circle.exp Real.pi = (-1 : Circle) := by
  apply Circle.ext
  rw [Circle.coe_exp, Complex.exp_pi_mul_I]
  rfl

/-- The half-period class maps to `-1` under the circle exponential. -/
lemma toCircle_halfPeriod : AddCircle.toCircle (T := period) (halfPeriod : AddCircle period) = (-1 : Circle) := by
  have h := AddCircle.toCircle_apply_mk (T := period) halfPeriod
  rw [h]
  have hsc : 2 * Real.pi / period * halfPeriod = Real.pi := by
    unfold halfPeriod
    field_simp [period_ne_zero, Real.pi_ne_zero]
  rw [hsc]
  exact Circle_exp_pi_neg_one

/-- The parameter circle homeomorphism is the exponential `AddCircle.toCircle`. -/
lemma paramCircleHomeo_eq_toCircle (x : AddCircle period) :
    paramCircleHomeo x = AddCircle.toCircle x := by
  change AddCircle.homeomorphCircle (T := period) period_ne_zero x = AddCircle.toCircle x
  exact AddCircle.homeomorphCircle_apply period_ne_zero x

/-- Shifting a parameter by the half period negates its circle image
(`paramCircleHomeo (t + halfPeriod) = - paramCircleHomeo t`). -/
lemma paramCircleHomeo_add_halfPeriod (t : AddCircle period) :
    paramCircleHomeo (t + halfPeriod) = - paramCircleHomeo t := by
  rw [paramCircleHomeo_eq_toCircle, paramCircleHomeo_eq_toCircle]
  rw [AddCircle.toCircle_add]
  rw [toCircle_halfPeriod]
  simp

/-- The inverse: negating a circle point shifts the parameter by the half
period. -/
lemma paramCircleHomeo_symm_neg (u : Circle) :
    paramCircleHomeo.symm (-u) = paramCircleHomeo.symm u + halfPeriod := by
  apply paramCircleHomeo.injective
  rw [paramCircleHomeo_add_halfPeriod]
  simp [paramCircleHomeo.apply_symm_apply]

/-! ### Antipodal pairs give diameters -/

/-- The raw chord normal of an antipodal pair is `-I·u`. -/
lemma rawCircleNormal_neg (u : Circle) :
    rawCircleNormal (u : ℂ) (-(u : ℂ)) = -I * (u : ℂ) := by
  unfold rawCircleNormal
  have hnorm : ‖-(u : ℂ) - (u : ℂ)‖ = 2 := by
    rw [show -(u : ℂ) - (u : ℂ) = -(2 : ℂ) * (u : ℂ) by ring]
    rw [norm_mul]
    simp
    all_goals exact Circle.norm_coe u
  rw [hnorm]
  rw [show -(u : ℂ) - (u : ℂ) = -(2 : ℂ) * (u : ℂ) by ring]
  have h2 : (2 : ℂ) ≠ 0 := by norm_num
  have hu0 : (u : ℂ) ≠ 0 := by
    intro hz
    have := Circle.norm_coe u
    rw [hz] at this
    norm_num at this
  field_simp [h2, hu0]
  norm_num

/-- The chord through an antipodal pair of unit points passes through the
origin (offset `0`). -/
lemma circleChordOffset_neg_zero (u : Circle) (h : u ≠ -u) :
    circleChordOffset u (-u) h = 0 := by
  unfold circleChordOffset chordOffset
  rw [inner_complex]
  have hn' : ((circleNormal (u : ℂ) ((↑(-u : Circle)) : ℂ) (ne_symm_of_ne h) : Circle) : ℂ) =
      -I * (u : ℂ) := by
    change rawCircleNormal (u : ℂ) ((↑(-u : Circle)) : ℂ) = -I * (u : ℂ)
    simpa using rawCircleNormal_neg u
  rw [hn']
  have huc : (u : ℂ) * conj (u : ℂ) = (1 : ℂ) := by
    rw [mul_comm]
    rw [← Complex.normSq_eq_conj_mul_self]
    norm_num [Complex.normSq_eq_norm_sq, Circle.norm_coe]
  rw [mul_assoc, huc]
  simp

/-- A circle point and its antipode are distinct. -/
lemma neg_ne_of_neg_ne_self (u : Circle) : u ≠ -u := by
  intro h
  exact Circle.neg_ne_self u h.symm

/-- The circle image of a parameter and its antipode are distinct. -/
lemma paramCircleHomeo_neg (t : AddCircle period) :
    paramCircleHomeo t ≠ -paramCircleHomeo t :=
  neg_ne_of_neg_ne_self (paramCircleHomeo t)

/-- Chord data of an antipodal pair is a diameter (chord data with offset
`0`). -/
lemma chordDataOf_neg_eq_coreChord (u : Circle) (h : u ≠ -u) :
    chordDataOf u (-u) h = coreChord (circleNormal (u : ℂ) ((↑(-u : Circle)) : ℂ) (ne_symm_of_ne h)) := by
  apply Subtype.ext
  ext
  · rfl
  · exact circleChordOffset_neg_zero u h

/-- Chord data is value-congruent in the second endpoint (endpoint replaced
by an equal point; the distinctness proofs are irrelevant). -/
lemma chordDataOf_congr_right {u v w : Circle} (h : u ≠ v) (h2 : u ≠ w) (hw : v = w) :
    chordDataOf u v h = chordDataOf u w h2 := by
  apply Subtype.ext
  change (circleNormal (u : ℂ) (v : ℂ) (ne_symm_of_ne h),
      circleChordOffset u v h) =
    (circleNormal (u : ℂ) (w : ℂ) (ne_symm_of_ne h2),
      circleChordOffset u w h2)
  refine Prod.ext ?_ ?_
  · apply Circle.ext
    change rawCircleNormal (u : ℂ) (v : ℂ) = rawCircleNormal (u : ℂ) (w : ℂ)
    rw [congrArg (fun x : Circle => (x : ℂ)) hw]
  · unfold circleChordOffset chordOffset
    have hnorm : circleNormal (u : ℂ) (v : ℂ) (ne_symm_of_ne h) =
        circleNormal (u : ℂ) (w : ℂ) (ne_symm_of_ne h2) := by
      apply Circle.ext
      change rawCircleNormal (u : ℂ) (v : ℂ) = rawCircleNormal (u : ℂ) (w : ℂ)
      rw [congrArg (fun x : Circle => (x : ℂ)) hw]
    rw [hnorm]

/-- The forward image of a core point of the open Möbius band is a core
(diameter) of the chord model. -/
lemma forwardModel_core_mem_mobiusCore (t : AddCircle period) :
    forwardModel (core t) ∈ Set.range mobiusCore := by
  have hval : forwardModel (core t) =
      mobiusCore (circleNormal (paramCircleHomeo t : ℂ) ((↑(-(paramCircleHomeo t : Circle)) : ℂ))
        (ne_symm_of_ne (paramCircleHomeo_neg t))) := by
    unfold core
    rw [forwardModel_mobiusCover]
    unfold forwardRep
    have hφ := paramCircleHomeo_add_halfPeriod t
    have hcd : forwardChordData (corePair t) =
        chordDataOf (paramCircleHomeo t) (-(paramCircleHomeo t))
          (paramCircleHomeo_neg t) := by
      unfold forwardChordData
      exact chordDataOf_congr_right (u := paramCircleHomeo t)
        (v := paramCircleHomeo (t + halfPeriod))
        (w := -(paramCircleHomeo t))
        (paramCircleHomeo_injective_ne (corePair t).2) (paramCircleHomeo_neg t) hφ
    rw [hcd]
    have hcore := chordDataOf_neg_eq_coreChord (paramCircleHomeo t) (paramCircleHomeo_neg t)
    rw [hcore]
  exact ⟨circleNormal (paramCircleHomeo t : ℂ) ((↑(-(paramCircleHomeo t : Circle)) : ℂ))
    (ne_symm_of_ne (paramCircleHomeo_neg t)), hval.symm⟩

/-! ### Diameters give antipodal pairs; the retraction transport -/

/-- The two endpoints of the diameter `(n,0)` are antipodal (`n·I` and
`-n·I`). -/
lemma chordEndpointMinus_neg_endpoint (n : Circle) (hd : (0 : ℝ) ∈ Set.Ioo (-1) 1) :
    chordEndpointMinus n 0 hd = - chordEndpointPlus n 0 hd := by
  apply Circle.ext
  rw [Circle.coe_neg]
  simp [chordEndpointMinus, chordEndpointPlus, unitCircleOf]

/-- The `+` endpoint of a diameter has nonzero coefficient. -/
lemma chordEndpointPlus_coe_ne_zero (n : Circle) (hd : (0 : ℝ) ∈ Set.Ioo (-1) 1) :
    (chordEndpointPlus n 0 hd : ℂ) ≠ 0 := by
  intro hz
  have := Circle.norm_coe (chordEndpointPlus n 0 hd)
  rw [hz] at this
  norm_num at this

/-- The backward image of a core (diameter) of the chord model is a core
point of the open Möbius band. -/
lemma backwardModel_mobiusCore_mem_core (n : Circle) :
    backwardModel (mobiusCore n) ∈ Set.range coreFactor := by
  -- backwardModel (⟦coreChord n⟧): endpoints of the diameter are antipodal:
  let mem0 : (0 : ℝ) ∈ Set.Ioo (-1) 1 := by norm_num
  have hbwd : backwardChordClass (coreChord n) =
      ⟦(chordEndpointPlus n 0 mem0, chordEndpointMinus n 0 mem0)⟧ := by
    unfold backwardChordClass
    congr 1
  have hminus : chordEndpointMinus n 0 mem0 = - chordEndpointPlus n 0 mem0 :=
    chordEndpointMinus_neg_endpoint n mem0
  unfold backwardModel
  have hbc : backwardCircle (⟦coreChord n⟧) =
      ⟨⟦(chordEndpointPlus n 0 mem0, -chordEndpointPlus n 0 mem0)⟧,
        circleClass_not_diag_of_ne (neg_ne_of_neg_ne_self (chordEndpointPlus n 0 mem0))⟩ := by
    apply Subtype.ext
    change backwardLift (⟦coreChord n⟧) = ⟦(chordEndpointPlus n 0 mem0, -chordEndpointPlus n 0 mem0)⟧
    have h1 : backwardLift (⟦coreChord n⟧) = backwardChordClass (coreChord n) := by
      rfl
    rw [h1, hbwd, hminus]
  rw [hbc]
  have hs := openMobiusCircleEquiv_symm_mk (chordEndpointPlus n 0 mem0)
    (-(chordEndpointPlus n 0 mem0)) (neg_ne_of_neg_ne_self (chordEndpointPlus n 0 mem0))
  rw [hs]
  have hneg := paramCircleHomeo_symm_neg (chordEndpointPlus n 0 mem0)
  have hcover : mobiusCover ⟨(paramCircleHomeo.symm (chordEndpointPlus n 0 mem0),
        paramCircleHomeo.symm (-(chordEndpointPlus n 0 mem0))),
        paramCircleHomeo_symm_injective_ne (chordEndpointPlus n 0 mem0)
          (-(chordEndpointPlus n 0 mem0)) (neg_ne_of_neg_ne_self (chordEndpointPlus n 0 mem0))⟩ =
      core (paramCircleHomeo.symm (chordEndpointPlus n 0 mem0)) := by
    apply congrArg mobiusCover
    ext
    · rfl
    · exact hneg
  rw [hcover]
  rw [coreFactor_range_eq_core_range]
  exact ⟨paramCircleHomeo.symm (chordEndpointPlus n 0 mem0), rfl⟩

/-- **The open Möbius band deformation-retracts onto its core circle**:
transporting the chord slide `mobius_core_retract` of the model Möbius band
through the homeomorphism `openMobiusModelHomeo`, using the core
correspondence (`forwardModel` maps core to diameters and `backwardModel`
maps diameters to core).  This is the `OpenMobiusCoreRetract` statement
formulated in `Submission/Pi1Mobius.lean`. -/
lemma openMobiusCoreRetract : OpenMobiusCoreRetract := by
  rcases mobius_core_retract with ⟨ρm, hcont_m, h0_m, h1_m, hfix_m⟩
  refine ⟨fun z => openMobiusModelHomeo.symm (ρm (openMobiusModelHomeo z.1, z.2)),
    ?cont, ?h0, ?h1, ?hfix⟩
  · have hz1 : Continuous (fun z : OpenMobius × Set.Icc (0 : ℝ) 1 => openMobiusModelHomeo z.1) :=
      openMobiusModelHomeo.continuous.comp continuous_fst
    have hprod : Continuous (fun z : OpenMobius × Set.Icc (0 : ℝ) 1 =>
        (openMobiusModelHomeo z.1, z.2)) := hz1.prodMk continuous_snd
    exact openMobiusModelHomeo.symm.continuous.comp (hcont_m.comp hprod)
  · intro c
    change openMobiusModelHomeo.symm
      (ρm (openMobiusModelHomeo c, ⟨(0 : ℝ), by norm_num⟩)) = c
    rw [h0_m (openMobiusModelHomeo c)]
    simp [openMobiusModelHomeo.symm_apply_apply]
  · intro c
    rcases h1_m (openMobiusModelHomeo c) with ⟨n, hn⟩
    change openMobiusModelHomeo.symm
      (ρm (openMobiusModelHomeo c, ⟨(1 : ℝ), by norm_num⟩)) ∈ Set.range coreFactor
    rw [hn]
    -- openMobiusModelHomeo.symm = backwardModel (definitionally):
    simpa [openMobiusModelHomeo] using (backwardModel_mobiusCore_mem_core n)
  · intro x t
    have hmem_core : openMobiusModelHomeo (coreFactor x) ∈ Set.range mobiusCore := by
      have hrange : coreFactor x ∈ Set.range core := by
        rw [← coreFactor_range_eq_core_range]
        exact ⟨x, rfl⟩
      rcases hrange with ⟨t0, ht⟩
      rw [← ht]
      exact forwardModel_core_mem_mobiusCore t0
    rcases hmem_core with ⟨n, hn⟩
    change openMobiusModelHomeo.symm
      (ρm (openMobiusModelHomeo (coreFactor x), t)) = coreFactor x
    rw [hn.symm, hfix_m n t]
    rw [hn]
    simp [openMobiusModelHomeo.symm_apply_apply]

end LeanEval.KnotTheory.Quadrisecant