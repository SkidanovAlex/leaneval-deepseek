import ChallengeDeps
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseB1Cube.aemeas_winFibreAmp
import Submission.Work.BoseB1Cube.fibreAmpDecay_gen
import Submission.Work.BoseB1Cube.integrableOn_tBamp_boxQInd_abox
import Submission.Work.BoseB1Cube.integrable_winFibreJoint
import Submission.Work.BoseB1Cube.integrable_winFibreTdiag
import Submission.Work.BoseFixB1B.cubeWordDefs
import Submission.Work.BoseFixB1B.sharpSlotBound
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseB1Cube

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "X" => Submission.BoseGases.X

open Submission.BoseGases Work.PerSector Work.UBBInputs8 Work.SmallBoxSliding

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

variable {N : ℕ}

/-! ## 1. The windowed amplitude energies at a general window -/

/-- The ambient amplitude energy of the `i`-th slot of the slot piece, at the window `χ`. -/
noncomputable def cubeSlotAmpEnergy (χ : E3 → ℝ) (L d : ℝ) (u : E3) (S : Finset (Fin N))
    (Φ : X N → ℝ) (i : Fin N) (p : E3) : ℝ :=
  ∫ x in abox N L, ‖Work.SmallBoxTBWord.tBamp χ p
      (boxQInd (boxMass L d u) (dlBox L d u) i (slotPiece (dlBox L d u) S Φ)) i x‖ ^ 2

/-- The fibre amplitude energy of the `j`-th fibre slot, at the window `χ`. -/
noncomputable def cubeFibreAmpEnergy (χ : E3 → ℝ) (L d : ℝ) (u : E3) (S : Finset (Fin N))
    (Φ : X N → ℝ) (e : SlotIn N S ≃ Fin S.card) (j : Fin S.card) (p : E3)
    (y : SlotOut N S → E3) : ℝ :=
  ∫ z in abox S.card L, ‖Work.SmallBoxTBWord.tBamp χ p
      (boxQInd (boxMass L d u) (dlBox L d u) j
        (slotFibreState S e (slotPiece (dlBox L d u) S Φ) y)) j z‖ ^ 2

/-- The `j`-th summand of the joint `(p, y)`-integrand of the fibre form. -/
noncomputable def cubeFibreIntegrand (χ : E3 → ℝ) (L d : ℝ) (u : E3) (S : Finset (Fin N))
    (Φ : X N → ℝ) (e : SlotIn N S ≃ Fin S.card) (F : ℝ → ℝ) (j : Fin S.card) (p : E3)
    (y : SlotOut N S → E3) : ℝ :=
  F ‖p‖ * ((L ^ 3)⁻¹ * cubeFibreAmpEnergy χ L d u S Φ e j p y)

/-- The joint `(p, y)`-integrand of the fibre form, as a sum over the fibre slots. -/
noncomputable def cubeFibreJoint (χ : E3 → ℝ) (L d : ℝ) (u : E3) (S : Finset (Fin N))
    (Φ : X N → ℝ) (e : SlotIn N S ≃ Fin S.card) (F : ℝ → ℝ) (p : E3)
    (y : SlotOut N S → E3) : ℝ :=
  ∑ j : Fin S.card, cubeFibreIntegrand χ L d u S Φ e F j p y

theorem cubeFibreJoint_eq_sum (χ : E3 → ℝ) (L d : ℝ) (u : E3) (S : Finset (Fin N))
    (Φ : X N → ℝ) (e : SlotIn N S ≃ Fin S.card) (F : ℝ → ℝ) (p : E3)
    (y : SlotOut N S → E3) :
    cubeFibreJoint χ L d u S Φ e F p y
      = ∑ j : Fin S.card, cubeFibreIntegrand χ L d u S Φ e F j p y := rfl

theorem cubeFibreIntegrand_nonneg {χ : E3 → ℝ} {L d : ℝ} {u : E3} {S : Finset (Fin N)}
    {Φ : X N → ℝ} {e : SlotIn N S ≃ Fin S.card} {F : ℝ → ℝ} (hF : ∀ r, 0 ≤ F r) (hL : 0 < L)
    (j : Fin S.card) (p : E3) (y : SlotOut N S → E3) :
    0 ≤ cubeFibreIntegrand χ L d u S Φ e F j p y := by
  unfold cubeFibreIntegrand
  refine mul_nonneg (hF _) (mul_nonneg ?_ ?_)
  · positivity
  · unfold cubeFibreAmpEnergy
    exact MeasureTheory.integral_nonneg (fun z => sq_nonneg _)

/-! ## 2. The elementary slot facts -/

theorem cubeBoxQInd_slotPiece_eq_zero_of_notMem {L d : ℝ} (u : E3) (S : Finset (Fin N))
    (Φ : X N → ℝ) (i : Fin N) (hi : i ∉ S) :
    boxQInd (boxMass L d u) (dlBox L d u) i (slotPiece (dlBox L d u) S Φ) = 0 := by
  funext x
  refine Work.PerSector.boxQInd_slotPiece_eq_zero_of_notMem_slotShiftSet
    (measurableSet_dlBox L d u) i S ?_
  intro hx
  exact hi hx.1

theorem cubeSlotAmpEnergy_eq_zero_of_notMem (χ : E3 → ℝ) (L d : ℝ) (u : E3)
    (S : Finset (Fin N)) (Φ : X N → ℝ) (i : Fin N) (hi : i ∉ S) (p : E3) :
    cubeSlotAmpEnergy χ L d u S Φ i p = 0 := by
  unfold cubeSlotAmpEnergy
  rw [cubeBoxQInd_slotPiece_eq_zero_of_notMem u S Φ i hi]
  simp

/-- **The pointwise amplitude identity at a general window.** -/
theorem tBamp_boxQInd_slotPiece_eq_fibre_gen {L d : ℝ} (hL : 0 < L) (hd : 0 < d)
    (χ : E3 → ℝ) (u : E3) (S : Finset (Fin N)) (Φ : X N → ℝ)
    (e : SlotIn N S ≃ Fin S.card) (i : Fin N) (hi : i ∈ S) (p : E3) (z : X S.card)
    (y : SlotOut N S → E3) :
    Work.SmallBoxTBWord.tBamp χ p
        (boxQInd (boxMass L d u) (dlBox L d u) i (slotPiece (dlBox L d u) S Φ)) i
        (Work.SlotWord.fibreIn S e y z)
      = Work.SmallBoxTBWord.tBamp χ p
          (boxQInd (boxMass L d u) (dlBox L d u) (e ⟨i, hi⟩)
            (slotFibreState S e (slotPiece (dlBox L d u) S Φ) y)) (e ⟨i, hi⟩) z := by
  rw [Work.SmallBoxTBWord.tBamp, Work.SmallBoxTBWord.tBamp]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun w => ?_))
  refine congrArg (fun t : ℝ =>
    (χ w : ℂ) * Complex.exp (-(Complex.I * (inner ℝ p w : ℂ))) * (t : ℂ)) ?_
  rw [Work.SlotWord.fibreIn_update S e i hi y z w]
  exact (Work.SlotWord.boxQInd_slotFibre_transfer S e i hi y (slotPiece (dlBox L d u) S Φ)
    (boxMass L d u) (dlBox L d u) (Function.update z (e ⟨i, hi⟩) w)).symm

/-! ## 3. The slot splitting at a general window -/

theorem cubeSlotAmpEnergy_eq_integral_fibre {L d : ℝ} (hL : 0 < L) (hd : 0 < d)
    (χ : E3 → ℝ) (u : E3) (hχsupp : ∀ z : E3, χ z ≠ 0 → z ∈ dlBox L d u)
    (S : Finset (Fin N)) (Φ : X N → ℝ) (e : SlotIn N S ≃ Fin S.card) (i : Fin N) (hi : i ∈ S)
    (p : E3)
    (hint : MeasureTheory.IntegrableOn (fun x : X N =>
      ‖Work.SmallBoxTBWord.tBamp χ p
        (boxQInd (boxMass L d u) (dlBox L d u) i (slotPiece (dlBox L d u) S Φ)) i x‖ ^ 2)
      (abox N L)) :
    cubeSlotAmpEnergy χ L d u S Φ i p
      = ∫ y in slotOutside L (dlBox L d u) S,
          cubeFibreAmpEnergy χ L d u S Φ e (e ⟨i, hi⟩) p y := by
  classical
  set f : X N → ℝ := fun x => ‖Work.SmallBoxTBWord.tBamp χ p
      (boxQInd (boxMass L d u) (dlBox L d u) i (slotPiece (dlBox L d u) S Φ)) i x‖ ^ 2 with hf
  have hout : ∀ x : X N, f x ≠ 0 → ∀ j : SlotOut N S, x j ∉ dlBox L d u := by
    intro x hx j
    have hne : Work.SmallBoxTBWord.tBamp χ p
        (boxQInd (boxMass L d u) (dlBox L d u) i (slotPiece (dlBox L d u) S Φ)) i x ≠ 0 := by
      intro h0
      exact hx (by rw [hf]; simp [h0])
    have hmem : x ∈ slotAmpSet (dlBox L d u) S i := by
      by_contra hxnot
      exact hne (Work.PerSector.tBamp_slotPiece_eq_zero_of_notMem_slotAmpSet
        χ hχsupp i S p hxnot)
    have h2 := (mem_slotAmpSet_iff (dlBox L d u) S i x).mp hmem
    have hji : j.1 ≠ i := fun hc => j.2 (hc ▸ hi)
    intro hc
    exact j.2 ((h2.2 j.1 hji).mp hc)
  have hsplit := Work.SlotWord.FibreSpec.slotSplit_integral_ampSet (N := N) L
    (A := dlBox L d u) S e (f := f) hint hout
  have hLHS : cubeSlotAmpEnergy χ L d u S Φ i p = ∫ x in abox N L, f x := rfl
  rw [hLHS, hsplit]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun y => ?_))
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
  change f (Work.SlotWord.fibreIn S e y z)
    = ‖Work.SmallBoxTBWord.tBamp χ p
        (boxQInd (boxMass L d u) (dlBox L d u) (e ⟨i, hi⟩)
          (slotFibreState S e (slotPiece (dlBox L d u) S Φ) y)) (e ⟨i, hi⟩) z‖ ^ 2
  rw [hf]
  exact congrArg (fun w : ℂ => ‖w‖ ^ 2)
    (tBamp_boxQInd_slotPiece_eq_fibre_gen hL hd χ u S Φ e i hi p z y)

/-- The same splitting, indexed by the image slot `j` of the transport. -/
theorem cubeSlotAmpEnergy_eq_integral_fibre_apply {L d : ℝ} (hL : 0 < L) (hd : 0 < d)
    (χ : E3 → ℝ) (u : E3) (hχsupp : ∀ z : E3, χ z ≠ 0 → z ∈ dlBox L d u)
    (S : Finset (Fin N)) (Φ : X N → ℝ) (e : SlotIn N S ≃ Fin S.card) (j : Fin S.card) (p : E3)
    (hint : MeasureTheory.IntegrableOn (fun x : X N =>
      ‖Work.SmallBoxTBWord.tBamp χ p
        (boxQInd (boxMass L d u) (dlBox L d u) (e.symm j).1
          (slotPiece (dlBox L d u) S Φ)) (e.symm j).1 x‖ ^ 2) (abox N L)) :
    cubeSlotAmpEnergy χ L d u S Φ (e.symm j).1 p
      = ∫ y in slotOutside L (dlBox L d u) S,
          cubeFibreAmpEnergy χ L d u S Φ e j p y := by
  have h := cubeSlotAmpEnergy_eq_integral_fibre hL hd χ u hχsupp S Φ e (e.symm j).1 (e.symm j).2 p
    hint
  simpa using h

/-- The `y`-integral of the `j`-th summand of the joint integrand. -/
theorem cubeIntegral_fibreIntegrand (χ : E3 → ℝ) (L d : ℝ) (u : E3) (S : Finset (Fin N))
    (Φ : X N → ℝ) (e : SlotIn N S ≃ Fin S.card) (F : ℝ → ℝ) (j : Fin S.card) (p : E3) :
    (∫ y in slotOutside L (dlBox L d u) S, cubeFibreIntegrand χ L d u S Φ e F j p y)
      = F ‖p‖ * ((L ^ 3)⁻¹ *
          ∫ y in slotOutside L (dlBox L d u) S, cubeFibreAmpEnergy χ L d u S Φ e j p y) := by
  rw [show (∫ y in slotOutside L (dlBox L d u) S, cubeFibreIntegrand χ L d u S Φ e F j p y)
      = ∫ y in slotOutside L (dlBox L d u) S,
          F ‖p‖ * ((L ^ 3)⁻¹ * cubeFibreAmpEnergy χ L d u S Φ e j p y)
      from MeasureTheory.integral_congr_ae
        (Filter.Eventually.of_forall (fun y => rfl))]
  rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]

/-! ## 4. The reindexing of the slot sum -/

theorem cubeSum_slotAmpEnergy_eq_sum_fibre (χ : E3 → ℝ) (L d : ℝ) (u : E3) (S : Finset (Fin N))
    (Φ : X N → ℝ) (e : SlotIn N S ≃ Fin S.card) (F : ℝ → ℝ) :
    (∑ i : Fin N, ((2 * Real.pi) ^ 3)⁻¹ *
        ∫ p : E3, F ‖p‖ * ((L ^ 3)⁻¹ * cubeSlotAmpEnergy χ L d u S Φ i p))
      = ∑ j : Fin S.card, ((2 * Real.pi) ^ 3)⁻¹ *
        ∫ p : E3, F ‖p‖ * ((L ^ 3)⁻¹ * cubeSlotAmpEnergy χ L d u S Φ (e.symm j).1 p) := by
  classical
  set g : Fin N → ℝ := fun i => ((2 * Real.pi) ^ 3)⁻¹ *
      ∫ p : E3, F ‖p‖ * ((L ^ 3)⁻¹ * cubeSlotAmpEnergy χ L d u S Φ i p) with hg
  have hzero : ∀ i : Fin N, i ∉ S → g i = 0 := by
    intro i hi
    simp only [hg]
    have hpt : (fun p : E3 => F ‖p‖ * ((L ^ 3)⁻¹ * cubeSlotAmpEnergy χ L d u S Φ i p))
        = fun _ => 0 := by
      funext p
      rw [cubeSlotAmpEnergy_eq_zero_of_notMem χ L d u S Φ i hi]
      ring
    rw [hpt]
    simp
  have h1 : ∑ i : Fin N, g i = ∑ i ∈ Finset.univ.filter (fun i => i ∈ S), g i := by
    refine (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
    intro i _ hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi
    exact hzero i hi
  have h2 : ∑ i ∈ Finset.univ.filter (fun i => i ∈ S), g i = ∑ i : SlotIn N S, g i.1 :=
    Finset.sum_subtype (Finset.univ.filter (fun i => i ∈ S)) (fun i => by simp) g
  have h3 : ∑ i : SlotIn N S, g i.1 = ∑ j : Fin S.card, g (e.symm j).1 :=
    Fintype.sum_equiv e (fun i : SlotIn N S => g i.1) (fun j : Fin S.card => g (e.symm j).1)
      (fun i => by simp)
  rw [h1, h2, h3]

/-! ## 5. The left-hand side as the `p`- then `y`-integral of the joint integrand -/

theorem cubeTdiagFormInd_eq_sum_fibre {L d : ℝ} (hL : 0 < L) (hd : 0 < d)
    (χ : E3 → ℝ) (u : E3) (hχsupp : ∀ z : E3, χ z ≠ 0 → z ∈ dlBox L d u)
    (S : Finset (Fin N)) (Φ : X N → ℝ) (e : SlotIn N S ≃ Fin S.card) (F : ℝ → ℝ)
    (hint : ∀ (i : Fin N) (p : E3), MeasureTheory.IntegrableOn (fun x : X N =>
      ‖Work.SmallBoxTBWord.tBamp χ p
        (boxQInd (boxMass L d u) (dlBox L d u) i (slotPiece (dlBox L d u) S Φ)) i x‖ ^ 2)
      (abox N L)) :
    Work.UBBInputs8.tBdiagFormInd L (dlBox L d u) (boxMass L d u) χ F
        (slotPiece (dlBox L d u) S Φ)
      = ((2 * Real.pi) ^ 3)⁻¹ * ∑ j : Fin S.card,
          ∫ p : E3,
            ∫ y in slotOutside L (dlBox L d u) S, cubeFibreIntegrand χ L d u S Φ e F j p y := by
  have h1 : Work.UBBInputs8.tBdiagFormInd L (dlBox L d u) (boxMass L d u) χ F
        (slotPiece (dlBox L d u) S Φ)
      = ∑ i : Fin N, ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : E3, F ‖p‖ *
          ((L ^ 3)⁻¹ * cubeSlotAmpEnergy χ L d u S Φ i p) := rfl
  rw [h1, cubeSum_slotAmpEnergy_eq_sum_fibre χ L d u S Φ e F]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  have hkey : (∫ p : E3, F ‖p‖ *
        ((L ^ 3)⁻¹ * cubeSlotAmpEnergy χ L d u S Φ (e.symm j).1 p))
      = ∫ p : E3, ∫ y in slotOutside L (dlBox L d u) S,
          cubeFibreIntegrand χ L d u S Φ e F j p y := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun p => ?_))
    show F ‖p‖ * ((L ^ 3)⁻¹ * cubeSlotAmpEnergy χ L d u S Φ (e.symm j).1 p)
      = ∫ y in slotOutside L (dlBox L d u) S, cubeFibreIntegrand χ L d u S Φ e F j p y
    rw [cubeIntegral_fibreIntegrand χ L d u S Φ e F j p,
      cubeSlotAmpEnergy_eq_integral_fibre_apply hL hd χ u hχsupp S Φ e j p (hint _ _)]
  rw [hkey]
/-! ## 6. The right-hand side as the `p`- then `y`-integral of the joint integrand -/

theorem cubeFibreIntegral_eq_sum {L d : ℝ} (hL : 0 < L) (hd : 0 < d)
    (χ : E3 → ℝ) (u : E3) (S : Finset (Fin N)) (Φ : X N → ℝ) (e : SlotIn N S ≃ Fin S.card)
    (F : ℝ → ℝ) (hF : ∀ r, 0 ≤ F r) (hFm : Measurable F)
    (hmeas : ∀ j : Fin S.card, AEStronglyMeasurable
      (fun q : E3 × (SlotOut N S → E3) =>
        ∫ z in abox S.card L,
          ‖Work.SmallBoxTBWord.tBamp χ q.1
            (boxQInd (boxMass L d u) (dlBox L d u) j
              (slotFibreState S e (slotPiece (dlBox L d u) S Φ) q.2)) j z‖ ^ 2)
      ((volume : Measure E3).prod (Work.SlotWord.FibreSpec.fibreOutMeasure L d u S)))
    (hswap : MeasureTheory.Integrable
      (fun q : E3 × (SlotOut N S → E3) => cubeFibreJoint χ L d u S Φ e F q.1 q.2)
      ((volume : Measure E3).prod (Work.SlotWord.FibreSpec.fibreOutMeasure L d u S))) :
    (∫ y in slotOutside L (dlBox L d u) S,
        Work.UBBInputs8.tBdiagFormInd L (dlBox L d u) (boxMass L d u) χ F
          (slotFibreState S e (slotPiece (dlBox L d u) S Φ) y))
      = ((2 * Real.pi) ^ 3)⁻¹ * ∑ j : Fin S.card,
          ∫ p : E3, ∫ y in slotOutside L (dlBox L d u) S,
            cubeFibreIntegrand χ L d u S Φ e F j p y := by
  classical
  have haesm : ∀ j : Fin S.card,
      AEStronglyMeasurable
        (Function.uncurry (fun (p : E3) (y : SlotOut N S → E3) =>
          cubeFibreIntegrand χ L d u S Φ e F j p y))
        ((volume : Measure E3).prod (Work.SlotWord.FibreSpec.fibreOutMeasure L d u S)) := by
    intro j
    have hE : AEStronglyMeasurable
        (fun q : E3 × (SlotOut N S → E3) => cubeFibreAmpEnergy χ L d u S Φ e j q.1 q.2)
        ((volume : Measure E3).prod (Work.SlotWord.FibreSpec.fibreOutMeasure L d u S)) := by
      have h := hmeas j
      simpa only [cubeFibreAmpEnergy] using h
    have hFn : AEStronglyMeasurable
        (fun q : E3 × (SlotOut N S → E3) => F ‖q.1‖)
        ((volume : Measure E3).prod (Work.SlotWord.FibreSpec.fibreOutMeasure L d u S)) :=
      (hFm.comp ((continuous_norm.measurable).comp measurable_fst)).aestronglyMeasurable
    have hthis := hFn.mul (hE.const_mul ((L ^ 3)⁻¹))
    have heq : ((fun q : E3 × (SlotOut N S → E3) => F ‖q.1‖) *
          (fun q : E3 × (SlotOut N S → E3) =>
            (L ^ 3)⁻¹ * cubeFibreAmpEnergy χ L d u S Φ e j q.1 q.2))
        = Function.uncurry (fun (p : E3) (y : SlotOut N S → E3) =>
            cubeFibreIntegrand χ L d u S Φ e F j p y) := by
      funext q; rfl
    rwa [heq] at hthis
  have hint : ∀ j : Fin S.card,
      MeasureTheory.Integrable
        (Function.uncurry (fun (p : E3) (y : SlotOut N S → E3) =>
          cubeFibreIntegrand χ L d u S Φ e F j p y))
        ((volume : Measure E3).prod (Work.SlotWord.FibreSpec.fibreOutMeasure L d u S)) := by
    intro j
    refine MeasureTheory.Integrable.mono' hswap (haesm j) ?_
    refine Filter.Eventually.of_forall (fun q => ?_)
    have hle : cubeFibreIntegrand χ L d u S Φ e F j q.1 q.2
        ≤ ∑ j' : Fin S.card, cubeFibreIntegrand χ L d u S Φ e F j' q.1 q.2 :=
      Finset.single_le_sum (fun j' _ => cubeFibreIntegrand_nonneg hF hL j' q.1 q.2)
        (Finset.mem_univ j)
    change ‖cubeFibreIntegrand χ L d u S Φ e F j q.1 q.2‖
      ≤ cubeFibreJoint χ L d u S Φ e F q.1 q.2
    rw [Real.norm_of_nonneg (cubeFibreIntegrand_nonneg hF hL j q.1 q.2), cubeFibreJoint_eq_sum]
    exact hle
  have hsec_y : ∀ᵐ y ∂(Work.SlotWord.FibreSpec.fibreOutMeasure L d u S), ∀ j : Fin S.card,
      MeasureTheory.Integrable (fun p : E3 => cubeFibreIntegrand χ L d u S Φ e F j p y)
        volume := by
    have hsm : ∀ᵐ y ∂(Work.SlotWord.FibreSpec.fibreOutMeasure L d u S), ∀ j : Fin S.card,
        AEStronglyMeasurable (fun p : E3 => cubeFibreIntegrand χ L d u S Φ e F j p y) volume :=
      Filter.eventually_all.2 (fun j => (haesm j).prodMk_right)
    have hJint : ∀ᵐ y ∂(Work.SlotWord.FibreSpec.fibreOutMeasure L d u S),
        MeasureTheory.Integrable (fun p : E3 => cubeFibreJoint χ L d u S Φ e F p y) volume :=
      hswap.prod_left_ae
    filter_upwards [hsm, hJint] with y hsm'y hJy
    intro j
    refine MeasureTheory.Integrable.mono' hJy (hsm'y j) ?_
    refine Filter.Eventually.of_forall (fun p => ?_)
    have hle : cubeFibreIntegrand χ L d u S Φ e F j p y
        ≤ ∑ j' : Fin S.card, cubeFibreIntegrand χ L d u S Φ e F j' p y :=
      Finset.single_le_sum (fun j' _ => cubeFibreIntegrand_nonneg hF hL j' p y)
        (Finset.mem_univ j)
    change ‖cubeFibreIntegrand χ L d u S Φ e F j p y‖ ≤ cubeFibreJoint χ L d u S Φ e F p y
    rw [Real.norm_of_nonneg (cubeFibreIntegrand_nonneg hF hL j p y), cubeFibreJoint_eq_sum]
    exact hle
  have hsec_p : ∀ᵐ p ∂(volume : Measure E3), ∀ j : Fin S.card,
      MeasureTheory.Integrable (fun y : SlotOut N S → E3 =>
        cubeFibreIntegrand χ L d u S Φ e F j p y)
        (Work.SlotWord.FibreSpec.fibreOutMeasure L d u S) := by
    have hsm : ∀ᵐ p ∂(volume : Measure E3), ∀ j : Fin S.card,
        AEStronglyMeasurable
          (fun y : SlotOut N S → E3 => cubeFibreIntegrand χ L d u S Φ e F j p y)
          (Work.SlotWord.FibreSpec.fibreOutMeasure L d u S) :=
      Filter.eventually_all.2 (fun j => (haesm j).prodMk_left)
    have hJint : ∀ᵐ p ∂(volume : Measure E3),
        MeasureTheory.Integrable (fun y : SlotOut N S → E3 =>
          cubeFibreJoint χ L d u S Φ e F p y)
          (Work.SlotWord.FibreSpec.fibreOutMeasure L d u S) := hswap.prod_right_ae
    filter_upwards [hsm, hJint] with p hsm'p hJp
    intro j
    refine MeasureTheory.Integrable.mono' hJp (hsm'p j) ?_
    refine Filter.Eventually.of_forall (fun y => ?_)
    have hle : cubeFibreIntegrand χ L d u S Φ e F j p y
        ≤ ∑ j' : Fin S.card, cubeFibreIntegrand χ L d u S Φ e F j' p y :=
      Finset.single_le_sum (fun j' _ => cubeFibreIntegrand_nonneg hF hL j' p y)
        (Finset.mem_univ j)
    change ‖cubeFibreIntegrand χ L d u S Φ e F j p y‖ ≤ cubeFibreJoint χ L d u S Φ e F p y
    rw [Real.norm_of_nonneg (cubeFibreIntegrand_nonneg hF hL j p y), cubeFibreJoint_eq_sum]
    exact hle
  have key_y : ∀ᵐ y ∂(Work.SlotWord.FibreSpec.fibreOutMeasure L d u S),
      Work.UBBInputs8.tBdiagFormInd L (dlBox L d u) (boxMass L d u) χ F
          (slotFibreState S e (slotPiece (dlBox L d u) S Φ) y)
        = ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : E3, cubeFibreJoint χ L d u S Φ e F p y := by
    filter_upwards [hsec_y] with y hy
    rw [show Work.UBBInputs8.tBdiagFormInd L (dlBox L d u) (boxMass L d u) χ F
          (slotFibreState S e (slotPiece (dlBox L d u) S Φ) y)
        = ∑ j : Fin S.card, ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : E3,
            F ‖p‖ * ((L ^ 3)⁻¹ * cubeFibreAmpEnergy χ L d u S Φ e j p y) from rfl]
    have hsum : (∫ p : E3, cubeFibreJoint χ L d u S Φ e F p y)
        = ∑ j : Fin S.card, ∫ p : E3, cubeFibreIntegrand χ L d u S Φ e F j p y := by
      rw [show (∫ p : E3, cubeFibreJoint χ L d u S Φ e F p y)
          = ∫ p : E3, ∑ j : Fin S.card, cubeFibreIntegrand χ L d u S Φ e F j p y from by
        exact MeasureTheory.integral_congr_ae
          (Filter.Eventually.of_forall (fun p => cubeFibreJoint_eq_sum χ L d u S Φ e F p y))]
      exact MeasureTheory.integral_finsetSum Finset.univ (fun i _ => hy i)
    rw [hsum, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    rfl
  have key_p : ∀ᵐ p ∂(volume : Measure E3),
      (∫ y in slotOutside L (dlBox L d u) S, cubeFibreJoint χ L d u S Φ e F p y)
        = ∑ j : Fin S.card,
            ∫ y in slotOutside L (dlBox L d u) S, cubeFibreIntegrand χ L d u S Φ e F j p y := by
    filter_upwards [hsec_p] with p hp
    rw [show (∫ y in slotOutside L (dlBox L d u) S, cubeFibreJoint χ L d u S Φ e F p y)
        = ∫ y in slotOutside L (dlBox L d u) S, ∑ j : Fin S.card,
            cubeFibreIntegrand χ L d u S Φ e F j p y from by
      exact MeasureTheory.integral_congr_ae
        (Filter.Eventually.of_forall (fun y => cubeFibreJoint_eq_sum χ L d u S Φ e F p y))]
    exact MeasureTheory.integral_finsetSum Finset.univ (fun i _ => hp i)
  have hFint : ∀ j : Fin S.card,
      MeasureTheory.Integrable (fun p : E3 => ∫ y in slotOutside L (dlBox L d u) S,
          cubeFibreIntegrand χ L d u S Φ e F j p y) volume :=
    fun j => (hint j).integral_prod_left
  calc (∫ y in slotOutside L (dlBox L d u) S,
        Work.UBBInputs8.tBdiagFormInd L (dlBox L d u) (boxMass L d u) χ F
          (slotFibreState S e (slotPiece (dlBox L d u) S Φ) y))
      = ∫ y in slotOutside L (dlBox L d u) S,
          ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : E3, cubeFibreJoint χ L d u S Φ e F p y :=
        MeasureTheory.integral_congr_ae key_y
    _ = ((2 * Real.pi) ^ 3)⁻¹ * ∫ y in slotOutside L (dlBox L d u) S,
          ∫ p : E3, cubeFibreJoint χ L d u S Φ e F p y :=
        MeasureTheory.integral_const_mul _ _
    _ = ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : E3,
          ∫ y in slotOutside L (dlBox L d u) S, cubeFibreJoint χ L d u S Φ e F p y := by
        rw [(MeasureTheory.integral_integral_swap hswap).symm]
    _ = ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : E3, ∑ j : Fin S.card,
          ∫ y in slotOutside L (dlBox L d u) S, cubeFibreIntegrand χ L d u S Φ e F j p y :=
        congrArg _ (MeasureTheory.integral_congr_ae key_p)
    _ = ((2 * Real.pi) ^ 3)⁻¹ * ∑ j : Fin S.card,
          ∫ p : E3, ∫ y in slotOutside L (dlBox L d u) S,
            cubeFibreIntegrand χ L d u S Φ e F j p y := by
        rw [MeasureTheory.integral_finsetSum Finset.univ (fun j _ => hFint j)]

/-! ## 7. The spectral fibre factorisation -/

theorem cubeTdiagFormInd_fibre {L d : ℝ} (hL : 0 < L) (hd : 0 < d)
    (χ : E3 → ℝ) (u : E3) (hχsupp : ∀ z : E3, χ z ≠ 0 → z ∈ dlBox L d u)
    (S : Finset (Fin N)) (Φ : X N → ℝ) (e : SlotIn N S ≃ Fin S.card)
    (F : ℝ → ℝ) (hF : ∀ r, 0 ≤ F r) (hFm : Measurable F)
    (hint : ∀ (i : Fin N) (p : E3), MeasureTheory.IntegrableOn (fun x : X N =>
      ‖Work.SmallBoxTBWord.tBamp χ p
        (boxQInd (boxMass L d u) (dlBox L d u) i (slotPiece (dlBox L d u) S Φ)) i x‖ ^ 2)
      (abox N L))
    (hmeas : ∀ j : Fin S.card, AEStronglyMeasurable
      (fun q : E3 × (SlotOut N S → E3) =>
        ∫ z in abox S.card L,
          ‖Work.SmallBoxTBWord.tBamp χ q.1
            (boxQInd (boxMass L d u) (dlBox L d u) j
              (slotFibreState S e (slotPiece (dlBox L d u) S Φ) q.2)) j z‖ ^ 2)
      ((volume : Measure E3).prod (Work.SlotWord.FibreSpec.fibreOutMeasure L d u S)))
    (hswap : MeasureTheory.Integrable
      (fun q : E3 × (SlotOut N S → E3) => cubeFibreJoint χ L d u S Φ e F q.1 q.2)
      ((volume : Measure E3).prod (Work.SlotWord.FibreSpec.fibreOutMeasure L d u S))) :
    Work.UBBInputs8.tBdiagFormInd L (dlBox L d u) (boxMass L d u) χ F
        (slotPiece (dlBox L d u) S Φ)
      = ∫ y in slotOutside L (dlBox L d u) S,
          Work.UBBInputs8.tBdiagFormInd L (dlBox L d u) (boxMass L d u) χ F
            (slotFibreState S e (slotPiece (dlBox L d u) S Φ) y) := by
  rw [cubeTdiagFormInd_eq_sum_fibre hL hd χ u hχsupp S Φ e F hint]
  exact (cubeFibreIntegral_eq_sum hL hd χ u S Φ e F hF hFm hmeas hswap).symm

/-- `chiSmallB M L d u` is `C³` for `M ≥ 4`. -/
theorem chiSmallB_contDiff_three' (M : ℕ) (hM : 4 ≤ M) (L d : ℝ) (hL : 0 < L) (hd : 0 < d)
    (u : E3) : ContDiff ℝ 3 (chiSmallB M L d u) :=
  Work.BoseFixB1S.win.contDiff_three_chiSmallB hM hL hd u

/-- `chiSmallB M L d u` is measurable. -/
theorem chiSmallB_measurable' (M : ℕ) (hM : 4 ≤ M) (L d : ℝ) (hL : 0 < L) (hd : 0 < d)
    (u : E3) : Measurable (chiSmallB M L d u) :=
  (chiSmallB_contDiff_three' M hM L d hL hd u).continuous.measurable

/-- `chiSmallB M L d u` is compactly supported. -/
theorem chiSmallB_hasCompactSupport' (M : ℕ) (hM : 1 ≤ M) (L d : ℝ) (hL : 0 < L) (u : E3) :
    HasCompactSupport (chiSmallB M L d u) :=
  Submission.BoseGases.chiSmallB_hasCompactSupport (M := M) (ℓ := L) (d := d) hM hL u

/-- `|chiSmallB M L d u|` is integrable. -/
theorem chiSmallB_integrable_abs' (M : ℕ) (hM : 4 ≤ M) (L d : ℝ) (hL : 0 < L) (hd : 0 < d)
    (u : E3) : MeasureTheory.Integrable (fun z : E3 => |chiSmallB M L d u z|) :=
  ((chiSmallB_contDiff_three' M hM L d hL hd u).continuous.integrable_of_hasCompactSupport
    (chiSmallB_hasCompactSupport' M (by omega) L d hL u)).abs

/-- The support of `chiSmallB M L d u` lies in the sliding box. -/
theorem chiSmallB_supp' (M : ℕ) (hM : 1 ≤ M) (L d : ℝ) (hL : 0 < L) (hd : 0 < d) (u : E3) :
    ∀ z : E3, chiSmallB M L d u z ≠ 0 → z ∈ dlBox L d u :=
  fun z hz => Work.SlotWord.chiSmallB_support_mem_dlBox (M := M) (L := L) (d := d) (u := u)
    hM hL hd hz

/-- The (R3)-integrability of the slot amplitude at the cube window. -/
theorem cubeTampIntegrableOn (M : ℕ) (hM : 4 ≤ M) (L d : ℝ) (hL : 0 < L) (hd : 0 < d) (u : E3)
    {N : ℕ} (S : Finset (Fin N)) (Φ : X N → ℝ) (hΦ : Continuous Φ) (i : Fin N) (p : E3) :
    MeasureTheory.IntegrableOn (fun x : X N =>
      ‖Work.SmallBoxTBWord.tBamp (chiSmallB M L d u) p
        (boxQInd (boxMass L d u) (dlBox L d u) i (slotPiece (dlBox L d u) S Φ)) i x‖ ^ 2)
      (abox N L) :=
  integrableOn_tBamp_boxQInd_abox hL (measurableSet_dlBox L d u) (dlBox_subset_acube L d u)
    (volume_dlBox_lt_top hL d u) (boxMass L d u) (boxMass_eq_measureReal L d u)
    (chiSmallB_measurable' M hM L d hL hd u) (chiSmallB_integrable_abs' M hM L d hL hd u)
    (chiSmallB_supp' M (by omega) L d hL hd u) hΦ i p

/-- The uniform `(1+‖p‖)⁻³` decay of the fibre amplitude at the cube window. -/
theorem cubeFibreDecay (M : ℕ) (hM : 4 ≤ M) (L d : ℝ) (hL : 0 < L) (hd : 0 < d) (u : E3)
    {N : ℕ} (S : Finset (Fin N)) (Φ : X N → ℝ) (hΦ : ContDiff ℝ (⊤ : ENat) Φ)
    (e : SlotIn N S ≃ Fin S.card) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (j : Fin S.card) (p : E3) (y : SlotOut N S → E3),
        y ∈ slotOutside L (dlBox L d u) S → ∀ ζ ∈ abox S.card L,
        ‖Work.SmallBoxTBWord.tBamp (chiSmallB M L d u) p
            (boxQInd (boxMass L d u) (dlBox L d u) j
              (slotFibreState S e (slotPiece (dlBox L d u) S Φ) y)) j ζ‖
          ≤ C / (1 + ‖p‖) ^ 3 :=
  fibreAmpDecay_gen L d hL hd u S hΦ e (chiSmallB_contDiff_three' M hM L d hL hd u)
    (chiSmallB_hasCompactSupport' M (by omega) L d hL u) (chiSmallB_supp' M (by omega) L d hL hd u)

/-- **The fibre factorisation of the matched (cube-cutoff) sliding word** `cubeWord` at the box
`dlBox L d u`, the volume `boxMass L d u`, the cube window `chiSmallB M L d u`, the gap `ε` and the
spectral cutoff `c`: the word of the slot piece is the integral, over the outside configurations,
of the word of the transported fibre, and that fibre integrand is integrable. -/
theorem cubeWord_fibre (M : ℕ) (hM : 4 ≤ M) (L d ε c : ℝ) (hL : 0 < L) (hd : 0 < d) (u : E3)
    {N : ℕ} (S : Finset (Fin N)) (Φ : X N → ℝ) (hΦ : ContDiff ℝ (⊤ : ENat) Φ)
    (e : SlotIn N S ≃ Fin S.card) :
    MeasureTheory.Integrable
        (fun y : SlotOut N S → E3 =>
          Work.BoseFixB1B.cubeWord M L d ε c u
            (slotFibreState S e (slotPiece (dlBox L d u) S Φ) y))
        ((MeasureTheory.volume : MeasureTheory.Measure (SlotOut N S → E3)).restrict
          (slotOutside L (dlBox L d u) S))
      ∧ Work.BoseFixB1B.cubeWord M L d ε c u (slotPiece (dlBox L d u) S Φ)
        = ∫ y in slotOutside L (dlBox L d u) S,
            Work.BoseFixB1B.cubeWord M L d ε c u
              (slotFibreState S e (slotPiece (dlBox L d u) S Φ) y) := by
  classical
  have hΦc : Continuous Φ := hΦ.continuous
  have hΦm : Measurable Φ := hΦc.measurable
  have hA : MeasurableSet (dlBox L d u) := measurableSet_dlBox L d u
  have hAc : dlBox L d u ⊆ acube L := dlBox_subset_acube L d u
  have hχm : Measurable (chiSmallB M L d u) := chiSmallB_measurable' M hM L d hL hd u
  obtain ⟨Cb, hCb0, hCb⟩ : ∃ Cb : ℝ, 0 ≤ Cb ∧
      ∀ x ∈ abox N L, |Φ x| ≤ Cb := by
    obtain ⟨C₀, hC₀⟩ :=
      (Work.UBBInputs9.B.abox_isCompact N L).exists_bound_of_continuousOn hΦc.continuousOn
    refine ⟨max C₀ 0, le_max_right _ _, fun x hx => ?_⟩
    have h1 := hC₀ x hx
    rw [Real.norm_eq_abs] at h1
    exact le_trans h1 (le_max_left _ _)
  -- the gap (excited-count) half
  have hgap := Work.SlotWord.FibreGap.cnPlusBoxInd_fibre L d hL hd u S Φ hΦc e
  have hgapI := Work.SlotWord.integrable_fibre_cnPlusBoxInd L hL hA hAc (boxMass L d u) S e
    hΦm hCb0 hCb
  -- the spectral half
  have hdec := cubeFibreDecay M hM L d hL hd u S Φ hΦ e
  have hhint : ∀ (i : Fin N) (p : E3), MeasureTheory.IntegrableOn (fun x : X N =>
      ‖Work.SmallBoxTBWord.tBamp (chiSmallB M L d u) p
        (boxQInd (boxMass L d u) (dlBox L d u) i (slotPiece (dlBox L d u) S Φ)) i x‖ ^ 2)
      (abox N L) := fun i p => cubeTampIntegrableOn M hM L d hL hd u S Φ hΦc i p
  have hhmeas : ∀ j : Fin S.card, AEStronglyMeasurable
      (fun q : E3 × (SlotOut N S → E3) =>
        ∫ z in abox S.card L,
          ‖Work.SmallBoxTBWord.tBamp (chiSmallB M L d u) q.1
            (boxQInd (boxMass L d u) (dlBox L d u) j
              (slotFibreState S e (slotPiece (dlBox L d u) S Φ) q.2)) j z‖ ^ 2)
      ((volume : Measure E3).prod (Work.SlotWord.FibreSpec.fibreOutMeasure L d u S)) :=
    fun j => aemeas_winFibreAmp L d u S hΦm e hχm j
  have hhswap : MeasureTheory.Integrable
      (fun q : E3 × (SlotOut N S → E3) =>
        cubeFibreJoint (chiSmallB M L d u) L d u S Φ e (Submission.BoseGases.fsKinCoeff c)
          q.1 q.2)
      ((volume : Measure E3).prod (Work.SlotWord.FibreSpec.fibreOutMeasure L d u S)) :=
    integrable_winFibreJoint L d c hL hd u S hΦm e hχm hdec
  have hspec := cubeTdiagFormInd_fibre hL hd (chiSmallB M L d u) u
    (chiSmallB_supp' M (by omega) L d hL hd u) S Φ e (Submission.BoseGases.fsKinCoeff c)
    (Submission.BoseGases.fsKinCoeff_nonneg c) (Work.BoseKinLoc.Kinetic.measurable_fsKinCoeff c)
    hhint hhmeas hhswap
  have hspecI := integrable_winFibreTdiag L d c hL hd u S hΦm e hχm hdec
  refine ⟨?_, ?_⟩
  · refine ((hgapI.const_mul (Work.SmallBoxTBWord.tbGapCoeff (L * d) ε)).add hspecI).congr ?_
    filter_upwards with y
    simp only [Work.BoseFixB1B.cubeWord, Work.UBBInputs8.tBwordInd, Work.UBBInputs8.tBwordKinInd,
      Pi.add_apply]
  · calc Work.BoseFixB1B.cubeWord M L d ε c u (slotPiece (dlBox L d u) S Φ)
        = Work.SmallBoxTBWord.tbGapCoeff (L * d) ε
            * Work.UBBInputs8.cnPlusBoxInd L (dlBox L d u) (boxMass L d u)
                (slotPiece (dlBox L d u) S Φ)
          + Work.UBBInputs8.tBdiagFormInd L (dlBox L d u) (boxMass L d u) (chiSmallB M L d u)
                (Submission.BoseGases.fsKinCoeff c) (slotPiece (dlBox L d u) S Φ) := by
          simp only [Work.BoseFixB1B.cubeWord, Work.UBBInputs8.tBwordInd,
            Work.UBBInputs8.tBwordKinInd]
      _ = Work.SmallBoxTBWord.tbGapCoeff (L * d) ε
            * (∫ y in slotOutside L (dlBox L d u) S,
                Work.UBBInputs8.cnPlusBoxInd L (dlBox L d u) (boxMass L d u)
                  (slotFibreState S e (slotPiece (dlBox L d u) S Φ) y))
          + (∫ y in slotOutside L (dlBox L d u) S,
                Work.UBBInputs8.tBdiagFormInd L (dlBox L d u) (boxMass L d u) (chiSmallB M L d u)
                  (Submission.BoseGases.fsKinCoeff c)
                  (slotFibreState S e (slotPiece (dlBox L d u) S Φ) y)) := by
          rw [hgap, hspec]
      _ = ∫ y in slotOutside L (dlBox L d u) S,
            (Work.SmallBoxTBWord.tbGapCoeff (L * d) ε
              * Work.UBBInputs8.cnPlusBoxInd L (dlBox L d u) (boxMass L d u)
                  (slotFibreState S e (slotPiece (dlBox L d u) S Φ) y)
            + Work.UBBInputs8.tBdiagFormInd L (dlBox L d u) (boxMass L d u) (chiSmallB M L d u)
                  (Submission.BoseGases.fsKinCoeff c)
                  (slotFibreState S e (slotPiece (dlBox L d u) S Φ) y)) := by
          rw [MeasureTheory.integral_add (hgapI.const_mul (Work.SmallBoxTBWord.tbGapCoeff (L * d) ε))
            hspecI, MeasureTheory.integral_const_mul]
      _ = ∫ y in slotOutside L (dlBox L d u) S,
            Work.BoseFixB1B.cubeWord M L d ε c u
              (slotFibreState S e (slotPiece (dlBox L d u) S Φ) y) := by
          refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
          simp only [Work.BoseFixB1B.cubeWord, Work.UBBInputs8.tBwordInd,
            Work.UBBInputs8.tBwordKinInd]

/-- **THE TARGET**: the matched (cube-cutoff) sliding kinetic word `sbKinCube` factorises at the
slot fibres. -/
theorem sbKinCube_slotFibre {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v) (hv : 0 ≤ v)
    (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      ∀ u : EuclideanSpace ℝ (Fin 3), u ∈ Work.SmallBoxSliding.goodSet (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          ((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d) μ →
      ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))),
        ∀ (S : Finset (Fin n)), 0 < S.card → ∀ e : Work.PerSector.SlotIn n S ≃ Fin S.card,
          MeasureTheory.Integrable
            (fun y : Work.PerSector.SlotOut n S → EuclideanSpace ℝ (Fin 3) =>
              Work.BoseFixB1B.sbKinCube v μ u (Work.SlotWord.pieceFibre (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                ((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d) u) S e (Φ : Submission.BoseGases.X n → ℝ) y))
            ((MeasureTheory.volume : MeasureTheory.Measure (Work.PerSector.SlotOut n S → EuclideanSpace ℝ (Fin 3))).restrict
              (Work.PerSector.slotOutside (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d) u) S))
          ∧ Work.BoseFixB1B.sbKinCube v μ u
              (Work.PerSector.slotPiece (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                ((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d) u) S (Φ : Submission.BoseGases.X n → ℝ))
            = ∫ y in Work.PerSector.slotOutside (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d) u) S,
                Work.BoseFixB1B.sbKinCube v μ u (Work.SlotWord.pieceFibre (Submission.BoseGases.dlBox (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  ((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d) u) S e (Φ : Submission.BoseGases.X n → ℝ) y) := by
  classical
  refine ⟨1, one_pos, fun μ hμ u hu n Φ S hS e => ?_⟩
  have hL : 0 < Work.BoseBox.sideAt μ (_root_.BoseGases.a v) := Work.BoseFixB1.adm_ell_pos hμ
  have hd : 0 < (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d := Work.BoseFixB1.adm_d_pos hμ
  have hM : 4 ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M := by
    simp only [Work.BoseBox.paramsAt, Work.BoseBox.fsParams, Work.BoseBox.mValue]
    norm_num
  have hmain := cubeWord_fibre (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M hM
    (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d)
    ((Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT) (Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v))
    hL hd u S (Φ : Submission.BoseGases.X n → ℝ) Φ.contDiff e
  simpa only [Work.BoseFixB1B.sbKinCube, Work.BoseFixB1B.cubeSpectral, Work.BoseFixB1B.cubeWord,
    Work.BoseFixB1.bGapCoeff, Work.BoseFixB1.bSide, Work.BoseFixB1.bD, Work.BoseFixB1.bM,
    Work.BoseFixB1.bA, Work.BoseFixB1.bV, Work.UBBInputs8.tBwordInd, Work.UBBInputs8.tBwordKinInd,
    Work.SlotWord.pieceFibre] using hmain

end Work.BoseB1Cube
