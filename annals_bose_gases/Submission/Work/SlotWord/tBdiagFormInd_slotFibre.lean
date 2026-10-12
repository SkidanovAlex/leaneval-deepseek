import Mathlib.Tactic.Have
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.SpecialFunctions.Inner
import Submission.Work.SlotWord.ThetaDefs
import Submission.Work.SlotWord.aemeasurable_fibreAmpEnergy
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.SlotWord.tBdiagFormInd_slotFibre`
-/

namespace Work.SlotWord

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open Submission.BoseGases
open BoseGases
open Work.PerSector
open Work.UBB
open Work.SmallBoxSliding
open Work.UBBInputs8
open Work.FockBridge

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

variable {N : ℕ}

/-! ## 0. Auxiliary definitions and elementary facts -/

/-- The ambient amplitude energy of the `i`-th slot. -/
noncomputable def slotAmpEnergy (L d : ℝ) (u : ℝ³) (S : Finset (Fin N)) (Φ : X N → ℝ)
    (i : Fin N) (p : ℝ³) : ℝ :=
  ∫ x in abox N L, ‖Work.SmallBoxTBWord.tBamp (chiB L d u) p
      (boxQInd (boxMass L d u) (dlBox L d u) i (slotPiece (dlBox L d u) S Φ)) i x‖ ^ 2

/-- The fibre amplitude energy of the `j`-th fibre slot. -/
noncomputable def fibreAmpEnergy (L d : ℝ) (u : ℝ³) (S : Finset (Fin N)) (Φ : X N → ℝ)
    (e : SlotIn N S ≃ Fin S.card) (j : Fin S.card) (p : ℝ³) (y : SlotOut N S → ℝ³) : ℝ :=
  ∫ z in abox S.card L, ‖Work.SmallBoxTBWord.tBamp (chiB L d u) p
      (boxQInd (boxMass L d u) (dlBox L d u) j
        (slotFibreState S e (slotPiece (dlBox L d u) S Φ) y)) j z‖ ^ 2

theorem tBdiagFibreJoint_eq (L d : ℝ) (u : ℝ³) (S : Finset (Fin N)) (Φ : X N → ℝ)
    (e : SlotIn N S ≃ Fin S.card) (F : ℝ → ℝ) (p : ℝ³) (y : SlotOut N S → ℝ³) :
    tBdiagFibreJoint L d u S Φ e F p y
      = ∑ j : Fin S.card, F ‖p‖ * ((L ^ 3)⁻¹ * fibreAmpEnergy L d u S Φ e j p y) := rfl

theorem tBdiagFormInd_fibre_eq (L d : ℝ) (u : ℝ³) (S : Finset (Fin N)) (Φ : X N → ℝ)
    (e : SlotIn N S ≃ Fin S.card) (F : ℝ → ℝ) (y : SlotOut N S → ℝ³) :
    tBdiagFormInd L (dlBox L d u) (boxMass L d u) (chiB L d u) F
        (slotFibreState S e (slotPiece (dlBox L d u) S Φ) y)
      = ∑ j : Fin S.card,
          ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : ℝ³, F ‖p‖ * ((L ^ 3)⁻¹ * fibreAmpEnergy L d u S Φ e j p y) :=
  rfl

@[simp] theorem tBamp_zero {N : ℕ} (χ : ℝ³ → ℝ) (p : ℝ³) (i : Fin N) (x : X N) :
    Work.SmallBoxTBWord.tBamp χ p (0 : X N → ℝ) i x = 0 := by
  simp [Work.SmallBoxTBWord.tBamp]

theorem boxQInd_slotPiece_eq_zero_of_notMem {N : ℕ} (L d : ℝ) (u : ℝ³)
    (S : Finset (Fin N)) (Φ : X N → ℝ) (i : Fin N) (hi : i ∉ S) :
    boxQInd (boxMass L d u) (dlBox L d u) i (slotPiece (dlBox L d u) S Φ) = 0 := by
  funext x
  refine boxQInd_slotPiece_eq_zero_of_notMem_slotShiftSet (measurableSet_dlBox L d u) i S ?_
  intro hx
  exact hi hx.1

theorem slotAmpEnergy_eq_zero_of_notMem {N : ℕ} (L d : ℝ) (u : ℝ³)
    (S : Finset (Fin N)) (Φ : X N → ℝ) (i : Fin N) (hi : i ∉ S) (p : ℝ³) :
    slotAmpEnergy L d u S Φ i p = 0 := by
  unfold slotAmpEnergy
  rw [boxQInd_slotPiece_eq_zero_of_notMem L d u S Φ i hi]
  simp


/-! ## 1. The per-slot word integrand of the fibre -/

open Classical in
/-- The `j`-th summand of the right-hand `p`-integrand. -/
noncomputable def fibreWordIntegrand (L d : ℝ) (u : ℝ³) (S : Finset (Fin N)) (Φ : X N → ℝ)
    (e : SlotIn N S ≃ Fin S.card) (F : ℝ → ℝ) (j : Fin S.card) (p : ℝ³)
    (y : SlotOut N S → ℝ³) : ℝ :=
  F ‖p‖ * ((L ^ 3)⁻¹ * fibreAmpEnergy L d u S Φ e j p y)

theorem tBdiagFibreJoint_eq_sum (L d : ℝ) (u : ℝ³) (S : Finset (Fin N)) (Φ : X N → ℝ)
    (e : SlotIn N S ≃ Fin S.card) (F : ℝ → ℝ) (p : ℝ³) (y : SlotOut N S → ℝ³) :
    tBdiagFibreJoint L d u S Φ e F p y
      = ∑ j : Fin S.card, fibreWordIntegrand L d u S Φ e F j p y := rfl

theorem fibreWordIntegrand_nonneg {L d : ℝ} {u : ℝ³} {S : Finset (Fin N)} {Φ : X N → ℝ}
    {e : SlotIn N S ≃ Fin S.card} {F : ℝ → ℝ} (hF : ∀ r, 0 ≤ F r) (hL : 0 < L)
    (j : Fin S.card) (p : ℝ³) (y : SlotOut N S → ℝ³) :
    0 ≤ fibreWordIntegrand L d u S Φ e F j p y := by
  unfold fibreWordIntegrand
  refine mul_nonneg (hF _) (mul_nonneg ?_ ?_)
  · positivity
  · unfold fibreAmpEnergy
    exact MeasureTheory.integral_nonneg (fun z => sq_nonneg _)

/-! ## 2. The reindexing of the slot sum -/

theorem sum_slotAmpEnergy_eq_sum_fibre {N : ℕ} (L d : ℝ) (u : ℝ³) (S : Finset (Fin N))
    (Φ : X N → ℝ) (e : SlotIn N S ≃ Fin S.card) (F : ℝ → ℝ) :
    (∑ i : Fin N, ((2 * Real.pi) ^ 3)⁻¹ *
        ∫ p : ℝ³, F ‖p‖ * ((L ^ 3)⁻¹ * slotAmpEnergy L d u S Φ i p))
      = ∑ j : Fin S.card, ((2 * Real.pi) ^ 3)⁻¹ *
        ∫ p : ℝ³, F ‖p‖ * ((L ^ 3)⁻¹ * slotAmpEnergy L d u S Φ (e.symm j).1 p) := by
  classical
  set g : Fin N → ℝ := fun i => ((2 * Real.pi) ^ 3)⁻¹ *
      ∫ p : ℝ³, F ‖p‖ * ((L ^ 3)⁻¹ * slotAmpEnergy L d u S Φ i p) with hg
  have hzero : ∀ i : Fin N, i ∉ S → g i = 0 := by
    intro i hi
    simp only [hg]
    have hpt : (fun p : ℝ³ => F ‖p‖ * ((L ^ 3)⁻¹ * slotAmpEnergy L d u S Φ i p)) = fun _ => 0 := by
      funext p
      rw [slotAmpEnergy_eq_zero_of_notMem L d u S Φ i hi]
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
    Fintype.sum_equiv e (fun i : SlotIn N S => g i.1)
      (fun j : Fin S.card => g (e.symm j).1) (fun i => by simp)
  rw [h1, h2, h3]

/-! ## 4. The outside measure -/

/-- The measure on the outside configurations used throughout. -/
noncomputable def slotOutMeasure (L d : ℝ) (u : ℝ³) (S : Finset (Fin N)) :
    MeasureTheory.Measure (SlotOut N S → ℝ³) :=
  (MeasureTheory.volume : MeasureTheory.Measure (SlotOut N S → ℝ³)).restrict
    (slotOutside L (dlBox L d u) S)

@[simp] theorem slotOutMeasure_def (L d : ℝ) (u : ℝ³) (S : Finset (Fin N)) :
    slotOutMeasure L d u S
      = (MeasureTheory.volume : MeasureTheory.Measure (SlotOut N S → ℝ³)).restrict
          (slotOutside L (dlBox L d u) S) := rfl

instance (L d : ℝ) (u : ℝ³) (S : Finset (Fin N)) :
    MeasureTheory.SFinite (slotOutMeasure L d u S) := by
  rw [slotOutMeasure_def]
  infer_instance

/-! ## 5. The right-hand side as the sum of the fibre slots -/

theorem integral_rHS_eq_sum {N : ℕ} (L d : ℝ) (hL : 0 < L) (hd : 0 < d) (u : ℝ³)
    (S : Finset (Fin N)) (Φ : X N → ℝ) (hΦ : Continuous Φ) (e : SlotIn N S ≃ Fin S.card)
    (F : ℝ → ℝ) (hF : ∀ r, 0 ≤ F r) (hFm : Measurable F)
    (hM1 : ∀ j : Fin S.card, MeasureTheory.AEStronglyMeasurable
      (fun q : ℝ³ × (SlotOut N S → ℝ³) => fibreAmpEnergy L d u S Φ e j q.1 q.2)
      ((MeasureTheory.volume : MeasureTheory.Measure ℝ³).prod (slotOutMeasure L d u S)))
    (hswap : MeasureTheory.Integrable
      (fun q : ℝ³ × (SlotOut N S → ℝ³) => tBdiagFibreJoint L d u S Φ e F q.1 q.2)
      ((MeasureTheory.volume : MeasureTheory.Measure ℝ³).prod (slotOutMeasure L d u S))) :
    (∫ y in slotOutside L (dlBox L d u) S,
        tBdiagFormInd L (dlBox L d u) (boxMass L d u) (chiB L d u) F
          (slotFibreState S e (slotPiece (dlBox L d u) S Φ) y))
      = ((2 * Real.pi) ^ 3)⁻¹ * ∑ j : Fin S.card,
          ∫ p : ℝ³, ∫ y in slotOutside L (dlBox L d u) S,
            fibreWordIntegrand L d u S Φ e F j p y := by
  classical
  -- (a) a.e. strong measurability of the summands
  have haesm : ∀ j : Fin S.card,
      MeasureTheory.AEStronglyMeasurable
        (Function.uncurry (fun (p : ℝ³) (y : SlotOut N S → ℝ³) =>
          fibreWordIntegrand L d u S Φ e F j p y))
        ((MeasureTheory.volume : MeasureTheory.Measure ℝ³).prod (slotOutMeasure L d u S)) := by
    intro j
    have hE : MeasureTheory.AEStronglyMeasurable
        (fun q : ℝ³ × (SlotOut N S → ℝ³) => fibreAmpEnergy L d u S Φ e j q.1 q.2)
        ((MeasureTheory.volume : MeasureTheory.Measure ℝ³).prod (slotOutMeasure L d u S)) :=
      hM1 j
    have hFn : MeasureTheory.AEStronglyMeasurable
        (fun q : ℝ³ × (SlotOut N S → ℝ³) => F ‖q.1‖)
        ((MeasureTheory.volume : MeasureTheory.Measure ℝ³).prod (slotOutMeasure L d u S)) :=
      (hFm.comp ((continuous_norm.measurable).comp measurable_fst)).aestronglyMeasurable
    have this := hFn.mul (hE.const_mul ((L ^ 3)⁻¹))
    have heq : ((fun q : ℝ³ × (SlotOut N S → ℝ³) => F ‖q.1‖) *
          (fun q : ℝ³ × (SlotOut N S → ℝ³) => (L ^ 3)⁻¹ * fibreAmpEnergy L d u S Φ e j q.1 q.2))
        = Function.uncurry (fun (p : ℝ³) (y : SlotOut N S → ℝ³) =>
            fibreWordIntegrand L d u S Φ e F j p y) := by
      funext q; rfl
    rwa [heq] at this
  -- (b) integrability of the summands
  have hint : ∀ j : Fin S.card,
      MeasureTheory.Integrable
        (Function.uncurry (fun (p : ℝ³) (y : SlotOut N S → ℝ³) =>
          fibreWordIntegrand L d u S Φ e F j p y))
        ((MeasureTheory.volume : MeasureTheory.Measure ℝ³).prod (slotOutMeasure L d u S)) := by
    intro j
    refine MeasureTheory.Integrable.mono' hswap (haesm j) ?_
    refine Filter.Eventually.of_forall (fun q => ?_)
    have hle : fibreWordIntegrand L d u S Φ e F j q.1 q.2
        ≤ ∑ j' : Fin S.card, fibreWordIntegrand L d u S Φ e F j' q.1 q.2 :=
      Finset.single_le_sum (fun j' _ => fibreWordIntegrand_nonneg hF hL j' q.1 q.2)
        (Finset.mem_univ j)
    change ‖fibreWordIntegrand L d u S Φ e F j q.1 q.2‖
      ≤ tBdiagFibreJoint L d u S Φ e F q.1 q.2
    rw [Real.norm_of_nonneg (fibreWordIntegrand_nonneg hF hL j q.1 q.2), tBdiagFibreJoint_eq_sum]
    exact hle
  -- (c) a.e. `y`, integrability in `p`
  have hsec_y : ∀ᵐ y ∂(slotOutMeasure L d u S), ∀ j : Fin S.card,
      MeasureTheory.Integrable (fun p : ℝ³ => fibreWordIntegrand L d u S Φ e F j p y)
        MeasureTheory.volume := by
    have hsm : ∀ᵐ y ∂(slotOutMeasure L d u S), ∀ j : Fin S.card,
        MeasureTheory.AEStronglyMeasurable
          (fun p : ℝ³ => fibreWordIntegrand L d u S Φ e F j p y) MeasureTheory.volume :=
      Filter.eventually_all.2 (fun j => (haesm j).prodMk_right)
    have hJint : ∀ᵐ y ∂(slotOutMeasure L d u S),
        MeasureTheory.Integrable (fun p : ℝ³ => tBdiagFibreJoint L d u S Φ e F p y)
          MeasureTheory.volume := hswap.prod_left_ae
    filter_upwards [hsm, hJint] with y hsm'y hJy
    intro j
    refine MeasureTheory.Integrable.mono' hJy (hsm'y j) ?_
    refine Filter.Eventually.of_forall (fun p => ?_)
    have hle : fibreWordIntegrand L d u S Φ e F j p y
        ≤ ∑ j' : Fin S.card, fibreWordIntegrand L d u S Φ e F j' p y :=
      Finset.single_le_sum (fun j' _ => fibreWordIntegrand_nonneg hF hL j' p y)
        (Finset.mem_univ j)
    change ‖fibreWordIntegrand L d u S Φ e F j p y‖
      ≤ tBdiagFibreJoint L d u S Φ e F p y
    rw [Real.norm_of_nonneg (fibreWordIntegrand_nonneg hF hL j p y), tBdiagFibreJoint_eq_sum]
    exact hle
  -- (d) a.e. `p`, integrability in `y`
  have hsec_p : ∀ᵐ p ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ³), ∀ j : Fin S.card,
      MeasureTheory.Integrable (fun y : SlotOut N S → ℝ³ => fibreWordIntegrand L d u S Φ e F j p y)
        (slotOutMeasure L d u S) := by
    have hsm : ∀ᵐ p ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ³), ∀ j : Fin S.card,
        MeasureTheory.AEStronglyMeasurable
          (fun y : SlotOut N S → ℝ³ => fibreWordIntegrand L d u S Φ e F j p y)
          (slotOutMeasure L d u S) :=
      Filter.eventually_all.2 (fun j => (haesm j).prodMk_left)
    have hJint : ∀ᵐ p ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ³),
        MeasureTheory.Integrable (fun y : SlotOut N S → ℝ³ => tBdiagFibreJoint L d u S Φ e F p y)
          (slotOutMeasure L d u S) := hswap.prod_right_ae
    filter_upwards [hsm, hJint] with p hsm'p hJp
    intro j
    refine MeasureTheory.Integrable.mono' hJp (hsm'p j) ?_
    refine Filter.Eventually.of_forall (fun y => ?_)
    have hle : fibreWordIntegrand L d u S Φ e F j p y
        ≤ ∑ j' : Fin S.card, fibreWordIntegrand L d u S Φ e F j' p y :=
      Finset.single_le_sum (fun j' _ => fibreWordIntegrand_nonneg hF hL j' p y)
        (Finset.mem_univ j)
    change ‖fibreWordIntegrand L d u S Φ e F j p y‖
      ≤ tBdiagFibreJoint L d u S Φ e F p y
    rw [Real.norm_of_nonneg (fibreWordIntegrand_nonneg hF hL j p y), tBdiagFibreJoint_eq_sum]
    exact hle
  -- the two almost-everywhere keys
  have key_y : ∀ᵐ y ∂(slotOutMeasure L d u S),
      tBdiagFormInd L (dlBox L d u) (boxMass L d u) (chiB L d u) F
          (slotFibreState S e (slotPiece (dlBox L d u) S Φ) y)
        = ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : ℝ³, tBdiagFibreJoint L d u S Φ e F p y := by
    filter_upwards [hsec_y] with y hy
    rw [tBdiagFormInd_fibre_eq]
    have hsum : (∫ p : ℝ³, tBdiagFibreJoint L d u S Φ e F p y)
        = ∑ j : Fin S.card, ∫ p : ℝ³, fibreWordIntegrand L d u S Φ e F j p y := by
      rw [show (∫ p : ℝ³, tBdiagFibreJoint L d u S Φ e F p y)
          = ∫ p : ℝ³, ∑ j : Fin S.card, fibreWordIntegrand L d u S Φ e F j p y from by
        exact MeasureTheory.integral_congr_ae
          (Filter.Eventually.of_forall (fun p => tBdiagFibreJoint_eq_sum L d u S Φ e F p y))]
      exact MeasureTheory.integral_finsetSum Finset.univ (fun i _ => hy i)
    rw [hsum, Finset.mul_sum]
    simp only [fibreWordIntegrand]
  have key_p : ∀ᵐ p ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ³),
      (∫ y, tBdiagFibreJoint L d u S Φ e F p y ∂(slotOutMeasure L d u S))
        = ∑ j : Fin S.card,
            ∫ y, fibreWordIntegrand L d u S Φ e F j p y ∂(slotOutMeasure L d u S) := by
    filter_upwards [hsec_p] with p hp
    rw [show (∫ y, tBdiagFibreJoint L d u S Φ e F p y ∂(slotOutMeasure L d u S))
        = ∫ y, ∑ j : Fin S.card,
            fibreWordIntegrand L d u S Φ e F j p y ∂(slotOutMeasure L d u S) from by
      exact MeasureTheory.integral_congr_ae
        (Filter.Eventually.of_forall (fun y => tBdiagFibreJoint_eq_sum L d u S Φ e F p y))]
    exact MeasureTheory.integral_finsetSum Finset.univ (fun i _ => hp i)
  -- the chain
  have hFint : ∀ j : Fin S.card,
      MeasureTheory.Integrable
        (fun p : ℝ³ => ∫ y, fibreWordIntegrand L d u S Φ e F j p y
          ∂(slotOutMeasure L d u S)) MeasureTheory.volume :=
    fun j => (hint j).integral_prod_left
  calc (∫ y in slotOutside L (dlBox L d u) S,
        tBdiagFormInd L (dlBox L d u) (boxMass L d u) (chiB L d u) F
          (slotFibreState S e (slotPiece (dlBox L d u) S Φ) y))
      = ∫ y, ((2 * Real.pi) ^ 3)⁻¹ * (∫ p : ℝ³, tBdiagFibreJoint L d u S Φ e F p y)
            ∂(slotOutMeasure L d u S) :=
        MeasureTheory.integral_congr_ae key_y
    _ = ((2 * Real.pi) ^ 3)⁻¹ * ∫ y, (∫ p : ℝ³, tBdiagFibreJoint L d u S Φ e F p y)
            ∂(slotOutMeasure L d u S) :=
        MeasureTheory.integral_const_mul _ _
    _ = ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : ℝ³, (∫ y, tBdiagFibreJoint L d u S Φ e F p y
            ∂(slotOutMeasure L d u S)) :=
        congrArg (fun t => ((2 * Real.pi) ^ 3)⁻¹ * t)
          (MeasureTheory.integral_integral_swap hswap).symm
    _ = ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : ℝ³, ∑ j : Fin S.card,
          (∫ y, fibreWordIntegrand L d u S Φ e F j p y
            ∂(slotOutMeasure L d u S)) :=
        congrArg _ (MeasureTheory.integral_congr_ae key_p)
    _ = ((2 * Real.pi) ^ 3)⁻¹ * ∑ j : Fin S.card,
          ∫ p : ℝ³, (∫ y, fibreWordIntegrand L d u S Φ e F j p y
            ∂(slotOutMeasure L d u S)) := by
        rw [MeasureTheory.integral_finsetSum Finset.univ (fun i _ => hFint i)]
    _ = ((2 * Real.pi) ^ 3)⁻¹ * ∑ j : Fin S.card,
          ∫ p : ℝ³, ∫ y in slotOutside L (dlBox L d u) S,
            fibreWordIntegrand L d u S Φ e F j p y := rfl


/-! ## 6. The ambient amplitude energy is integrable on the box -/

theorem measurableSet_slotSet {N : ℕ} {A : Set ℝ³} (hA : MeasurableSet A) (S : Finset (Fin N)) :
    MeasurableSet (slotSet A S) := by
  have h : slotSet A S
      = ⋂ i : Fin N, (if i ∈ S then {x : X N | x i ∈ A} else {x : X N | x i ∉ A}) := by
    ext x
    simp only [slotSet, Set.mem_ofPred_eq, Set.mem_iInter]
    constructor
    · intro h i
      by_cases hi : i ∈ S
      · rw [if_pos hi]; exact (h i).mpr hi
      · rw [if_neg hi]; exact fun hc => hi ((h i).mp hc)
    · intro h i
      by_cases hi : i ∈ S
      · have hh := h i
        rw [if_pos hi] at hh
        exact ⟨fun _ => hi, fun _ => hh⟩
      · constructor
        · intro hc
          have hh := h i
          rw [if_neg hi] at hh
          exact absurd hc hh
        · intro hci; exact absurd hci hi
  rw [h]
  refine MeasurableSet.iInter (fun i => ?_)
  by_cases hi : i ∈ S
  · rw [if_pos hi]; exact (measurable_pi_apply i) hA
  · rw [if_neg hi]; exact ((measurable_pi_apply i) hA).compl

/-- **The box mean of a function bounded by `C` on the box is bounded by `C`.** -/
theorem abs_mul_inv_mul_setIntegral_le {A : Set ℝ³} {g : ℝ³ → ℝ} {C volA : ℝ}
    (hA : MeasurableSet A) (hvol : volA = (MeasureTheory.volume : MeasureTheory.Measure ℝ³).real A)
    (hfin : (MeasureTheory.volume : MeasureTheory.Measure ℝ³) A < ⊤) (hC : 0 ≤ C)
    (hg : ∀ z ∈ A, |g z| ≤ C) :
    |(1 / volA) * ∫ z in A, g z| ≤ C := by
  have hvol0 : 0 ≤ volA := by rw [hvol]; exact MeasureTheory.measureReal_nonneg
  rcases eq_or_lt_of_le hvol0 with hzero | hpos
  · rw [← hzero, one_div, inv_zero, zero_mul, abs_zero]; exact hC
  · have hI : |∫ z in A, g z| ≤ ∫ z in A, |g z| := by
      rw [show (∫ z in A, g z)
            = ∫ z, g z ∂((MeasureTheory.volume : MeasureTheory.Measure ℝ³).restrict A) from rfl,
        show (∫ z in A, |g z|)
            = ∫ z, |g z| ∂((MeasureTheory.volume : MeasureTheory.Measure ℝ³).restrict A) from rfl]
      exact MeasureTheory.norm_integral_le_integral_norm g
    have hConstInt : MeasureTheory.Integrable (fun _ : ℝ³ => C)
        ((MeasureTheory.volume : MeasureTheory.Measure ℝ³).restrict A) := by
      rw [MeasureTheory.integrable_const_iff]
      exact Or.inr (MeasureTheory.isFiniteMeasure_restrict.mpr (ne_of_lt hfin))
    have hmono : (∫ z in A, |g z|) ≤ ∫ z in A, C :=
      MeasureTheory.integral_mono_of_nonneg (Filter.Eventually.of_forall (fun z => abs_nonneg _))
        hConstInt (by
          filter_upwards [MeasureTheory.ae_restrict_mem hA] with z hz
          exact hg z hz)
    have hCv : (∫ z in A, C) = C * volA := by
      rw [MeasureTheory.setIntegral_const, smul_eq_mul, ← hvol]
      ring
    calc |(1 / volA) * ∫ z in A, g z|
        = (1 / volA) * |∫ z in A, g z| := by
          rw [abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ 1 / volA)]
      _ ≤ (1 / volA) * (C * volA) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact hI.trans (hmono.trans (le_of_eq hCv))
      _ = C := by
          rw [one_div, mul_comm C volA, inv_mul_cancel_left₀ (ne_of_gt hpos)]

/-- **The mean-free projection is bounded on the box.** -/
theorem abs_boxQInd_le {N : ℕ} (L : ℝ) {A : Set ℝ³} (hA : MeasurableSet A) {volA : ℝ}
    (hvol : volA = (MeasureTheory.volume : MeasureTheory.Measure ℝ³).real A)
    (hfin : (MeasureTheory.volume : MeasureTheory.Measure ℝ³) A < ⊤)
    (hAL : A ⊆ Submission.BoseGases.acube L) {Ψ : X N → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (hΨ : ∀ x ∈ Submission.BoseGases.abox N L, |Ψ x| ≤ C) (i : Fin N) :
    ∀ x ∈ Submission.BoseGases.abox N L,
      |Work.UBBInputs8.boxQInd volA A i Ψ x| ≤ 2 * C := by
  intro x hx
  rw [Submission.BoseGases.mem_abox_iff] at hx
  have hQeq : Work.UBBInputs8.boxQInd volA A i Ψ x
      = A.indicator (fun _ => (1 : ℝ)) (x i)
        * (Ψ x - (1 / volA) * ∫ z in A, Ψ (Function.update x i z)) := by
    simp only [Work.UBBInputs8.boxQInd, Work.UBBInputs8.boxPInd]
    ring
  rw [hQeq]
  by_cases hxi : x i ∈ A
  · rw [Set.indicator_of_mem hxi, one_mul]
    have h1 : |Ψ x| ≤ C := hΨ x (by rw [Submission.BoseGases.mem_abox_iff]; exact hx)
    have h2 : |(1 / volA) * ∫ z in A, Ψ (Function.update x i z)| ≤ C := by
      refine abs_mul_inv_mul_setIntegral_le hA hvol hfin hC ?_
      intro z hz
      refine hΨ (Function.update x i z) ?_
      rw [Submission.BoseGases.mem_abox_iff]
      intro j
      rw [Function.update_apply]
      by_cases hj : j = i
      · rw [if_pos hj]; exact hAL hz
      · rw [if_neg hj]; exact hx j
    calc |Ψ x - (1 / volA) * ∫ z in A, Ψ (Function.update x i z)|
        ≤ |Ψ x| + |(1 / volA) * ∫ z in A, Ψ (Function.update x i z)| := abs_sub _ _
      _ ≤ C + C := add_le_add h1 h2
      _ = 2 * C := by ring
  · rw [Set.indicator_of_notMem hxi, zero_mul, abs_zero]; linarith


/-- The sliding cutoff is integrable. -/
theorem integrable_abs_chiB (L d : ℝ) (hL : 0 < L) (hd : 0 < d) (u : ℝ³) :
    MeasureTheory.Integrable (fun w : ℝ³ => |Submission.BoseGases.chiB L d u w|) := by
  have h : MeasureTheory.Integrable (Submission.BoseGases.chiB L d u) :=
    (Work.SmallBoxTBWord.contDiff_chiB hL hd u).continuous.integrable_of_hasCompactSupport
      (Work.SmallBoxTBWord.hasCompactSupport_chiB hL hd u)
  simpa only [Real.norm_eq_abs] using h.norm

/-- **The ambient amplitude energy of the slot piece is integrable on the box.** -/
theorem integrableOn_slotAmpEnergy {N : ℕ} (L d : ℝ) (hL : 0 < L) (hd : 0 < d) (u : ℝ³)
    (S : Finset (Fin N)) (Φ : X N → ℝ) (hΦ : Continuous Φ) (i : Fin N) (p : ℝ³) :
    MeasureTheory.IntegrableOn
      (fun x : X N => ‖Work.SmallBoxTBWord.tBamp (Submission.BoseGases.chiB L d u) p
        (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass L d u)
          (Submission.BoseGases.dlBox L d u) i
          (Work.PerSector.slotPiece (Submission.BoseGases.dlBox L d u) S Φ)) i x‖ ^ 2)
      (Submission.BoseGases.abox N L) := by
  classical
  -- ## A bound on the state on the box
  obtain ⟨B₀, hB₀⟩ := (Submission.BoseGases.abox_compact N hL).exists_bound_of_continuousOn
    (s := Submission.BoseGases.abox N L) (f := Φ) hΦ.continuousOn
  set B : ℝ := max B₀ 0 with hBdef
  have hB0 : 0 ≤ B := le_max_right _ _
  have hB : ∀ x ∈ Submission.BoseGases.abox N L, |Φ x| ≤ B := by
    intro x hx
    rw [← Real.norm_eq_abs]
    exact (hB₀ x hx).trans (le_max_left _ _)
  have hcube_lt : (MeasureTheory.volume : MeasureTheory.Measure ℝ³)
      (Submission.BoseGases.acube L) < ⊤ := Submission.BoseGases.acube_lt_top L hL.le
  have hAfin : (MeasureTheory.volume : MeasureTheory.Measure ℝ³)
      (Submission.BoseGases.dlBox L d u) < ⊤ :=
    lt_of_le_of_lt (measure_mono (fun x hx =>
      (Submission.BoseGases.mem_dlBox_iff L d u x).mp hx |>.1)) hcube_lt
  have hboxFin : IsFiniteMeasure
      ((MeasureTheory.volume : MeasureTheory.Measure (X N)).restrict
        (Submission.BoseGases.abox N L)) := by
    rw [Submission.BoseGases.restrict_abox_eq_pi N L]
    infer_instance
  have hΨb : ∀ x ∈ Submission.BoseGases.abox N L,
      |Work.PerSector.slotPiece (Submission.BoseGases.dlBox L d u) S Φ x| ≤ B := by
    intro x hx
    rw [Work.PerSector.slotPiece]
    by_cases hxS : x ∈ Work.PerSector.slotSet (Submission.BoseGases.dlBox L d u) S
    · rw [Set.indicator_of_mem hxS]; exact hB x hx
    · rw [Set.indicator_of_notMem hxS, abs_zero]; exact hB0
  have hQb : ∀ x ∈ Submission.BoseGases.abox N L,
      |Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass L d u)
        (Submission.BoseGases.dlBox L d u) i
        (Work.PerSector.slotPiece (Submission.BoseGases.dlBox L d u) S Φ) x| ≤ 2 * B :=
    abs_boxQInd_le L (measurableSet_dlBox L d u) (boxMass_eq_measureReal L d u) hAfin
      (fun x hx => (Submission.BoseGases.mem_dlBox_iff L d u x).mp hx |>.1) hB0 hΨb i
  -- ## The amplitude is bounded
  have hχint : MeasureTheory.Integrable
      (fun w : ℝ³ => (2 * B) * |Submission.BoseGases.chiB L d u w|) :=
    (integrable_abs_chiB L d hL hd u).const_mul (2 * B)
  have htb : ∀ x ∈ Submission.BoseGases.abox N L,
      ‖Work.SmallBoxTBWord.tBamp (Submission.BoseGases.chiB L d u) p
        (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass L d u)
          (Submission.BoseGases.dlBox L d u) i
          (Work.PerSector.slotPiece (Submission.BoseGases.dlBox L d u) S Φ)) i x‖
      ≤ 2 * B * ∫ w : ℝ³, |Submission.BoseGases.chiB L d u w| := by
    intro x hx
    rw [Work.SmallBoxTBWord.tBamp]
    refine (MeasureTheory.norm_integral_le_integral_norm _).trans ?_
    have hpt : ∀ w : ℝ³,
        ‖(Submission.BoseGases.chiB L d u w : ℂ) *
            Complex.exp (-(Complex.I * (inner ℝ p w : ℂ))) *
            ((Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass L d u)
              (Submission.BoseGases.dlBox L d u) i
              (Work.PerSector.slotPiece (Submission.BoseGases.dlBox L d u) S Φ)
              (Function.update x i w)) : ℂ)‖
          ≤ (2 * B) * |Submission.BoseGases.chiB L d u w| := by
      intro w
      by_cases hw : Submission.BoseGases.chiB L d u w = 0
      · simp [hw]
      · have hwA : w ∈ Submission.BoseGases.dlBox L d u :=
          Submission.BoseGases.chiB_support_mem hL hd u w hw
        have hmem : Function.update x i w ∈ Submission.BoseGases.abox N L := by
          rw [Submission.BoseGases.mem_abox_iff] at hx ⊢
          intro j
          rw [Function.update_apply]
          by_cases hj : j = i
          · rw [if_pos hj]
            exact (Submission.BoseGases.mem_dlBox_iff L d u w).mp hwA |>.1
          · rw [if_neg hj]; exact hx j
        have hQx := hQb _ hmem
        have h1 : ‖(Submission.BoseGases.chiB L d u w : ℂ) *
              Complex.exp (-(Complex.I * (inner ℝ p w : ℂ))) *
              ((Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass L d u)
                (Submission.BoseGases.dlBox L d u) i
                (Work.PerSector.slotPiece (Submission.BoseGases.dlBox L d u) S Φ)
                (Function.update x i w)) : ℂ)‖
            = |Submission.BoseGases.chiB L d u w| *
              |Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass L d u)
                (Submission.BoseGases.dlBox L d u) i
                (Work.PerSector.slotPiece (Submission.BoseGases.dlBox L d u) S Φ)
                (Function.update x i w)| := by
          rw [Complex.norm_mul, Complex.norm_mul, Complex.norm_exp]
          have hre : (-(Complex.I * (inner ℝ p w : ℂ))).re = 0 := by simp
          rw [hre, Real.exp_zero, mul_one]
          simp
        rw [h1, mul_comm (2 * B) |Submission.BoseGases.chiB L d u w|]
        exact mul_le_mul_of_nonneg_left hQx (abs_nonneg _)
    calc ∫ w : ℝ³, ‖(Submission.BoseGases.chiB L d u w : ℂ) *
            Complex.exp (-(Complex.I * (inner ℝ p w : ℂ))) *
            ((Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass L d u)
              (Submission.BoseGases.dlBox L d u) i
              (Work.PerSector.slotPiece (Submission.BoseGases.dlBox L d u) S Φ)
              (Function.update x i w)) : ℂ)‖
        ≤ ∫ w : ℝ³, (2 * B) * |Submission.BoseGases.chiB L d u w| :=
          MeasureTheory.integral_mono_of_nonneg
            (Filter.Eventually.of_forall (fun w => norm_nonneg _)) hχint
            (Filter.Eventually.of_forall hpt)
      _ = 2 * B * ∫ w : ℝ³, |Submission.BoseGases.chiB L d u w| :=
          MeasureTheory.integral_const_mul _ _
  -- ## A.e. strong measurability
  have hSmeas : MeasurableSet (Work.PerSector.slotSet (Submission.BoseGases.dlBox L d u) S) :=
    measurableSet_slotSet (measurableSet_dlBox L d u) S
  have hΨ₀ : Measurable (Work.PerSector.slotPiece (Submission.BoseGases.dlBox L d u) S Φ) := by
    rw [Work.PerSector.slotPiece]
    exact hΦ.measurable.indicator hSmeas
  have hU : Measurable (fun q : X N × ℝ³ =>
      Work.PerSector.slotPiece (Submission.BoseGases.dlBox L d u) S Φ
        (Function.update q.1 i q.2)) :=
    hΨ₀.comp (measurable_update' (a := i))
  have hIntV : MeasureTheory.AEStronglyMeasurable
      (fun q : X N × ℝ³ => ∫ z in Submission.BoseGases.dlBox L d u,
        Work.PerSector.slotPiece (Submission.BoseGases.dlBox L d u) S Φ (Function.update q.1 i z))
      (((MeasureTheory.volume : MeasureTheory.Measure (X N)).restrict
          (Submission.BoseGases.abox N L)).prod (MeasureTheory.volume : MeasureTheory.Measure ℝ³)) := by
    have hjoint : Measurable (fun w : (X N × ℝ³) × ℝ³ =>
        Work.PerSector.slotPiece (Submission.BoseGases.dlBox L d u) S Φ
          (Function.update w.1.1 i w.2)) :=
      hΨ₀.comp (by fun_prop : Measurable (fun w : (X N × ℝ³) × ℝ³ =>
        Function.update w.1.1 i w.2))
    exact hjoint.aestronglyMeasurable.integral_prod_right'
      (μ := ((MeasureTheory.volume : MeasureTheory.Measure (X N)).restrict
          (Submission.BoseGases.abox N L)).prod (MeasureTheory.volume : MeasureTheory.Measure ℝ³))
      (ν := (MeasureTheory.volume : MeasureTheory.Measure ℝ³).restrict
        (Submission.BoseGases.dlBox L d u))
  have hJQ : MeasureTheory.AEStronglyMeasurable
      (fun q : X N × ℝ³ =>
        Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass L d u)
          (Submission.BoseGases.dlBox L d u) i
          (Work.PerSector.slotPiece (Submission.BoseGases.dlBox L d u) S Φ)
          (Function.update q.1 i q.2))
      (((MeasureTheory.volume : MeasureTheory.Measure (X N)).restrict
          (Submission.BoseGases.abox N L)).prod (MeasureTheory.volume : MeasureTheory.Measure ℝ³)) := by
    have hInd : Measurable (fun q : X N × ℝ³ =>
        (Submission.BoseGases.dlBox L d u).indicator (fun _ => (1:ℝ)) q.2) :=
      (Measurable.indicator measurable_const (measurableSet_dlBox L d u)).comp measurable_snd
    have hbase : MeasureTheory.AEStronglyMeasurable
        (fun q : X N × ℝ³ =>
          (Submission.BoseGases.dlBox L d u).indicator (fun _ => (1:ℝ)) q.2 *
            (Work.PerSector.slotPiece (Submission.BoseGases.dlBox L d u) S Φ
                (Function.update q.1 i q.2)
              - (1 / Work.SmallBoxSliding.boxMass L d u)
                * ∫ z in Submission.BoseGases.dlBox L d u,
                    Work.PerSector.slotPiece (Submission.BoseGases.dlBox L d u) S Φ
                      (Function.update q.1 i z)))
        (((MeasureTheory.volume : MeasureTheory.Measure (X N)).restrict
            (Submission.BoseGases.abox N L)).prod (MeasureTheory.volume : MeasureTheory.Measure ℝ³)) :=
      hInd.aestronglyMeasurable.mul (hU.aestronglyMeasurable.sub (hIntV.const_mul _))
    refine hbase.congr (Filter.Eventually.of_forall (fun q => ?_))
    simp only [Work.UBBInputs8.boxQInd, Work.UBBInputs8.boxPInd, Function.update_self,
      Function.update_idem]
    ring
  have hJt : MeasureTheory.AEStronglyMeasurable
      (fun q : X N × ℝ³ =>
        (Submission.BoseGases.chiB L d u q.2 : ℂ) *
          Complex.exp (-(Complex.I * (inner ℝ p q.2 : ℂ))) *
          ((Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass L d u)
            (Submission.BoseGases.dlBox L d u) i
            (Work.PerSector.slotPiece (Submission.BoseGases.dlBox L d u) S Φ)
            (Function.update q.1 i q.2)) : ℂ))
      (((MeasureTheory.volume : MeasureTheory.Measure (X N)).restrict
          (Submission.BoseGases.abox N L)).prod (MeasureTheory.volume : MeasureTheory.Measure ℝ³)) := by
    have h1 : AEMeasurable (fun q : X N × ℝ³ => (Submission.BoseGases.chiB L d u q.2 : ℂ))
        (((MeasureTheory.volume : MeasureTheory.Measure (X N)).restrict
            (Submission.BoseGases.abox N L)).prod (MeasureTheory.volume : MeasureTheory.Measure ℝ³)) :=
      (Complex.continuous_ofReal.measurable.comp
        ((Work.SmallBoxTBWord.contDiff_chiB hL hd u).continuous.measurable.comp
          measurable_snd)).aemeasurable
    have h2 : AEMeasurable
        (fun q : X N × ℝ³ => Complex.exp (-(Complex.I * (inner ℝ p q.2 : ℂ))))
        (((MeasureTheory.volume : MeasureTheory.Measure (X N)).restrict
            (Submission.BoseGases.abox N L)).prod (MeasureTheory.volume : MeasureTheory.Measure ℝ³)) :=
      (Complex.measurable_exp.comp (by fun_prop)).aemeasurable
    have h3 : AEMeasurable
        (fun q : X N × ℝ³ =>
          ((Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass L d u)
            (Submission.BoseGases.dlBox L d u) i
            (Work.PerSector.slotPiece (Submission.BoseGases.dlBox L d u) S Φ)
            (Function.update q.1 i q.2)) : ℂ))
        (((MeasureTheory.volume : MeasureTheory.Measure (X N)).restrict
            (Submission.BoseGases.abox N L)).prod (MeasureTheory.volume : MeasureTheory.Measure ℝ³)) :=
      Complex.continuous_ofReal.measurable.comp_aemeasurable hJQ.aemeasurable
    exact ((h1.mul h2).mul h3).aestronglyMeasurable
  have haesm : MeasureTheory.AEStronglyMeasurable
      (fun x : X N => ‖Work.SmallBoxTBWord.tBamp (Submission.BoseGases.chiB L d u) p
        (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass L d u)
          (Submission.BoseGases.dlBox L d u) i
          (Work.PerSector.slotPiece (Submission.BoseGases.dlBox L d u) S Φ)) i x‖ ^ 2)
      ((MeasureTheory.volume : MeasureTheory.Measure (X N)).restrict
        (Submission.BoseGases.abox N L)) := by
    have h := hJt.integral_prod_right' (ν := (MeasureTheory.volume : MeasureTheory.Measure ℝ³))
    have h' : MeasureTheory.AEStronglyMeasurable
        (fun x : X N => ‖∫ w : ℝ³,
          (Submission.BoseGases.chiB L d u w : ℂ) *
            Complex.exp (-(Complex.I * (inner ℝ p w : ℂ))) *
            ((Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass L d u)
              (Submission.BoseGases.dlBox L d u) i
              (Work.PerSector.slotPiece (Submission.BoseGases.dlBox L d u) S Φ)
              (Function.update x i w)) : ℂ)‖ ^ 2)
        ((MeasureTheory.volume : MeasureTheory.Measure (X N)).restrict
          (Submission.BoseGases.abox N L)) := (h.norm).pow 2
    simpa only [Work.SmallBoxTBWord.tBamp] using h'
  -- ## Integrability
  refine MeasureTheory.Integrable.of_bound haesm
    ((2 * B * ∫ w : ℝ³, |Submission.BoseGases.chiB L d u w|) ^ 2) ?_
  filter_upwards [MeasureTheory.ae_restrict_mem (Submission.BoseGases.abox_measurable N L)]
    with x hx
  have h0 : (0:ℝ) ≤ ∫ w : ℝ³, |Submission.BoseGases.chiB L d u w| :=
    MeasureTheory.integral_nonneg (fun w => abs_nonneg _)
  have h2 : ‖Work.SmallBoxTBWord.tBamp (Submission.BoseGases.chiB L d u) p
        (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass L d u)
          (Submission.BoseGases.dlBox L d u) i
          (Work.PerSector.slotPiece (Submission.BoseGases.dlBox L d u) S Φ)) i x‖ ^ 2
      ≤ (2 * B * ∫ w : ℝ³, |Submission.BoseGases.chiB L d u w|) ^ 2 := by
    refine sq_le_sq' ?_ (htb x hx)
    nlinarith [norm_nonneg (Work.SmallBoxTBWord.tBamp (Submission.BoseGases.chiB L d u) p
      (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass L d u)
        (Submission.BoseGases.dlBox L d u) i
        (Work.PerSector.slotPiece (Submission.BoseGases.dlBox L d u) S Φ)) i x)]
  rw [Real.norm_of_nonneg (sq_nonneg _)]
  exact h2



/-! ## 2b. The splitting of the integral over the amplitude shift set

This is the amplitude-shift-set companion of `Work.SlotWord.slotSplit_integral_slotBox` (it is the
same lemma as `Work.SlotWord.slotSplit_integral_ampSet` of the sibling module
`Submission.Work.SlotWord.integral_slotFibre_ampEnergy`, restated here so that the present file is
self-contained): if `f` is integrable on the corpus box and vanishes as soon as one of the *outside*
slots of `S` lies in `A`, then the `abox N L`-integral of `f` factors as the integral over the
outside configurations `y ∈ slotOutside L A S` of the `|S|`-particle box integral of `f` read at the
reassembled configuration `slotComb S (ζ ∘ e) y`.  Here the in-box slots are *not* restricted to
`A`, which is exactly what the amplitude of a slot piece needs (`tBamp` is constant in the slot-`i`
coordinate). -/

theorem slotSplit_integral_ampShift (L : ℝ) {A : Set ℝ³} (S : Finset (Fin N))
    (e : SlotIn N S ≃ Fin S.card) {f : X N → ℝ}
    (hint : MeasureTheory.IntegrableOn f (abox N L))
    (hout : ∀ x : X N, f x ≠ 0 → ∀ j : SlotOut N S, x j ∉ A) :
    ∫ x in abox N L, f x
      = ∫ y in slotOutside L A S,
          ∫ ζ in abox S.card L, f (slotComb S (fun k : SlotIn N S => ζ (e k)) y) := by
  classical
  let t : Set (X S.card × (SlotOut N S → ℝ³)) :=
    abox S.card L ×ˢ slotBox (ι := SlotOut N S) (acube L)
  let U : Set (X S.card × (SlotOut N S → ℝ³)) :=
    abox S.card L ×ˢ slotOutside L A S
  have hmp := slotTheta_measurePreserving S e
  have hcv : ∫ x in abox N L, f x = ∫ p in t, f (slotTheta S e p) := by
    have h := (hmp.setIntegral_preimage_emb (slotTheta S e).measurableEmbedding f (abox N L)).symm
    rw [slotTheta_preimage_abox S e L] at h
    exact h
  have hInt : MeasureTheory.IntegrableOn (fun p => f (slotTheta S e p)) t MeasureTheory.volume := by
    have h := (hmp.integrableOn_comp_preimage (slotTheta S e).measurableEmbedding (f := f)
      (s := abox N L)).mpr hint
    rwa [slotTheta_preimage_abox S e L] at h
  have hUt : U ⊆ t := fun p hp =>
    ⟨hp.1, Work.PerSector.Work.PerSector.slotBox_mono Set.inter_subset_left hp.2⟩
  have htmeas : MeasurableSet t :=
    (abox_measurable S.card L).prod
      (Work.PerSector.Work.PerSector.slotBox_measurable (ι := SlotOut N S) (acube_measurable L))
  have hzero : ∀ p ∈ t \ U, f (slotTheta S e p) = 0 := by
    rintro ⟨ζ, y⟩ ⟨hpt, hpU⟩
    rw [Set.mem_prod, mem_slotBox_iff] at hpt
    by_contra hne
    exact hpU (Set.mk_mem_prod hpt.1 (mem_slotOutside_iff.mpr ⟨hpt.2, fun j => by
      have h := hout (slotTheta S e (ζ, y)) hne j
      rwa [slotTheta_apply, slotComb_apply, dif_neg j.2] at h⟩))
  have hrestrict : ∫ p in t, f (slotTheta S e p) = ∫ p in U, f (slotTheta S e p) :=
    setIntegral_eq_of_subset_of_forall_sdiff_eq_zero htmeas hUt hzero
  have hIntU : MeasureTheory.IntegrableOn (fun p => f (slotTheta S e p)) U MeasureTheory.volume :=
    hInt.mono_set hUt
  have hInt' : MeasureTheory.Integrable
      (fun p : X S.card × (SlotOut N S → ℝ³) => f (slotTheta S e p))
      (((MeasureTheory.volume : Measure (X S.card)).restrict (abox S.card L)).prod
        ((MeasureTheory.volume : Measure (SlotOut N S → ℝ³)).restrict (slotOutside L A S))) := by
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod (X S.card) (SlotOut N S → ℝ³)]
    exact hIntU
  have hFub : ∫ p in U, f (slotTheta S e p)
      = ∫ y in slotOutside L A S, ∫ ζ in abox S.card L, f (slotTheta S e (ζ, y)) := by
    dsimp only [U]
    rw [Measure.volume_eq_prod (X S.card) (SlotOut N S → ℝ³)]
    rw [← Measure.prod_restrict]
    exact integral_prod_symm (fun p : X S.card × (SlotOut N S → ℝ³) => f (slotTheta S e p)) hInt'
  rw [hcv, hrestrict, hFub]
  simp only [slotTheta_apply]

/-! ## 3. The amplitude energy of the slot is the fibre integral -/

theorem slotAmpEnergy_eq_integral_fibre {N : ℕ} (L d : ℝ) (hL : 0 < L) (hd : 0 < d)
    (u : ℝ³) (S : Finset (Fin N)) (Φ : X N → ℝ) (hΦ : Continuous Φ)
    (e : SlotIn N S ≃ Fin S.card) (j : Fin S.card) (p : ℝ³) :
    slotAmpEnergy L d u S Φ (e.symm j).1 p
      = ∫ y in slotOutside L (dlBox L d u) S, fibreAmpEnergy L d u S Φ e j p y := by
  set i : Fin N := (e.symm j).1 with hi
  have hii : i ∈ S := (e.symm j).2
  have hh : (⟨i, hii⟩ : SlotIn N S) = e.symm j := Subtype.ext rfl
  -- the splitting of the ambient integral over the amplitude shift set
  have hsplit := slotSplit_integral_ampShift (A := Submission.BoseGases.dlBox L d u) L S e
    (f := fun x : X N => ‖Work.SmallBoxTBWord.tBamp (Submission.BoseGases.chiB L d u) p
      (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass L d u)
        (Submission.BoseGases.dlBox L d u) i
        (Work.PerSector.slotPiece (Submission.BoseGases.dlBox L d u) S Φ)) i x‖ ^ 2)
    (integrableOn_slotAmpEnergy L d hL hd u S Φ hΦ i p) ?_
  · rw [slotAmpEnergy, hsplit]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun y => ?_))
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun ζ => ?_))
    simp only []
    have h := tBamp_boxQInd_slotPiece_eq_fibre L d hL hd u S Φ e i hii p ζ y
    have hei : e (⟨i, hii⟩ : SlotIn N S) = j := by
      rw [hh]; exact e.apply_symm_apply j
    rw [← hei, ← h]
    rfl
  · intro x hx j'
    have hne : Work.SmallBoxTBWord.tBamp (Submission.BoseGases.chiB L d u) p
        (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass L d u)
          (Submission.BoseGases.dlBox L d u) i
          (Work.PerSector.slotPiece (Submission.BoseGases.dlBox L d u) S Φ)) i x ≠ 0 := by
      intro h0
      exact hx (by simp [h0])
    have hmem : x ∈ Work.PerSector.slotAmpSet (Submission.BoseGases.dlBox L d u) S i := by
      by_contra hxnot
      exact hne (tBamp_slotPiece_eq_zero_of_notMem_slotAmpSet (Submission.BoseGases.chiB L d u)
        (fun z hz => Submission.BoseGases.chiB_support_mem hL hd u z hz) i S p hxnot)
    have h2 := (Work.PerSector.mem_slotAmpSet_iff (Submission.BoseGases.dlBox L d u) S i x).mp hmem
    have hne' : j'.1 ≠ i := fun hc => j'.2 (hc ▸ hii)
    intro hc
    exact j'.2 ((h2.2 j'.1 hne').mp hc)

/-! ## 6. The fibre factorisation of the spectral form -/

theorem tBdiagFormInd_slotFibre {N : ℕ} (L d : ℝ) (hL : 0 < L) (hd : 0 < d)
    (u : EuclideanSpace ℝ (Fin 3)) (S : Finset (Fin N)) (Φ : Submission.BoseGases.X N → ℝ)
    (hΦ : Continuous Φ) (e : Work.PerSector.SlotIn N S ≃ Fin S.card) (F : ℝ → ℝ)
    (hF : ∀ r, 0 ≤ F r) (hFm : Measurable F)
    (hswap : MeasureTheory.Integrable
      (fun q : EuclideanSpace ℝ (Fin 3) ×
          (Work.PerSector.SlotOut N S → EuclideanSpace ℝ (Fin 3)) =>
        Work.SlotWord.tBdiagFibreJoint L d u S Φ e F q.1 q.2)
      ((MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℝ (Fin 3))).prod
        ((MeasureTheory.volume : MeasureTheory.Measure
            (Work.PerSector.SlotOut N S → EuclideanSpace ℝ (Fin 3))).restrict
          (Work.PerSector.slotOutside L (Submission.BoseGases.dlBox L d u) S)))) :
    Work.UBBInputs8.tBdiagFormInd L (Submission.BoseGases.dlBox L d u)
        (Work.SmallBoxSliding.boxMass L d u) (Submission.BoseGases.chiB L d u) F
        (Work.PerSector.slotPiece (Submission.BoseGases.dlBox L d u) S Φ)
      = ∫ y in Work.PerSector.slotOutside L (Submission.BoseGases.dlBox L d u) S,
          Work.UBBInputs8.tBdiagFormInd L (Submission.BoseGases.dlBox L d u)
            (Work.SmallBoxSliding.boxMass L d u) (Submission.BoseGases.chiB L d u) F
            (Work.PerSector.slotFibreState S e
              (Work.PerSector.slotPiece (Submission.BoseGases.dlBox L d u) S Φ) y) := by
  classical
  have hM1 : ∀ j : Fin S.card, MeasureTheory.AEStronglyMeasurable
      (fun q : ℝ³ × (SlotOut N S → ℝ³) => fibreAmpEnergy L d u S Φ e j q.1 q.2)
      ((MeasureTheory.volume : MeasureTheory.Measure ℝ³).prod (slotOutMeasure L d u S)) :=
    fun j => aemeasurable_fibreAmpEnergy L d u S Φ hΦ e j
  have hRHS := integral_rHS_eq_sum L d hL hd u S Φ hΦ e F hF hFm hM1 hswap
  have hL : tBdiagFormInd L (dlBox L d u) (boxMass L d u) (chiB L d u) F
        (slotPiece (dlBox L d u) S Φ)
      = ∑ j : Fin S.card, ((2 * Real.pi) ^ 3)⁻¹ *
          ∫ p : ℝ³, ∫ y in slotOutside L (dlBox L d u) S,
            fibreWordIntegrand L d u S Φ e F j p y := by
    rw [show tBdiagFormInd L (dlBox L d u) (boxMass L d u) (chiB L d u) F
          (slotPiece (dlBox L d u) S Φ)
        = ∑ i : Fin N, ((2 * Real.pi) ^ 3)⁻¹ *
            ∫ p : ℝ³, F ‖p‖ * ((L ^ 3)⁻¹ * slotAmpEnergy L d u S Φ i p) from rfl]
    rw [sum_slotAmpEnergy_eq_sum_fibre L d u S Φ e F]
    refine Finset.sum_congr rfl (fun j _ => ?_)
    congr 1
    have hpt : (fun p : ℝ³ =>
          F ‖p‖ * ((L ^ 3)⁻¹ * slotAmpEnergy L d u S Φ (↑(e.symm j)) p))
        = fun p : ℝ³ =>
          ∫ y in slotOutside L (dlBox L d u) S, fibreWordIntegrand L d u S Φ e F j p y := by
      funext p
      rw [slotAmpEnergy_eq_integral_fibre L d hL hd u S Φ hΦ e j p]
      simp only [fibreWordIntegrand]
      rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
    rw [hpt]
  rw [hL, hRHS, Finset.mul_sum]



end

end Work.SlotWord
