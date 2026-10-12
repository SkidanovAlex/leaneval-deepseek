import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.SlotWord.FibreSpec.tBamp_slotPiece_ampSq_integrable
import Submission.Work.SlotWord.SlotFibreInfra
import Submission.Work.SlotWord.ThetaDefs
import Submission.Work.SlotWord.slotSplit_integral_slotBox
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.SlotWord.FibreSpec.tBdiagFormInd_fibre`

The fibre factorisation of the spectral half of the FS word: the `p`-diagonal kinetic form
`tBdiagFormInd` of the slot piece `slotPiece B S Φ` equals the `y`-integral, over the outside
configurations, of the `|S|`-particle form of the transported fibre `slotFibreState S e · y`.

## The mathematics

Write `B = dlBox L d u`, `χ = chiB L d u`, `Ψ = slotPiece B S Φ`.  Unfolding the definition of
`tBdiagFormInd`, the left-hand side is

    Σ_{i : Fin N} (2π)⁻³ ∫_p F ‖p‖ · (L³)⁻¹ ∫_{x ∈ abox N L} ‖tBamp χ p (Q_{B,i}Ψ) i x‖² .

Since the amplitude `tBamp χ p (Q_{B,i}Ψ) i x` is *independent of the `i`-th coordinate of `x`*
(the windowed Fourier transform replaces that coordinate by the integration variable), the only
constraint on `x` is that its *other* slots agree with `S` (`x ∈ slotAmpSet B S i`); the
`(L³)⁻¹ = |acube L|⁻¹` normalisation is exactly the correction of the thereby over-counted slot
volume.  Hence:

* for `i ∉ S` the summand vanishes (`boxQInd_slotPiece_eq_zero_of_notMem`);
* for `i ∈ S` the change of variables along the slot reassembly `slotTheta S e` (which pulls
  `abox N L` back to `abox |S| L ×ˢ slotBox (SlotOut N S) (acube L)`, `slotTheta_preimage_abox`)
  together with the support of the amplitude in the outside slots turns the `x`-integral into the
  iterated integral over `y ∈ slotOutside L B S` and `z ∈ abox |S| L`
  (`slotSplit_integral_ampSet`); the pointwise amplitude identity
  `tBamp_boxQInd_slotPiece_eq_fibre` (`slotFibre_pointwise`) identifies the integrand with the
  `|S|`-particle amplitude energy of the fibre, giving the per-slot splitting
  `slotAmpEnergy = ∫_y fibreAmpEnergy` (`slotAmpEnergy_eq_integral_fibre`);
* reindexing the slot sum along `e` (`sum_slotAmpEnergy_eq_sum_fibre`) gives the left-hand side in
  the `p`-outer/`y`-inner form of the right-hand side;
* the right-hand side is rewritten by `fibreWordIntegral_eq_sum` in the *same* form, using
  Fubini in the restricted fibre measure; the integrability input is exactly the (R3) side
  condition `hswap`, and the a.e.-strong measurability of the fibre amplitude energy is
  `Work.SlotWord.aemeasurable_fibreAmpEnergy`.

The integrability of the amplitude energy on the box (used by the slot splitting) is
`Work.SlotWord.FibreSpec.tBamp_slotPiece_ampSq_integrable`.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.SlotWord.FibreSpec

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open Submission.BoseGases
open BoseGases
open Work.PerSector
open Work.SmallBoxSliding
open Work.UBBInputs8

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

variable {N : ℕ}

/-! ## 1. The per-slot amplitude energies -/

/-- The ambient amplitude energy of the `i`-th slot of the slot piece. -/
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

/-- The `j`-th summand of the joint `(p, y)`-integrand of the fibre form. -/
noncomputable def fibreWordIntegrand (L d : ℝ) (u : ℝ³) (S : Finset (Fin N)) (Φ : X N → ℝ)
    (e : SlotIn N S ≃ Fin S.card) (F : ℝ → ℝ) (j : Fin S.card) (p : ℝ³)
    (y : SlotOut N S → ℝ³) : ℝ :=
  F ‖p‖ * ((L ^ 3)⁻¹ * fibreAmpEnergy L d u S Φ e j p y)

theorem tBdiagFibreJoint_eq_sum (L d : ℝ) (u : ℝ³) (S : Finset (Fin N)) (Φ : X N → ℝ)
    (e : SlotIn N S ≃ Fin S.card) (F : ℝ → ℝ) (p : ℝ³) (y : SlotOut N S → ℝ³) :
    tBdiagFibreJoint L d u S Φ e F p y
      = ∑ j : Fin S.card, fibreWordIntegrand L d u S Φ e F j p y := rfl

theorem tBdiagFormInd_fibre_eq (L d : ℝ) (u : ℝ³) (S : Finset (Fin N)) (Φ : X N → ℝ)
    (e : SlotIn N S ≃ Fin S.card) (F : ℝ → ℝ) (y : SlotOut N S → ℝ³) :
    Work.UBBInputs8.tBdiagFormInd L (dlBox L d u) (boxMass L d u) (chiB L d u) F
        (slotFibreState S e (slotPiece (dlBox L d u) S Φ) y)
      = ∑ j : Fin S.card,
          ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : ℝ³,
            F ‖p‖ * ((L ^ 3)⁻¹ * fibreAmpEnergy L d u S Φ e j p y) := rfl

@[simp] theorem tBamp_zero {N : ℕ} (χ : ℝ³ → ℝ) (p : ℝ³) (i : Fin N) (x : X N) :
    Work.SmallBoxTBWord.tBamp χ p (0 : X N → ℝ) i x = 0 := by
  simp [Work.SmallBoxTBWord.tBamp]

theorem fibreWordIntegrand_nonneg {L d : ℝ} {u : ℝ³} {S : Finset (Fin N)} {Φ : X N → ℝ}
    {e : SlotIn N S ≃ Fin S.card} {F : ℝ → ℝ} (hF : ∀ r, 0 ≤ F r) (hL : 0 < L)
    (j : Fin S.card) (p : ℝ³) (y : SlotOut N S → ℝ³) :
    0 ≤ fibreWordIntegrand L d u S Φ e F j p y := by
  unfold fibreWordIntegrand
  refine mul_nonneg (hF _) (mul_nonneg ?_ ?_)
  · positivity
  · unfold fibreAmpEnergy
    exact MeasureTheory.integral_nonneg (fun z => sq_nonneg _)

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
    have hpt : (fun p : ℝ³ => F ‖p‖ * ((L ^ 3)⁻¹ * slotAmpEnergy L d u S Φ i p))
        = fun _ => 0 := by
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
    Fintype.sum_equiv e (fun i : SlotIn N S => g i.1) (fun j : Fin S.card => g (e.symm j).1)
      (fun i => by simp)
  rw [h1, h2, h3]

/-! ## 3. The slot splitting for an amplitude-shift-set integrand -/

/-- **The slot splitting for a function carried by the amplitude shift set.**  If `f : X N → ℝ` is
integrable on the corpus box and vanishes as soon as one of the *outside* slots of `S` lies in `A`
(`A` a sliding box, typically `dlBox L d u`), then the `abox N L`-integral of `f` factors as the
integral over the outside configurations `y ∈ slotOutside L A S` of the `|S|`-particle box integral
of `f` read at the reassembled configuration `slotComb S (ζ ∘ e) y`.

Here the in-box slots are *not* restricted to `A` (the amplitude is constant in the slot-`i`
coordinate), so the inner integral runs over the full `|S|`-particle box `abox |S| L`. -/
theorem slotSplit_integral_ampSet {N : ℕ} (L : ℝ) {A : Set ℝ³} (S : Finset (Fin N))
    (e : SlotIn N S ≃ Fin S.card) {f : X N → ℝ}
    (hint : IntegrableOn f (abox N L))
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
  have hInt : IntegrableOn (fun p => f (slotTheta S e p)) t volume := by
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
  have hIntU : IntegrableOn (fun p => f (slotTheta S e p)) U volume := hInt.mono_set hUt
  have hInt' : Integrable (fun p : X S.card × (SlotOut N S → ℝ³) => f (slotTheta S e p))
      (((volume : Measure (X S.card)).restrict (abox S.card L)).prod
        ((volume : Measure (SlotOut N S → ℝ³)).restrict (slotOutside L A S))) := by
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

/-! ## 4. The per-slot splitting of the amplitude energy -/

theorem slotAmpEnergy_eq_integral_fibre_aux {N : ℕ} (L d : ℝ) (hL : 0 < L) (hd : 0 < d)
    (u : ℝ³) (S : Finset (Fin N)) (Φ : X N → ℝ) (hΦ : Continuous Φ)
    (e : SlotIn N S ≃ Fin S.card) (i : Fin N) (hi : i ∈ S) (p : ℝ³)
    (hint : IntegrableOn (fun x : X N =>
      ‖Work.SmallBoxTBWord.tBamp (chiB L d u) p
        (boxQInd (boxMass L d u) (dlBox L d u) i (slotPiece (dlBox L d u) S Φ)) i x‖ ^ 2)
      (abox N L)) :
    slotAmpEnergy L d u S Φ i p
      = ∫ y in slotOutside L (dlBox L d u) S,
          fibreAmpEnergy L d u S Φ e (e ⟨i, hi⟩) p y := by
  classical
  set f : X N → ℝ := fun x => ‖Work.SmallBoxTBWord.tBamp (chiB L d u) p
      (boxQInd (boxMass L d u) (dlBox L d u) i (slotPiece (dlBox L d u) S Φ)) i x‖ ^ 2 with hf
  have hout : ∀ x : X N, f x ≠ 0 → ∀ j : SlotOut N S, x j ∉ dlBox L d u := by
    intro x hx j
    have hne : Work.SmallBoxTBWord.tBamp (chiB L d u) p
        (boxQInd (boxMass L d u) (dlBox L d u) i (slotPiece (dlBox L d u) S Φ)) i x ≠ 0 := by
      intro h0
      exact hx (by rw [hf]; simp [h0])
    have hmem : x ∈ slotAmpSet (dlBox L d u) S i := by
      by_contra hxnot
      exact hne (tBamp_slotPiece_eq_zero_of_notMem_slotAmpSet (chiB L d u)
        (fun z hz => chiB_support_mem hL hd u z hz) i S p hxnot)
    have h2 := (mem_slotAmpSet_iff (dlBox L d u) S i x).mp hmem
    have hji : j.1 ≠ i := fun hc => j.2 (hc ▸ hi)
    intro hc
    exact j.2 ((h2.2 j.1 hji).mp hc)
  have hsplit := slotSplit_integral_ampSet (N := N) L (A := dlBox L d u) S e (f := f) hint hout
  have hLHS : slotAmpEnergy L d u S Φ i p = ∫ x in abox N L, f x := rfl
  rw [hLHS, hsplit]
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun y => ?_))
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun z => ?_))
  change f (fibreIn S e y z)
    = ‖Work.SmallBoxTBWord.tBamp (chiB L d u) p
        (boxQInd (boxMass L d u) (dlBox L d u) (e ⟨i, hi⟩)
          (slotFibreState S e (slotPiece (dlBox L d u) S Φ) y)) (e ⟨i, hi⟩) z‖ ^ 2
  rw [hf]
  exact congrArg (fun w : ℂ => ‖w‖ ^ 2)
    (tBamp_boxQInd_slotPiece_eq_fibre L d hL hd u S Φ e i hi p z y)

theorem slotAmpEnergy_eq_integral_fibre {N : ℕ} (L d : ℝ) (hL : 0 < L) (hd : 0 < d)
    (u : ℝ³) (S : Finset (Fin N)) (Φ : X N → ℝ) (hΦ : Continuous Φ)
    (e : SlotIn N S ≃ Fin S.card) (j : Fin S.card) (p : ℝ³)
    (hint : IntegrableOn (fun x : X N =>
      ‖Work.SmallBoxTBWord.tBamp (chiB L d u) p
        (boxQInd (boxMass L d u) (dlBox L d u) (e.symm j).1
          (slotPiece (dlBox L d u) S Φ)) (e.symm j).1 x‖ ^ 2)
      (abox N L)) :
    slotAmpEnergy L d u S Φ (e.symm j).1 p
      = ∫ y in slotOutside L (dlBox L d u) S, fibreAmpEnergy L d u S Φ e j p y := by
  have h := slotAmpEnergy_eq_integral_fibre_aux (N := N) L d hL hd u S Φ hΦ e
    (e.symm j).1 (e.symm j).2 p hint
  simpa using h

theorem integral_fibreWordIntegrand {N : ℕ} (L d : ℝ) (u : ℝ³) (S : Finset (Fin N))
    (Φ : X N → ℝ) (e : SlotIn N S ≃ Fin S.card) (F : ℝ → ℝ) (j : Fin S.card) (p : ℝ³) :
    (∫ y in slotOutside L (dlBox L d u) S, fibreWordIntegrand L d u S Φ e F j p y)
      = F ‖p‖ * ((L ^ 3)⁻¹ *
          ∫ y in slotOutside L (dlBox L d u) S, fibreAmpEnergy L d u S Φ e j p y) := by
  simp only [fibreWordIntegrand]
  rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]

/-! ## 5. The left-hand side as the `p`- then `y`-integral of the joint integrand -/

theorem tBdiagFormInd_eq_sum_fibre {N : ℕ} (L d : ℝ) (hL : 0 < L) (hd : 0 < d)
    (u : ℝ³) (S : Finset (Fin N)) (Φ : X N → ℝ) (hΦ : Continuous Φ)
    (e : SlotIn N S ≃ Fin S.card) (F : ℝ → ℝ)
    (hint : ∀ (i : Fin N) (p : ℝ³), IntegrableOn (fun x : X N =>
      ‖Work.SmallBoxTBWord.tBamp (chiB L d u) p
        (boxQInd (boxMass L d u) (dlBox L d u) i
          (slotPiece (dlBox L d u) S Φ)) i x‖ ^ 2) (abox N L)) :
    Work.UBBInputs8.tBdiagFormInd L (dlBox L d u)
        (boxMass L d u) (chiB L d u) F
        (slotPiece (dlBox L d u) S Φ)
      = ((2 * Real.pi) ^ 3)⁻¹ * ∑ j : Fin S.card,
          ∫ p : ℝ³,
            ∫ y in slotOutside L (dlBox L d u) S, fibreWordIntegrand L d u S Φ e F j p y := by
  have h1 : Work.UBBInputs8.tBdiagFormInd L (dlBox L d u)
        (boxMass L d u) (chiB L d u) F
        (slotPiece (dlBox L d u) S Φ)
      = ∑ i : Fin N, ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : ℝ³, F ‖p‖ *
          ((L ^ 3)⁻¹ * slotAmpEnergy L d u S Φ i p) := rfl
  rw [h1, sum_slotAmpEnergy_eq_sum_fibre L d u S Φ e F]
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun j _ => ?_)
  have hkey : (∫ p : ℝ³, F ‖p‖ *
        ((L ^ 3)⁻¹ * slotAmpEnergy L d u S Φ (e.symm j).1 p))
      = ∫ p : ℝ³, ∫ y in slotOutside L (dlBox L d u) S,
          fibreWordIntegrand L d u S Φ e F j p y := by
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun p => ?_))
    show F ‖p‖ * ((L ^ 3)⁻¹ * slotAmpEnergy L d u S Φ (e.symm j).1 p)
      = ∫ y in slotOutside L (dlBox L d u) S, fibreWordIntegrand L d u S Φ e F j p y
    rw [integral_fibreWordIntegrand L d u S Φ e F j p,
      slotAmpEnergy_eq_integral_fibre L d hL hd u S Φ hΦ e j p (hint _ _)]
  rw [hkey]

/-! ## 6. The right-hand side as the `p`- then `y`-integral of the joint integrand -/

/-- The measure on the outside configurations used throughout. -/
noncomputable def fibreOutMeasure (L d : ℝ) (u : ℝ³) (S : Finset (Fin N)) :
    Measure (SlotOut N S → ℝ³) :=
  (volume : Measure (SlotOut N S → ℝ³)).restrict (slotOutside L (dlBox L d u) S)

@[simp] theorem fibreOutMeasure_def (L d : ℝ) (u : ℝ³) (S : Finset (Fin N)) :
    fibreOutMeasure L d u S
      = (volume : Measure (SlotOut N S → ℝ³)).restrict
          (slotOutside L (dlBox L d u) S) := rfl

instance (L d : ℝ) (u : ℝ³) (S : Finset (Fin N)) : SFinite (fibreOutMeasure L d u S) := by
  rw [fibreOutMeasure_def]
  infer_instance

theorem fibreWordIntegral_eq_sum {N : ℕ} (L d : ℝ) (hL : 0 < L) (hd : 0 < d)
    (u : ℝ³) (S : Finset (Fin N)) (Φ : X N → ℝ) (hΦ : Continuous Φ)
    (e : SlotIn N S ≃ Fin S.card) (F : ℝ → ℝ)
    (hF : ∀ r, 0 ≤ F r) (hFm : Measurable F)
    (hmeas : ∀ j : Fin S.card, AEStronglyMeasurable
      (fun q : ℝ³ × (SlotOut N S → ℝ³) =>
        ∫ z in abox S.card L,
          ‖Work.SmallBoxTBWord.tBamp (chiB L d u) q.1
            (boxQInd (boxMass L d u) (dlBox L d u) j
              (slotFibreState S e (slotPiece (dlBox L d u) S Φ) q.2)) j z‖ ^ 2)
      ((volume : Measure ℝ³).prod (fibreOutMeasure L d u S)))
    (hswap : Integrable
      (fun q : ℝ³ × (SlotOut N S → ℝ³) => tBdiagFibreJoint L d u S Φ e F q.1 q.2)
      ((volume : Measure ℝ³).prod (fibreOutMeasure L d u S))) :
    (∫ y in slotOutside L (dlBox L d u) S,
        Work.UBBInputs8.tBdiagFormInd L (dlBox L d u) (boxMass L d u) (chiB L d u) F
          (slotFibreState S e (slotPiece (dlBox L d u) S Φ) y))
      = ((2 * Real.pi) ^ 3)⁻¹ * ∑ j : Fin S.card,
          ∫ p : ℝ³, ∫ y in slotOutside L (dlBox L d u) S,
            fibreWordIntegrand L d u S Φ e F j p y := by
  classical
  -- (a) a.e. strong measurability of the summands
  have haesm : ∀ j : Fin S.card,
      AEStronglyMeasurable
        (Function.uncurry (fun (p : ℝ³) (y : SlotOut N S → ℝ³) =>
          fibreWordIntegrand L d u S Φ e F j p y))
        ((volume : Measure ℝ³).prod (fibreOutMeasure L d u S)) := by
    intro j
    have hE : AEStronglyMeasurable
        (fun q : ℝ³ × (SlotOut N S → ℝ³) => fibreAmpEnergy L d u S Φ e j q.1 q.2)
        ((volume : Measure ℝ³).prod (fibreOutMeasure L d u S)) := by
      have h := hmeas j
      simpa only [fibreAmpEnergy, fibreOutMeasure_def] using h
    have hFn : AEStronglyMeasurable
        (fun q : ℝ³ × (SlotOut N S → ℝ³) => F ‖q.1‖)
        ((volume : Measure ℝ³).prod (fibreOutMeasure L d u S)) :=
      (hFm.comp ((continuous_norm.measurable).comp measurable_fst)).aestronglyMeasurable
    have hthis := hFn.mul (hE.const_mul ((L ^ 3)⁻¹))
    have heq : ((fun q : ℝ³ × (SlotOut N S → ℝ³) => F ‖q.1‖) *
          (fun q : ℝ³ × (SlotOut N S → ℝ³) =>
            (L ^ 3)⁻¹ * fibreAmpEnergy L d u S Φ e j q.1 q.2))
        = Function.uncurry (fun (p : ℝ³) (y : SlotOut N S → ℝ³) =>
            fibreWordIntegrand L d u S Φ e F j p y) := by
      funext q; rfl
    rwa [heq] at hthis
  -- (b) integrability of the summands
  have hint : ∀ j : Fin S.card,
      Integrable
        (Function.uncurry (fun (p : ℝ³) (y : SlotOut N S → ℝ³) =>
          fibreWordIntegrand L d u S Φ e F j p y))
        ((volume : Measure ℝ³).prod (fibreOutMeasure L d u S)) := by
    intro j
    refine Integrable.mono' hswap (haesm j) ?_
    refine Filter.Eventually.of_forall (fun q => ?_)
    have hle : fibreWordIntegrand L d u S Φ e F j q.1 q.2
        ≤ ∑ j' : Fin S.card, fibreWordIntegrand L d u S Φ e F j' q.1 q.2 :=
      Finset.single_le_sum (fun j' _ => fibreWordIntegrand_nonneg hF hL j' q.1 q.2)
        (Finset.mem_univ j)
    change ‖fibreWordIntegrand L d u S Φ e F j q.1 q.2‖
        ≤ tBdiagFibreJoint L d u S Φ e F q.1 q.2
    rw [Real.norm_of_nonneg (fibreWordIntegrand_nonneg hF hL j q.1 q.2),
      tBdiagFibreJoint_eq_sum]
    exact hle
  -- (c) a.e. `y`, integrability in `p`
  have hsec_y : ∀ᵐ y ∂(fibreOutMeasure L d u S), ∀ j : Fin S.card,
      Integrable (fun p : ℝ³ => fibreWordIntegrand L d u S Φ e F j p y) volume := by
    have hsm : ∀ᵐ y ∂(fibreOutMeasure L d u S), ∀ j : Fin S.card,
        AEStronglyMeasurable (fun p : ℝ³ => fibreWordIntegrand L d u S Φ e F j p y) volume :=
      Filter.eventually_all.2 (fun j => (haesm j).prodMk_right)
    have hJint : ∀ᵐ y ∂(fibreOutMeasure L d u S),
        Integrable (fun p : ℝ³ => tBdiagFibreJoint L d u S Φ e F p y) volume :=
      hswap.prod_left_ae
    filter_upwards [hsm, hJint] with y hsm'y hJy
    intro j
    refine Integrable.mono' hJy (hsm'y j) ?_
    refine Filter.Eventually.of_forall (fun p => ?_)
    have hle : fibreWordIntegrand L d u S Φ e F j p y
        ≤ ∑ j' : Fin S.card, fibreWordIntegrand L d u S Φ e F j' p y :=
      Finset.single_le_sum (fun j' _ => fibreWordIntegrand_nonneg hF hL j' p y)
        (Finset.mem_univ j)
    change ‖fibreWordIntegrand L d u S Φ e F j p y‖ ≤ tBdiagFibreJoint L d u S Φ e F p y
    rw [Real.norm_of_nonneg (fibreWordIntegrand_nonneg hF hL j p y), tBdiagFibreJoint_eq_sum]
    exact hle
  -- (d) a.e. `p`, integrability in `y`
  have hsec_p : ∀ᵐ p ∂(volume : Measure ℝ³), ∀ j : Fin S.card,
      Integrable (fun y : SlotOut N S → ℝ³ => fibreWordIntegrand L d u S Φ e F j p y)
        (fibreOutMeasure L d u S) := by
    have hsm : ∀ᵐ p ∂(volume : Measure ℝ³), ∀ j : Fin S.card,
        AEStronglyMeasurable
          (fun y : SlotOut N S → ℝ³ => fibreWordIntegrand L d u S Φ e F j p y)
          (fibreOutMeasure L d u S) :=
      Filter.eventually_all.2 (fun j => (haesm j).prodMk_left)
    have hJint : ∀ᵐ p ∂(volume : Measure ℝ³),
        Integrable (fun y : SlotOut N S → ℝ³ => tBdiagFibreJoint L d u S Φ e F p y)
          (fibreOutMeasure L d u S) := hswap.prod_right_ae
    filter_upwards [hsm, hJint] with p hsm'p hJp
    intro j
    refine Integrable.mono' hJp (hsm'p j) ?_
    refine Filter.Eventually.of_forall (fun y => ?_)
    have hle : fibreWordIntegrand L d u S Φ e F j p y
        ≤ ∑ j' : Fin S.card, fibreWordIntegrand L d u S Φ e F j' p y :=
      Finset.single_le_sum (fun j' _ => fibreWordIntegrand_nonneg hF hL j' p y)
        (Finset.mem_univ j)
    change ‖fibreWordIntegrand L d u S Φ e F j p y‖ ≤ tBdiagFibreJoint L d u S Φ e F p y
    rw [Real.norm_of_nonneg (fibreWordIntegrand_nonneg hF hL j p y), tBdiagFibreJoint_eq_sum]
    exact hle
  -- the two almost-everywhere keys
  have key_y : ∀ᵐ y ∂(fibreOutMeasure L d u S),
      Work.UBBInputs8.tBdiagFormInd L (dlBox L d u) (boxMass L d u) (chiB L d u) F
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
    rfl
  have key_p : ∀ᵐ p ∂(volume : Measure ℝ³),
      (∫ y in slotOutside L (dlBox L d u) S, tBdiagFibreJoint L d u S Φ e F p y)
        = ∑ j : Fin S.card,
            ∫ y in slotOutside L (dlBox L d u) S, fibreWordIntegrand L d u S Φ e F j p y := by
    filter_upwards [hsec_p] with p hp
    rw [show (∫ y in slotOutside L (dlBox L d u) S, tBdiagFibreJoint L d u S Φ e F p y)
        = ∫ y in slotOutside L (dlBox L d u) S, ∑ j : Fin S.card,
            fibreWordIntegrand L d u S Φ e F j p y from by
      exact MeasureTheory.integral_congr_ae
        (Filter.Eventually.of_forall (fun y => tBdiagFibreJoint_eq_sum L d u S Φ e F p y))]
    exact MeasureTheory.integral_finsetSum Finset.univ (fun i _ => hp i)
  -- the chain
  have hFint : ∀ j : Fin S.card,
      Integrable (fun p : ℝ³ => ∫ y in slotOutside L (dlBox L d u) S,
          fibreWordIntegrand L d u S Φ e F j p y) volume :=
    fun j => (hint j).integral_prod_left
  calc (∫ y in slotOutside L (dlBox L d u) S,
        Work.UBBInputs8.tBdiagFormInd L (dlBox L d u) (boxMass L d u) (chiB L d u) F
          (slotFibreState S e (slotPiece (dlBox L d u) S Φ) y))
      = ∫ y in slotOutside L (dlBox L d u) S,
          ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : ℝ³, tBdiagFibreJoint L d u S Φ e F p y :=
        MeasureTheory.integral_congr_ae key_y
    _ = ((2 * Real.pi) ^ 3)⁻¹ * ∫ y in slotOutside L (dlBox L d u) S,
          ∫ p : ℝ³, tBdiagFibreJoint L d u S Φ e F p y :=
        MeasureTheory.integral_const_mul _ _
    _ = ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : ℝ³,
          ∫ y in slotOutside L (dlBox L d u) S, tBdiagFibreJoint L d u S Φ e F p y := by
        rw [(MeasureTheory.integral_integral_swap hswap).symm]
    _ = ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : ℝ³, ∑ j : Fin S.card,
          ∫ y in slotOutside L (dlBox L d u) S, fibreWordIntegrand L d u S Φ e F j p y :=
        congrArg _ (MeasureTheory.integral_congr_ae key_p)
    _ = ((2 * Real.pi) ^ 3)⁻¹ * ∑ j : Fin S.card,
          ∫ p : ℝ³, ∫ y in slotOutside L (dlBox L d u) S,
            fibreWordIntegrand L d u S Φ e F j p y := by
        rw [MeasureTheory.integral_finsetSum Finset.univ (fun j _ => hFint j)]

/-! ## 7. The target -/

theorem tBdiagFormInd_fibre {N : ℕ} (L d : ℝ) (hL : 0 < L) (hd : 0 < d)
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
  have hint : ∀ (i : Fin N) (p : EuclideanSpace ℝ (Fin 3)), MeasureTheory.IntegrableOn
      (fun x : Submission.BoseGases.X N =>
        ‖Work.SmallBoxTBWord.tBamp (Submission.BoseGases.chiB L d u) p
          (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass L d u)
            (Submission.BoseGases.dlBox L d u) i
            (Work.PerSector.slotPiece (Submission.BoseGases.dlBox L d u) S Φ)) i x‖ ^ 2)
      (Submission.BoseGases.abox N L) := fun i p =>
    tBamp_slotPiece_ampSq_integrable L d hL hd u S Φ hΦ i p
  rw [tBdiagFormInd_eq_sum_fibre L d hL hd u S Φ hΦ e F hint]
  exact (fibreWordIntegral_eq_sum L d hL hd u S Φ hΦ e F hF hFm
    (fun j => Work.SlotWord.aemeasurable_fibreAmpEnergy L d u S Φ hΦ e j) hswap).symm

end Work.SlotWord.FibreSpec
