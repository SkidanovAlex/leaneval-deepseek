import Submission.NBody.LYZIoc
import Mathlib

/-!
# The action integral without collision-freeness

The lemmas of `Submission.NBody.EnergyLevel` and `Submission.NBody.LYZIoc` assume the curve to be
collision free on the whole interval.  For a *minimiser* this hypothesis is in fact unnecessary:
the finiteness of the action already forces the collision set to be null, and the energy identity
(hence the identity `∫ ‖γ̇‖² = A_{L+h}(γ)`) can be recovered component by component on the
complement of the collision set.

This module proves:

* `measurable_lagrangian` — the Lagrangian is Borel measurable;
* `ae_withoutCollisions_of_actionOn_lt_top` — a curve of finite action is collision free
  almost everywhere;
* `actionOn_eq_ofReal_integral_lagR_of_ae` — `A_{L+h}(γ) = ofReal (∫ L_h(γ, γ̇))` for an
  absolutely continuous curve of finite action whose collision set is null;
* `ae_energy_eq_of_minimizer` — an `h`-minimiser of finite action has energy `h` a.e.;
* `integral_weightedNorm_sq_eq_actionOn_of_min` — the **Marchal-free energy identity**;
* `ae_sqrt_two_h_le_weightedNorm_of_min` — the **Marchal-free speed bound** `√(2h) ≤ ‖γ̇‖_[m]`.

None of these uses `MarchalProperty`: the collision-freeness of a minimiser is *not* needed for the
variational estimates of Liu--Yan--Zhou, only for the smoothness of the limiting curve.
-/

open ViscositySolutions
open Filter Gradient Real Set Metric
open scoped BigOperators Topology ENNReal
open MeasureTheory

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
variable [Nontrivial E]
variable {N : ℕ}

namespace Submission.NBody

/-- The colliding configurations form a closed set. -/
lemma isClosed_collisions : IsClosed {x : EN E N | ¬ WithoutCollisions x} := by
  have hset : {x : EN E N | ¬ WithoutCollisions x}
      = ⋃ (i : Fin N) (j : Fin N), {x : EN E N | i ≠ j ∧ r x i j = 0} := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_iUnion, WithoutCollisions]
    constructor
    · intro hx
      push Not at hx
      obtain ⟨i, j, hij, hxij⟩ := hx
      exact ⟨i, j, hij, hxij⟩
    · rintro ⟨i, j, hij, hxij⟩ hc
      exact hc i j hij hxij
  rw [hset]
  refine isClosed_iUnion_of_finite fun i => isClosed_iUnion_of_finite fun j => ?_
  by_cases hij : i = j
  · subst hij
    have h0 : {x : EN E N | i ≠ i ∧ r x i i = 0} = (∅ : Set (EN E N)) := by
      ext x; simp
    rw [h0]; exact isClosed_empty
  · have h2 : {x : EN E N | i ≠ j ∧ r x i j = 0}
        = {x : EN E N | dist (x i) (x j) = 0} := by
      ext x; simp only [Set.mem_setOf_eq, r]
      exact ⟨fun h => h.2, fun h => ⟨hij, h⟩⟩
    rw [h2]
    exact isClosed_eq
      ((PiLp.continuous_apply 2 (fun _ : Fin N => E) i).dist
        (PiLp.continuous_apply 2 (fun _ : Fin N => E) j)) continuous_const

/-- **A curve of finite action is collision free almost everywhere.** -/
lemma ae_withoutCollisions_of_actionOn_lt_top {m : Fin N → ℝ} {h : ℝ} {γ : ℝ → EN E N} {a b : ℝ}
    (hac : AbsolutelyContinuousOnInterval γ a b) (hfin : actionOn m h γ a b < ⊤) :
    ∀ᵐ t ∂(volume.restrict (Set.Ioc a b)), WithoutCollisions (γ t) := by
  letI : MeasurableSpace (EN E N) := borel (EN E N)
  haveI : BorelSpace (EN E N) := ⟨rfl⟩
  set S : Set ℝ := {t ∈ Set.Ioc a b | ¬ WithoutCollisions (γ t)} with hSdef
  have hSmeas : MeasurableSet S := by
    have hclosed : IsClosed (Set.uIcc a b ∩ (fun t : ℝ => γ t) ⁻¹'
        {x : EN E N | ¬ WithoutCollisions x}) :=
      (hac.continuousOn.preimage_isClosed_of_isClosed isClosed_Icc isClosed_collisions)
    have h1 : S = (Set.uIcc a b ∩ (fun t : ℝ => γ t) ⁻¹'
        {x : EN E N | ¬ WithoutCollisions x}) ∩ Set.Ioc a b := by
      ext t
      simp only [hSdef, Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage]
      constructor
      · rintro ⟨⟨hta, htb⟩, hnc⟩
        exact ⟨⟨Set.mem_uIcc.mpr (Or.inl ⟨hta.le, htb⟩), hnc⟩, ⟨hta, htb⟩⟩
      · rintro ⟨⟨-, hnc⟩, ⟨hta, htb⟩⟩
        exact ⟨⟨hta, htb⟩, hnc⟩
    rw [h1]
    exact hclosed.measurableSet.inter measurableSet_Ioc
  have hmono : (∫⁻ t, Set.indicator S (fun _ : ℝ => (⊤ : ℝ≥0∞)) t
        ∂(volume.restrict (Set.Ioc a b)))
      ≤ ∫⁻ t, lagrangian m h (γ t) (deriv γ t) ∂(volume.restrict (Set.Ioc a b)) :=
    lintegral_mono (fun t => by
      by_cases ht : t ∈ S
      · rw [Set.indicator_of_mem ht]
        exact le_of_eq ((lagrangian_eq_top_iff).mpr ht.2).symm
      · rw [Set.indicator_of_notMem ht]
        simp)
  have hind : (∫⁻ t, Set.indicator S (fun _ : ℝ => (⊤ : ℝ≥0∞)) t
        ∂(volume.restrict (Set.Ioc a b)))
      = (volume.restrict (Set.Ioc a b)) S * ⊤ := by
    rw [lintegral_indicator_const hSmeas ⊤, mul_comm]
  have htop : (volume.restrict (Set.Ioc a b)) S = 0 := by
    by_contra hne
    have h1 : (volume.restrict (Set.Ioc a b)) S * (⊤ : ℝ≥0∞) = ⊤ := ENNReal.mul_top hne
    rw [hind, h1] at hmono
    exact absurd (lt_of_le_of_lt hmono (show (∫⁻ t,
      lagrangian m h (γ t) (deriv γ t) ∂(volume.restrict (Set.Ioc a b))) < ⊤ from hfin))
      (lt_irrefl _)
  have hvol : volume S = 0 := by
    rw [Measure.restrict_apply hSmeas] at htop
    rwa [Set.inter_eq_self_of_subset_left (fun t ht => ht.1)] at htop
  rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioc, MeasureTheory.ae_iff]
  have hset : {t : ℝ | ¬ (t ∈ Set.Ioc a b → WithoutCollisions (γ t))} = S := by
    ext t
    simp only [hSdef, Set.mem_setOf_eq, Classical.not_imp]
  rw [hset]
  exact hvol

/-- The Newtonian potential is Borel measurable (it is a finite sum of compositions of continuous
functions with `x ↦ x⁻¹`). -/
lemma measurable_U (m : Fin N → ℝ) :
    @Measurable (EN E N) ℝ (borel (EN E N)) (borel ℝ) (U m) := by
  letI : MeasurableSpace (EN E N) := borel (EN E N)
  haveI : BorelSpace (EN E N) := ⟨rfl⟩
  unfold U r
  refine Finset.measurable_sum _ (fun j _ => Finset.measurable_sum _ (fun i _ => ?_))
  have hdist : Measurable (fun x : EN E N => (dist (x i) (x j))⁻¹) := by
    have h1 : Continuous (fun x : EN E N => x i) := PiLp.continuous_apply 2 (fun _ : Fin N => E) i
    have h2 : Continuous (fun x : EN E N => x j) := PiLp.continuous_apply 2 (fun _ : Fin N => E) j
    exact (h1.dist h2).measurable.inv
  exact (measurable_const : Measurable (fun _ : EN E N => m i * m j)).mul hdist

/-- **On an interval where the curve is collision free almost everywhere, the action is the real
integral of the real Lagrangian.**  (No continuity of the potential along the curve is needed: the
potential is Borel measurable, and the derivative of an absolutely continuous curve is a.e.
strongly measurable.) -/
theorem actionOn_eq_ofReal_integral_lagR_of_ae {m : Fin N → ℝ} {h : ℝ} {γ : ℝ → EN E N} {a b : ℝ}
    (hab : a ≤ b) (hm : ∀ i, 0 ≤ m i) (hh : 0 ≤ h)
    (hac : AbsolutelyContinuousOnInterval γ a b)
    (hnc : ∀ᵐ t ∂(volume.restrict (Set.Ioc a b)), WithoutCollisions (γ t))
    (hfin : actionOn m h γ a b < ⊤) :
    actionOn m h γ a b = ENNReal.ofReal (∫ t in a..b, lagR m h (γ t) (deriv γ t)) := by
  have hnn : ∀ t, 0 ≤ lagR m h (γ t) (deriv γ t) := by
    intro t
    rw [lagR]
    have hU := U_nonneg hm (γ t)
    have hK := kinetic_nonneg m hm (deriv γ t)
    rw [kinetic] at hK
    linarith
  have hpt : ∀ᵐ t ∂(volume.restrict (Set.Ioc a b)),
      lagrangian m h (γ t) (deriv γ t) = ENNReal.ofReal (lagR m h (γ t) (deriv γ t)) :=
    hnc.mono fun t ht => lagrangian_eq_ofReal_lagR ht
  have h1 : (∫⁻ t in Set.Ioc a b, ENNReal.ofReal (lagR m h (γ t) (deriv γ t)))
      = actionOn m h γ a b := by
    rw [actionOn]
    exact (lintegral_congr_ae hpt).symm
  letI : MeasurableSpace (EN E N) := borel (EN E N)
  haveI : BorelSpace (EN E N) := ⟨rfl⟩
  have hγmeas : AEMeasurable γ (volume.restrict (Set.Ioc a b)) :=
    (hac.continuousOn.mono (fun t ht => Set.mem_uIcc.mpr (Or.inl ⟨ht.1.le, ht.2⟩))).aestronglyMeasurable
      measurableSet_Ioc |>.aemeasurable
  have hmeas : AEStronglyMeasurable (fun t => lagR m h (γ t) (deriv γ t))
      (volume.restrict (Set.Ioc a b)) := by
    have hK : AEStronglyMeasurable (fun t => kinetic m (deriv γ t))
        (volume.restrict (Set.Ioc a b)) :=
      (continuous_kinetic m).aestronglyMeasurable.comp_aemeasurable
        (Commons.MeasureTheory.Integral.aestronglyMeasurable_deriv_of_absolutelyContinuousOnInterval
          hac).aemeasurable
    have hU : AEStronglyMeasurable (fun t => U m (γ t)) (volume.restrict (Set.Ioc a b)) :=
      (measurable_U m).aestronglyMeasurable.comp_aemeasurable hγmeas
    have hconst : AEStronglyMeasurable (fun _ : ℝ => h) (volume.restrict (Set.Ioc a b)) :=
      aestronglyMeasurable_const
    have hfun : (fun t : ℝ => lagR m h (γ t) (deriv γ t))
        = (fun t : ℝ => kinetic m (deriv γ t)) + ((fun t : ℝ => U m (γ t)) + fun _ => h) := by
      funext t
      simp only [lagR, kinetic, Pi.add_apply]
      ring
    rw [hfun]
    exact hK.add (hU.add hconst)
  have hInt : Integrable (fun t => lagR m h (γ t) (deriv γ t)) (volume.restrict (Set.Ioc a b)) := by
    refine ⟨hmeas, ?_⟩
    have h4 : (∫⁻ t in Set.Ioc a b, ‖lagR m h (γ t) (deriv γ t)‖ₑ)
        = ∫⁻ t in Set.Ioc a b, ENNReal.ofReal (lagR m h (γ t) (deriv γ t)) :=
      lintegral_congr fun t => by
        rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (hnn t)]
    have h3 : (∫⁻ t in Set.Ioc a b, ‖lagR m h (γ t) (deriv γ t)‖ₑ) < ⊤ := by
      rw [h4, h1]
      exact hfin
    simpa only [HasFiniteIntegral] using h3
  have h2 : (∫⁻ t in Set.Ioc a b, ENNReal.ofReal (lagR m h (γ t) (deriv γ t)))
      = ENNReal.ofReal (∫ t in Set.Ioc a b, lagR m h (γ t) (deriv γ t)) :=
    (MeasureTheory.ofReal_integral_eq_lintegral_ofReal hInt (Eventually.of_forall hnn)).symm
  have hfin' : actionOn m h γ a b
      = ENNReal.ofReal (∫ t in Set.Ioc a b, lagR m h (γ t) (deriv γ t)) := by
    rw [← h2]
    exact h1.symm
  rwa [intervalIntegral.integral_of_le hab]

/-! ## The `(0,T]`-collision-free versions

The following lemmas are the versions of the corresponding `EnergyLevel` lemmas in which collision
freeness is only assumed almost everywhere (which, by `ae_withoutCollisions_of_actionOn_lt_top`, is
automatic for a curve of finite action). -/

/-- The set of collision times of a curve continuous on `[min a b, max a b]` is measurable. -/
lemma measurableSet_collisions_of_continuousOn {γ : ℝ → EN E N} {a b : ℝ}
    (hcont : ContinuousOn γ (Set.uIcc a b)) :
    MeasurableSet {t ∈ Set.Ioc a b | ¬ WithoutCollisions (γ t)} := by
  have hclosed : IsClosed (Set.uIcc a b ∩ (fun t : ℝ => γ t) ⁻¹'
      {x : EN E N | ¬ WithoutCollisions x}) :=
    hcont.preimage_isClosed_of_isClosed isClosed_Icc isClosed_collisions
  have h1 : {t ∈ Set.Ioc a b | ¬ WithoutCollisions (γ t)}
      = (Set.uIcc a b ∩ (fun t : ℝ => γ t) ⁻¹' {x : EN E N | ¬ WithoutCollisions x})
        ∩ Set.Ioc a b := by
    ext t
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff, Set.mem_preimage]
    constructor
    · rintro ⟨⟨hta, htb⟩, hnc⟩
      exact ⟨⟨Set.mem_uIcc.mpr (Or.inl ⟨hta.le, htb⟩), hnc⟩, ⟨hta, htb⟩⟩
    · rintro ⟨⟨-, hnc⟩, ⟨hta, htb⟩⟩
      exact ⟨⟨hta, htb⟩, hnc⟩
  rw [h1]
  exact hclosed.measurableSet.inter measurableSet_Ioc

/-- `EnergyLevel.lintegral_kinetic_lt_top_of_actionOn_lt_top` with collision freeness only
almost everywhere. -/
lemma lintegral_kinetic_lt_top_of_actionOn_lt_top_of_ae {m : Fin N → ℝ} {h T : ℝ}
    {γ : ℝ → EN E N} (hm : ∀ i, 0 ≤ m i) (hh : 0 ≤ h)
    (hnc : ∀ᵐ t ∂(volume.restrict (Set.Ioc 0 T)), WithoutCollisions (γ t))
    (hfin : actionOn m h γ 0 T < ⊤) :
    (∫⁻ s in Set.Ioc 0 T, ENNReal.ofReal (kinetic m (deriv γ s))) < ⊤ ∧
      (∫⁻ s in Set.Ioc 0 T, pairPot m (γ s)) < ⊤ := by
  have hAT : actionOn m h γ 0 T = actionDec m h γ T := actionOn_eq_actionDec_of_ae hh hm hnc
  have hdec : actionDec m h γ T
      = (∫⁻ s in Set.Ioc 0 T, ENNReal.ofReal (kinetic m (deriv γ s)))
        + (∫⁻ s in Set.Ioc 0 T, pairPot m (γ s)) + ENNReal.ofReal h * ENNReal.ofReal T :=
    actionDec_eq h γ T
  have hlt : (∫⁻ s in Set.Ioc 0 T, ENNReal.ofReal (kinetic m (deriv γ s)))
      + (∫⁻ s in Set.Ioc 0 T, pairPot m (γ s)) + ENNReal.ofReal h * ENNReal.ofReal T < ⊤ := by
    rw [← hdec, ← hAT]; exact hfin
  exact ⟨lt_of_le_of_lt (le_trans le_self_add le_self_add) hlt,
    lt_of_le_of_lt (le_trans (le_add_left le_rfl) le_self_add) hlt⟩

/-- `EnergyLevel.lintegral_ofReal_U_eq_lintegral_pairPot` with collision freeness only almost
everywhere. -/
lemma lintegral_ofReal_U_eq_lintegral_pairPot_of_ae {m : Fin N → ℝ} {T : ℝ} {γ : ℝ → EN E N}
    (hm : ∀ i, 0 ≤ m i)
    (hnc : ∀ᵐ t ∂(volume.restrict (Set.Ioc 0 T)), WithoutCollisions (γ t)) :
    (∫⁻ s in Set.Ioc 0 T, ENNReal.ofReal (U m (γ s)))
      = ∫⁻ s in Set.Ioc 0 T, pairPot m (γ s) := by
  refine lintegral_congr_ae ?_
  filter_upwards [hnc] with s hs
  exact (pairPot_eq_ofReal_U hm hs).symm

/-- **Collision freeness transfers to a linear reparametrisation.**  If `γ` is collision free almost
everywhere on `(0,T]` then `t ↦ γ ((T/τ) t)` is collision free almost everywhere on `(0,τ]`. -/
lemma ae_withoutCollisions_comp_mul_left {γ : ℝ → EN E N} {T τ : ℝ} (hT : 0 < T) (hτ : 0 < τ)
    (hcont : ContinuousOn γ (Set.uIcc 0 T))
    (hnc : ∀ᵐ t ∂(volume.restrict (Set.Ioc 0 T)), WithoutCollisions (γ t)) :
    ∀ᵐ t ∂(volume.restrict (Set.Ioc 0 τ)), WithoutCollisions (γ ((T / τ) * t)) := by
  have hTτ : (0:ℝ) < T / τ := div_pos hT hτ
  set Z : Set ℝ := {t ∈ Set.Ioc 0 T | ¬ WithoutCollisions (γ t)} with hZdef
  have hZnull : volume Z = 0 := by
    rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioc, MeasureTheory.ae_iff] at hnc
    rw [← hnc]
    congr 1
    ext t
    simp only [hZdef, Set.mem_setOf_eq, Set.mem_Ioc, Classical.not_imp]
  have hpre : volume ((fun t : ℝ => (T / τ) * t) ⁻¹' Z) = 0 := by
    rw [Real.volume_preimage_mul_left (ne_of_gt hTτ), hZnull, mul_zero]
  have hmain : volume ((fun t : ℝ => (T / τ) * t) ⁻¹' Z ∩ Set.Ioc 0 τ) = 0 :=
    measure_mono_null Set.inter_subset_left hpre
  rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioc, MeasureTheory.ae_iff]
  have hset : {t : ℝ | ¬ (t ∈ Set.Ioc 0 τ → WithoutCollisions (γ ((T / τ) * t)))}
      = (fun t : ℝ => (T / τ) * t) ⁻¹' Z ∩ Set.Ioc 0 τ := by
    ext t
    simp only [Set.mem_setOf_eq, Classical.not_imp, Set.mem_inter_iff, Set.mem_preimage, hZdef,
      Set.mem_Ioc]
    constructor
    · rintro ⟨⟨ht0, htτ⟩, hnc'⟩
      refine ⟨⟨⟨mul_pos hTτ ht0, ?_⟩, hnc'⟩, ht0, htτ⟩
      have h5 : (T / τ) * t ≤ (T / τ) * τ := mul_le_mul_of_nonneg_left htτ hTτ.le
      rwa [div_mul_cancel₀ _ (ne_of_gt hτ)] at h5
    · rintro ⟨⟨⟨-, -⟩, hnc'⟩, ht0, htτ⟩
      exact ⟨⟨ht0, htτ⟩, hnc'⟩
  rw [hset]
  exact hmain

/-- **The action of a linearly reparametrised curve, in real terms**, with collision freeness
assumed only almost everywhere (`EnergyLevel.actionOn_comp_mul_left` with a weaker hypothesis). -/
lemma actionOn_comp_mul_left_of_ae {m : Fin N → ℝ} {h T τ : ℝ} {γ : ℝ → EN E N}
    (hT : 0 < T) (hτ : 0 < τ) (hm : ∀ i, 0 ≤ m i) (hh : 0 ≤ h)
    (hac : AbsolutelyContinuousOnInterval γ 0 T)
    (hnc : ∀ᵐ t ∂(volume.restrict (Set.Ioc 0 T)), WithoutCollisions (γ t))
    (hfin : actionOn m h γ 0 T < ⊤) :
    actionOn m h (fun s : ℝ => γ ((T / τ) * s)) 0 τ
      = ENNReal.ofReal ((T / τ) * kineticIntegral m γ T + (τ / T) * potentialIntegral m γ T
          + h * τ) := by
  obtain ⟨hK1, hP1⟩ := lintegral_kinetic_lt_top_of_actionOn_lt_top_of_ae hm hh hnc hfin
  have hK : (∫⁻ s in Set.Ioc 0 T, ENNReal.ofReal (kinetic m (deriv γ s)))
      = ENNReal.ofReal (kineticIntegral m γ T) := (ENNReal.ofReal_toReal hK1.ne).symm
  have hP : (∫⁻ s in Set.Ioc 0 T, pairPot m (γ s))
      = ENNReal.ofReal (potentialIntegral m γ T) := (ENNReal.ofReal_toReal hP1.ne).symm
  have hnc' : ∀ᵐ t ∂(volume.restrict (Set.Ioc 0 τ)),
      WithoutCollisions ((fun s : ℝ => γ ((T / τ) * s)) t) :=
    ae_withoutCollisions_comp_mul_left hT hτ hac.continuousOn hnc
  have hAO : actionDec m h (fun s : ℝ => γ ((T / τ) * s)) τ
      = actionOn m h (fun s : ℝ => γ ((T / τ) * s)) 0 τ :=
    (actionOn_eq_actionDec_of_ae hh hm hnc').symm
  have hcomp := actionDec_comp_mul_left_eq (m := m) (h := h) (γ := γ) hT hτ
  rw [hAO, hK, hP] at hcomp
  have hKm : 0 ≤ kineticIntegral m γ T := kineticIntegral_nonneg m γ T
  have hPm : 0 ≤ potentialIntegral m γ T := potentialIntegral_nonneg m γ T
  rw [hcomp, ofReal_mul_add_reparam hT hτ hKm hPm hh]

/-- `EnergyLevel.integral_U_eq_potentialIntegral` with collision freeness only almost everywhere. -/
lemma integral_U_eq_potentialIntegral_of_ae {m : Fin N → ℝ} {T : ℝ} {γ : ℝ → EN E N}
    (hm : ∀ i, 0 ≤ m i)
    (hnc : ∀ᵐ t ∂(volume.restrict (Set.Ioc 0 T)), WithoutCollisions (γ t))
    (hac : AbsolutelyContinuousOnInterval γ 0 T)
    (h : (∫⁻ s in Set.Ioc 0 T, pairPot m (γ s)) < ⊤) :
    ∫ s in Set.Ioc 0 T, U m (γ s) = potentialIntegral m γ T := by
  have hpair := lintegral_ofReal_U_eq_lintegral_pairPot_of_ae (m := m) (T := T) hm hnc
  letI : MeasurableSpace (EN E N) := borel (EN E N)
  haveI : BorelSpace (EN E N) := ⟨rfl⟩
  have hγmeas : AEMeasurable γ (volume.restrict (Set.Ioc 0 T)) :=
    (hac.continuousOn.mono (fun t ht => Set.mem_uIcc.mpr (Or.inl ⟨ht.1.le, ht.2⟩))).aestronglyMeasurable
      measurableSet_Ioc |>.aemeasurable
  have hU : AEStronglyMeasurable (fun s : ℝ => U m (γ s)) (volume.restrict (Set.Ioc 0 T)) :=
    (measurable_U m).aestronglyMeasurable.comp_aemeasurable hγmeas
  have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioc 0 T)] fun s => U m (γ s) :=
    Filter.Eventually.of_forall fun s => U_nonneg hm (γ s)
  have hint : Integrable (fun s : ℝ => U m (γ s)) (volume.restrict (Set.Ioc 0 T)) :=
    (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable hU hnn).mp (by rw [hpair]; exact h.ne)
  have hbridge := MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint hnn
  have h1 : ENNReal.ofReal (∫ s in Set.Ioc 0 T, U m (γ s))
      = ENNReal.ofReal (potentialIntegral m γ T) := by
    rw [hbridge, hpair]
    exact (ENNReal.ofReal_toReal h.ne).symm
  have h2 : 0 ≤ ∫ s in Set.Ioc 0 T, U m (γ s) :=
    MeasureTheory.integral_nonneg fun s => U_nonneg hm (γ s)
  have h3 : 0 ≤ potentialIntegral m γ T := potentialIntegral_nonneg m γ T
  have h4 := congrArg ENNReal.toReal h1
  rwa [ENNReal.toReal_ofReal h2, ENNReal.toReal_ofReal h3] at h4

/-- **The energy of an `h`-minimiser is `h` almost everywhere**, with no collision-freeness
hypothesis: the finiteness of the action already forces the collision set to be null. -/
theorem ae_energy_eq_of_minimizer {m : Fin N → ℝ} {h : ℝ} {γ : ℝ → EN E N} {τ : ℝ}
    (hm : ∀ i, 0 < m i) (hh : 0 ≤ h) (hτ : 0 < τ)
    (hac : AbsolutelyContinuousOnInterval γ 0 τ)
    (hmin : IsHMinimizer m h γ 0 τ)
    (hfin : actionPot m h (γ 0) (γ τ) < ⊤) :
    ∀ᵐ s ∂(volume.restrict (Set.Ioo 0 τ)), energy m γ s = h := by
  classical
  letI : MeasurableSpace (EN E N) := borel (EN E N)
  haveI : BorelSpace (EN E N) := ⟨rfl⟩
  have hm0 : ∀ i, 0 ≤ m i := fun i => (hm i).le
  have hOn : actionOn m h γ 0 τ < ⊤ := hmin ▸ hfin
  have hnc : ∀ᵐ t ∂(volume.restrict (Set.Ioc 0 τ)), WithoutCollisions (γ t) :=
    ae_withoutCollisions_of_actionOn_lt_top hac hOn
  obtain ⟨hK1, hP1⟩ := lintegral_kinetic_lt_top_of_actionOn_lt_top_of_ae hm0 hh hnc hOn
  -- the linearity of the integral
  have hmeasK : AEStronglyMeasurable (fun s : ℝ => kinetic m (deriv γ s))
      (volume.restrict (Set.Ioc 0 τ)) :=
    (continuous_kinetic m).aestronglyMeasurable.comp_aemeasurable
      (Commons.MeasureTheory.Integral.aestronglyMeasurable_deriv_of_absolutelyContinuousOnInterval hac).aemeasurable
  have hmeasU : AEStronglyMeasurable (fun s : ℝ => U m (γ s)) (volume.restrict (Set.Ioc 0 τ)) := by
    have hγmeas : AEMeasurable γ (volume.restrict (Set.Ioc 0 τ)) :=
      (hac.continuousOn.mono (fun t ht => Set.mem_uIcc.mpr (Or.inl ⟨ht.1.le, ht.2⟩))).aestronglyMeasurable
        measurableSet_Ioc |>.aemeasurable
    exact (measurable_U m).aestronglyMeasurable.comp_aemeasurable hγmeas
  have hintK : Integrable (fun s : ℝ => kinetic m (deriv γ s)) (volume.restrict (Set.Ioc 0 τ)) :=
    (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable hmeasK
      (Filter.Eventually.of_forall fun s => kinetic_nonneg m hm0 (deriv γ s))).mp hK1.ne
  have hP1U : (∫⁻ a in Set.Ioc 0 τ, ENNReal.ofReal (U m (γ a))) < ⊤ := by
    rw [lintegral_ofReal_U_eq_lintegral_pairPot_of_ae hm0 hnc]; exact hP1
  have hintU : Integrable (fun s : ℝ => U m (γ s)) (volume.restrict (Set.Ioc 0 τ)) :=
    (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable hmeasU
      (Filter.Eventually.of_forall fun s => U_nonneg hm0 (γ s))).mp hP1U.ne
  -- (1) the identity on every `[0,t]`
  have hzero : ∀ t : ℝ, 0 < t → t ≤ τ → ∫ s in (0:ℝ)..t, (energy m γ s - h) = 0 := by
    intro t ht htτ
    have hOn_t : actionOn m h γ 0 t < ⊤ := actionOn_lt_top_of_le ht.le htτ hOn
    have hnc_t : ∀ᵐ s ∂(volume.restrict (Set.Ioc 0 t)), WithoutCollisions (γ s) := by
      rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioc] at hnc ⊢
      exact hnc.mono (fun s hs hst => hs ⟨hst.1, le_trans hst.2 htτ⟩)
    obtain ⟨hK1', hP1'⟩ := lintegral_kinetic_lt_top_of_actionOn_lt_top_of_ae hm0 hh hnc_t hOn_t
    have hac_t : AbsolutelyContinuousOnInterval γ 0 t := hac.mono (by
      rw [uIcc_of_le ht.le, uIcc_of_le hτ.le]
      exact Set.Icc_subset_Icc_right htτ)
    have hmin_t : IsHMinimizer m h γ 0 t := IsHMinimizer.sub_left_of_le hac hmin hOn ht htτ
    -- (a) the action as an `ofReal`
    have hA : actionOn m h γ 0 t
        = ENNReal.ofReal (kineticIntegral m γ t + potentialIntegral m γ t + h * t) := by
      have hAT : actionOn m h γ 0 t = actionDec m h γ t := actionOn_eq_actionDec_of_ae hh hm0 hnc_t
      have hKof : (∫⁻ s in Set.Ioc 0 t, ENNReal.ofReal (kinetic m (deriv γ s)))
          = ENNReal.ofReal (kineticIntegral m γ t) := (ENNReal.ofReal_toReal hK1'.ne).symm
      have hPof : (∫⁻ s in Set.Ioc 0 t, pairPot m (γ s))
          = ENNReal.ofReal (potentialIntegral m γ t) := (ENNReal.ofReal_toReal hP1'.ne).symm
      rw [hAT, actionDec_eq h γ t, hKof, hPof, ofReal_add_mul_ofReal ht.le
        (kineticIntegral_nonneg m γ t) (potentialIntegral_nonneg m γ t) hh]
    -- (b) the reparametrisation inequality
    have hineq : ∀ s : ℝ, 0 < s → kineticIntegral m γ t + potentialIntegral m γ t + h * t
        ≤ (t / s) * kineticIntegral m γ t + (s / t) * potentialIntegral m γ t + h * s := by
      intro s hs
      have hAC' : AbsolutelyContinuousOnInterval (fun u : ℝ => γ ((t / s) * u)) 0 s := by
        have h1 : t / (t / s) = s := by field_simp
        have h := Commons.MeasureTheory.Integral.absolutelyContinuousOnInterval_comp_affine
          (f := γ) (a := 0) (b := t) (c := t / s) (d := 0) (div_ne_zero ht.ne' hs.ne') hac_t
        simpa [h1] using h
      have h1 : actionOn m h (fun u : ℝ => γ ((t / s) * u)) 0 s
          = ENNReal.ofReal ((t / s) * kineticIntegral m γ t
              + (s / t) * potentialIntegral m γ t + h * s) :=
        actionOn_comp_mul_left_of_ae (m := m) (h := h) (T := t) (τ := s) ht hs hm0 hh hac_t
          hnc_t hOn_t
      have h2 : actionPot m h (γ 0) (γ t) ≤ actionOn m h (fun u : ℝ => γ ((t / s) * u)) 0 s :=
        actionPot_le_of hs (by simp) (by
          show γ ((t / s) * s) = γ t
          rw [div_mul_cancel₀ _ (ne_of_gt hs)]) hAC'
      rw [h1] at h2
      have h3 : ENNReal.ofReal (kineticIntegral m γ t + potentialIntegral m γ t + h * t)
          ≤ ENNReal.ofReal ((t / s) * kineticIntegral m γ t
              + (s / t) * potentialIntegral m γ t + h * s) := by
        rw [← hA, hmin_t]; exact h2
      have hnn : 0 ≤ (t / s) * kineticIntegral m γ t + (s / t) * potentialIntegral m γ t + h * s :=
        add_nonneg (add_nonneg (mul_nonneg (div_pos ht hs).le (kineticIntegral_nonneg m γ t))
          (mul_nonneg (div_pos hs ht).le (potentialIntegral_nonneg m γ t))) (mul_nonneg hh hs.le)
      exact (ENNReal.ofReal_le_ofReal_iff hnn).mp h3
    have hKP : kineticIntegral m γ t - potentialIntegral m γ t = h * t :=
      sub_eq_of_reparam_min ht hineq
    -- (c) the real integrals
    have hKin : ∫ s in (0:ℝ)..t, kinetic m (deriv γ s) = kineticIntegral m γ t := by
      rw [intervalIntegral.integral_of_le ht.le]
      exact integral_kinetic_eq_kineticIntegral hm0 hac_t hK1'
    have hPot : ∫ s in (0:ℝ)..t, U m (γ s) = potentialIntegral m γ t := by
      rw [intervalIntegral.integral_of_le ht.le]
      exact integral_U_eq_potentialIntegral_of_ae hm0 hnc_t hac_t hP1'
    have hintK_t : Integrable (fun s : ℝ => kinetic m (deriv γ s)) (volume.restrict (Set.Ioc 0 t)) :=
      (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable
        ((continuous_kinetic m).aestronglyMeasurable.comp_aemeasurable
          (Commons.MeasureTheory.Integral.aestronglyMeasurable_deriv_of_absolutelyContinuousOnInterval
            hac_t).aemeasurable)
        (Filter.Eventually.of_forall fun s => kinetic_nonneg m hm0 (deriv γ s))).mp hK1'.ne
    have hP1U_t : (∫⁻ a in Set.Ioc 0 t, ENNReal.ofReal (U m (γ a))) < ⊤ := by
      rw [lintegral_ofReal_U_eq_lintegral_pairPot_of_ae hm0 hnc_t]; exact hP1'
    have hintU_t : Integrable (fun s : ℝ => U m (γ s)) (volume.restrict (Set.Ioc 0 t)) := by
      refine (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable ?_
        (Filter.Eventually.of_forall fun s => U_nonneg hm0 (γ s))).mp hP1U_t.ne
      exact (measurable_U m).aestronglyMeasurable.comp_aemeasurable
        ((hac_t.continuousOn.mono (fun s hs => Set.mem_uIcc.mpr (Or.inl ⟨hs.1.le, hs.2⟩))).aestronglyMeasurable
          measurableSet_Ioc |>.aemeasurable)
    have hIK : IntervalIntegrable (fun s : ℝ => kinetic m (deriv γ s)) volume 0 t :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le ht.le).mpr hintK_t
    have hIU : IntervalIntegrable (fun s : ℝ => U m (γ s)) volume 0 t :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le ht.le).mpr hintU_t
    have hKinI : ∫ s in (0:ℝ)..t, kinetic m (deriv γ s) = kineticIntegral m γ t := by
      rw [intervalIntegral.integral_of_le ht.le]
      exact integral_kinetic_eq_kineticIntegral hm0 hac_t hK1'
    have hPotI : ∫ s in (0:ℝ)..t, U m (γ s) = potentialIntegral m γ t := by
      rw [intervalIntegral.integral_of_le ht.le]
      exact integral_U_eq_potentialIntegral_of_ae hm0 hnc_t hac_t hP1'
    have hintK_t : Integrable (fun s : ℝ => kinetic m (deriv γ s)) (volume.restrict (Set.Ioc 0 t)) :=
      (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable
        ((continuous_kinetic m).aestronglyMeasurable.comp_aemeasurable
          (Commons.MeasureTheory.Integral.aestronglyMeasurable_deriv_of_absolutelyContinuousOnInterval
            hac_t).aemeasurable)
        (Filter.Eventually.of_forall fun s => kinetic_nonneg m hm0 (deriv γ s))).mp hK1'.ne
    have hP1U_t : (∫⁻ a in Set.Ioc 0 t, ENNReal.ofReal (U m (γ a))) < ⊤ := by
      rw [lintegral_ofReal_U_eq_lintegral_pairPot_of_ae hm0 hnc_t]; exact hP1'
    have hintU_t : Integrable (fun s : ℝ => U m (γ s)) (volume.restrict (Set.Ioc 0 t)) :=
      (MeasureTheory.lintegral_ofReal_ne_top_iff_integrable
        ((measurable_U m).aestronglyMeasurable.comp_aemeasurable
          ((hac_t.continuousOn.mono (fun s hs => Set.mem_uIcc.mpr (Or.inl ⟨hs.1.le, hs.2⟩))).aestronglyMeasurable
            measurableSet_Ioc |>.aemeasurable))
        (Filter.Eventually.of_forall fun s => U_nonneg hm0 (γ s))).mp hP1U_t.ne
    have hIK : IntervalIntegrable (fun s : ℝ => kinetic m (deriv γ s)) volume 0 t :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le ht.le).mpr hintK_t
    have hIU : IntervalIntegrable (fun s : ℝ => U m (γ s)) volume 0 t :=
      (intervalIntegrable_iff_integrableOn_Ioc_of_le ht.le).mpr hintU_t
    have hcon : ∀ s : ℝ, energy m γ s - h = kinetic m (deriv γ s) - U m (γ s) - h := by
      intro s; rw [energy_eq_kinetic_sub_U]
    have h1 : (∫ s in (0:ℝ)..t, (kinetic m (deriv γ s) - U m (γ s) - h))
        = (∫ s in (0:ℝ)..t, (kinetic m (deriv γ s) - U m (γ s)))
          - (∫ s in (0:ℝ)..t, h) :=
      intervalIntegral.integral_sub (hIK.sub hIU) intervalIntegrable_const
    have h2 : (∫ s in (0:ℝ)..t, (kinetic m (deriv γ s) - U m (γ s)))
        = (∫ s in (0:ℝ)..t, kinetic m (deriv γ s)) - (∫ s in (0:ℝ)..t, U m (γ s)) :=
      intervalIntegral.integral_sub hIK hIU
    have h3 : (∫ s in (0:ℝ)..t, h) = h * t := by
      rw [intervalIntegral.integral_const, smul_eq_mul, sub_zero, mul_comm]
    rw [intervalIntegral.integral_congr (fun s _ => hcon s), h1, h2, h3, hKinI, hPotI]
    linarith [hKP]
  -- (2) the indefinite integral is constant, so the differentiation theorem gives the result
  have hintK_τ : IntervalIntegrable (fun s : ℝ => kinetic m (deriv γ s)) volume 0 τ :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hτ.le).mpr hintK
  have hintU_τ : IntervalIntegrable (fun s : ℝ => U m (γ s)) volume 0 τ :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hτ.le).mpr hintU
  have hInt_f : IntervalIntegrable (fun s : ℝ => energy m γ s - h) volume 0 τ := by
    have h1 : (fun s : ℝ => energy m γ s - h)
        = fun s => kinetic m (deriv γ s) - U m (γ s) - h := by
      funext s; rw [energy_eq_kinetic_sub_U]
    rw [h1]
    exact (hintK_τ.sub hintU_τ).sub intervalIntegrable_const
  have hAE : ∀ᵐ x ∂(volume.restrict (Set.Ioo 0 τ)), energy m γ x - h = 0 := by
    have h1 := MeasureTheory.ae_restrict_of_ae (s := Set.Ioo 0 τ)
      (IntervalIntegrable.ae_hasDerivAt_integral hInt_f)
    filter_upwards [h1, MeasureTheory.ae_restrict_mem measurableSet_Ioo] with x hx hxIoo
    have hxmem : x ∈ Set.uIcc (0:ℝ) τ := by
      rw [uIcc_of_le hτ.le]; exact ⟨hxIoo.1.le, hxIoo.2.le⟩
    have hzmem : (0:ℝ) ∈ Set.uIcc (0:ℝ) τ := by
      rw [uIcc_of_le hτ.le]; exact ⟨le_rfl, hτ.le⟩
    have h2 : HasDerivAt (fun u : ℝ => ∫ s in (0:ℝ)..u, (energy m γ s - h))
        (energy m γ x - h) x := hx hxmem 0 hzmem
    have h3 : HasDerivAt (fun u : ℝ => ∫ s in (0:ℝ)..u, (energy m γ s - h)) 0 x := by
      refine (hasDerivAt_const x (0:ℝ)).congr_of_eventuallyEq ?_
      filter_upwards [isOpen_Ioo.mem_nhds hxIoo] with u hu
      exact hzero u hu.1 (le_of_lt hu.2)
    exact h2.unique h3
  filter_upwards [hAE] with x hx
  linarith

/-- **The Marchal-free energy identity.**  For an `h`-minimiser of finite action on `[0,τ]`,
`∫₀^τ ‖γ̇‖²_[m] = (A_{L+h}(γ)).toReal` — with *no* collision-freeness hypothesis. -/
theorem integral_weightedNorm_sq_eq_actionOn_of_min {m : Fin N → ℝ} {h : ℝ} {γ : ℝ → EN E N}
    {τ : ℝ} (hm : ∀ i, 0 < m i) (hh : 0 ≤ h) (hτ : 0 < τ)
    (hac : AbsolutelyContinuousOnInterval γ 0 τ)
    (hmin : IsHMinimizer m h γ 0 τ)
    (hfin : actionPot m h (γ 0) (γ τ) < ⊤) :
    ∫ s in (0:ℝ)..τ, ‖deriv γ s‖_[m] ^ 2 = (actionOn m h γ 0 τ).toReal := by
  have hm0 : ∀ i, 0 ≤ m i := fun i => (hm i).le
  have hOn : actionOn m h γ 0 τ < ⊤ := hmin ▸ hfin
  have hnc := ae_withoutCollisions_of_actionOn_lt_top hac hOn
  have h1 : actionOn m h γ 0 τ
      = ENNReal.ofReal (∫ s in (0:ℝ)..τ, lagR m h (γ s) (deriv γ s)) :=
    actionOn_eq_ofReal_integral_lagR_of_ae hτ.le hm0 hh hac hnc hOn
  have hlagR0 : ∀ s : ℝ, 0 ≤ lagR m h (γ s) (deriv γ s) := by
    intro s
    rw [lagR]
    have hU := U_nonneg hm0 (γ s)
    have hK := kinetic_nonneg m hm0 (deriv γ s)
    rw [kinetic] at hK
    linarith
  have h2 : (actionOn m h γ 0 τ).toReal = ∫ s in (0:ℝ)..τ, lagR m h (γ s) (deriv γ s) := by
    rw [h1, ENNReal.toReal_ofReal (intervalIntegral.integral_nonneg hτ.le (fun s _ => hlagR0 s))]
  rw [h2]
  refine intervalIntegral.integral_congr_ae ?_
  have hE := (MeasureTheory.ae_restrict_iff' measurableSet_Ioo).mp
    (ae_energy_eq_of_minimizer hm hh hτ hac hmin hfin)
  have h0 : ∀ᵐ s : ℝ ∂volume, s ≠ 0 := by
    rw [MeasureTheory.ae_iff]; simp
  have hτ' : ∀ᵐ s : ℝ ∂volume, s ≠ τ := by
    rw [MeasureTheory.ae_iff]; simp
  filter_upwards [hE, h0, hτ'] with s hs hs0 hsτ huIoc
  have hsIoo : s ∈ Set.Ioo (0:ℝ) τ := by
    rw [uIoc_of_le hτ.le] at huIoc
    exact ⟨huIoc.1, lt_of_le_of_ne huIoc.2 hsτ⟩
  have henergy : energy m γ s = h := hs hsIoo
  have h3 : kinetic m (deriv γ s) - U m (γ s) = h := henergy
  have hk : kinetic m (deriv γ s) = (1 / 2) * ∑ i, m i * ‖(deriv γ s) i‖ ^ 2 := rfl
  have hw := weightedNorm_sq hm0 (deriv γ s)
  rw [lagR, hw]
  have h4 : (1 / 2) * ∑ i, m i * ‖(deriv γ s) i‖ ^ 2 = U m (γ s) + h := by
    rw [← hk]; linarith
  linarith [h4]

/-- **The Marchal-free speed bound.**  Along an `h`-minimiser of finite action, `√(2h) ≤ ‖γ̇‖_[m]`
almost everywhere. -/
theorem ae_sqrt_two_h_le_weightedNorm_of_min {m : Fin N → ℝ} {h : ℝ} {γ : ℝ → EN E N} {τ : ℝ}
    (hm : ∀ i, 0 < m i) (hh : 0 < h) (hτ : 0 < τ)
    (hac : AbsolutelyContinuousOnInterval γ 0 τ)
    (hmin : IsHMinimizer m h γ 0 τ)
    (hfin : actionPot m h (γ 0) (γ τ) < ⊤) :
    ∀ᵐ s ∂(volume.restrict (Set.Ioo 0 τ)), Real.sqrt (2 * h) ≤ ‖deriv γ s‖_[m] := by
  have hm0 : ∀ i, 0 ≤ m i := fun i => (hm i).le
  have hE := ae_energy_eq_of_minimizer hm hh.le hτ hac hmin hfin
  filter_upwards [hE] with s hs
  have hk : kinetic m (deriv γ s) = (1 / 2) * ∑ i, m i * ‖(deriv γ s) i‖ ^ 2 := rfl
  have hU := U_nonneg hm0 (γ s)
  have hx : 0 ≤ ‖deriv γ s‖_[m] := weightedNorm_nonneg m _
  have h1 : (1 / 2) * ∑ i, m i * ‖(deriv γ s) i‖ ^ 2 - U m (γ s) = h := by
    rw [← hk]; exact hs
  have h2 : (‖deriv γ s‖_[m]) ^ 2 = 2 * (U m (γ s) + h) := by
    rw [weightedNorm_sq hm0]
    linarith [h1]
  have h3 : 2 * h ≤ (‖deriv γ s‖_[m]) ^ 2 := by linarith
  calc Real.sqrt (2 * h) ≤ Real.sqrt ((‖deriv γ s‖_[m]) ^ 2) := Real.sqrt_le_sqrt h3
    _ = ‖deriv γ s‖_[m] := Real.sqrt_sq hx

/-- The energy identity of `ae_energy_eq_of_minimizer` in the `Ioc` form used by the estimates. -/
lemma ae_energy_eq_of_minimizer_Ioc {m : Fin N → ℝ} {h : ℝ} {γ : ℝ → EN E N} {τ : ℝ}
    (hm : ∀ i, 0 < m i) (hh : 0 ≤ h) (hτ : 0 < τ)
    (hac : AbsolutelyContinuousOnInterval γ 0 τ)
    (hmin : IsHMinimizer m h γ 0 τ)
    (hfin : actionPot m h (γ 0) (γ τ) < ⊤) :
    ∀ᵐ s ∂(volume.restrict (Set.Ioc 0 τ)), energy m γ s = h := by
  rw [MeasureTheory.ae_restrict_iff' measurableSet_Ioc]
  have h1 := (MeasureTheory.ae_restrict_iff' measurableSet_Ioo).mp
    (ae_energy_eq_of_minimizer hm hh hτ hac hmin hfin)
  have ht' : ∀ᵐ s : ℝ ∂volume, s ≠ τ := by rw [MeasureTheory.ae_iff]; simp
  filter_upwards [h1, ht'] with s hs hst hsIoc
  exact hs ⟨hsIoc.1, lt_of_le_of_ne hsIoc.2 hst⟩

/-- `lagR` is the squared mass norm of the velocity a.e. along an `h`-minimiser of finite action
(no collision-freeness hypothesis). -/
lemma ae_lagR_eq_weightedNorm_sq_of_min {m : Fin N → ℝ} {h : ℝ} {γ : ℝ → EN E N} {τ : ℝ}
    (hm : ∀ i, 0 < m i) (hh : 0 ≤ h) (hτ : 0 < τ)
    (hac : AbsolutelyContinuousOnInterval γ 0 τ)
    (hmin : IsHMinimizer m h γ 0 τ)
    (hfin : actionPot m h (γ 0) (γ τ) < ⊤) :
    ∀ᵐ s ∂(volume.restrict (Set.Ioo 0 τ)),
      lagR m h (γ s) (deriv γ s) = ‖deriv γ s‖_[m] ^ 2 := by
  have hm0 : ∀ i, 0 ≤ m i := fun i => (hm i).le
  have hE := ae_energy_eq_of_minimizer hm hh hτ hac hmin hfin
  filter_upwards [hE] with s hs
  have hk : kinetic m (deriv γ s) = (1 / 2) * ∑ i, m i * ‖(deriv γ s) i‖ ^ 2 := rfl
  have h1 : kinetic m (deriv γ s) - U m (γ s) = h := hs
  have h4 : (1 / 2) * ∑ i, m i * ‖(deriv γ s) i‖ ^ 2 = U m (γ s) + h := by
    rw [← hk]; linarith
  rw [lagR, weightedNorm_sq hm0 (deriv γ s)]
  linarith [h4]

/-- Pointwise form: where the energy of a curve equals `h`, the Lagrangian is the squared mass norm
of the velocity. -/
lemma lagR_eq_weightedNorm_sq_of_energy_eq {m : Fin N → ℝ} {h : ℝ} {γ : ℝ → EN E N} {s : ℝ}
    (hm : ∀ i, 0 ≤ m i) (hE : energy m γ s = h) :
    lagR m h (γ s) (deriv γ s) = ‖deriv γ s‖_[m] ^ 2 := by
  have hk : kinetic m (deriv γ s) = (1 / 2) * ∑ i, m i * ‖(deriv γ s) i‖ ^ 2 := rfl
  have h1 : (1 / 2) * ∑ i, m i * ‖(deriv γ s) i‖ ^ 2 - U m (γ s) = h := by
    rw [← hk]; exact hE
  have h4 : (1 / 2) * ∑ i, m i * ‖(deriv γ s) i‖ ^ 2 = U m (γ s) + h := by linarith
  rw [lagR, weightedNorm_sq hm (deriv γ s)]
  linarith [h4]

/-- Pointwise form: where the energy of a curve equals `h > 0`, the speed is at least `√(2h)`. -/
lemma sqrt_two_h_le_weightedNorm_of_energy_eq {m : Fin N → ℝ} {h : ℝ} {γ : ℝ → EN E N} {s : ℝ}
    (hm : ∀ i, 0 ≤ m i) (hE : energy m γ s = h) :
    Real.sqrt (2 * h) ≤ ‖deriv γ s‖_[m] := by
  have hk : kinetic m (deriv γ s) = (1 / 2) * ∑ i, m i * ‖(deriv γ s) i‖ ^ 2 := rfl
  have h1 : (1 / 2) * ∑ i, m i * ‖(deriv γ s) i‖ ^ 2 - U m (γ s) = h := by
    rw [← hk]; exact hE
  have h2 : (‖deriv γ s‖_[m]) ^ 2 = 2 * (U m (γ s) + h) := by
    rw [weightedNorm_sq hm]
    linarith [h1]
  have h3 : 2 * h ≤ (‖deriv γ s‖_[m]) ^ 2 := by
    have hU := U_nonneg hm (γ s); linarith [h2]
  have hx : 0 ≤ ‖deriv γ s‖_[m] := weightedNorm_nonneg m _
  calc Real.sqrt (2 * h) ≤ Real.sqrt ((‖deriv γ s‖_[m]) ^ 2) := Real.sqrt_le_sqrt h3
    _ = ‖deriv γ s‖_[m] := Real.sqrt_sq hx

end Submission.NBody
