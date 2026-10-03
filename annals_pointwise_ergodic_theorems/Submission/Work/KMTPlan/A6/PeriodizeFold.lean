import Mathlib
import Submission.Work.KMTPlan.A6.projVanishingG

/-!
# The periodisation / "fold" identity on the frequency circle `ℝ/ℤ`

For an integrable `φ : ℝ → ℂ` and a continuous `X : ℝ/ℤ → ℂ` we prove

  `∫ t, periodize φ t * X t ∂circleMeasure = ∫ x, φ x * X (x : ℝ/ℤ)`,

where `periodize φ ξ = ∑' k : ℤ, φ (x₀ + k)` (`x₀ ∈ [0,1)` the canonical representative of `ξ`).

This is the standard unfolding of the Haar measure of `ℝ/ℤ` (`circleMeasure`, of total mass `1`)
against the covering `ℝ → ℝ/ℤ`:

* the interval `(0,1]` is a fundamental domain for the group `ℤ • 1 ⊆ ℝ`;
* on `(0,1]` the integrand `periodize φ t * X t` equals `∑' k, g (a + k)`, where
  `g x = φ x * X (x : ℝ/ℤ)` — the periodisation of `g`;
* interchanging the sum with the integral (Tonelli, using `g ∈ L¹(ℝ)`) and splitting `∫_ℝ g`
  into the pieces over `(k, k+1]` (the fundamental-domain decomposition, indexed by
  `ℤ ≃ ℤ • 1`) gives the claim.

The whole content is thus that the sum over the `ℤ`-orbit defining `periodize` and the
sum over the translates of the fundamental domain defining `∫_ℝ` are the same sum.
-/

namespace Work.KMTPlan.A6

open MeasureTheory MeasureTheory.Measure
open scoped BigOperators

/-! Integration note (owner of area A6, H61): the local `abbrev Circ` of this module was
removed, because `Submission.Work.KMTPlan.A6.projVanishingG` declares the same
`Work.KMTPlan.A6.Circ` and the two names collided in every module importing both (in particular
in `Work.KMTAreas.area_A6`).  This module now imports `projVanishingG` and uses its declaration;
the statements below are unchanged. -/
/-- The (additive) isomorphism `ℤ ≃ ℤ • 1 ⊆ ℝ` sending `k` to `k`.  It is used to reindex the
`tsum` over the group of periods of the fundamental domain `(0,1]` by `ℤ`. -/
noncomputable def zmultiplesOneEquivInt : ℤ ≃ AddSubgroup.zmultiples (1 : ℝ) where
  toFun k := ⟨(k : ℝ), by rw [AddSubgroup.mem_zmultiples_iff]; exact ⟨k, by simp⟩⟩
  invFun y := Classical.choose (AddSubgroup.mem_zmultiples_iff.mp y.2)
  left_inv k := by
    apply Int.cast_injective (α := ℝ)
    have h := Classical.choose_spec (AddSubgroup.mem_zmultiples_iff.mp
      (show ((k : ℝ) : ℝ) ∈ AddSubgroup.zmultiples (1 : ℝ) from by
        rw [AddSubgroup.mem_zmultiples_iff]; exact ⟨k, by simp⟩))
    simpa using h
  right_inv y := by
    have h := Classical.choose_spec (AddSubgroup.mem_zmultiples_iff.mp y.2)
    ext
    simpa using h

lemma zmultiplesOneEquivInt_val (k : ℤ) :
    ((zmultiplesOneEquivInt k : AddSubgroup.zmultiples (1 : ℝ)) : ℝ) = (k : ℝ) := rfl

/-- The action of the period `k ∈ ℤ • 1` on `ℝ` is `x ↦ x + k`. -/
lemma zmultiplesOne_vadd (k : ℤ) (x : ℝ) :
    zmultiplesOneEquivInt k +ᵥ x = x + (k : ℝ) := by
  change (↑(zmultiplesOneEquivInt k) : ℝ) + x = x + (k : ℝ)
  rw [zmultiplesOneEquivInt_val, add_comm]

theorem PeriodizeFold {φ : ℝ → ℂ} (hφ : MeasureTheory.Integrable φ)
    {X : Work.Analysis.IonescuWainger.Circle → ℂ} (hX : Continuous X) :
    ∫ t : Work.Analysis.IonescuWainger.Circle,
        Work.Analysis.IonescuWainger.periodize φ t * X t
      ∂Work.Analysis.IonescuWainger.circleMeasure
      = ∫ x : ℝ, φ x * X ((x : ℝ) : Work.Analysis.IonescuWainger.Circle) := by
  -- The function on `ℝ` whose periodisation appears on the left-hand side.
  set g : ℝ → ℂ := fun x => φ x * X ((x : ℝ) : Circ) with hgdef
  -- `g` is integrable: `φ` is, and `X` is bounded (the circle is compact).
  have hmeasX : AEStronglyMeasurable (fun x : ℝ => X ((x : ℝ) : Circ)) volume :=
    (hX.measurable.comp AddCircle.measurable_mk').aestronglyMeasurable
  have hXbdd : ∃ C, ∀ t : Circ, ‖X t‖ ≤ C := by
    let Xc : C(Circ, ℂ) := ContinuousMap.mk X hX
    exact ⟨‖Xc‖, fun t => ContinuousMap.norm_coe_le_norm Xc t⟩
  obtain ⟨C, hC⟩ := hXbdd
  have hg : Integrable g volume :=
    hφ.mul_bdd hmeasX (Filter.Eventually.of_forall (fun x => hC (x : Circ)))
  -- Pointwise, `periodize φ t * X t = ∑' k, g (a + k)` for `t = (a : ℝ/ℤ)`: the periodisation of
  -- the product `φ · (X ∘ coe)` — the factor `X` is constant along the `ℤ`-orbit.
  have hpt : ∀ a : ℝ, Work.Analysis.IonescuWainger.periodize φ (a : Circ) * X (a : Circ)
      = ∑' k : ℤ, g (a + k) := by
    intro a
    rw [Work.KMTContract.periodizeCoeEqTsum φ a, ← tsum_mul_right]
    refine tsum_congr (fun k => ?_)
    have hk0 : (((k : ℝ)) : Circ) = 0 := by
      rw [AddCircle.coe_eq_zero_iff]; exact ⟨k, by simp⟩
    have hcoe : ((a + (k : ℝ) : ℝ) : Circ) = (a : Circ) := by
      rw [AddCircle.coe_add, hk0, add_zero]
    simp only [hgdef, hcoe]
  -- Unfold the integral over the circle as the integral over the fundamental domain `(0,1]`.
  have hL : ∫ t : Circ, Work.Analysis.IonescuWainger.periodize φ t * X t
        ∂Work.Analysis.IonescuWainger.circleMeasure
      = ∫ a in Set.Ioc (0 : ℝ) 1, ∑' k : ℤ, g (a + k) := by
    rw [Work.Analysis.IonescuWainger.circleMeasure, AddCircle.integral_haarAddCircle]
    simp only [inv_one, one_smul]
    rw [← AddCircle.integral_preimage (1 : ℝ) 0
      (fun t : Circ => Work.Analysis.IonescuWainger.periodize φ t * X t)]
    simp only [zero_add]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun a => ?_))
    exact hpt a
  -- `(0,1]` is a fundamental domain for `ℤ • 1`.
  have hfd : IsAddFundamentalDomain (AddSubgroup.zmultiples (1 : ℝ)) (Set.Ioc (0 : ℝ) 1) volume := by
    simpa using isAddFundamentalDomain_Ioc (T := (1 : ℝ)) one_pos 0
  -- Summability of the `ℤ`-family of `(‖·‖ₑ)`-integrals, from the fundamental-domain identity.
  have hsumm : ∑' k : ℤ, ∫⁻ a, ‖g (a + k)‖ₑ ∂(volume.restrict (Set.Ioc (0 : ℝ) 1))
      = ∫⁻ x : ℝ, ‖g x‖ₑ := by
    rw [hfd.lintegral_eq_tsum'' (fun x : ℝ => ‖g x‖ₑ)]
    rw [(Equiv.tsum_eq zmultiplesOneEquivInt (fun n : AddSubgroup.zmultiples (1 : ℝ) =>
        ∫⁻ x in Set.Ioc (0 : ℝ) 1, ‖g (n +ᵥ x)‖ₑ)).symm]
    apply tsum_congr
    intro k
    apply lintegral_congr_ae
    filter_upwards with x
    rw [zmultiplesOne_vadd k x]
  -- Decompose `∫_ℝ g` along the translates of the fundamental domain.
  have hR : ∫ x : ℝ, g x = ∑' k : ℤ, ∫ a in Set.Ioc (0 : ℝ) 1, g (a + k) := by
    rw [hfd.integral_eq_tsum'' g hg]
    rw [(Equiv.tsum_eq zmultiplesOneEquivInt (fun n : AddSubgroup.zmultiples (1 : ℝ) =>
        ∫ x in Set.Ioc (0 : ℝ) 1, g (n +ᵥ x))).symm]
    apply tsum_congr
    intro k
    apply integral_congr_ae
    filter_upwards with x
    rw [zmultiplesOne_vadd k x]
  -- Interchange the sum with the integral over `(0,1]`.
  have hton : ∫ a in Set.Ioc (0 : ℝ) 1, ∑' k : ℤ, g (a + k)
      = ∑' k : ℤ, ∫ a in Set.Ioc (0 : ℝ) 1, g (a + k) := by
    have hint : ∀ k : ℤ, Integrable (fun a : ℝ => g (a + k))
        (volume.restrict (Set.Ioc (0 : ℝ) 1)) := by
      intro k
      have h1 : Integrable (fun a : ℝ => g (a + (k : ℝ))) volume :=
        ((measurePreserving_add_right volume (k : ℝ)).integrable_comp
          hg.aestronglyMeasurable).mpr hg
      exact h1.mono_measure MeasureTheory.Measure.restrict_le_self
    have hfin : ∑' k : ℤ, ∫⁻ a, ‖g (a + k)‖ₑ ∂(volume.restrict (Set.Ioc (0 : ℝ) 1)) ≠ ⊤ := by
      rw [hsumm]
      exact (hasFiniteIntegral_iff_enorm.mp hg.hasFiniteIntegral).ne
    exact MeasureTheory.integral_tsum (fun k => (hint k).aestronglyMeasurable) hfin
  rw [hL, hton, ← hR]

end Work.KMTPlan.A6
