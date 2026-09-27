import Mathlib
import Submission.Work.EKLContract.All
import Submission.Work.EKLRelCross.Instances
import Submission.Work.EKLRelCross.LeafBasic
import Submission.Work.EKLRelCross.crossSection_trivial

/-!
# `Work.EKLRelCross.leafwise_crossSection` — (U3): trivial leafwise measures ⇔ cross-section

This is clause (U3) of the frozen component `Work.EKLContract.P_Leafwise` (Pisa 6.23): for a
probability measure `μ` on `X₃ = SL₃(ℝ)/SL₃(ℤ)`, a horospherical subgroup `U` and a system
`ν` of leafwise measures for `U` (`Work.EKLContract.IsLeafwise μ U ν X'`),

  `CrossSection μ U ↔ ν x = δ₁` for `μ`-a.e. `x`.

The two directions are proved separately:

* `crossSection_of_ae_dirac` (proved here, the direction `⇐`, i.e. *no* mathematician would call it
  the easy one, but it is the direction that uses only the equivariance axiom): if `ν x = δ₁` for
  a.e. `x`, let `B = X' ∩ Tᶜ` where `T` is a Borel null superset of `{x | ν x ≠ δ₁}`
  (`MeasureTheory.toMeasurable`).  `B` is a conull cross-section: if `x ∈ B`, `u ∈ U` and
  `u • x ∈ B`, then both `ν x` and `ν (u • x)` are `δ₁`, so the equivariance axiom
  (`IsLeafwise.equivariant`) gives `δ₁ = c • (δ₁).map (g ↦ g * u) = c • δ_u` with `0 < c < ∞`, and
  evaluating at `{1}` forces `u = 1`.

* the direction `⇒` is `Work.EKLRelCross.crossSection_trivial` (Pisa 6.23 for the flower of the
  cross-section, Pisa §6.7–6.15): if a conull cross-section `B` exists, the `condexp` axiom of
  `IsLeafwise` applied to the flower σ-algebra of `B` and the test function `1_{Bᶜ}` shows that
  `ν x` charges each box `V δ ∩ U` only at the identity, and letting `δ → ∞` gives `ν x = δ₁`.

Almost everywhere free `U`-orbits — the hypothesis of `crossSection_trivial` — are
`Work.EKLRelCross.ae_free_orbit`, proved from Poincaré recurrence for the contracting element
`α^{t₀}` and local freeness (`P_X3`); this is why the statement of `leafwise_crossSection` can
dispose of the hypothesis `hfree`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

noncomputable section

namespace Work.EKLRelCross

open Work.EKLContract

/-- **(U3), direction `⇐`.**  If the leafwise measures of `U` are a.e. the Dirac mass at the
identity, then `U` admits a conull cross-section.

The cross-section is `B = X' ∩ Tᶜ`, where `T` is a Borel null superset of the null set
`{x | ν x ≠ δ₁}`; the equivariance axiom of `IsLeafwise` then rules out `u ≠ 1`. -/
theorem crossSection_of_ae_dirac {μ : Measure X3} [IsProbabilityMeasure μ]
    {U : Subgroup SL3} {ν : X3 → Measure SL3} {X' : Set X3} (hL : IsLeafwise μ U ν X')
    (hν : ∀ᵐ x ∂μ, ν x = Measure.dirac 1) : CrossSection μ U := by
  -- a Borel null superset of the bad set
  have hbad : μ {x | ν x ≠ Measure.dirac 1} = 0 := MeasureTheory.ae_iff.mp hν
  set T := MeasureTheory.toMeasurable μ {x | ν x ≠ Measure.dirac 1} with hTdef
  have hTmeas : MeasurableSet T := MeasureTheory.measurableSet_toMeasurable μ _
  have hTzero : μ T = 0 := by
    rw [hTdef, MeasureTheory.measure_toMeasurable]; exact hbad
  have hsub : {x | ν x ≠ Measure.dirac 1} ⊆ T := MeasureTheory.subset_toMeasurable μ _
  refine ⟨X' ∩ Tᶜ, hL.meas_dom.inter hTmeas.compl, ?_, ?_⟩
  · -- `B` is conull
    have hsub2 : (X' ∩ Tᶜ)ᶜ ⊆ X'ᶜ ∪ T := by
      intro x hx
      by_cases h : x ∈ X'
      · right; by_contra hT; exact hx ⟨h, hT⟩
      · left; exact h
    refine le_antisymm (le_trans (measure_mono hsub2) ?_) bot_le
    calc μ (X'ᶜ ∪ T) ≤ μ X'ᶜ + μ T := measure_union_le _ _
      _ = 0 := by rw [hL.conull, hTzero, add_zero]
  · -- the cross-section property
    intro x hx u hu hux
    obtain ⟨hxX', hxT⟩ := hx
    have huxX' : u • x ∈ X' := hux.1
    have hxν : ν x = Measure.dirac 1 := by
      by_contra h; exact hxT (hsub h)
    have huxν : ν (u • x) = Measure.dirac 1 := by
      by_contra h; exact hux.2 (hsub h)
    obtain ⟨c, _hc0, _hct, hce⟩ := hL.equivariant x hxX' u hu huxX'
    rw [hxν, huxν] at hce
    have hmap : (Measure.dirac (1 : SL3)).map (fun g : SL3 => g * u) = Measure.dirac u := by
      rw [Measure.map_dirac]; simp
    rw [hmap] at hce
    have happ := congrArg (fun m : Measure SL3 => m ({1} : Set SL3)) hce
    rw [Measure.smul_apply] at happ
    rw [Measure.dirac_apply_of_mem (Set.mem_singleton 1)] at happ
    by_cases hu1 : u = 1
    · exact hu1
    · exfalso
      have hzu : (Measure.dirac u : Measure SL3) ({1} : Set SL3) = 0 := by
        simp [hu1]
      rw [hzu, smul_zero] at happ
      exact one_ne_zero happ

theorem leafwise_crossSection (h2 : Work.EKLContract.P_X3) (μ : MeasureTheory.Measure Work.EKLContract.X3) [MeasureTheory.IsProbabilityMeasure μ]
    (U : Subgroup Work.EKLContract.SL3) (hU : Work.EKLContract.IsHoro U) (t0 : Fin 3 → ℝ)
    (ht0 : MeasureTheory.MeasurePreserving (fun x : Work.EKLContract.X3 => Work.EKLContract.aDiag t0 • x) μ μ)
    (hcontr : ∀ u ∈ U, Filter.Tendsto (fun n : ℕ => Work.EKLContract.aDiag t0 ^ n * u * (Work.EKLContract.aDiag t0 ^ n)⁻¹) Filter.atTop (nhds 1))
    (ν : Work.EKLContract.X3 → MeasureTheory.Measure Work.EKLContract.SL3) (X' : Set Work.EKLContract.X3) (hL : Work.EKLContract.IsLeafwise μ U ν X') :
    Work.EKLContract.CrossSection μ U ↔ ∀ᵐ x ∂μ, ν x = MeasureTheory.Measure.dirac 1 := by
  refine ⟨fun hCS => ?_, fun hν => crossSection_of_ae_dirac hL hν⟩
  exact crossSection_trivial h2 hU (ae_free_orbit h2 μ U hU t0 ht0 hcontr) hL hCS

end Work.EKLRelCross
