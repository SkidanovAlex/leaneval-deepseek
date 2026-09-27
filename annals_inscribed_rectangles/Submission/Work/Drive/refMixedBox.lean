import Mathlib
import Submission.Work.Drive.mixedFactorDelta
import Submission.Work.Drive.sideGermDefs
import Submission.Work.Drive.referenceClassCount
import Submission.Work.Drive.geometricCount

/-!
# The mixed factors `(F1)` of the `hn2` reference triple in the **box** form, uniformly in the
perturbation

`Work.Drive.exists_delta_odd_coreSideCountPt_mixed` (`Drive/mixedFactorDelta.lean`) proves the mixed
factors of the reference triple odd for the *geometric* (parameterisation-free) count
`Work.Drive.coreSideCountPt`, for **every** perturbation parameter of norm below an explicit radius,
after the reference functional `φ` has been chosen generic along the two class lifts.  The transport
`T6` of the `hn2` producer, on the other hand, computes with the **box** count
`Work.Drive.coreSideCount` (the number of *parameter pairs* of `coreMeet`), and the two counts agree
exactly when the box parameterisation of the meet set is injective
(`Work.Drive.coreMeetPt_ncard_eq_iff`).

This module supplies the dictionary, in the form the producer can consume:

* `Work.Drive.coreLoop_chartPert_rotCapping_injModOne` — the core loop of a *perturbed rotated* plane
  chart is injective modulo the period (transported from `Work.Drive.coreLoop_injective_mod_one`);
* **`Work.Drive.injOn_coreMeet_of_goodPair`** — the faithfulness brick: for a `GoodPair` whose meet
  parameters are strictly interior, the loop parameter determines the whole parameter pair, provided
  the loop is injective mod `1` and the sweep is injective on the box.  (The *chain* half is what the
  interiority clause buys: the plane parameter is recovered from the sweep's injectivity, and the loop
  parameter from the loop's injectivity, the two being in `(0,1)`.)
* **`Work.Drive.exists_delta_odd_coreSideCount_mixed`** — the box form of `(F1)`, uniformly in the
  perturbation: the same `φ` and radius as the geometric statement, with the two *geometric* hypotheses
  per parameter — the mixed pair's `GoodPair` (so the meets are finite, interior and transverse) and
  the sweep's injectivity on the box — turned into the oddness of the two box counts.

The two hypotheses are exactly the good-configuration conditions of the design's Sard: `GoodPair` is
open and dense in the perturbation parameters for a pair of *independent* base charts — the
generalisation of `Work.Drive.goodPair_pertChart_isOpen` /
`Work.Drive.goodPair_pertChart_exists_near` from `(Ξ t ∘ Q, rotCapping w ∘ Ξ t' ∘ Q)` to
`(Ξ t ∘ Q₁, Ξ t' ∘ Q₂)`, i.e. the mixed pair `(chartPert τ₀ ∘ rotCapping u ∘ Q,
chartPert τ₂ ∘ linPlaneChart φ lam)` of the reference triple.  The sweep's injectivity is
`Work.Drive.clampedSweep_injOn_unitBox` fed by the plane's class-injectivity on the interior of the
square (`Work.Drive.diskPlane_linPlaneChart_injOn_interior` for the reference plane, and the chart's
injectivity clause for the configuration charts).
-/

namespace Work.Drive

open Manifold Set Filter
open scoped Manifold ContDiff Topology

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace Work.Drive.projCharted

noncomputable section

set_option maxHeartbeats 1000000
set_option linter.unusedSimpArgs false
set_option warn.classDefReducibility false

/-- **The core loop of a perturbed rotated plane chart is injective modulo the period.**  The chart
invariance `coreLoop Q t = Q (coreLoopArg t)` reduces the statement to the injectivity of
`chartPert τ` (a bijection of the capping space, `Work.Drive.chartPert_injective`) and of `rotCapping u`
(`Work.Drive.rotCapping_injective'`), and then to `Work.Drive.coreLoop_injective_mod_one`. -/
theorem coreLoop_chartPert_rotCapping_injModOne {γ : Circle → ℝ × ℝ} {hγne : ∀ x : Circle, γ x ≠ 0}
    {Q : ℂ → CappingSpace} (hγ : IsSmoothEmbedding (𝓡 1) 𝓘(ℝ, ℝ × ℝ) ∞ γ)
    (hQ : IsPlaneChart γ hγne Q) (u : UnitAddCircle) (τ : Eucl 3) {s s' : ℝ}
    (h : coreLoop (fun z : ℂ => chartPert τ (rotCapping u (Q z))) s
      = coreLoop (fun z : ℂ => chartPert τ (rotCapping u (Q z))) s') :
    ∃ k : ℤ, s' = s + k := by
  simp only [coreLoop_eq, Function.comp_apply] at h
  have h1 : rotCapping u (Q (coreLoopArg s)) = rotCapping u (Q (coreLoopArg s')) :=
    chartPert_injective τ h
  have h2 : Q (coreLoopArg s) = Q (coreLoopArg s') := rotCapping_injective' u h1
  exact coreLoop_injective_mod_one hγ hγne hQ (by simpa only [coreLoop_eq] using h2)

/-- **Faithfulness of the box parameterisation of a `GoodPair`.**  If the meet set is finite, all its
parameters are strictly interior, the loop is injective modulo the period and the sweep is injective on
the box, then the loop parameter determines the parameter pair: two meet parameters with the same loop
value have the same chain parameter (sweep injectivity) and loop parameters equal modulo `1`
(loop injectivity mod `1`), hence equal because both lie in `(0,1)`.

This is the two-clause faithfulness of `Work.Drive.odd_coreSideCount_of_meetPt_ncard_eq`, i.e. the
`hfinBox`/`hinjBox` of `Drive/mixedFactorBox.lean`, from the good-configuration data alone. -/
theorem injOn_coreMeet_of_goodPair {Q₁ Q₂ : ℂ → CappingSpace} {c : ℝ} (h : GoodPair Q₁ Q₂ c)
    (hloop : ∀ s s' : ℝ, coreLoop Q₁ s = coreLoop Q₁ s' → ∃ k : ℤ, s' = s + k)
    (hsweep : Set.InjOn (clampedSweep c (fun t => 1 - t) (diskPlane Q₂))
      {x : EuclideanSpace ℝ (Fin 3) | ∀ i, x i ∈ Set.Ioo (0 : ℝ) 1}) :
    Set.InjOn (fun p : ℝ × Amb 2 => coreLoop Q₁ p.1) (coreMeet Q₁ c (diskPlane Q₂)) := by
  intro p hp q hq hpq
  obtain ⟨hp1, hp2, hp3⟩ := hp
  obtain ⟨hq1, hq2, hq3⟩ := hq
  have hint := h.2.2.2.1
  have hpint := hint p ⟨hp1, hp2, hp3⟩
  have hqint := hint q ⟨hq1, hq2, hq3⟩
  -- the two chain parameters coincide
  have hsweep_eq : clampedSweep c (fun t => 1 - t) (diskPlane Q₂) p.2
      = clampedSweep c (fun t => 1 - t) (diskPlane Q₂) q.2 := by
    have hpq' : coreLoop Q₁ p.1 = coreLoop Q₁ q.1 := hpq
    rw [← hp3, hpq', hq3]
  have hpq2 : p.2 = q.2 := hsweep hpint.2 hqint.2 hsweep_eq
  -- the two loop parameters coincide
  obtain ⟨k, hk⟩ := hloop p.1 q.1 hpq
  have hk0 : k = 0 := by
    have h1 : p.1 ∈ Set.Ioo (0 : ℝ) 1 := hpint.1
    have h2 : q.1 ∈ Set.Ioo (0 : ℝ) 1 := hqint.1
    have hk1 : (k : ℝ) < 1 := by
      have : (k : ℝ) = q.1 - p.1 := by linarith
      linarith [h2.2, h1.1]
    have hk2 : -(1 : ℝ) < (k : ℝ) := by
      have : (k : ℝ) = q.1 - p.1 := by linarith
      linarith [h1.2, h2.1]
    have hkint1 : k < 1 := by exact_mod_cast hk1
    have hkint2 : -1 < k := by exact_mod_cast hk2
    omega
  refine Prod.ext ?_ hpq2
  rw [hk, hk0]
  simp

/-- **The mixed factors `(F1)` of the reference triple in the box form, uniformly in the
perturbation.**  Same `φ` and radius as `Work.Drive.exists_delta_odd_coreSideCountPt_mixed`; for every
parameter below the radius the two mixed *box* counts are odd, as soon as, at that parameter, the two
mixed pairs are `GoodPair`s (finite interior transverse meets) and the reference plane's sweep is
injective on the box.

The chart `chartPert τ ∘ rotCapping u ∘ Q` and the chain `diskPlane (chartPert τ' ∘ linPlaneChart φ lam)`
are exactly the two objects whose pairing is the mixed factor of the `hn2` reference triple. -/
theorem exists_delta_odd_coreSideCount_mixed {γ : Circle → ℝ × ℝ}
    (hγ : IsSmoothEmbedding (𝓡 1) 𝓘(ℝ, ℝ × ℝ) ∞ γ) {hγne : ∀ x : Circle, γ x ≠ 0}
    {Q : ℂ → CappingSpace} (hQ : IsPlaneChart γ hγne Q)
    (u₀ u₁ : UnitAddCircle)
    {c β lam c₂ : ℝ} (hc : 0 < c) (hβpos : 0 < β) (hlampos : 0 < lam) (hc₂ : 0 < c₂)
    (hc₂c : c₂ < c) (hβlam : β < lam)
    (hclow : ∀ z : ℂ, ‖z‖ ≤ 1 → c ≤ levelOf (Q z))
    (hβ : ∀ z : ℂ, ‖z‖ ≤ 1 → levelOf (Q z) ≤ β) :
    ∃ (φ : Eucl 3 ≃L[ℝ] Eucl 3) (δ : ℝ), 0 < δ ∧
      ∀ τ₀ τ₁ τ₂ : Eucl 3, ‖τ₀‖ < δ → ‖τ₁‖ < δ → ‖τ₂‖ < δ →
        (GoodPair (fun z : ℂ => chartPert τ₀ (rotCapping u₀ (Q z)))
            (fun z : ℂ => chartPert τ₂ (linPlaneChart φ lam hlampos z)) c₂ →
          Set.InjOn (clampedSweep c₂ (fun t => 1 - t)
            (diskPlane (fun z : ℂ => chartPert τ₂ (linPlaneChart φ lam hlampos z))))
            {x : EuclideanSpace ℝ (Fin 3) | ∀ i, x i ∈ Set.Ioo (0 : ℝ) 1} →
          Odd (coreSideCount (fun z : ℂ => chartPert τ₀ (rotCapping u₀ (Q z))) c₂
            (diskPlane (fun z : ℂ => chartPert τ₂ (linPlaneChart φ lam hlampos z))))) ∧
        (GoodPair (fun z : ℂ => chartPert τ₁ (rotCapping u₁ (Q z)))
            (fun z : ℂ => chartPert τ₂ (linPlaneChart φ lam hlampos z)) c₂ →
          Set.InjOn (clampedSweep c₂ (fun t => 1 - t)
            (diskPlane (fun z : ℂ => chartPert τ₂ (linPlaneChart φ lam hlampos z))))
            {x : EuclideanSpace ℝ (Fin 3) | ∀ i, x i ∈ Set.Ioo (0 : ℝ) 1} →
          Odd (coreSideCount (fun z : ℂ => chartPert τ₁ (rotCapping u₁ (Q z))) c₂
            (diskPlane (fun z : ℂ => chartPert τ₂ (linPlaneChart φ lam hlampos z))))) := by
  obtain ⟨φ, δ, hδpos, hgeo⟩ :=
    exists_delta_odd_coreSideCountPt_mixed hγ hQ u₀ u₁ hc hβpos hlampos hc₂ hc₂c hβlam hclow hβ
  refine ⟨φ, δ, hδpos, fun τ₀ τ₁ τ₂ h₀ h₁ h₂ => ⟨?_, ?_⟩⟩
  · intro hgp hsweep
    obtain ⟨h₀', h₁'⟩ := hgeo τ₀ τ₁ τ₂ h₀ h₁ h₂
    have hloop : ∀ s s' : ℝ,
        coreLoop (fun z : ℂ => chartPert τ₀ (rotCapping u₀ (Q z))) s
          = coreLoop (fun z : ℂ => chartPert τ₀ (rotCapping u₀ (Q z))) s' → ∃ k : ℤ, s' = s + k :=
      fun s s' hs => coreLoop_chartPert_rotCapping_injModOne hγ hQ u₀ τ₀ hs
    exact odd_coreSideCount_of_meetPt_ncard_eq (fun z : ℂ => chartPert τ₀ (rotCapping u₀ (Q z))) c₂
      (diskPlane (fun z : ℂ => chartPert τ₂ (linPlaneChart φ lam hlampos z))) hgp.2.2.1
      (injOn_coreMeet_of_goodPair hgp hloop hsweep) h₀'
  · intro hgp hsweep
    obtain ⟨h₀', h₁'⟩ := hgeo τ₀ τ₁ τ₂ h₀ h₁ h₂
    have hloop : ∀ s s' : ℝ,
        coreLoop (fun z : ℂ => chartPert τ₁ (rotCapping u₁ (Q z))) s
          = coreLoop (fun z : ℂ => chartPert τ₁ (rotCapping u₁ (Q z))) s' → ∃ k : ℤ, s' = s + k :=
      fun s s' hs => coreLoop_chartPert_rotCapping_injModOne hγ hQ u₁ τ₁ hs
    exact odd_coreSideCount_of_meetPt_ncard_eq (fun z : ℂ => chartPert τ₁ (rotCapping u₁ (Q z))) c₂
      (diskPlane (fun z : ℂ => chartPert τ₂ (linPlaneChart φ lam hlampos z))) hgp.2.2.1
      (injOn_coreMeet_of_goodPair hgp hloop hsweep) h₁'

end

end Work.Drive
