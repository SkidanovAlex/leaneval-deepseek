/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/EpsE4Thr/AesmRestrict.lean` — the horizon-restricted
a.e. strong measurability, and its use in the diagonal-energy derivative

The `L²`-route derivative `hasDerivAt_integral_diag_var_ioo` of the diagonal energy carries the
hypothesis that the *uncurried* families

  `(s,p) ↦ u s p.1 p.2`,  `(s,p) ↦ udot s p.1 p.2`

are a.e. strongly measurable for the **full** product measure `volume.prod diaM`.  That hypothesis
is *unprovable* from the data of the `ε`-flow: the flow is only known on the horizon `[0,T]`
(`IsEpsSolP` constrains `slice g τ` for `τ ∈ Icc 0 T` only), so a family may be redefined
arbitrarily — even non-measurably — on the complement of `[0,T] × ℝ²`, which has infinite
`volume.prod diaM`-measure.  Nothing in the argument ever uses the values off the horizon: the
difference-quotient argument of `hasDerivAt_integral_diag_var` works on a window
`(τ - δ, τ + δ) ⊆ (0,T)`.

This module therefore records the **honest** hypothesis and proves that it suffices:

* `aesm_clamp_restrict` — a.e. strong measurability for `(volume.restrict (Icc 0 T)).prod ν`
  implies a.e. strong measurability of the *clamped* function
  `q ↦ if q.1 ∈ Icc 0 T then U q else 0` for the full product `volume.prod ν`
  (the two clamped functions differ only on a null subset of the slab `Icc 0 T ×ˢ univ`, and
  `(volume.restrict (Icc 0 T)).prod ν` is literally `(volume.prod ν).restrict (Icc 0 T ×ˢ univ)`);
* `hasDerivAt_integral_diag_var_ioo_restricted` — the same derivative with the restricted
  hypothesis: clamp both families to `[0,T]`, apply the full-measure version to the clamps, and
  transport the conclusion back (the clamps agree with the originals on the neighbourhood
  `Icc 0 T ∈ 𝓝 τ`, so the two integrals agree eventually).

Everything here is `sorry`-free.
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.EpsE4Thr.DiaDefs
import Submission.Work.FTS.StrongEps.EpsE4Thr.hasDerivAt_integral_diag_var
import Submission.Work.FTS.StrongEps.EpsE4Thr.hasDerivAt_integral_diag_var_ioo

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr

set_option autoImplicit false

/-! ## Clamping turns restricted measurability into full measurability -/

/-- **Clamping to the horizon turns restricted a.e. strong measurability into full a.e. strong
measurability.** -/
theorem aesm_clamp_restrict {β : Type*} [MeasurableSpace β]
    {ν : MeasureTheory.Measure β} [MeasureTheory.SFinite ν]
    {U : ℝ × β → ℝ} {T : ℝ}
    (h : MeasureTheory.AEStronglyMeasurable U
      ((MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)).prod ν)) :
    MeasureTheory.AEStronglyMeasurable
      (fun q : ℝ × β => if q.1 ∈ Set.Icc (0 : ℝ) T then U q else 0)
      ((MeasureTheory.volume : MeasureTheory.Measure ℝ).prod ν) := by
  obtain ⟨G, hG, hEq⟩ := h
  -- `(volume.restrict (Icc 0 T)).prod ν` is `(volume.prod ν)` restricted to the slab
  have hmeasA : MeasurableSet (Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set β)) :=
    measurableSet_Icc.prod MeasurableSet.univ
  have hrestrict : (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)).prod ν
      = ((MeasureTheory.volume : MeasureTheory.Measure ℝ).prod ν).restrict
          (Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set β)) := by
    conv_lhs => rw [← Measure.restrict_univ (μ := ν)]
    rw [MeasureTheory.Measure.prod_restrict]
  have h1 : ((MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)).prod ν)
      {q : ℝ × β | U q ≠ G q} = 0 := MeasureTheory.ae_iff.mp hEq
  have h2 : (((MeasureTheory.volume : MeasureTheory.Measure ℝ).prod ν).restrict
      (Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set β))) {q : ℝ × β | U q ≠ G q} = 0 := by
    rw [← hrestrict]; exact h1
  have hnull : ((MeasureTheory.volume : MeasureTheory.Measure ℝ).prod ν)
      ({q : ℝ × β | U q ≠ G q} ∩ (Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set β))) = 0 := by
    have h3 := Measure.restrict_apply₀
      (μ := (MeasureTheory.volume : MeasureTheory.Measure ℝ).prod ν)
      (s := Set.Icc (0 : ℝ) T ×ˢ (Set.univ : Set β)) (t := {q : ℝ × β | U q ≠ G q})
      (MeasureTheory.NullMeasurableSet.of_null h2)
    rw [← h3]; exact h2
  refine ⟨fun q : ℝ × β => if q.1 ∈ Set.Icc (0 : ℝ) T then G q else 0, ?_, ?_⟩
  · exact hG.ite (measurableSet_Icc.preimage measurable_fst) stronglyMeasurable_const
  · refine MeasureTheory.ae_iff.mpr (measure_mono_null ?_ hnull)
    intro q hq
    simp only [Set.mem_setOf_eq] at hq ⊢
    by_cases hA : q.1 ∈ Set.Icc (0 : ℝ) T
    · refine ⟨?_, hA, trivial⟩
      simpa [hA] using hq
    · exact absurd (by simpa [hA]) hq

/-! ## The horizon-restricted diagonal-energy derivative -/

/-- **The `L²`-route derivative of the diagonal energy with the *honest* measurability
hypothesis**: the two families only need to be a.e. strongly measurable for
`(volume.restrict (Icc 0 T)).prod diaM`.

Proof: clamp both families to the horizon (using `aesm_clamp_restrict` for the two measurability
hypotheses, and `HasDerivAt.congr_of_eventuallyEq` / `ContinuousOn.congr` / eventual equality of
the integrals for the rest), apply `hasDerivAt_integral_diag_var_ioo` to the clamps, and transport
the conclusion back along `Icc 0 T ∈ 𝓝 τ`. -/

theorem hasDerivAt_integral_diag_var_ioo_restricted {ρ : ℝ → ℝ → ℝ}
    {u udot : ℝ → Work.FTS.Galerkin.Fn}
    {τ T : ℝ} (hT : 0 ≤ T) (hτ : τ ∈ Set.Ioo 0 T)
    (hρmeas : AEMeasurable (Function.uncurry ρ) diaM)
    (hρnn : ∀ᵐ p ∂diaM, 0 ≤ ρ p.1 p.2)
    (hdiag : ∀ s ∈ Set.Icc (0 : ℝ) T, MeasureTheory.Integrable
      (fun p : ℝ × ℝ => (u s p.1 p.2) ^ 2 * ρ p.1 p.2) diaM)
    (hdiagd : ∀ s ∈ Set.Icc (0 : ℝ) T, MeasureTheory.Integrable
      (fun p : ℝ × ℝ => (udot s p.1 p.2) ^ 2 * ρ p.1 p.2) diaM)
    (hmeas : MeasureTheory.AEStronglyMeasurable
      (fun q : ℝ × (ℝ × ℝ) => u q.1 q.2.1 q.2.2)
      ((MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)).prod diaM))
    (hmeasd : MeasureTheory.AEStronglyMeasurable
      (fun q : ℝ × (ℝ × ℝ) => udot q.1 q.2.1 q.2.2)
      ((MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)).prod diaM))
    (hderiv : ∀ᵐ p ∂diaM, ∀ s ∈ Set.Ioo (0 : ℝ) T,
      HasDerivAt (fun t : ℝ => u t p.1 p.2) (udot s p.1 p.2) s)
    (hcont : ∀ᵐ p ∂diaM, ContinuousOn (fun s : ℝ => u s p.1 p.2) (Set.Ioo 0 T))
    (hK : ∃ K : ℝ, 0 ≤ K ∧ ∀ σ ∈ Set.Icc (0 : ℝ) T,
      ∫ p : ℝ × ℝ, (udot σ p.1 p.2) ^ 2 * ρ p.1 p.2 ∂diaM ≤ K)
    (hcontU : Filter.Tendsto (fun σ : ℝ => ∫ p : ℝ × ℝ,
        (udot σ p.1 p.2 - udot τ p.1 p.2) ^ 2 * ρ p.1 p.2 ∂diaM) (nhds τ) (nhds 0)) :
    HasDerivAt (fun s : ℝ => ∫ p : ℝ × ℝ, u s p.1 p.2 * u s p.1 p.2 * ρ p.1 p.2 ∂diaM)
      (2 * ∫ p : ℝ × ℝ, udot τ p.1 p.2 * u τ p.1 p.2 * ρ p.1 p.2 ∂diaM) τ := by
  have hτIcc : τ ∈ Set.Icc (0 : ℝ) T := ⟨hτ.1.le, hτ.2.le⟩
  -- the horizon is a neighbourhood of `τ`
  have hnbd : Set.Icc (0 : ℝ) T ∈ nhds τ := Icc_mem_nhds hτ.1 hτ.2
  set u' : ℝ → Work.FTS.Galerkin.Fn :=
    fun s => if s ∈ Set.Icc (0 : ℝ) T then u s else 0 with hu'def
  set ud' : ℝ → Work.FTS.Galerkin.Fn :=
    fun s => if s ∈ Set.Icc (0 : ℝ) T then udot s else 0 with hud'def
  have hu'_eq : ∀ s ∈ Set.Icc (0 : ℝ) T, u' s = u s := by
    intro s hs; rw [hu'def]; simp only [hs, if_true]
  have hud'_eq : ∀ s ∈ Set.Icc (0 : ℝ) T, ud' s = udot s := by
    intro s hs; rw [hud'def]; simp only [hs, if_true]
  have hdiag' : ∀ s ∈ Set.Icc (0 : ℝ) T, MeasureTheory.Integrable
      (fun p : ℝ × ℝ => (u' s p.1 p.2) ^ 2 * ρ p.1 p.2) diaM := by
    intro s hs
    rw [show (fun p : ℝ × ℝ => (u' s p.1 p.2) ^ 2 * ρ p.1 p.2)
        = (fun p : ℝ × ℝ => (u s p.1 p.2) ^ 2 * ρ p.1 p.2) from by
      funext p; rw [hu'_eq s hs]]
    exact hdiag s hs
  have hdiagd' : ∀ s ∈ Set.Icc (0 : ℝ) T, MeasureTheory.Integrable
      (fun p : ℝ × ℝ => (ud' s p.1 p.2) ^ 2 * ρ p.1 p.2) diaM := by
    intro s hs
    rw [show (fun p : ℝ × ℝ => (ud' s p.1 p.2) ^ 2 * ρ p.1 p.2)
        = (fun p : ℝ × ℝ => (udot s p.1 p.2) ^ 2 * ρ p.1 p.2) from by
      funext p; rw [hud'_eq s hs]]
    exact hdiagd s hs
  have hmeas' : MeasureTheory.AEStronglyMeasurable
      (fun q : ℝ × (ℝ × ℝ) => u' q.1 q.2.1 q.2.2)
      ((MeasureTheory.volume : MeasureTheory.Measure ℝ).prod diaM) := by
    have hc := aesm_clamp_restrict (ν := diaM) (U := fun q : ℝ × (ℝ × ℝ) => u q.1 q.2.1 q.2.2)
      (T := T) hmeas
    simpa only [hu'def, ite_apply, Pi.zero_apply] using hc
  have hmeasd' : MeasureTheory.AEStronglyMeasurable
      (fun q : ℝ × (ℝ × ℝ) => ud' q.1 q.2.1 q.2.2)
      ((MeasureTheory.volume : MeasureTheory.Measure ℝ).prod diaM) := by
    have hc := aesm_clamp_restrict (ν := diaM) (U := fun q : ℝ × (ℝ × ℝ) => udot q.1 q.2.1 q.2.2)
      (T := T) hmeasd
    simpa only [hud'def, ite_apply, Pi.zero_apply] using hc
  have hderiv' : ∀ᵐ p ∂diaM, ∀ s ∈ Set.Ioo (0 : ℝ) T,
      HasDerivAt (fun t : ℝ => u' t p.1 p.2) (ud' s p.1 p.2) s := by
    filter_upwards [hderiv] with p hp
    intro s hs
    have hsIcc : s ∈ Set.Icc (0 : ℝ) T := ⟨hs.1.le, hs.2.le⟩
    rw [show ud' s p.1 p.2 = udot s p.1 p.2 from by rw [hud'_eq s hsIcc]]
    refine (hp s hs).congr_of_eventuallyEq ?_
    filter_upwards [Icc_mem_nhds hs.1 hs.2] with t ht
    rw [show u' t p.1 p.2 = u t p.1 p.2 from by rw [hu'_eq t ht]]
  have hcont' : ∀ᵐ p ∂diaM, ContinuousOn (fun s : ℝ => u' s p.1 p.2) (Set.Ioo 0 T) := by
    filter_upwards [hcont] with p hp
    refine hp.congr (fun s hs => ?_)
    rw [show u' s p.1 p.2 = u s p.1 p.2 from by
      rw [hu'_eq s ⟨hs.1.le, hs.2.le⟩]]
  have hK' : ∃ K : ℝ, 0 ≤ K ∧ ∀ σ ∈ Set.Icc (0 : ℝ) T,
      ∫ p : ℝ × ℝ, (ud' σ p.1 p.2) ^ 2 * ρ p.1 p.2 ∂diaM ≤ K := by
    obtain ⟨K, hK0, hKb⟩ := hK
    refine ⟨K, hK0, fun σ hσ => ?_⟩
    rw [show (∫ p : ℝ × ℝ, (ud' σ p.1 p.2) ^ 2 * ρ p.1 p.2 ∂diaM)
        = ∫ p : ℝ × ℝ, (udot σ p.1 p.2) ^ 2 * ρ p.1 p.2 ∂diaM from by
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
      rw [hud'_eq σ hσ]]
    exact hKb σ hσ
  have hcontU' : Filter.Tendsto (fun σ : ℝ => ∫ p : ℝ × ℝ,
      (ud' σ p.1 p.2 - ud' τ p.1 p.2) ^ 2 * ρ p.1 p.2 ∂diaM) (nhds τ) (nhds 0) := by
    refine hcontU.congr' ?_
    filter_upwards [hnbd] with σ hσ
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    rw [hud'_eq σ hσ, hud'_eq τ hτIcc]
  have hmain := hasDerivAt_integral_diag_var_ioo (ρ := ρ) (u := u') (udot := ud') (τ := τ) (T := T)
    hT hτ hρmeas hρnn hdiag' hdiagd' hmeas' hmeasd' hderiv' hcont' hK' hcontU'
  have hval : 2 * (∫ p : ℝ × ℝ, ud' τ p.1 p.2 * u' τ p.1 p.2 * ρ p.1 p.2 ∂diaM)
      = 2 * (∫ p : ℝ × ℝ, udot τ p.1 p.2 * u τ p.1 p.2 * ρ p.1 p.2 ∂diaM) := by
    congr 1
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    rw [hud'_eq τ hτIcc, hu'_eq τ hτIcc]
  rw [hval] at hmain
  refine hmain.congr_of_eventuallyEq ?_
  filter_upwards [hnbd] with s hs
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
  rw [hu'_eq s hs]

theorem hasDerivAt_integral_diag_var_restricted {ρ : ℝ → ℝ → ℝ}
    {u udot : ℝ → Work.FTS.Galerkin.Fn}
    {τ T : ℝ} (hT : 0 ≤ T) (hτ : τ ∈ Set.Ioo 0 T)
    (hρmeas : AEMeasurable (Function.uncurry ρ) diaM)
    (hρnn : ∀ᵐ p ∂diaM, 0 ≤ ρ p.1 p.2)
    (hdiag : ∀ s ∈ Set.Icc (0 : ℝ) T, MeasureTheory.Integrable
      (fun p : ℝ × ℝ => (u s p.1 p.2) ^ 2 * ρ p.1 p.2) diaM)
    (hdiagd : ∀ s ∈ Set.Icc (0 : ℝ) T, MeasureTheory.Integrable
      (fun p : ℝ × ℝ => (udot s p.1 p.2) ^ 2 * ρ p.1 p.2) diaM)
    (hmeas : MeasureTheory.AEStronglyMeasurable
      (fun q : ℝ × (ℝ × ℝ) => u q.1 q.2.1 q.2.2)
      ((MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)).prod diaM))
    (hmeasd : MeasureTheory.AEStronglyMeasurable
      (fun q : ℝ × (ℝ × ℝ) => udot q.1 q.2.1 q.2.2)
      ((MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)).prod diaM))
    (hderiv : ∀ᵐ p ∂diaM, ∀ s ∈ Set.Ioo (0 : ℝ) T,
      HasDerivAt (fun t : ℝ => u t p.1 p.2) (udot s p.1 p.2) s)
    (hcont : ∀ᵐ p ∂diaM, ContinuousOn (fun s : ℝ => u s p.1 p.2) (Set.Icc 0 T))
    (hK : ∃ K : ℝ, 0 ≤ K ∧ ∀ σ ∈ Set.Icc (0 : ℝ) T,
      ∫ p : ℝ × ℝ, (udot σ p.1 p.2) ^ 2 * ρ p.1 p.2 ∂diaM ≤ K)
    (hcontU : Filter.Tendsto (fun σ : ℝ => ∫ p : ℝ × ℝ,
        (udot σ p.1 p.2 - udot τ p.1 p.2) ^ 2 * ρ p.1 p.2 ∂diaM) (nhds τ) (nhds 0)) :
    HasDerivAt (fun s : ℝ => ∫ p : ℝ × ℝ, u s p.1 p.2 * u s p.1 p.2 * ρ p.1 p.2 ∂diaM)
      (2 * ∫ p : ℝ × ℝ, udot τ p.1 p.2 * u τ p.1 p.2 * ρ p.1 p.2 ∂diaM) τ := by
  have hτIcc : τ ∈ Set.Icc (0 : ℝ) T := ⟨hτ.1.le, hτ.2.le⟩
  -- the horizon is a neighbourhood of `τ`
  have hnbd : Set.Icc (0 : ℝ) T ∈ nhds τ := Icc_mem_nhds hτ.1 hτ.2
  set u' : ℝ → Work.FTS.Galerkin.Fn :=
    fun s => if s ∈ Set.Icc (0 : ℝ) T then u s else 0 with hu'def
  set ud' : ℝ → Work.FTS.Galerkin.Fn :=
    fun s => if s ∈ Set.Icc (0 : ℝ) T then udot s else 0 with hud'def
  have hu'_eq : ∀ s ∈ Set.Icc (0 : ℝ) T, u' s = u s := by
    intro s hs; rw [hu'def]; simp only [hs, if_true]
  have hud'_eq : ∀ s ∈ Set.Icc (0 : ℝ) T, ud' s = udot s := by
    intro s hs; rw [hud'def]; simp only [hs, if_true]
  have hdiag' : ∀ s ∈ Set.Icc (0 : ℝ) T, MeasureTheory.Integrable
      (fun p : ℝ × ℝ => (u' s p.1 p.2) ^ 2 * ρ p.1 p.2) diaM := by
    intro s hs
    rw [show (fun p : ℝ × ℝ => (u' s p.1 p.2) ^ 2 * ρ p.1 p.2)
        = (fun p : ℝ × ℝ => (u s p.1 p.2) ^ 2 * ρ p.1 p.2) from by
      funext p; rw [hu'_eq s hs]]
    exact hdiag s hs
  have hdiagd' : ∀ s ∈ Set.Icc (0 : ℝ) T, MeasureTheory.Integrable
      (fun p : ℝ × ℝ => (ud' s p.1 p.2) ^ 2 * ρ p.1 p.2) diaM := by
    intro s hs
    rw [show (fun p : ℝ × ℝ => (ud' s p.1 p.2) ^ 2 * ρ p.1 p.2)
        = (fun p : ℝ × ℝ => (udot s p.1 p.2) ^ 2 * ρ p.1 p.2) from by
      funext p; rw [hud'_eq s hs]]
    exact hdiagd s hs
  have hmeas' : MeasureTheory.AEStronglyMeasurable
      (fun q : ℝ × (ℝ × ℝ) => u' q.1 q.2.1 q.2.2)
      ((MeasureTheory.volume : MeasureTheory.Measure ℝ).prod diaM) := by
    have hc := aesm_clamp_restrict (ν := diaM) (U := fun q : ℝ × (ℝ × ℝ) => u q.1 q.2.1 q.2.2)
      (T := T) hmeas
    simpa only [hu'def, ite_apply, Pi.zero_apply] using hc
  have hmeasd' : MeasureTheory.AEStronglyMeasurable
      (fun q : ℝ × (ℝ × ℝ) => ud' q.1 q.2.1 q.2.2)
      ((MeasureTheory.volume : MeasureTheory.Measure ℝ).prod diaM) := by
    have hc := aesm_clamp_restrict (ν := diaM) (U := fun q : ℝ × (ℝ × ℝ) => udot q.1 q.2.1 q.2.2)
      (T := T) hmeasd
    simpa only [hud'def, ite_apply, Pi.zero_apply] using hc
  have hderiv' : ∀ᵐ p ∂diaM, ∀ s ∈ Set.Ioo (0 : ℝ) T,
      HasDerivAt (fun t : ℝ => u' t p.1 p.2) (ud' s p.1 p.2) s := by
    filter_upwards [hderiv] with p hp
    intro s hs
    have hsIcc : s ∈ Set.Icc (0 : ℝ) T := ⟨hs.1.le, hs.2.le⟩
    rw [show ud' s p.1 p.2 = udot s p.1 p.2 from by rw [hud'_eq s hsIcc]]
    refine (hp s hs).congr_of_eventuallyEq ?_
    filter_upwards [Icc_mem_nhds hs.1 hs.2] with t ht
    rw [show u' t p.1 p.2 = u t p.1 p.2 from by rw [hu'_eq t ht]]
  have hcont' : ∀ᵐ p ∂diaM, ContinuousOn (fun s : ℝ => u' s p.1 p.2) (Set.Icc 0 T) := by
    filter_upwards [hcont] with p hp
    refine hp.congr (fun s hs => ?_)
    rw [show u' s p.1 p.2 = u s p.1 p.2 from by rw [hu'_eq s hs]]
  have hK' : ∃ K : ℝ, 0 ≤ K ∧ ∀ σ ∈ Set.Icc (0 : ℝ) T,
      ∫ p : ℝ × ℝ, (ud' σ p.1 p.2) ^ 2 * ρ p.1 p.2 ∂diaM ≤ K := by
    obtain ⟨K, hK0, hKb⟩ := hK
    refine ⟨K, hK0, fun σ hσ => ?_⟩
    rw [show (∫ p : ℝ × ℝ, (ud' σ p.1 p.2) ^ 2 * ρ p.1 p.2 ∂diaM)
        = ∫ p : ℝ × ℝ, (udot σ p.1 p.2) ^ 2 * ρ p.1 p.2 ∂diaM from by
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
      rw [hud'_eq σ hσ]]
    exact hKb σ hσ
  have hcontU' : Filter.Tendsto (fun σ : ℝ => ∫ p : ℝ × ℝ,
      (ud' σ p.1 p.2 - ud' τ p.1 p.2) ^ 2 * ρ p.1 p.2 ∂diaM) (nhds τ) (nhds 0) := by
    refine hcontU.congr' ?_
    filter_upwards [hnbd] with σ hσ
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    rw [hud'_eq σ hσ, hud'_eq τ hτIcc]
  have hmain := hasDerivAt_integral_diag_var (ρ := ρ) (u := u') (udot := ud') (τ := τ) (T := T)
    hT hτ hρmeas hρnn hdiag' hdiagd' hmeas' hmeasd' hderiv' hcont' hK' hcontU'
  have hval : 2 * (∫ p : ℝ × ℝ, ud' τ p.1 p.2 * u' τ p.1 p.2 * ρ p.1 p.2 ∂diaM)
      = 2 * (∫ p : ℝ × ℝ, udot τ p.1 p.2 * u τ p.1 p.2 * ρ p.1 p.2 ∂diaM) := by
    congr 1
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    rw [hud'_eq τ hτIcc, hu'_eq τ hτIcc]
  rw [hval] at hmain
  refine hmain.congr_of_eventuallyEq ?_
  filter_upwards [hnbd] with s hs
  refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
  rw [hu'_eq s hs]

end Work.FTS.StrongEps.EpsE4Thr
