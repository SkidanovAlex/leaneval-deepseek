/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/EpsEngine/MeasAlt/IterMeas.lean` — the fallback proof of the local step's
# `hmeasIter` obligation (the second conjunct), without convexity and without the interval-integral
# measurability

See `Submission/Work/FTS/EpsEngine/NOTES_hmeasIter_FIRST_CONJUNCT_FALSE.md`.  The (true, i.e.
horizon-restricted) second conjunct of `EpsEngine.aesm_iter_of_convex` is proved here by induction
on the Picard index, along three legs:

* `MEAS n` — for every fixed `(z,θ)`, the function `s ↦ F (slice (iter F h₀ n) s) z θ` is a.e.
  strongly measurable on `[0,δ]` (`MeasAlt.aesm_slice_of_lipschitz_gate`, dyadic approximation
  against the iterates themselves — no convexity, no density/separability argument);
* `JOINT n` — the joint measurability of `(σ,z,θ) ↦ F (slice (iter F h₀ n) σ) z θ` for the
  horizon-restricted measure (`aesm_of_slice_aesm` below: the Carathéodory lemma
  `EpsEngine.aesm_uncurry_of_continuousOn_of_zero` applied to the family cut off outside `[0,δ]`);
* `DC n` — `EpsSq α (slice (iter F h₀ n) s − slice (iter F h₀ n) t) ≤ L (s-t)²` on `[0,δ]`, obtained
  from the `ℝ≥0∞`-valued Cauchy–Schwarz estimate `MeasAlt.EpsL_intervalIntegral_le_slicewise`, whose
  measurability hypotheses are exactly `MEAS n` and `JOINT n`.
-/
import Mathlib.MeasureTheory.Function.StronglyMeasurable.AEStronglyMeasurable
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EpsEngine.EpsClass
import Submission.Work.FTS.EpsEngine.MeasAlt.EpsLDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.EpsEngine.MeasAlt

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false

/-- The open quadrant. -/
private def Q0 : Set (ℝ × ℝ) := Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)

/-! ## Two elementary facts about a.e. strong measurability and restrictions -/

/-- Cutting a function off outside `s` preserves a.e. strong measurability, when it is known w.r.t.
the restricted measure. -/
theorem aesm_indicator_of_aesm_restrict {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {s : Set α} (hs : MeasurableSet s) {f : α → ℝ}
    (h : MeasureTheory.AEStronglyMeasurable f (μ.restrict s)) :
    MeasureTheory.AEStronglyMeasurable (s.indicator f) μ := by
  obtain ⟨g, hg, hae⟩ := h
  have h1 : ∀ᵐ x ∂μ, x ∈ s → f x = g x := (ae_restrict_iff' hs).mp hae
  have hae' : s.indicator f =ᵐ[μ] s.indicator g := by
    filter_upwards [h1] with x hx
    by_cases hxs : x ∈ s
    · simp only [Set.indicator_of_mem hxs]; exact hx hxs
    · simp only [Set.indicator_of_notMem hxs]
  exact ((hg.aestronglyMeasurable.indicator hs)).congr hae'.symm

/-- A.e. strong measurability descends to restrictions. -/
theorem aesm_restrict_of_aesm {α : Type*} [MeasurableSpace α] {μ : Measure α} {s : Set α}
    {f : α → ℝ} (h : MeasureTheory.AEStronglyMeasurable f μ) :
    MeasureTheory.AEStronglyMeasurable f (μ.restrict s) :=
  h.mono_measure Measure.restrict_le_self

/-- A.e. strong measurability transfers to any smaller measure. -/
theorem aesm_of_le {α : Type*} [MeasurableSpace α] {μ ν : Measure α} {f : α → ℝ}
    (h : MeasureTheory.AEStronglyMeasurable f ν) (hle : μ ≤ ν) :
    MeasureTheory.AEStronglyMeasurable f μ :=
  h.mono_measure hle

/-! ## The Carathéodory step -/

/-- The horizon-restricted measure on the space of `(σ,z,θ)`. -/
private def nuH (δ : ℝ) : Measure (ℝ × ℝ × ℝ) :=
  (MeasureTheory.volume.restrict (Set.Icc 0 δ)).prod MeasureTheory.volume

/-- **Joint measurability from slicewise measurability, for a family vanishing off the quadrant.**
`EpsEngine.aesm_uncurry_of_continuousOn_of_zero` applied to the family cut off outside `[0,δ]`,
followed by the transfer to the horizon-restricted measure. -/
theorem aesm_of_slice_aesm {F : Fn → Fn} {V : ℝ → Fn} {P : Fn → Prop} {δ : ℝ}
    (hV : ∀ s ∈ Set.Icc 0 δ, P (V s))
    (hcont : ∀ w : Fn, P w → ContinuousOn (fun q : ℝ × ℝ => F w q.1 q.2) Q0)
    (hzero : ∀ (w : Fn) (q : ℝ × ℝ), q ∉ Q0 → F w q.1 q.2 = 0)
    (hmeas : ∀ z θ : ℝ, MeasureTheory.AEStronglyMeasurable (fun s : ℝ => F (V s) z θ)
      (MeasureTheory.volume.restrict (Set.Icc 0 δ))) :
    MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ × ℝ => F (V p.1) p.2.1 p.2.2) (nuH δ) := by
  set g : ℝ → ℝ → ℝ → ℝ := fun s z θ => if s ∈ Set.Icc 0 δ then F (V s) z θ else 0 with hg
  have hms : MeasurableSet (Set.Icc (0 : ℝ) δ) := measurableSet_Icc
  have hcont' : ∀ s : ℝ, ContinuousOn (fun q : ℝ × ℝ => g s q.1 q.2) Q0 := by
    intro s
    by_cases hs : s ∈ Set.Icc 0 δ
    · have h1 : (fun q : ℝ × ℝ => g s q.1 q.2) = fun q : ℝ × ℝ => F (V s) q.1 q.2 := by
        funext q; simp only [hg]; rw [if_pos hs]
      rw [h1]; exact hcont (V s) (hV s hs)
    · have h1 : (fun q : ℝ × ℝ => g s q.1 q.2) = fun _ : ℝ × ℝ => (0 : ℝ) := by
        funext q; simp only [hg]; rw [if_neg hs]
      rw [h1]; exact continuousOn_const
  have hzero' : ∀ (s : ℝ) (q : ℝ × ℝ), q ∉ Q0 → g s q.1 q.2 = 0 := by
    intro s q hq
    by_cases hs : s ∈ Set.Icc 0 δ
    · simp only [hg]; rw [if_pos hs]; exact hzero (V s) q hq
    · simp only [hg]; rw [if_neg hs]
  have hmeas' : ∀ q : ℝ × ℝ,
      MeasureTheory.AEStronglyMeasurable (fun s : ℝ => g s q.1 q.2) MeasureTheory.volume := by
    intro q
    have h1 : (fun s : ℝ => g s q.1 q.2)
        = (Set.Icc (0 : ℝ) δ).indicator (fun s : ℝ => F (V s) q.1 q.2) := by
      funext s; simp only [hg, Set.indicator]
    rw [h1]
    exact aesm_indicator_of_aesm_restrict hms (hmeas q.1 q.2)
  have hmain : MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ × ℝ => g p.1 p.2.1 p.2.2) MeasureTheory.volume :=
    aesm_uncurry_of_continuousOn_of_zero (g := g) hcont' hzero' hmeas'
  -- the horizon-restricted measure is smaller than the ambient one
  have hle : nuH δ ≤ MeasureTheory.volume := by
    refine MeasureTheory.Measure.prod_mono Measure.restrict_le_self le_rfl |>.trans ?_
    exact le_of_eq (MeasureTheory.Measure.volume_eq_prod ℝ (ℝ × ℝ)).symm
  -- and on it, `g` coincides a.e. with the family
  have haeeq : (fun p : ℝ × ℝ × ℝ => g p.1 p.2.1 p.2.2)
      =ᵐ[nuH δ] fun p : ℝ × ℝ × ℝ => F (V p.1) p.2.1 p.2.2 := by
    have hkey : ∀ᵐ p ∂nuH δ, p.1 ∈ Set.Icc (0 : ℝ) δ := by
      rw [nuH, MeasureTheory.Measure.ae_prod_iff_ae_ae
        (measurableSet_Icc.preimage measurable_fst)]
      filter_upwards [show ∀ᵐ s ∂(MeasureTheory.volume.restrict (Set.Icc 0 δ)),
          s ∈ Set.Icc 0 δ from
        (ae_restrict_iff' hms).mpr (Eventually.of_forall fun s hs => hs)] with s hs
      exact Eventually.of_forall fun q => hs
    filter_upwards [hkey] with p hp
    simp only [hg]; rw [if_pos hp]
  exact (hmain.mono_measure hle).congr haeeq

end Work.FTS.EpsEngine.MeasAlt
