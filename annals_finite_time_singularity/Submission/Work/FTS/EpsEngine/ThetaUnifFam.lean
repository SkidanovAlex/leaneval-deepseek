/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/EpsEngine/ThetaUnifFam.lean` — the FAMILY-uniform angular flatness

`ThetaUnif α k f` (`EpsEngine/UnifTraceDefs.lean`) is the angular (`ε`-`δ`, uniform in `z`)
flatness of a *single* profile.  The class-`C` invariance of the local step needs the same data for
a whole *curve* `s ↦ H s` of right-hand sides, *uniformly in* `s`: the interval-integral leg
`EpsEngine.ThetaUnifInterval` consumes exactly that shape (its `ht0`/`ht1` quantify over
`s ∈ Icc 0 T` inside the `∃δ`).

This module fixes the vocabulary

    `ThetaUnifFam α k T H`
      = the two `ε`-`δ` angular conditions of `ThetaUnif`, uniformly in `z > 0` AND in
        `s ∈ Icc 0 T`, for every slot `a + b ≤ k`,

proves the two elementary consequences

* `ThetaUnifFam.pointwise` — the family form implies the memberwise form (so every lemma proved
  for `ThetaUnif` can still be used memberwise), and
* `thetaUnifFam_intervalIntegral` — the fake-time integral `(z,θ) ↦ ∫_a^b H s z θ ds` of a
  family-uniformly-flat curve is flat (`ThetaUnif α k`),

and leaves the *transfer through the mollifier and the projection* (`ThetaUnifFamJeps`,
`ThetaUnifFam_Pz`) as the two remaining mechanical legs — they are the family forms of the proved
single-profile lemmas `ThetaUnifJeps` and `EpsEngine.thetaUnif_Pz`, with the same `δ`-bookkeeping
and one extra `∀ s ∈ Icc 0 T`.

Everything here is `sorry`-free.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.EpsEngine.ThetaUnifPz

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EpsEngine

open scoped Real Topology
open MeasureTheory Set Filter
open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **The family-uniform angular flatness**: the two `ε`-`δ` conditions of `ThetaUnif`, uniformly
in `z > 0` and in the curve parameter `s ∈ Icc 0 T`, for every slot `a + b ≤ k`. -/
structure ThetaUnifFam (α : ℝ) (k : ℕ) (T : ℝ) (H : ℝ → ℝ → ℝ → ℝ) : Prop where
  /-- angular vanishing at `θ → 0⁺`, uniformly in `z` and in `s`. -/
  t0 : ∀ ε' > 0, ∃ δ > 0, ∀ θ : ℝ, 0 < θ → θ < δ → ∀ z : ℝ, 0 < z →
    ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ a b : ℕ, a + b ≤ k →
      Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) * (Work.Spaces.mixed b a (H s) z θ) ^ 2 ≤ ε'
  /-- angular vanishing at `θ → (π/2)⁻`, uniformly in `z` and in `s`. -/
  t1 : ∀ ε' > 0, ∃ δ > 0, ∀ θ : ℝ, θ < Real.pi / 2 → Real.pi / 2 - δ < θ → ∀ z : ℝ, 0 < z →
    ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ a b : ℕ, a + b ≤ k →
      Real.sin (2 * θ) ^ (1 - Work.Spaces.gam α) * (Work.Spaces.mixed b a (H s) z θ) ^ 2 ≤ ε'

/-- The family form implies the memberwise form. -/
theorem ThetaUnifFam.pointwise {α : ℝ} {k : ℕ} {T : ℝ} {H : ℝ → ℝ → ℝ → ℝ}
    (h : ThetaUnifFam α k T H) {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) T) :
    ThetaUnif α k (H s) :=
  ⟨fun a b hab ε' hε' => by
      obtain ⟨δ, hδ, hp⟩ := h.t0 ε' hε'
      exact ⟨δ, hδ, fun θ hθ0 hθδ z hz => hp θ hθ0 hθδ z hz s hs a b hab⟩,
   fun a b hab ε' hε' => by
      obtain ⟨δ, hδ, hp⟩ := h.t1 ε' hε'
      exact ⟨δ, hδ, fun θ hθ2 hθδ z hz => hp θ hθ2 hθδ z hz s hs a b hab⟩⟩

/-- **The fake-time integral of a family-uniformly-flat curve is flat.**

`(z,θ) ↦ ∫_a^b H s z θ ds` satisfies `ThetaUnif α k` as soon as the curve is family-uniformly flat
(`ThetaUnifFam`), smooth on the open quadrant at every `s ∈ [0,T]`, a.e.-strongly measurable in `s`
in every slot of order `≤ k`, and uniformly bounded in `s` in every slot on compacta of the open
quadrant.  (The last three are the hypotheses of the exchange identity
`PerzTools.mixed_intervalIntegral_eq_gen_restricted`.) -/
theorem thetaUnifFam_intervalIntegral {α T : ℝ} {k : ℕ} {a b : ℝ} {H : ℝ → ℝ → ℝ → ℝ}
    (hT : 0 ≤ T) (haT : a ∈ Set.Icc (0 : ℝ) T) (hbT : b ∈ Set.Icc (0 : ℝ) T) (hab : a ≤ b)
    (hfam : ThetaUnifFam α k T H)
    (hsm : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry (H s))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hmeas : ∀ (j i : ℕ), j + i ≤ k → ∀ z θ : ℝ,
      (z, θ) ∈ (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) →
      MeasureTheory.AEStronglyMeasurable (fun s : ℝ => Work.Spaces.mixed j i (H s) z θ)
        (MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) T)))
    (hsup : ∀ (j i : ℕ), j + i ≤ k → ∀ K : Set (ℝ × ℝ), IsCompact K →
      K ⊆ (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ q ∈ K,
        |Work.Spaces.mixed j i (H s) q.1 q.2| ≤ C) :
    ThetaUnif α k (fun z θ => ∫ s in a..b, H s z θ) :=
  ThetaUnifInterval (α := α) (T := T) (k := k) hT haT hbT hab hsm hmeas hsup
    (fun ε' hε' => hfam.t0 ε' hε') (fun ε' hε' => hfam.t1 ε' hε')

end Work.FTS.EpsEngine
