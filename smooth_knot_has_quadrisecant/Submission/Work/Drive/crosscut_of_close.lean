import Mathlib
import Submission.Work.Drive.oFatDefs
import Submission.Work.Drive.crosscut_or_spreadQuad
import Submission.Work.Drive.fatMiddle_slab
import Submission.Work.Drive.separation_of_far_parameters

/-!
# `E3` in the `C¹`-ball form: the constants of the design

`Work.Drive.crosscut_or_spreadQuad` (`E3`) is stated at a *given* knot `r'`, with the four constants
of the design as hypotheses:

* `t₀`, `η` — the farthest point and the slab radius of `E3a` (`Work.Drive.fatMiddle_slab`);
* `s` — the separation constant of `Work.Drive.separation_of_far_parameters` at scale `ρ`;
* `V` — a Lipschitz constant of `knotMap r'`.

This module instantiates them, *uniformly over a `C¹`-ball* around a reference knot `r₀`, so that
the result can be consumed by the crux `Work.Drive.SpreadCrux` (which quantifies over the
approximants `r'` in a `C¹`-ball).  Concretely: there is a radius `ε₁ > 0` (the minimum of the
radius of `E3a`, the radius of the separation statement and `1`) such that every knot `r'` in the
`C¹`-ball of radius `ε₁` around `r₀` either has a `δ`-spread quadrisecant for some `δ > 0`, or
carries a bottom–top crosscut of the period strip avoiding `OFatObstruction r' ρ`.

The Lipschitz constant used for `r'` is `V + 1`, where `V` bounds the speed of the reference knot.
-/

noncomputable section

namespace Work.Drive

open LeanEval.KnotTheory.Quadrisecant Set

open scoped unitInterval

/-- A speed bound for a knot gives a Lipschitz bound for its `knotMap` on the parameter circle. -/
lemma knotMap_lipschitz_of_velocity {r : ℝ → Space} (hr : IsSmoothKnot r) {M : ℝ}
    (hM : ∀ t : ℝ, ‖velocity r t‖ ≤ M) :
    ∀ a b : KnotParam, ‖knotMap r a - knotMap r b‖ ≤ M * dist a b := by
  intro a b
  obtain ⟨t, s, ht, hs, hts⟩ := exists_representatives_dist a b
  have h1 : knotMap r a = r t := by rw [← ht, knotMap_eq_of_periodic hr.periodic t]
  have h2 : knotMap r b = r s := by rw [← hs, knotMap_eq_of_periodic hr.periodic s]
  rw [h1, h2, ← hts]
  exact norm_sub_le_of_velocity_bound hr.smooth hM s t

/-- **`E3` uniformly over the `C¹`-ball of a reference knot.**  Let `r₀` be a smooth knot whose
speed is bounded by `V > 0`.  There is `ε₁ ∈ (0, 1]` such that, for every `ρ > 0` and every smooth
knot `r'` which is `C¹`-`ε₁`-close to `r₀`, is in tangent-chord general position and has no
inflection points, either `r'` has a `δ`-spread quadrisecant for some `δ > 0`, or the period strip
carries a bottom–top crosscut avoiding `OFatObstruction r' ρ`.

(The four constants of `E3` are instantiated as follows: `η` and `t₀` come from `E3a`
`Work.Drive.fatMiddle_slab` at the given `ρ` (with `η` capped by `period/4` so that `2η < period`),
`s` from `Work.Drive.separation_of_far_parameters` for `r₀` at scale `ρ` (using the `C¹`-closeness),
and the Lipschitz constant `V + 1` for `r'` from the speed bound `V` of `r₀` and the `C¹`-closeness
with `ε₁ ≤ 1`.) -/
theorem crosscut_or_spreadQuad_of_close
    {r₀ : ℝ → Space} (hr₀ : IsSmoothKnot r₀) {V : ℝ} (hVpos : 0 < V)
    (hvel₀ : ∀ t : ℝ, ‖velocity r₀ t‖ ≤ V) :
    ∃ ε₁ : ℝ, 0 < ε₁ ∧ ε₁ ≤ 1 ∧
      ∀ {ρ : ℝ}, 0 < ρ → ∃ δ : ℝ, 0 < δ ∧
      ∀ r' : ℝ → Space, IsSmoothKnot r' → TangentChordGP r' →
        (∀ t : ℝ, LinearIndependent ℝ ![deriv r' t, deriv (deriv r') t]) →
        (∀ t : ℝ, ‖r' t - r₀ t‖ < ε₁ ∧ ‖velocity r' t - velocity r₀ t‖ < ε₁) →
        ((∃ a b z w : ℝ, SpreadQuad δ a b z w ∧
            IsMiddleOnChord r' (a : KnotParam) (b : KnotParam) (z : KnotParam) ∧
            IsMiddleOnChord r' (a : KnotParam) (b : KnotParam) (w : KnotParam)) ∨
          StripCrosscutAvoidingOFat r' ρ) := by
  obtain ⟨εs, hεspos, hs⟩ := separation_of_far_parameters hr₀
  obtain ⟨εa, hεapos, hE3a⟩ := fatMiddle_slab hr₀
  refine ⟨min (min εs εa) 1, by positivity, min_le_right _ _, ?_⟩
  have hε1s : min (min εs εa) 1 ≤ εs := le_trans (min_le_left _ _) (min_le_left _ _)
  have hε1a : min (min εs εa) 1 ≤ εa := le_trans (min_le_left _ _) (min_le_right _ _)
  have hε1_1 : min (min εs εa) 1 ≤ 1 := min_le_right _ _
  intro ρ hρ
  obtain ⟨s, hspos, hsep₀⟩ := hs ρ hρ
  obtain ⟨η₀, hη₀pos, hslab₀⟩ := hE3a ρ hρ
  -- cap `η` so that the cells are nonempty
  set η : ℝ := min η₀ (period / 4) with hηdef
  have hηpos : 0 < η := lt_min hη₀pos (by linarith [period_pos])
  have hηP : 2 * η < period := by
    have h1 : η ≤ period / 4 := min_le_right _ _
    linarith [period_pos]
  refine ⟨min ρ (min (2 * η) (2 * s / (V + 1))), by positivity, ?_⟩
  intro r' hr' htc hinfl hclose
  have hcl_s : ∀ t : ℝ, ‖r' t - r₀ t‖ < εs ∧ ‖velocity r' t - velocity r₀ t‖ < εs :=
    fun t => ⟨lt_of_lt_of_le (hclose t).1 hε1s, lt_of_lt_of_le (hclose t).2 hε1s⟩
  have hcl_a : ∀ t : ℝ, ‖r' t - r₀ t‖ < εa ∧ ‖velocity r' t - velocity r₀ t‖ < εa :=
    fun t => ⟨lt_of_lt_of_le (hclose t).1 hε1a, lt_of_lt_of_le (hclose t).2 hε1a⟩
  have hsep : ∀ a b : KnotParam, ρ ≤ dist a b → s ≤ ‖knotMap r' a - knotMap r' b‖ :=
    hsep₀ r' hr' hcl_s
  obtain ⟨t₀, ht₀⟩ := hslab₀ r' hr' hcl_a
  have hslab : ∀ u : ℝ, FatMiddle r' ρ u → ∀ k : ℤ, η < |u - (t₀ + (k : ℝ) * period)| :=
    fun u hu k => lt_of_le_of_lt (min_le_left _ _) (ht₀ u hu k)
  -- the Lipschitz constant `V + 1` for `r'`
  have hvel' : ∀ t : ℝ, ‖velocity r' t‖ ≤ V + 1 := by
    intro t
    have h1 : ‖velocity r' t‖ ≤ ‖velocity r₀ t‖ + ‖velocity r' t - velocity r₀ t‖ := by
      have h := norm_add_le (velocity r₀ t) (velocity r' t - velocity r₀ t)
      rwa [add_sub_cancel] at h
    have h2 : ‖velocity r' t - velocity r₀ t‖ < 1 := lt_of_lt_of_le (hclose t).2 hε1_1
    have h3 : ‖velocity r₀ t‖ ≤ V := hvel₀ t
    linarith
  have hlip : ∀ a b : KnotParam, ‖knotMap r' a - knotMap r' b‖ ≤ (V + 1) * dist a b :=
    knotMap_lipschitz_of_velocity hr' hvel'
  exact crosscut_or_spreadQuad hr' hinfl htc hρ hηpos hηP hslab hspos (by linarith) hsep hlip

end Work.Drive
