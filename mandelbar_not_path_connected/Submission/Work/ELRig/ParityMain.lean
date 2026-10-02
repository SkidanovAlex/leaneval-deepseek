/-
# ELRig — R-a3 by crossing parity (assembly)

`Submission/Work/ELRig/NOTES.md` §9 reduced R-a3 (`equatorTail_mem_near`: the equator tail lies
in the near side of the `α`-pair) to a parity computation along a vertical segment, and left the
parity itself open.  This file closes it.

The two geometric facts that make the parity work are proved in `TailBand.lean`:

* **the band bound** (`band₁`): the lift `γ₁` meets the far-left half plane `{Re < -R}` only in
  the band `|Im| ≤ R₀` of the flower's `Ψ_ends`;
* **the window bound** (`re_sub_bounded`): `Re (γ₁ s) = s + O(1)`, so every crossing of a far-left
  level lies on the *tail* of the lift, and **the tail lies in one open half plane**
  (`exists_tail_one_side`, because the real axis is off the lift there under `hE`).

Consequently, at a far-left level `x₀` whose `γ₁`-crossings are finite, odd in number and
transversal (`odd_transversal_level`, from the analyticity of the lift), the vertical segment from
the real point `x₀` in the direction of the tail meets the pair curve *only* at those crossings
(`segment_sep`); each crossing flips the side (`hflipgen`, the content of
`Work.ELRig.exists_side_flip`), the far end of the segment lies in the petal `Pa ⊆ pairSide P`,
and the number of crossings is odd, so `Ψ (x₀) ∈ pairSideNear P`
(`exists_pairSideNear_of_crossingOdd`).  The rest of the far-left real axis follows because the
side of `Ψ` there is locally constant (`side_constant_left`).
-/
import Mathlib
import Submission.Work.ELRig.TailBand
import Submission.Work.ELRig.exists_analytic_rayCylLift
import Submission.Work.ELRig.exists_pairSideNear_of_crossingOdd
import Submission.Work.ELRig.rigidity
import Submission.Work.ELRig.reach

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set
open scoped Topology

set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

noncomputable section

namespace Work.ELRig

open Work.EL

/-- The conclusion of the **side flip** at a crossing of the lift with the vertical line
`{Re = x₀}`: the two points of the line at distance `δ` above and below the crossing height `y`
have `Ψ`-images in the two different sides of the pair `P`. -/
abbrev FlipConclusion {c : ℂ} {d : Work.EL.RootParabolic c}
    (fl : Work.EL.ParabolicFlower (Work.EL.F c) ((LeanEval.ComplexAnalysis.Tantibar c)^[5]) d.z₁)
    (P : Work.EL.CoPair d.hN) (x₀ y δ : ℝ) : Prop :=
  ((fl.Ψ ((x₀ : ℂ) + (y + δ) * Complex.I) ∈ Work.EL.pairSide P ∧
    fl.Ψ ((x₀ : ℂ) + (y - δ) * Complex.I) ∈ Work.EL.pairSideNear P) ∨
   (fl.Ψ ((x₀ : ℂ) + (y + δ) * Complex.I) ∈ Work.EL.pairSideNear P ∧
    fl.Ψ ((x₀ : ℂ) + (y - δ) * Complex.I) ∈ Work.EL.pairSide P))

/-- The hypothesis "the side of `Ψ` flips at every transversal crossing of the level `Re = x₀`
with the lift".  It is exactly the conclusion of `Work.ELRig.exists_side_flip` (which supplies it
from the local angle-side lemma at the lift, the local biholomorphy of `Ψ` there, and the Jordan
curve theorem `hJ`). -/
abbrev FlipHyp {c : ℂ} {d : Work.EL.RootParabolic c}
    (fl : Work.EL.ParabolicFlower (Work.EL.F c) ((LeanEval.ComplexAnalysis.Tantibar c)^[5]) d.z₁)
    (P : Work.EL.CoPair d.hN) (L : RayCylLift d fl) : Prop :=
  ∀ (x₀ : ℝ), x₀ < -L.R → ∀ s : ℝ, (L.γ₁ s).re = x₀ →
    deriv (fun t : ℝ => (L.γ₁ t).re) s ≠ 0 → ∃ ε > 0, ∀ δ : ℝ, 0 < δ → δ < ε →
      ((x₀ : ℂ) + ((L.γ₁ s).im + δ) * Complex.I) ∉ Set.range L.γ₁ ∪ Set.range L.γ₂ →
      ((x₀ : ℂ) + ((L.γ₁ s).im - δ) * Complex.I) ∉ Set.range L.γ₁ ∪ Set.range L.γ₂ →
      FlipConclusion fl P x₀ (L.γ₁ s).im δ

/-- **R-a3 by crossing parity.**  Assume the equator is contained in the filled Julia set (`hE`),
the first lift `γ₁` of the root ray is real-analytic on each period (`han`), and the side of `Ψ`
flips at every transversal crossing of a far-left vertical line with the lift (`hflip`).  Then the
equator tail `Ψ x`, `x < -R`, lies in the *near* side of the `α`-pair of the nest. -/
theorem htail_of_flip {c : ℂ} (d : Work.EL.RootParabolic c)
    (fl : Work.EL.ParabolicFlower (Work.EL.F c) ((LeanEval.ComplexAnalysis.Tantibar c)^[5]) d.z₁)
    (nest : Work.EL.Z1Nest d.hN d.z₁ fl.Pa)
    (L : RayCylLift d fl)
    (han : ∀ n : ℤ, AnalyticOn ℝ (fun s : ℝ => L.γ₁ s) (Set.Ioo (n : ℝ) ((n : ℝ) + 1)))
    (hflip : FlipHyp fl nest.P0 L)
    (hE : ∀ x : ℝ, fl.Ψ (x : ℂ) ∈ Work.EL.K c) :
    ∃ R' : ℝ, ∀ x : ℝ, x < -R' → fl.Ψ (x : ℂ) ∈ Work.EL.pairSideNear nest.P0 := by
  obtain ⟨R₀, hR₀R, hγ⟩ := L.hγtail
  obtain ⟨M, hM⟩ := re_sub_bounded L
  obtain ⟨s₁, ε₁, hε₁, hsign⟩ := exists_tail_one_side L hE
  obtain ⟨x₀, hx₀lt, hodd, htrans⟩ :=
    odd_transversal_level L.cont₁ L.per₁ han (R := max L.R (M - s₁) + 1)
  have hx₀LR : x₀ < -L.R := by
    have h1 : L.R ≤ max L.R (M - s₁) := le_max_left _ _
    linarith
  have hxM : x₀ + M ≤ s₁ := by
    have h1 : M - s₁ ≤ max L.R (M - s₁) := le_max_right _ _
    linarith
  have hxM₂ : x₀ - 1 / 2 + M ≤ s₁ := by linarith
  have hmem₁ : ∀ s : ℝ, (L.γ₁ s).re = x₀ → s ≤ s₁ := fun s hs => le_of_crossing L hM hxM hs
  have hmem₂ : ∀ s : ℝ, (L.γ₁ s).re = x₀ - 1 / 2 → s ≤ s₁ :=
    fun s hs => le_of_crossing L hM hxM₂ hs
  have hband1 : ∀ s : ℝ, (L.γ₁ s).re = x₀ → |(L.γ₁ s).im| ≤ R₀ :=
    fun s hs => band₁ L hR₀R hγ (by rw [hs]; exact hx₀LR)
  have hpos : ∀ s : ℝ, (L.γ₁ s).re = x₀ → 0 < ε₁ * (L.γ₁ s).im :=
    fun s hs => hsign s (hmem₁ s hs)
  have hsep : ∀ t : ℝ, 0 ≤ ε₁ * t → ε₁ * t ≤ R₀ + 1 →
      (((x₀ : ℂ) + t * Complex.I) ∈ Set.range L.γ₁ ∪ Set.range L.γ₂ ↔
        ∃ s : ℝ, (L.γ₁ s).re = x₀ ∧ t = (L.γ₁ s).im) :=
    fun t h1 _ => segment_sep L hsign hmem₂ t h1
  have hflip₀ : ∀ s : ℝ, (L.γ₁ s).re = x₀ → ∃ ε > 0, ∀ δ : ℝ, 0 < δ → δ < ε →
      ((x₀ : ℂ) + ((L.γ₁ s).im + δ) * Complex.I) ∉ Set.range L.γ₁ ∪ Set.range L.γ₂ →
      ((x₀ : ℂ) + ((L.γ₁ s).im - δ) * Complex.I) ∉ Set.range L.γ₁ ∪ Set.range L.γ₂ →
      ((fl.Ψ ((x₀ : ℂ) + ((L.γ₁ s).im + δ) * Complex.I) ∈ Work.EL.pairSide nest.P0 ∧
        fl.Ψ ((x₀ : ℂ) + ((L.γ₁ s).im - δ) * Complex.I) ∈ Work.EL.pairSideNear nest.P0) ∨
       (fl.Ψ ((x₀ : ℂ) + ((L.γ₁ s).im + δ) * Complex.I) ∈ Work.EL.pairSideNear nest.P0 ∧
        fl.Ψ ((x₀ : ℂ) + ((L.γ₁ s).im - δ) * Complex.I) ∈ Work.EL.pairSide nest.P0)) :=
    fun s hs => hflip x₀ hx₀LR s hs (htrans s hs)
  have hfin : ({s : ℝ | (L.γ₁ s).re = x₀}).Finite := by
    by_contra hf
    rw [Set.not_finite] at hf
    rw [hf.ncard] at hodd
    exact absurd hodd (by rintro ⟨k, hk⟩; omega)
  have hnear : fl.Ψ (x₀ : ℂ) ∈ Work.EL.pairSideNear nest.P0 :=
    exists_pairSideNear_of_crossingOdd d fl nest.P0 nest.P0_spec.1 nest.P0_spec.2.1
      nest.P0_spec.2.2 nest.sides_P0 L nest.Pa_far hx₀LR hR₀R hγ (injective₁ L) hfin hodd hε₁
      hpos hband1 hsep hflip₀
  exact ⟨L.R, fun x hx => side_constant_left d fl nest.P0 nest.P0_spec.2.2 nest.sides_P0 L hE
    hx₀LR hx hnear⟩

end Work.ELRig

end
