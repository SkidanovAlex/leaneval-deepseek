import Mathlib
import Submission.Work.Drive.Interfaces
import Submission.Work.Theorem3Endgame
import Submission.Work.Drive.OrderBase
import Submission.Work.Drive.isOpen_Zc
import Submission.Work.Drive.parityCoreOfLiveNodes

/-! Guidance from the project lead (the requester):

# Guidance (project lead) — orderSplit_chains
Read HANDOFF.md and `_ref/OneThird.tex` (Thm 2, Lemmas 1–6). You prove the geometric core, OrderSplitHolds γ,
by mod-2 intersection counting WITHOUT building ℝ×ℝP³. A colleague attacks the same statement through the
ℝ×ℝP³ model; do not coordinate, just finish.

The contracts are hypotheses: hU (Umlaufsatz) and hP (box parity). Both are proved in parallel by others.

Plan, in the configuration space C = ℝ² × (ℝ/ℤ) × [0,∞) (midpoint, doubled direction, length), acted on by
rotation of the angle coordinate (`actC`):
1. M = image of `muOrd` over unordered pairs, a Möbius strip; ∂M lies over the diagonal (length 0). Prove the
   embedding and regularity facts you need. Where is smoothness of γ needed? At the diagonal; use γ' ≠ 0.
2. For u with M ∩ uM = ∅ (u ∉ GoodC γ), define b(u) ∈ ZMod 2 as the parity of #(core loop of M ∩ u·V), where V is
   an explicit 3-chain with ∂V ⊇ M. A proposed V (unchecked): the scaling trace ⋃_{s∈(0,1]} s·M, scaling the midpoint
   around a fixed interior point c of γ and scaling the length. Scaling commutes with rotation, so u·V is the chain
   of uM. Make intersections transverse by a generic small perturbation (Sard: `Projection/*`).
3. b is locally constant on the open set (GoodC γ)ᶜ: homotopy + hP.
4. Antisymmetry, b(u) + b(−u) = 1: count the endpoints of V ∩ uV ∩ H (H = a hyperplane-type slice) with hP.
   The end at the axis contributes 1 (this uses hU: ∂M is the (2,1) torus knot).
5. Transitivity: if M, aM and (a+b)M are pairwise disjoint and b(a) = b(b) = 1, then b(a+b) = 1. This is hP on
   V ∩ aV ∩ (a+b)V.
6. W := {u ∉ GoodC γ | b(u) = 1} gives OrderSplitHolds (openness from 3; the triple condition from 5 and 4).
Delegate each numbered step with an EXACT Lean statement. Make sure the definitions (V, b) live in one shared file
that you write first.
-/

namespace Work.Drive

open Manifold in
open scoped Manifold ContDiff in
/-- The geometric core of Hugelmeyer's theorem: the order split of the non-collision angles. -/
theorem orderSplit_chains (hU : Submission.Drive.UmlaufProp) (hP : Submission.Drive.ParityProp)
    (γ : Circle → ℝ × ℝ) (hγ : IsSmoothEmbedding (𝓡 1) 𝓘(ℝ, ℝ × ℝ) ∞ γ) :
    Submission.Configuration.OrderSplitHolds γ := by
  -- Route 1 (no intermediate wall): the germ route's counting datum and the density node
  -- (`Work.Drive.hn2_refTripleAt_producer` through the *live* chain `Work.Drive.hn2_off_half` /
  -- `Work.Drive.hn2_refCountExists`, and `Work.Drive.hdense_sideGerm`) are the *only* open inputs of
  -- `ParityCore γ`; everything else (the capped plane chart of a suitable translate, the chart
  -- perturbation, the level bound, the germ assembly, the transport back along the translation) is
  -- proved.  See `Submission/Work/Drive/parityCoreOfLiveNodes.lean`.
  exact orderSplitHolds_of_ParityCore (isOpen_Zc γ hγ) (parityCore_of_liveNodes hU γ hγ)
  -- Route 2 (through the wall `Work.Drive.chainParity`, the project lead's organisation):
  --   exact orderSplitHolds_of_ParityCore (isOpen_Zc γ hγ) (chainParity hU hP γ hγ)
  -- Equivalent pairwise-order route:
  --   obtain ⟨Rel, hRel⟩ := stripRel_exists hU hP γ hγ
  --   exact orderSplitHolds_of_ParityCore (isOpen_Zc γ hγ) (parityCore_of_stripRel hRel)

end Work.Drive
