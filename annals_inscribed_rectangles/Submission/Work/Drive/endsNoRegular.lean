import Mathlib
import Submission.Work.Drive.odd_sum_bottomBdryMeet_of_classTriple

set_option maxHeartbeats 800000

/-!
# The ends clause of the counting route **does not need `ClassTripleRegular`**

`Work.Drive.odd_sum_bottomBdryMeet_of_classTriple` (the ends clause of Hugelmeyer's Lemmas 3–4, i.e.
the parity `Odd (n_{-λ})` of the paper's four-face count) is stated with the hypothesis

> `hreg : ClassTripleRegular P`

— the *plane regularity* of the design's triple (smoothness, the seam clause, the immersion `hci` of
the three class maps on the open square and the general position `hV` of the three class `2`-planes).
That hypothesis is **never used** by the proof: it occurs only in the signature.  (Verified by
inspection: the body builds the `Work.Drive.EndDesign P` from the *design data* alone and concludes
through `EndDesign.ncard_bottomBdryMeet_zero_eq_ncard_classTripleSet` and
`Work.Drive.bottomBdryMeet_eq_empty_of_lt_level_local`, neither of which mentions `hreg`.)

This matters, because `ClassTripleRegular` is **not** available for the honest chart of every smooth
Jordan curve: `Submission/Work/Drive/HC_VS_PLANE_IMMERSION.md` §2 exhibits a curve (a "pac-man") whose
plane chart has a class map of rank `≤ 1` on an *open* set of parameters, so `hci` fails there, and no
chart perturbation repairs it (`planeClassMap (Ξ τ ∘ P) = classEquiv τ ∘ planeClassMap P`, and
`classEquiv τ` is a diffeomorphism of `ℝP³`).  Since the engine's `Meet3Hyp` for the design's *perturbed*
triple is produced by the Sard route (`Work.Drive.exists_meet3Hyp_sweepChartFam_of_locus`) rather than by
`ClassTripleRegular`, the `hci` obstruction previously blocked only the ends clause — and this file
shows that it does **not** block it.

The sharpened statement (this file) drops `hreg`, and along with it the two hypotheses of the original
that `EndDesign` does not carry (`hψ`, the smoothness of the cutoff, and `hck`):

> for three plane presentations `P` and cutoff/level data `ψ`, `c` of the design (with the strict
> level trichotomy `c 1 < c 0`, `c 2 < c 0` and all truncation levels below the planes' levels), the
> oddness of the **class-triple count** `#(classTripleSet P)` gives
> `Odd (Σ_k #(bottomBdryMeet_k))`.

The finiteness hypothesis of the original is dropped as well: `Odd (classTripleSet P).ncard` implies it
(`Work.Drive.odd_ncard_classTripleSet_of_hasClassLinearization`'s companion `Work.Drive.finite_of_odd_ncard`).

Consequently the ends clause of the counting route consumes *only*
`Odd (classTripleSet P).ncard` — which the linearization lane supplies from
`Work.Drive.HasClassLinearization P` (`Work.Drive.odd_ncard_classTripleSet_of_hasClassLinearization`) —
plus the design's level data.
-/

namespace Work.Drive

open Manifold
open scoped Manifold ContDiff

noncomputable section

/-- **The ends clause without `ClassTripleRegular`** (the sharpened
`Work.Drive.odd_sum_bottomBdryMeet_of_classTriple`: `hreg`, the cutoff smoothness `hψ` and the level
compatibility `hck` are dropped, and the finiteness of the class-triple set follows from the oddness of
its `ncard`). -/
theorem odd_sum_bottomBdryMeet_of_classTripleSet
    (P : Fin 3 → EuclideanSpace ℝ (Fin 2) → CappingSpace)
    (c : Fin 3 → ℝ) (ψ : ℝ → ℝ)
    (hψ0 : ψ 0 = 1) (hψ1 : ψ 1 = 0)
    (hψ01 : ∀ t ∈ Set.Icc (0 : ℝ) 1, ψ t ∈ Set.Icc (0 : ℝ) 1)
    (hcont : ContinuousOn ψ (Set.Icc (0 : ℝ) 1)) (hanti : StrictAntiOn ψ (Set.Icc (0 : ℝ) 1))
    (hcpos : ∀ k : Fin 3, 0 < c k)
    (hc1 : c 1 < c 0) (hc2 : c 2 < c 0)
    (hlev : ∀ (k : Fin 3) (y : EuclideanSpace ℝ (Fin 2)), c 0 < levelOf (P k y))
    (hodd : Odd (classTripleSet P).ncard) :
    Odd ((bottomBdryMeet CappingSpace
            (fun k => clampedSweep (c k) ψ (P k)) 0).ncard
      + (bottomBdryMeet CappingSpace
            (fun k => clampedSweep (c k) ψ (P k)) 1).ncard
      + (bottomBdryMeet CappingSpace
            (fun k => clampedSweep (c k) ψ (P k)) 2).ncard) := by
  classical
  let D : EndDesign P :=
    { c := c
      psi := ψ
      hcpos := hcpos
      hcne := by
        intro k hk
        fin_cases k
        · exact absurd rfl hk
        · exact hc1
        · exact hc2
      hlev := hlev
      hψ0 := hψ0
      hψ1 := hψ1
      hψ01 := hψ01
      hcont := hcont
      hanti := hanti }
  change Odd ((bottomBdryMeet CappingSpace D.sweep 0).ncard
    + (bottomBdryMeet CappingSpace D.sweep 1).ncard
    + (bottomBdryMeet CappingSpace D.sweep 2).ncard)
  have hlev' : ∀ (k : Fin 3) (y : EuclideanSpace ℝ (Fin 2)), D.c k ≤ levelOf (P k y) := by
    intro k y
    fin_cases k
    · exact le_of_lt (D.hlev 0 y)
    · exact le_trans (le_of_lt (D.hcne 1 fin3_one_ne_zero)) (le_of_lt (D.hlev 1 y))
    · exact le_trans (le_of_lt (D.hcne 2 fin3_two_ne_zero)) (le_of_lt (D.hlev 2 y))
  have hbot1 : bottomBdryMeet CappingSpace D.sweep 1 = ∅ :=
    bottomBdryMeet_eq_empty_of_lt_level_local D.c D.hcpos D.psi D.hψ0 D.hψ01 P hlev'
      (k := 1) (l := 0) (D.hcne 1 fin3_one_ne_zero)
  have hbot2 : bottomBdryMeet CappingSpace D.sweep 2 = ∅ :=
    bottomBdryMeet_eq_empty_of_lt_level_local D.c D.hcpos D.psi D.hψ0 D.hψ01 P hlev'
      (k := 2) (l := 0) (D.hcne 2 fin3_two_ne_zero)
  have hcard := D.ncard_bottomBdryMeet_zero_eq_ncard_classTripleSet
  rw [hbot1, hbot2, Set.ncard_empty]
  simp only [add_zero]
  rw [← hcard]
  exact hodd

/-- **The ends clause for the *perturbed* plane presentations of the counting family.**

The chains of the design's family `Work.Drive.sweepChartFam P Ξ c t` are
`clampedSweep (c k) (1 - ·) (fun z => Ξ (t k) (P k z))`, so the ends clause of the perturbed triple is
`odd_sum_bottomBdryMeet_of_classTripleSet` applied to the perturbed plane presentations.  This is the
exact `hbot` input of `Work.Drive.odd_sum_topBdryMeet_of_ends` for the design's family; note that no
`ClassTripleRegular` datum of the perturbed planes is needed. -/
theorem odd_sum_bottomBdryMeet_perturbedPlanes
    (P : Fin 3 → EuclideanSpace ℝ (Fin 2) → CappingSpace)
    (Ξ : EuclideanSpace ℝ (Fin 4) → CappingSpace → CappingSpace)
    (τ : Fin 3 → EuclideanSpace ℝ (Fin 4))
    (c : Fin 3 → ℝ)
    (hcpos : ∀ k : Fin 3, 0 < c k)
    (hc1 : c 1 < c 0) (hc2 : c 2 < c 0)
    (hlev : ∀ (k : Fin 3) (y : EuclideanSpace ℝ (Fin 2)),
      c 0 < levelOf ((fun z => Ξ (τ k) (P k z)) y))
    (hodd : Odd (classTripleSet (fun k => fun z => Ξ (τ k) (P k z))).ncard) :
    Odd ((bottomBdryMeet CappingSpace
            (fun k => clampedSweep (c k) (fun r => 1 - r)
              (fun z => Ξ (τ k) (P k z))) 0).ncard
      + (bottomBdryMeet CappingSpace
            (fun k => clampedSweep (c k) (fun r => 1 - r)
              (fun z => Ξ (τ k) (P k z))) 1).ncard
      + (bottomBdryMeet CappingSpace
            (fun k => clampedSweep (c k) (fun r => 1 - r)
              (fun z => Ξ (τ k) (P k z))) 2).ncard) := by
  refine odd_sum_bottomBdryMeet_of_classTripleSet (fun k => fun z => Ξ (τ k) (P k z)) c
    (fun r => 1 - r) ?_ ?_ ?_ ?_ ?_ hcpos hc1 hc2 hlev hodd
  · norm_num
  · norm_num
  · intro s hs
    exact ⟨by linarith [hs.2], by linarith [hs.1]⟩
  · exact (continuous_const.sub continuous_id).continuousOn
  · intro a ha b hb hab
    dsimp only
    linarith

end

end Work.Drive
