import Submission.Work.BoxShrink.PinchOff.SliceConnected
import Submission.Work.BoxShrink.PinchOff.signPartition_of_finite_zeros

/-!
# The sign split of a loop, for any pair of sets above the two closed halves

`Work.BoxShrink.PinchOff.alternatingPartitionDataWeak_of_finite_crossing` produces the
connector-free alternating-partition datum (`PairingData.lean`) for the two **closed halves**

  `UpperSide = Ω ∩ {y (σ 2) ≥ c (σ 2) + u}`,  `LowerSide = Ω ∩ {y (σ 2) ≤ c (σ 2) + u}`

of the pinch from the crossing finiteness of the loops (`FiniteCrossing`): the height function
`g t = (γ t) (σ 2) - (c (σ 2) + u)` splits the circle of the loop into finitely many arcs on which
`g ≥ 0` — hence which lie in `UpperSide` — alternating with arcs on which `g ≤ 0` — hence which lie
in `LowerSide` (`signPartition_of_finite_zeros`).

The only property of the halves used by that proof is the *containment*: an arc on which `g ≥ 0`
lies in `UpperSide`, and an arc on which `g ≤ 0` lies in `LowerSide`.  This module records the
generalization: the datum is available for **any** pair `A ⊇ UpperSide`, `B ⊇ LowerSide`.

That is what the pinch needs in order to be paired not against the two halves themselves but
against an **enlargement** of them — the collar pair of `CollarPair.lean`, whose intersection
(`A ∩ B`), and not the slice, is the interface whose path connectedness supplies the connectors of
the datum.  This is the point at which the finger move enters the argument: the interface can be
enlarged to a connected set exactly insofar as the crossings of the loops with the original slice
can be paired up.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.BoxShrink.PinchOff

noncomputable section

/-- **The sign split for any pair containing the two closed halves.**  If `A ⊇ UpperSide` and
`B ⊇ LowerSide` then, at a configuration whose loops cross the cutting plane finitely often, the
pair `(A, B)` carries the connector-free alternating-partition datum. -/
theorem alternatingPartitionDataWeak_of_finite_crossing_of_subset
    {ψ : Submission.Diffeo} {s : ℝ} {c : LeanEval.KnotTheory.PardonDistortion.R3}
    {σ : Equiv.Perm (Fin 3)} {u : ℝ} {A B : Set R3}
    (hA : Work.BoxShrink.PinchOff.UpperSide ψ s c σ u ⊆ A)
    (hB : Work.BoxShrink.PinchOff.LowerSide ψ s c σ u ⊆ B)
    (hO : A ∪ B ⊆ Omega ψ s c σ)
    (hfin : Work.BoxShrink.PinchOff.FiniteCrossing ψ s c σ u) :
    Work.BoxShrink.PinchOff.AlternatingPartitionDataWeak
      (Work.BoxShrink.PinchOff.surface ψ) A B := by
  intro γ hγ
  -- the loop hypothesis is membership in `Ω = UpperSide ∪ LowerSide`
  have hγΩ : ∀ t : ℝ, γ t ∈ Omega ψ s c σ := fun t => hO (hγ t)
  -- the one-dimensional height function over the cutting plane
  set g : ℝ → ℝ := fun t => (γ t) (σ 2) - (c (σ 2) + u) with hgdef
  have hgc : Continuous g := by
    rw [hgdef]
    exact ((PiLp.continuous_apply 2 (fun _ : Fin 3 => ℝ) (σ 2)).comp γ.cont).sub
      continuous_const
  have hgp : ∀ t : ℝ, g (t + 2 * Real.pi) = g t := by
    intro t; simp only [hgdef]; rw [γ.periodic]
  -- the dictionary between the sign of `g` and the three pieces of the configuration
  have hSig : ∀ t : ℝ, γ t ∈ Sigma ψ s c σ u ↔ g t = 0 := by
    intro t
    rw [hgdef, Sigma, Work.BoxShrink.Core.mem_sliceRegion]
    constructor
    · rintro ⟨-, -, h⟩; simp only; linarith
    · intro h
      exact ⟨(Work.BoxShrink.Core.mem_boxRegion.mp (hγΩ t)).1,
        (Work.BoxShrink.Core.mem_boxRegion.mp (hγΩ t)).2, by linarith⟩
  have hUp : ∀ t : ℝ, γ t ∈ UpperSide ψ s c σ u ↔ 0 ≤ g t := by
    intro t
    rw [hgdef, UpperSide, Set.mem_inter_iff, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨-, h⟩; simp only; linarith
    · intro h; exact ⟨hγΩ t, by simp only; linarith⟩
  have hLoS : ∀ t : ℝ, γ t ∈ LowerSide ψ s c σ u ↔ g t ≤ 0 := by
    intro t
    rw [hgdef, LowerSide, Set.mem_inter_iff, Set.mem_ofPred_eq]
    constructor
    · rintro ⟨-, h⟩; simp only; linarith
    · intro h; exact ⟨hγΩ t, by simp only; linarith⟩
  by_cases h1 : ∀ t : ℝ, γ t ∈ UpperSide ψ s c σ u
  · exact Or.inl fun t => hA (h1 t)
  by_cases h2 : ∀ t : ℝ, γ t ∈ LowerSide ψ s c σ u
  · exact Or.inr (Or.inl fun t => hB (h2 t))
  push Not at h1 h2
  -- finiteness of the crossings, from `hfin` through the dictionary
  have hfinZ : {t : ℝ | t ∈ Set.Icc 0 (2 * Real.pi) ∧ g t = 0}.Finite := by
    have hset : {t : ℝ | t ∈ Set.Icc 0 (2 * Real.pi) ∧ g t = 0}
        = {t : ℝ | t ∈ Set.Icc 0 (2 * Real.pi) ∧ γ t ∈ Sigma ψ s c σ u} := by
      ext t
      simp only [Set.mem_ofPred_eq]
      constructor
      · rintro ⟨ht, h0⟩; exact ⟨ht, (hSig t).mpr h0⟩
      · rintro ⟨ht, hσ⟩; exact ⟨ht, (hSig t).mp hσ⟩
    rw [hset]
    exact hfin γ hγΩ h1 h2
  rcases signPartition_of_finite_zeros g hgc hgp hfinZ with
    hpos | hneg | ⟨k, hk, sp, hs0, hslast, hmono, hzero, hArcA, hArcB⟩
  · exact Or.inl fun t => hA ((hUp t).mpr (hpos t))
  · exact Or.inr (Or.inl fun t => hB ((hLoS t).mpr (hneg t)))
  · refine Or.inr (Or.inr ⟨k, hk, sp, hs0, hslast, hmono, ?_, ?_⟩)
    · intro j hj t ht1 ht2
      exact hA ((hUp t).mpr (hArcA j hj t ht1 ht2))
    · intro j hj t ht1 ht2
      exact hB ((hLoS t).mpr (hArcB j hj t ht1 ht2))

end

end Work.BoxShrink.PinchOff
