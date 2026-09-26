import Mathlib
import Submission.Work.BoxShrink.PinchOff.SliceConnected
import Submission.Work.BoxShrink.PinchOff.signPartition_of_finite_zeros

/-!
# The connector-free alternating-partition datum from finite crossings

`Work.BoxShrink.PinchOff.alternatingPartitionDataWeak_of_finite_crossing`: if every loop of the
box region `Ω` which meets both sides of the cutting plane crosses the slice `Σ` only finitely
often, then the two closed halves carry an `AlternatingPartitionDataWeak` — the splitting of every
loop at its crossings with the slice, with **no** connectivity hypothesis on the slice.

The content is the same one-dimensional computation as in
`alternatingPartitionData_of_finite_crossing_of_isPathConnected_slice`.  A loop `γ` of `Ω` gives a
continuous `2π`-periodic function

  `g t = (γ t) (σ 2) - (c (σ 2) + u)`,

whose sign at `t` tells on which side of the cutting plane `γ t` lies (`≥ 0` on `UpperSide`,
`≤ 0` on `LowerSide`) and whose zeros are exactly the crossings `γ t ∈ Σ`.  `hfin` says that the
zero set of `g` in a period is finite, so `signPartition_of_finite_zeros` splits the circle into
finitely many alternating monochromatic arcs; the sign conditions translate back into membership in
the two closed halves.  The connectors of the strong datum are exactly the place where path
connectedness of the slice was used, and they are simply dropped here.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.BoxShrink.PinchOff

theorem alternatingPartitionDataWeak_of_finite_crossing
    {ψ : Submission.Diffeo} {s : ℝ} {c : LeanEval.KnotTheory.PardonDistortion.R3}
    {σ : Equiv.Perm (Fin 3)} {u : ℝ}
    (hfin : Work.BoxShrink.PinchOff.FiniteCrossing ψ s c σ u) :
    Work.BoxShrink.PinchOff.AlternatingPartitionDataWeak
      (Work.BoxShrink.PinchOff.surface ψ)
      (Work.BoxShrink.PinchOff.UpperSide ψ s c σ u)
      (Work.BoxShrink.PinchOff.LowerSide ψ s c σ u) := by
  intro γ hγ
  -- the loop hypothesis is membership in `Ω = UpperSide ∪ LowerSide`
  have hγΩ : ∀ t : ℝ, γ t ∈ Omega ψ s c σ := by
    intro t; rw [Omega_eq_upperSide_union_lowerSide]; exact hγ t
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
  · exact Or.inl h1
  by_cases h2 : ∀ t : ℝ, γ t ∈ LowerSide ψ s c σ u
  · exact Or.inr (Or.inl h2)
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
    hpos | hneg | ⟨k, hk, sp, hs0, hslast, hmono, hzero, hA, hB⟩
  · exact Or.inl fun t => (hUp t).mpr (hpos t)
  · exact Or.inr (Or.inl fun t => (hLoS t).mpr (hneg t))
  · refine Or.inr (Or.inr ⟨k, hk, sp, hs0, hslast, hmono, ?_, ?_⟩)
    · intro j hj t ht1 ht2
      exact (hUp t).mpr (hA j hj t ht1 ht2)
    · intro j hj t ht1 ht2
      exact (hLoS t).mpr (hB j hj t ht1 ht2)

end Work.BoxShrink.PinchOff
