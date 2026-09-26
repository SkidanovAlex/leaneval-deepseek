import Mathlib
import Submission.Work.BoxShrink.PinchOff.Basic
import Submission.Work.BoxShrink.PinchOff.windingSpan_bot_or_top_of_inessential_boundary

namespace Work.BoxShrink.PinchOff

open LeanEval.KnotTheory.PardonDistortion
open Set

noncomputable section

/-- The box `PBox s c σ = {boxNorm c σ < s}` is open. -/
theorem isOpen_PBox' (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) :
    IsOpen (Submission.PBox s c σ) := by
  have h : Submission.PBox s c σ = {y : R3 | Submission.boxNorm c σ y < s} := by
    ext y; exact Submission.mem_PBox_iff s c σ y
  rw [h]
  exact isOpen_lt (Work.Topology.SphereSlicing.boxNorm_continuous c σ) continuous_const

/-- The region of the surface strictly outside the box: `F ∩ {boxNorm > s}`. -/
def Outer (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) : Set R3 :=
  (surface ψ).carrier ∩ {y : R3 | s < Submission.boxNorm c σ y}

@[simp] theorem mem_Outer {ψ : Submission.Diffeo} {s : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)}
    {y : R3} : y ∈ Outer ψ s c σ ↔ y ∈ (surface ψ).carrier ∧ s < Submission.boxNorm c σ y :=
  Iff.rfl

/-- `Ω = F ∩ {boxNorm < s}` is open in the carrier. -/
theorem isOpenInCarrier_Omega (ψ : Submission.Diffeo) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) :
    Work.SurgeryInvariance.IsOpenInCarrier (surface ψ) (Omega ψ s c σ) := by
  have hbox : Omega ψ s c σ = (surface ψ).carrier ∩ Submission.PBox s c σ := rfl
  rw [hbox]
  exact Work.SurgeryInvariance.isOpenInCarrier_carrier_inter (isOpen_PBox' s c σ)

/-- The outer region `F ∩ {boxNorm > s}` is open in the carrier. -/
theorem isOpenInCarrier_Outer (ψ : Submission.Diffeo) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) :
    Work.SurgeryInvariance.IsOpenInCarrier (surface ψ) (Outer ψ s c σ) := by
  refine Work.SurgeryInvariance.isOpenInCarrier_carrier_inter ?_
  exact isOpen_lt continuous_const (Work.Topology.SphereSlicing.boxNorm_continuous c σ)

/-- `Ω` and the outer region are disjoint. -/
theorem disjoint_Omega_Outer (ψ : Submission.Diffeo) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) : Disjoint (Omega ψ s c σ) (Outer ψ s c σ) := by
  rw [Set.disjoint_left]
  rintro y hy hy'
  rw [Omega, Work.BoxShrink.Core.mem_boxRegion, Submission.mem_PBox_iff] at hy
  rw [mem_Outer] at hy'
  exact absurd hy.2 (not_lt.mpr hy'.2.le)

/-- The complement of the level set in the surface is `Ω ∪ Outer`. -/
theorem carrier_sdiff_levelSet (ψ : Submission.Diffeo) (s : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) :
    (surface ψ).carrier \ Work.Smooth.Morse.levelSet ψ (fun y => Submission.boxNorm c σ y) s
      = Omega ψ s c σ ∪ Outer ψ s c σ := by
  ext y
  rw [Set.mem_sdiff, Work.Smooth.Morse.mem_levelSet, Set.mem_union, mem_Outer, Omega,
    Work.BoxShrink.Core.mem_boxRegion, Submission.mem_PBox_iff]
  constructor
  · rintro ⟨hyc, hyne⟩
    have hneq : Submission.boxNorm c σ y ≠ s := fun h => hyne ⟨hyc, h⟩
    rcases lt_or_gt_of_ne hneq with h | h
    · exact Or.inl ⟨hyc, h⟩
    · exact Or.inr ⟨hyc, h⟩
  · rintro (⟨hyc, hyp⟩ | ⟨hyc, h⟩)
    · exact ⟨hyc, fun hc => absurd hc.2 (ne_of_lt hyp)⟩
    · exact ⟨hyc, fun hc => absurd hc.2 (ne_of_gt h)⟩

/-- **The rank of the box region at a nice level is `0` or `2`.**

At a nice level `s` of the box norm whose trace `F ∩ ∂PBox s c σ` carries no essential loop, the
winding span of `Ω = F ∩ PBox s c σ` is `⊥` or `⊤`, hence its `ℚ`-rank is `0` or `2`. -/
theorem niceLevel_boxRegion_rank_zero_or_two (ψ : Submission.Diffeo) (s : ℝ)
    (c : LeanEval.KnotTheory.PardonDistortion.R3) (σ : Equiv.Perm (Fin 3))
    (hnice : Work.Smooth.Morse.NiceLevel ψ (fun y => Submission.boxNorm c σ y) s)
    (hS : ¬ (Work.BoxShrink.PinchOff.surface ψ).ContainsEssentialLoop
      (Work.BoxShrink.PinchOff.SphereTrace s c σ)) :
    Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan (Work.BoxShrink.PinchOff.surface ψ)
        (Work.BoxShrink.PinchOff.Omega ψ s c σ)) = 0 ∨
      Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan (Work.BoxShrink.PinchOff.surface ψ)
        (Work.BoxShrink.PinchOff.Omega ψ s c σ)) = 2 := by
  obtain ⟨n, γ, hsimple, hdisj, hZeq⟩ := hnice.circleUnion
  -- each circle of the level set is inessential, since `hS` forbids an essential loop on the trace
  have hlevelSub : Work.Smooth.Morse.levelSet ψ (fun y => Submission.boxNorm c σ y) s
      ⊆ SphereTrace s c σ := by
    intro y hy
    rw [Work.Smooth.Morse.mem_levelSet] at hy
    rw [SphereTrace, Work.BoxShrink.Core.mem_sphereSet]
    exact hy.2
  have hess : ∀ i, ¬ Work.CoreTopology.IsEssential (surface ψ) (γ i) := by
    intro i hi
    refine hS ((surface ψ).containsEssentialLoop_mono hlevelSub ?_)
    exact ⟨γ i, hi, fun t => by rw [hZeq]; exact Set.mem_iUnion.mpr ⟨i, Set.mem_range_self t⟩⟩
  -- the complement of the level set is the disjoint union of the box region and the outer region
  have hcover : (surface ψ).carrier \ (⋃ i, Set.range (γ i).γ)
      = Omega ψ s c σ ∪ Outer ψ s c σ := by
    rw [← carrier_sdiff_levelSet ψ s c σ, hZeq]
  have hdich := windingSpan_bot_or_top_of_inessential_boundary (P := surface ψ)
    hsimple hess hdisj (isOpenInCarrier_Omega ψ s c σ) (isOpenInCarrier_Outer ψ s c σ)
    (disjoint_Omega_Outer ψ s c σ) hcover
  exact Work.BoxShrink.Pinch.finrank_eq_zero_or_two_of_pardonDichotomy hdich

end

end Work.BoxShrink.PinchOff
