import Submission.Work.BoxShrink.PinchOff.Laminar

/-!
# A case of Pardon's equation (1): an empty level set

Pardon's equation (1) (the classification of compact surfaces in the form his Lemma 2.3 consumes)
is carried by the parent chapter as `Work.BoxShrink.Pinch.Equation1Input`:

> a *nice* level set of a continuous function on the smooth torus of the challenge which carries no
> essential loop has sublevel region of winding span `⊥` or `⊤`.

This module proves the *degenerate case* in which the level set is empty: then the sublevel region is
either empty or the whole surface (the surface is connected, and `g` cannot change sign without
attaining the value `t`), so its winding span is `⊥` or `⊤`.  The instance is unconditional (an empty
level set is nice and carries no essential loop), and it is recorded because the two classical inputs
the deliverable permits -- `Equation1Input` and `BoxSliceNice` -- are stated as universally
quantified `Prop`s, so every *case* of them which is proved shrinks the carried input.
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.BoxShrink.PinchOff

noncomputable section

variable {ψ : Submission.Diffeo} {g : R3 → ℝ} {t : ℝ}

/-- **The surface of the challenge is connected**: it is the image of the (connected) parameter
plane under the continuous parametrisation. -/
theorem isPreconnected_carrier (ψ : Submission.Diffeo) :
    IsPreconnected (surface ψ).carrier := by
  rw [Work.Smooth.Morse.torus_carrier]
  exact isPreconnected_range (Work.Smooth.Morse.param_continuous ψ)

/-- `PreconnectedSpace` form of `isPreconnected_carrier`, for the connectedness arguments on the
subtype. -/
theorem preconnectedSpace_carrier (ψ : Submission.Diffeo) :
    PreconnectedSpace (surface ψ).carrier :=
  isPreconnected_iff_preconnectedSpace.mp (isPreconnected_carrier ψ)

/-- **If `g` misses the value `t` on the surface, then the sublevel region is either empty or the
whole surface.** -/
theorem region_eq_empty_or_carrier (hg : Continuous g)
    (h : Work.Smooth.Morse.levelSet ψ g t = ∅) :
    Work.Smooth.Morse.region ψ g t = ∅ ∨
      Work.Smooth.Morse.region ψ g t = (surface ψ).carrier := by
  haveI := preconnectedSpace_carrier ψ
  set A : Set (surface ψ).carrier := {p | g p.1 < t} with hA
  set B : Set (surface ψ).carrier := {p | t < g p.1} with hB
  have hAopen : IsOpen A := isOpen_lt (hg.comp continuous_subtype_val) continuous_const
  have hBopen : IsOpen B := isOpen_lt continuous_const (hg.comp continuous_subtype_val)
  have hdisj : Disjoint A B := by
    rw [Set.disjoint_left]
    intro p hpA hpB
    simp only [hA, Set.mem_ofPred_eq] at hpA
    simp only [hB, Set.mem_ofPred_eq] at hpB
    exact absurd hpA (not_lt.mpr hpB.le)
  have hcover : (Set.univ : Set (surface ψ).carrier) ⊆ A ∪ B := by
    intro p _
    have hne : g p.1 ≠ t := by
      intro hgt
      have : p.1 ∈ Work.Smooth.Morse.levelSet ψ g t := ⟨p.2, hgt⟩
      rw [h] at this
      exact this
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact Or.inl hlt
    · exact Or.inr hgt
  rcases IsPreconnected.subset_or_subset hAopen hBopen hdisj hcover
    (isPreconnected_univ : IsPreconnected (Set.univ : Set (surface ψ).carrier)) with hAc | hBc
  · -- `A` is everything: the region is the carrier
    right
    ext x
    constructor
    · rintro ⟨hx, -⟩; exact hx
    · intro hx
      refine ⟨hx, ?_⟩
      have hmem := hAc (Set.mem_univ (⟨x, hx⟩ : (surface ψ).carrier))
      simp only [hA, Set.mem_ofPred_eq] at hmem
      exact hmem
  · -- `B` is everything: the region is empty
    left
    ext x
    constructor
    · rintro ⟨hx, hlt⟩
      have hmem := hBc (Set.mem_univ (⟨x, hx⟩ : (surface ψ).carrier))
      simp only [hB, Set.mem_ofPred_eq] at hmem
      exact absurd hmem (not_lt.mpr hlt.le)
    · intro hx; exact absurd hx (Set.notMem_empty x)

/-- **An empty level set satisfies Pardon's equation (1)**: the sublevel region has winding span
`⊥` or `⊤`. -/
theorem pardonDichotomy_region_of_empty_levelSet (hg : Continuous g)
    (h : Work.Smooth.Morse.levelSet ψ g t = ∅) :
    Work.BoxShrink.Bubble.PardonDichotomy (surface ψ) (Work.Smooth.Morse.region ψ g t) := by
  rcases region_eq_empty_or_carrier (ψ := ψ) hg h with hempty | hcarrier
  · left
    rw [hempty]
    exact Work.BoxShrink.Pinch.windingSpan_empty (surface ψ)
  · right
    rw [hcarrier]
    exact Work.SurgeryInvariance.WindingSpan.carrier_eq_top (surface ψ)

end

end Work.BoxShrink.PinchOff
