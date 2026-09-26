import Submission.Work.BoxShrink.Pinch.Regions
import Submission.Work.CoreTopology.MustBeInessential
import Submission.Work.Smooth.Morse.Defs

/-!
# The pinch in level-set form, and Pardon's equation (1)

`Regions.lean` reduces Pardon's Lemma 3 to a one-parameter family of regions with (i) Pardon's
dichotomy at every parameter before the pinch and (ii) the dimension bound of a single surgery.
This module isolates the *geometric* content of the dichotomy.

## Pardon's equation (1)

Pardon's Lemma 2.3 uses (for `F` of genus `g` and `S_t` transverse to `F` with `S_t ∩ F` a union of
curves *inessential* in `F`):

  `dim_Q im (H₁ (F ∩ int S_t ; ℚ) → H₁ (F ; ℚ)) = 2g` if `F ∩ int S_t` has a component of genus
  `g`, and `0` otherwise.

This is a statement of the classification of compact surfaces: each component of `F ∖ S_t` is
either a planar surface with holes (whose boundary curves are inessential in `F`, so all its loops
are null-homotopic there and it contributes nothing to the image) or a genus-`g` surface with
holes (whose `H₁` injects into `H₁ (F) = ℚ^{2g}`).  Mathlib has no classification of surfaces, so
this is carried as an explicit hypothesis

`Work.BoxShrink.Pinch.Equation1Input`,

for *nice* level sets (`Work.Smooth.Morse.NiceLevel`: a compact finite disjoint union of simple
closed curves of the surface — Sard plus the classification of compact `1`-manifolds).  Everything
*about* the hypothesis is proved here: how it transfers to a level family
(`PinchLevels.toPinchRegions`) and how the counting hypothesis of Pardon's paper supplies the
inessentiality that it consumes (`pardonDichotomy_region_of_count`, via Pardon's Lemma 2.5
`Work.CoreTopology.mustbeinessential`).
-/

open LeanEval.KnotTheory.PardonDistortion
open Set

namespace Work.BoxShrink.Pinch

noncomputable section

/-! ## Pardon's equation (1) -/

/-- **Pardon's equation (1), as an isolated hypothesis.**  For a *nice* level set (a compact finite
disjoint union of simple closed curves of the surface) which carries no essential loop of the
surface, the sublevel region has winding span `⊥` or `⊤`.

This is the classification of compact surfaces in the form Pardon's Lemma 2.3 consumes; it is the
surface-theory input of the pinch, exactly as `Work.Smooth.Morse.CompactOneManifoldInput` is the
input of the level-set classification. -/
def Equation1Input : Prop :=
  ∀ (ψ : Submission.Diffeo) (g : R3 → ℝ) (t : ℝ), Continuous g →
    Work.Smooth.Morse.NiceLevel ψ g t →
    ¬ (Work.Smooth.Morse.torus ψ).ContainsEssentialLoop (Work.Smooth.Morse.levelSet ψ g t) →
    Work.BoxShrink.Bubble.PardonDichotomy (Work.Smooth.Morse.torus ψ)
      (Work.Smooth.Morse.region ψ g t)

/-! ## Pardon's Lemma 2.5 (the counting hypothesis) and the dichotomy -/

/-- **Pardon's Lemma 2.5, in the form the equation (1) consumes.**  If the trace `Z ∩ F` is
swept by compressing loops meeting `β` in no more points than `Z` does, and `Z` meets `β` fewer
than `I(F,β) = pardonsI` times, then `Z` carries no essential loop.  This is exactly
`Work.CoreTopology.mustbeinessential`, restated in the loop containment form of the chapter. -/
theorem not_containsEssentialLoop_of_count {ψ : Submission.Diffeo}
    (β : Work.CoreTopology.ClosedCurve (Work.Smooth.Morse.torus ψ)) (Z : Set R3)
    (hclean : ∀ α : Work.CoreTopology.ClosedCurve (Work.Smooth.Morse.torus ψ),
      Work.CoreTopology.IsEssential (Work.Smooth.Morse.torus ψ) α →
        (∀ t : ℝ, α.γ t ∈ Z) →
          ∃ α' : Work.CoreTopology.ClosedCurve (Work.Smooth.Morse.torus ψ),
            Work.CoreTopology.IsSimple (Work.Smooth.Morse.torus ψ) α' ∧
              Work.CoreTopology.IsEssential (Work.Smooth.Morse.torus ψ) α' ∧
                Work.CoreTopology.BoundsDiskInComplement (Work.Smooth.Morse.torus ψ) α' ∧
                  (Set.range α'.γ ∩ Set.range β.γ).encard ≤
                    (Set.range α.γ ∩ Set.range β.γ).encard)
    (hZ : (Set.range β.γ ∩ Z).encard <
      Work.CoreTopology.pardonsI (Work.Smooth.Morse.torus ψ) β) :
    ¬ (Work.Smooth.Morse.torus ψ).ContainsEssentialLoop Z := by
  intro hcon
  obtain ⟨γ, hess, hγ⟩ := hcon
  exact (Work.CoreTopology.mustbeinessential (Work.Smooth.Morse.torus ψ) β Z hclean
    hZ) γ hγ hess

/-- **Pardon's equation (1) from the counting hypothesis.**  A nice level set whose trace meets
`β` fewer than `I(F,β)` times carries no essential loop (Pardon's Lemma 2.5), whence its sublevel
region satisfies the dichotomy (equation (1)). -/
theorem pardonDichotomy_region_of_count (h : Equation1Input)
    {ψ : Submission.Diffeo} {g : R3 → ℝ} {t : ℝ} (β : Work.CoreTopology.ClosedCurve
      (Work.Smooth.Morse.torus ψ))
    (hclean : ∀ α : Work.CoreTopology.ClosedCurve (Work.Smooth.Morse.torus ψ),
      Work.CoreTopology.IsEssential (Work.Smooth.Morse.torus ψ) α →
        (∀ s : ℝ, α.γ s ∈ Work.Smooth.Morse.levelSet ψ g t) →
          ∃ α' : Work.CoreTopology.ClosedCurve (Work.Smooth.Morse.torus ψ),
            Work.CoreTopology.IsSimple (Work.Smooth.Morse.torus ψ) α' ∧
              Work.CoreTopology.IsEssential (Work.Smooth.Morse.torus ψ) α' ∧
                Work.CoreTopology.BoundsDiskInComplement (Work.Smooth.Morse.torus ψ) α' ∧
                  (Set.range α'.γ ∩ Set.range β.γ).encard ≤
                    (Set.range α.γ ∩ Set.range β.γ).encard)
    (hcount : (Set.range β.γ ∩ Work.Smooth.Morse.levelSet ψ g t).encard <
      Work.CoreTopology.pardonsI (Work.Smooth.Morse.torus ψ) β)
    (hg : Continuous g) (hnice : Work.Smooth.Morse.NiceLevel ψ g t) :
    Work.BoxShrink.Bubble.PardonDichotomy (Work.Smooth.Morse.torus ψ)
      (Work.Smooth.Morse.region ψ g t) :=
  h ψ g t hg hnice (not_containsEssentialLoop_of_count β _ hclean hcount)

/-! ## The pinch in level-set form -/

/-- **Pardon's pinching family, in level-set form.**

Each region `region t` (`t < 1`) is the level-`0` sublevel region of a level function `level t`
which is continuous, whose level set is nice (a compact finite disjoint union of simple closed
curves) and carries no essential loop of the surface.  Those three facts are the entire input of
Pardon's equation (1) at the parameter `t`; the dichotomy is then *derived*
(`PinchLevels.toPinchRegions`), so the level-set form is *strictly stronger* data than
`PinchRegions` (it is the form in which Pardon's counting hypothesis produces the family at every
level: `#(S_t ∩ β) ≤ #(S ∩ β) + 2 #(D ∩ β) < I(F,β)`).

At `t = 1` the family is the union of the two half-regions; the level functions are not required
there (the pinching parameter is the double bubble, not a sphere). -/
structure PinchLevels (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3))
    (u : ℝ) : Type where
  /-- the level function at the parameter `t` -/
  level : ℝ → R3 → ℝ
  /-- the region `F ∩ int (S_t)` -/
  region : ℝ → Set R3
  /-- at time `0` the region is the one inside the boundary sphere of the box -/
  zero : region 0 = Work.BoxShrink.Core.boxRegion (Work.Smooth.Morse.torus ψ) s c σ
  /-- at time `1` the region is the union of the two half-regions -/
  one : region 1 = Work.BoxShrink.Core.upperRegion (Work.Smooth.Morse.torus ψ) s c σ u ∪
    Work.BoxShrink.Core.lowerRegion (Work.Smooth.Morse.torus ψ) s c σ u
  /-- before the pinch, the region is the level-`0` sublevel region of the level function -/
  region_eq : ∀ t < 1, region t = Work.Smooth.Morse.region ψ (level t) 0
  /-- the level set is nice (a compact finite disjoint union of simple closed curves) -/
  nice : ∀ t < 1, Work.Smooth.Morse.NiceLevel ψ (level t) 0
  /-- the level function is continuous -/
  continuous : ∀ t < 1, Continuous (level t)
  /-- the trace of the level function is inessential -/
  trace_inessential : ∀ t < 1,
    ¬ (Work.Smooth.Morse.torus ψ).ContainsEssentialLoop
      (Work.Smooth.Morse.levelSet ψ (level t) 0)
  /-- the dimension bound of a single surgery -/
  step : ∀ t : ℝ, ∃ ε : ℝ, 0 < ε ∧ ∀ r : ℝ, |r - t| < ε →
    Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan (Work.Smooth.Morse.torus ψ)
        (region r)) ≤
        Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan (Work.Smooth.Morse.torus ψ)
          (region t)) + 1 ∧
      Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan (Work.Smooth.Morse.torus ψ)
          (region t)) ≤
        Module.finrank ℚ ↥(Work.SurgeryInvariance.WindingSpan (Work.Smooth.Morse.torus ψ)
          (region r)) + 1

/-- **The level-set form gives the invariant form**: Pardon's equation (1) at each level supplies
the dichotomy, and the dimension bound is copied. -/
def PinchLevels.toPinchRegions {ψ : Submission.Diffeo} {s : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {u : ℝ} (L : PinchLevels ψ s c σ u) (h : Equation1Input) :
    PinchRegions (Work.Smooth.Morse.torus ψ) s c σ u where
  region := L.region
  zero := L.zero
  one := L.one
  dichotomy := fun t ht => by
    rw [L.region_eq t ht]
    exact h ψ (L.level t) 0 (L.continuous t ht) (L.nice t ht) (L.trace_inessential t ht)
  step := L.step

/-- **The residual input of the chapter, in level-set form.** -/
def PinchLevelsInput : Prop :=
  ∀ (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ),
    ¬ (Work.Smooth.Morse.torus ψ).ContainsEssentialLoop (Work.BoxShrink.Core.sphereSet c σ s) →
    ¬ (Work.Smooth.Morse.torus ψ).ContainsEssentialLoop
        (Work.BoxShrink.Core.sliceRegion (Work.Smooth.Morse.torus ψ) s c σ u) →
    Nonempty (PinchLevels ψ s c σ u)

/-- **Pardon's equation (1) plus the level-set family give Pardon's Lemma 3 conclusion.** -/
theorem smoothHalfS_of_pinchLevelsInput (h1 : Equation1Input) (h2 : PinchLevelsInput) :
    SmoothHalfS :=
  fun ψ s c σ u hS hZ =>
    bubbleHalf_of_pinchRegions ((h2 ψ s c σ u hS hZ).some.toPinchRegions h1)

/-- The level-set form gives the invariant input as well. -/
theorem pinchRegionsSmoothAll_of_pinchLevelsInput (h1 : Equation1Input)
    (h2 : PinchLevelsInput) : PinchRegionsSmoothAll :=
  fun ψ s c σ u hS hZ => ⟨((h2 ψ s c σ u hS hZ).some.toPinchRegions h1)⟩

end

end Work.BoxShrink.Pinch
