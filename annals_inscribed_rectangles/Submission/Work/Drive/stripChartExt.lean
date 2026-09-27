import Mathlib
import Submission.Work.Drive.stripChartSmooth
import Submission.Work.Drive.contMDiffAt_confPiece_mk

/-!
# The configuration strip chart with a prescribed smooth unit direction

`Work.Drive.stripChart` (`stripChartSmooth.lean`) presents the configuration strip of `γ` in the
capping space, but only *off the diagonal*: there the `S¹`-coordinate (the doubled chord direction) has
the smooth square root `chordUnitDir γ`, which is the undoubled chord direction.

This file factors out the construction so that an **arbitrary smooth unit complex direction** `Z` can
be used instead.  The chart

> `Work.Drive.stripChartExt γ hγne Z hZ p = ⟦inl (stripR γ p, stripD γ p, circOf (Z p))⟧`

is the configuration point of the chord with parameters `p` whose *doubled* direction is
`circleOf (Z p)`, and it is `C^∞` (for the transparent structure `Work.Drive.cappingCharted`) as soon
as `Z` is smooth (and has unit modulus everywhere).  In particular

* `Z := chordUnitDir γ` recovers (off the diagonal) the strip chart of `stripChartSmooth.lean`;
* `Z :=` a smooth extension of `(chordUnitDir γ)²` across the diagonal (the delegated
  `Work.Drive.exists_contMDiffAt_chordDir_sq`) gives a smooth chart of the *closed* strip, i.e. of the
  configuration Möbius band together with its boundary — what a smooth presentation of the capped
  plane needs along the gluing curve.

Everything is proved from `Work.Drive.contMDiffAt_confPiece_mk` (the coordinate-level smoothness of
the configuration piece) and the explicit formulas `stripData_fst`, `stripData_snd` of
`stripChartSmooth.lean`.
-/

namespace Work.Drive

open Manifold
open scoped Manifold ContDiff Topology
open Classical
open Submission.Configuration Submission.Geometry Submission.Collision

noncomputable section

variable {γ : Circle → ℝ × ℝ}

/-- The capping radius of the chord is positive off the axis, for every parameter (in particular on
the diagonal), as soon as the curve avoids the origin. -/
lemma stripR_pos (hγne : ∀ x : Circle, γ x ≠ 0) (p : EuclideanSpace ℝ (Fin 2)) :
    0 < stripR γ p := by
  have h : 0 < (stripData γ p).1 := stripData_pos hγne p
  rwa [stripData_fst] at h

/-- Consequently the squared capping radius does not vanish. -/
lemma stripA_ne_zero (hγne : ∀ x : Circle, γ x ≠ 0) (p : EuclideanSpace ℝ (Fin 2)) :
    stripA γ p ≠ 0 := by
  intro h
  have hpos : 0 < stripR γ p := stripR_pos hγne p
  rw [stripR, h, Real.sqrt_zero] at hpos
  exact lt_irrefl 0 hpos

/-- The disk coordinate of the configuration point lies in the closed unit disk. -/
lemma stripD_le_one (γ : Circle → ℝ × ℝ) (p : EuclideanSpace ℝ (Fin 2)) :
    ‖stripD γ p‖ ≤ 1 := by
  rw [← stripData_snd γ p]
  exact confOf_snd_norm_le_one _

/-- **The configuration strip chart with a prescribed smooth unit direction.**  At the parameter `p`
this is the class in `CappingSpace` of the configuration point whose capping coordinates are
`(stripR γ p, stripD γ p)` and whose doubled chord direction is `circleOf (Z p)`. -/
def stripChartExt (γ : Circle → ℝ × ℝ) (hγne : ∀ x : Circle, γ x ≠ 0) (Z : EuclideanSpace ℝ (Fin 2) → ℂ)
    (hZ : ∀ p, ‖Z p‖ = 1) (p : EuclideanSpace ℝ (Fin 2)) : CappingSpace :=
  Quotient.mk'' (Sum.inl (⟨(stripR γ p, stripD γ p, circOf (Z p) (hZ p)),
    stripR_pos hγne p, stripD_le_one γ p⟩ : ConfigPiece))

/-- **Smoothness of the strip chart with a prescribed smooth unit direction.** -/
theorem contMDiffAt_stripChartExt
    (hγ : IsSmoothEmbedding (𝓡 1) 𝓘(ℝ, ℝ × ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) γ)
    (hγne : ∀ x : Circle, γ x ≠ 0)
    (p₀ : EuclideanSpace ℝ (Fin 2)) {Z : EuclideanSpace ℝ (Fin 2) → ℂ}
    (hZs : ContMDiffAt (𝓡 2) 𝓘(ℝ, ℂ) ((⊤ : ℕ∞) : WithTop ℕ∞) Z p₀)
    (hZ : ∀ p, ‖Z p‖ = 1) :
    letI := cappingCharted
    ContMDiffAt (𝓡 2) (𝓡 4) ((⊤ : ℕ∞) : WithTop ℕ∞) (stripChartExt γ hγne Z hZ) p₀ := by
  letI := cappingCharted
  have hA : stripA γ p₀ ≠ 0 := stripA_ne_zero hγne p₀
  -- the three coordinates, in the shape required by `contMDiffAt_confPiece_mk`
  set g : EuclideanSpace ℝ (Fin 2) → ℝ × ℂ × UnitAddCircle :=
    fun p => (stripR γ p, stripD γ p, circOf (Z p) (hZ p)) with hg
  have hg1 : ContMDiffAt (𝓡 2) 𝓘(ℝ, ℝ) ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p => (g p).1) p₀ := by
    have h := contMDiffAt_stripData_fst hγ hA
    refine h.congr_of_eventuallyEq (Filter.EventuallyEq.of_eq (funext (fun p => ?_)))
    simp only [hg]
    exact (stripData_fst γ p).symm
  have hg2 : ContMDiffAt (𝓡 2) 𝓘(ℝ, ℂ) ((⊤ : ℕ∞) : WithTop ℕ∞) (fun p => (g p).2.1) p₀ := by
    have h := contMDiffAt_stripData_snd hγ hA
    refine h.congr_of_eventuallyEq (Filter.EventuallyEq.of_eq (funext (fun p => ?_)))
    simp only [hg]
    exact (stripData_snd γ p).symm
  have hg3 : ContMDiffAt (𝓡 2) 𝓘(ℝ, ℂ) ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p => circleOf ((g p).2.2)) p₀ := by
    refine hZs.congr_of_eventuallyEq (Filter.EventuallyEq.of_eq (funext (fun p => ?_)))
    simp only [hg, circleOf_circOf]
  have hmain := contMDiffAt_confPiece_mk g p₀ hg1 hg2 hg3
    (fun p => stripR_pos hγne p) (fun p => stripD_le_one γ p)
  refine hmain.congr_of_eventuallyEq (Filter.EventuallyEq.of_eq (funext (fun p => ?_)))
  rfl

end

end Work.Drive
