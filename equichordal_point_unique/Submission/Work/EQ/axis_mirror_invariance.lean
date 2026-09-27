import Mathlib
import Submission.Work.EQ.Defs
import Submission.Work.EQ.SymDefs
import Submission.Work.EQ.normEqCurve_structure
import Submission.Work.EQ.polarPt_compact
import Submission.Work.EQ.eqT_reflections

/-!
# Invariance of the axis mirror of a normalised equichordal curve

Write `C` for the normalised equichordal curve, the range of `θ ↦ polarPt (-(a/2)) (ρ₁ θ) θ`,
and `C* = star '' C` for its mirror image in the real axis (complex conjugation).

The three facts proved here are the elementary structural inputs of the symmetry route:

* `C*` is compact (hence closed), being the continuous image of the compact curve `C`;
* Rychlik's map `eqT a = chordMap O₁ ∘ chordMap O₂` preserves `C*` (it commutes with
  conjugation, and preserves `C`);
* if a curve point `P ∈ C` is moved by `eqT a` into `C*`, then already `P ∈ C*`.  Indeed the
  reverse composition `chordMap O₂ ∘ chordMap O₁` is the inverse of `eqT a` on `C` and also
  preserves `C*`, so `P` is the image of `eqT a P ∈ C*` under a map preserving `C*`.
-/

namespace Work.EQ

open Complex

theorem axis_mirror_invariance {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {ρ₁ ρ₂ : ℝ → ℝ}
    (hC : NormEqCurve a ρ₁ ρ₂) :
    IsClosed (star '' Set.range (fun θ => polarPt (-(a/2)) (ρ₁ θ) θ)) ∧
    Set.MapsTo (eqT a) (star '' Set.range (fun θ => polarPt (-(a/2)) (ρ₁ θ) θ))
      (star '' Set.range (fun θ => polarPt (-(a/2)) (ρ₁ θ) θ)) ∧
    (∀ θ, eqT a (polarPt (-(a/2)) (ρ₁ θ) θ) ∈
        star '' Set.range (fun θ => polarPt (-(a/2)) (ρ₁ θ) θ) →
      polarPt (-(a/2)) (ρ₁ θ) θ ∈
        star '' Set.range (fun θ => polarPt (-(a/2)) (ρ₁ θ) θ)) := by
  obtain ⟨hcont₁, hcont₂, hpos₁, hpos₂, hchord₁, hchord₂, hrange⟩ := hC
  set S : Set ℂ := Set.range (fun θ => polarPt (-(a/2)) (ρ₁ θ) θ) with hS
  -- `ρ₁` is `2π`-periodic, by the chord identity
  have hper₁ : ∀ θ, ρ₁ (θ + 2 * Real.pi) = ρ₁ θ := by
    intro θ
    have h1 := hchord₁ θ
    have h2 := hchord₁ (θ + Real.pi)
    have harg : θ + Real.pi + Real.pi = θ + 2 * Real.pi := by ring
    rw [harg] at h2
    linarith
  -- the one-step chord maps preserve the curve
  have hA_maps : Set.MapsTo (chordMap (O1_sym a)) S S := by
    intro X hX
    obtain ⟨θ, rfl⟩ := hX
    rw [nec_chordMap_polarPt_O1 (a := a) hpos₁ hchord₁ θ]
    exact Set.mem_range_self _
  have hB_maps : Set.MapsTo (chordMap (O2_sym a)) S S := by
    intro X hX
    obtain ⟨φ, hφ⟩ := (show X ∈ Set.range (fun θ => polarPt (a/2) (ρ₂ θ) θ) from by
      rw [← hrange]; exact hX)
    rw [← hφ, nec_chordMap_polarPt_O2 (a := a) hpos₂ hchord₂ φ, hrange]
    exact Set.mem_range_self _
  have heqTmaps : Set.MapsTo (eqT a) S S := by
    intro X hX
    exact hA_maps (hB_maps hX)
  -- conjugation commutes with the one-step chord maps (the foci are real)
  have hstar1 : ∀ X : ℂ, chordMap (O1_sym a) (star X) = star (chordMap (O1_sym a) X) := by
    intro X
    have h : star (O1_sym a) = O1_sym a := by simp [O1_sym]
    simpa only [h] using chordMap_star (O1_sym a) X
  have hstar2 : ∀ X : ℂ, chordMap (O2_sym a) (star X) = star (chordMap (O2_sym a) X) := by
    intro X
    have h : star (O2_sym a) = O2_sym a := by simp [O2_sym]
    simpa only [h] using chordMap_star (O2_sym a) X
  -- the reverse composition preserves the mirror of the curve
  have hH_maps : ∀ X ∈ star '' S,
      chordMap (O2_sym a) (chordMap (O1_sym a) X) ∈ star '' S := by
    intro X hX
    obtain ⟨Y, hY, rfl⟩ := hX
    rw [hstar1 Y, hstar2 (chordMap (O1_sym a) Y)]
    exact ⟨chordMap (O2_sym a) (chordMap (O1_sym a) Y), hB_maps (hA_maps hY), rfl⟩
  have hO1val : O1_sym a = ((-(a/2) : ℝ) : ℂ) := by simp only [O1_sym]; push_cast; ring
  have hO2val : O2_sym a = (((a/2) : ℝ) : ℂ) := by rw [O2_sym]
  -- each one-step map is an involution on the curve
  have hA_inv : ∀ P ∈ S, chordMap (O1_sym a) (chordMap (O1_sym a) P) = P := by
    intro P hP
    obtain ⟨θ, rfl⟩ := hP
    have hb1 : 0 < ‖polarPt (-(a/2)) (ρ₁ θ) θ - O1_sym a‖ := by
      rw [hO1val, nec_norm_polarPt_sub (hpos₁ θ)]
      exact hpos₁ θ
    have hb2 : ‖polarPt (-(a/2)) (ρ₁ θ) θ - O1_sym a‖ < 1 := by
      rw [hO1val, nec_norm_polarPt_sub (hpos₁ θ)]
      have := hchord₁ θ
      linarith [hpos₁ (θ + Real.pi)]
    exact nec_chordMap_involutive hb1 hb2
  have hB_inv : ∀ P ∈ S, chordMap (O2_sym a) (chordMap (O2_sym a) P) = P := by
    intro P hP
    obtain ⟨φ, hφ⟩ := (show P ∈ Set.range (fun θ => polarPt (a/2) (ρ₂ θ) θ) from by
      rw [← hrange]; exact hP)
    have hb1 : 0 < ‖P - O2_sym a‖ := by
      rw [← hφ, hO2val, nec_norm_polarPt_sub (hpos₂ φ)]
      exact hpos₂ φ
    have hb2 : ‖P - O2_sym a‖ < 1 := by
      rw [← hφ, hO2val, nec_norm_polarPt_sub (hpos₂ φ)]
      have := hchord₂ φ
      linarith [hpos₂ (φ + Real.pi)]
    exact nec_chordMap_involutive hb1 hb2
  refine ⟨?_, ?_, ?_⟩
  · -- closedness: the mirror of a compact curve is compact
    exact ((polarPt_compact (a := a) hcont₁ hper₁).image continuous_star).isClosed
  · -- `eqT a` commutes with conjugation and preserves `C`
    intro X hX
    obtain ⟨Y, hY, rfl⟩ := hX
    rw [(eqT_reflections a).1 Y]
    exact ⟨eqT a Y, heqTmaps hY, rfl⟩
  · -- a curve point moved into the mirror was already in the mirror
    intro θ hθ
    have hP : polarPt (-(a/2)) (ρ₁ θ) θ ∈ S := Set.mem_range_self θ
    have hkey : polarPt (-(a/2)) (ρ₁ θ) θ
        = chordMap (O2_sym a) (chordMap (O1_sym a) (eqT a (polarPt (-(a/2)) (ρ₁ θ) θ))) := by
      rw [eqT]
      rw [hA_inv (chordMap (O2_sym a) (polarPt (-(a/2)) (ρ₁ θ) θ)) (hB_maps hP)]
      exact (hB_inv _ hP).symm
    rw [hkey]
    exact hH_maps _ hθ

end Work.EQ
