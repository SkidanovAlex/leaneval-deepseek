import Mathlib
import Submission.Work.EQ.Defs
import Submission.Work.EQ.SymDefs
import Submission.Work.EQ.normEqCurve_structure
import Submission.Work.EQ.polarPt_compact
import Submission.Work.EQ.eqT_reflections

/-!
# Invariance of the bisector mirror of a normalised equichordal curve

Write `C` for the normalised equichordal curve, the range of `θ ↦ polarPt (-(a/2)) (ρ₁ θ) θ`,
and `C‡ = (-star ·) '' C` for its mirror image in the **imaginary axis** (the bisector of the two
foci `O₁ = -a/2`, `O₂ = a/2`), i.e. the map `φ z = -conj z`.

The three facts proved here are the elementary structural inputs of the symmetry route:

* `C‡` is closed (indeed compact), being the continuous image of the compact curve `C`;
* Rychlik's map `eqT a = chordMap O₁ ∘ chordMap O₂` preserves `C‡`: the reflection `φ`
  intertwines `eqT a` with the reverse composition `H = chordMap O₂ ∘ chordMap O₁`, which
  preserves `C`, so `eqT a (φ Y) = φ (H Y) ∈ C‡`;
* if a curve point `P ∈ C` is moved by `eqT a` into `C‡`, then already `P ∈ C‡`: the reverse
  composition `H` is the inverse of `eqT a` on `C` and also preserves `C‡`, so `P` is the image
  of `eqT a P ∈ C‡` under a map preserving `C‡`.
-/

namespace Work.EQ

open Complex

theorem bis_mirror_invariance {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {ρ₁ ρ₂ : ℝ → ℝ}
    (hC : NormEqCurve a ρ₁ ρ₂) :
    IsClosed ((fun z : ℂ => -star z) '' Set.range (fun θ => polarPt (-(a/2)) (ρ₁ θ) θ)) ∧
    Set.MapsTo (eqT a)
      ((fun z : ℂ => -star z) '' Set.range (fun θ => polarPt (-(a/2)) (ρ₁ θ) θ))
      ((fun z : ℂ => -star z) '' Set.range (fun θ => polarPt (-(a/2)) (ρ₁ θ) θ)) ∧
    (∀ θ, eqT a (polarPt (-(a/2)) (ρ₁ θ) θ) ∈
        (fun z : ℂ => -star z) '' Set.range (fun θ => polarPt (-(a/2)) (ρ₁ θ) θ) →
      polarPt (-(a/2)) (ρ₁ θ) θ ∈
        (fun z : ℂ => -star z) '' Set.range (fun θ => polarPt (-(a/2)) (ρ₁ θ) θ)) := by
  obtain ⟨hcont₁, hcont₂, hpos₁, hpos₂, hchord₁, hchord₂, hrange⟩ := hC
  set S : Set ℂ := Set.range (fun θ => polarPt (-(a/2)) (ρ₁ θ) θ) with hS
  set φ : ℂ → ℂ := fun z => -star z with hφ
  have hφcont : Continuous φ := by rw [hφ]; fun_prop
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
    obtain ⟨ψ, hψ⟩ := (show X ∈ Set.range (fun θ => polarPt (a/2) (ρ₂ θ) θ) from by
      rw [← hrange]; exact hX)
    rw [← hψ, nec_chordMap_polarPt_O2 (a := a) hpos₂ hchord₂ ψ, hrange]
    exact Set.mem_range_self _
  have heqTmaps : Set.MapsTo (eqT a) S S := fun X hX => hA_maps (hB_maps hX)
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
    obtain ⟨ψ, hψ⟩ := (show P ∈ Set.range (fun θ => polarPt (a/2) (ρ₂ θ) θ) from by
      rw [← hrange]; exact hP)
    have hb1 : 0 < ‖P - O2_sym a‖ := by
      rw [← hψ, hO2val, nec_norm_polarPt_sub (hpos₂ ψ)]
      exact hpos₂ ψ
    have hb2 : ‖P - O2_sym a‖ < 1 := by
      rw [← hψ, hO2val, nec_norm_polarPt_sub (hpos₂ ψ)]
      have := hchord₂ ψ
      linarith [hpos₂ (ψ + Real.pi)]
    exact nec_chordMap_involutive hb1 hb2
  -- conjugation commutes with the one-step chord maps (the foci are real)
  have hstar1 : ∀ X : ℂ, chordMap (O1_sym a) (star X) = star (chordMap (O1_sym a) X) := by
    intro X
    have h : star (O1_sym a) = O1_sym a := by simp [O1_sym]
    simpa only [h] using chordMap_star (O1_sym a) X
  have hstar2 : ∀ X : ℂ, chordMap (O2_sym a) (star X) = star (chordMap (O2_sym a) X) := by
    intro X
    have h : star (O2_sym a) = O2_sym a := by simp [O2_sym]
    simpa only [h] using chordMap_star (O2_sym a) X
  -- central reflection anti-commutes with the one-step chord maps
  have hO2neg : O2_sym a = -(O1_sym a) := by simp [O1_sym, O2_sym]
  have hneg1 : ∀ W : ℂ, chordMap (O2_sym a) (-W) = - chordMap (O1_sym a) W := fun W => by
    rw [hO2neg]; exact chordMap_neg (O1_sym a) W
  have hneg2 : ∀ W : ℂ, chordMap (O1_sym a) (-W) = - chordMap (O2_sym a) W := fun W => by
    rw [show O1_sym a = -(O2_sym a) by rw [hO2neg]; ring]; exact chordMap_neg (O2_sym a) W
  -- the reverse composition preserves the mirror of the curve
  have hH_maps : ∀ X ∈ φ '' S, chordMap (O2_sym a) (chordMap (O1_sym a) X) ∈ φ '' S := by
    intro X hX
    obtain ⟨Y, hY, rfl⟩ := hX
    refine ⟨eqT a Y, heqTmaps hY, ?_⟩
    show -star (eqT a Y) = chordMap (O2_sym a) (chordMap (O1_sym a) (-star Y))
    rw [hneg2 (star Y), hstar2 Y, hneg1 (star (chordMap (O2_sym a) Y)),
        hstar1 (chordMap (O2_sym a) Y)]
    simp only [eqT]
  refine ⟨?_, ?_, ?_⟩
  · -- closedness: the mirror of a compact curve is compact
    exact ((polarPt_compact (a := a) hcont₁ hper₁).image hφcont).isClosed
  · -- `eqT a` intertwines `φ` with the reverse composition, which preserves `S`
    intro X hX
    obtain ⟨Y, hY, rfl⟩ := hX
    change eqT a (-star Y) ∈ φ '' S
    rw [(eqT_reflections a).2.2 Y]
    exact ⟨chordMap (O2_sym a) (chordMap (O1_sym a) Y), hB_maps (hA_maps hY), rfl⟩
  · -- a curve point moved into the mirror was already in the mirror
    intro θ hθ
    have hP : polarPt (-(a/2)) (ρ₁ θ) θ ∈ S := Set.mem_range_self θ
    have hkey : polarPt (-(a/2)) (ρ₁ θ) θ
        = chordMap (O2_sym a) (chordMap (O1_sym a) (eqT a (polarPt (-(a/2)) (ρ₁ θ) θ))) := by
      simp only [eqT]
      rw [hA_inv (chordMap (O2_sym a) (polarPt (-(a/2)) (ρ₁ θ) θ)) (hB_maps hP)]
      exact (hB_inv (polarPt (-(a/2)) (ρ₁ θ) θ) hP).symm
    rw [hkey]
    exact hH_maps _ hθ

end Work.EQ
