import Mathlib
import Submission.Work.EQ.normEqCurve_structure

/-!
# Sign of the imaginary part of `eqT a` on a normalised equichordal curve

`eqT a = chordMap (O1_sym a) ∘ chordMap (O2_sym a)` is the composite of the two chord involutions about
the real foci `O₂ = a/2`, `O₁ = -a/2`.  On a point `P` at distance `0 < ‖P - c‖ < 1` from a real
centre `c`, the chord involution acts by `chordMap c P = c + (1 - 1/‖P-c‖)(P - c)`, so it is a
homothety of negative ratio `1 - 1/‖P-c‖ < 0`:

  `(chordMap c P).im = (1 - 1/‖P-c‖) * P.im`.

Consequently applying it twice preserves the sign of the imaginary part.  For a normalised
equichordal curve, every point of the curve is at distance in `(0,1)` from *both* foci, and so is
its image under one chord map (the curve is invariant under `chordMap (O2_sym a)`).  Hence `eqT a`
preserves the sign of the imaginary part on the curve; since `(polarPt (-(a/2)) (ρ₁ θ) θ).im =
ρ₁ θ * sin θ` and `ρ₁ > 0`, the sign of the imaginary part of the image is the sign of `sin θ`.
-/

namespace Work.EQ

open Complex

/-- The imaginary part of `eqT a P` as a product of the two negative homothety ratios. -/
lemma eqT_im_eq (a : ℝ) (P : ℂ) :
    (eqT a P).im =
      (1 - 1/‖chordMap (O2_sym a) P - O1_sym a‖) * ((1 - 1/‖P - O2_sym a‖) * P.im) := by
  have h1 : ∀ Q : ℂ, (chordMap (O1_sym a) Q).im = (1 - 1/‖Q - O1_sym a‖) * Q.im :=
    fun Q => nec_im_chordMap (c := O1_sym a) (by rw [O1_sym]; simp) Q
  have h2 : ∀ Q : ℂ, (chordMap (O2_sym a) Q).im = (1 - 1/‖Q - O2_sym a‖) * Q.im :=
    fun Q => nec_im_chordMap (c := O2_sym a) (by rw [O2_sym]; simp) Q
  rw [eqT, h1, h2]

/-- Two consecutive chord involutions about real centres, with the intermediate points at
distance in `(0,1)`, send a point of the open upper half plane into the open upper half plane. -/
lemma eqT_im_pos_of {a : ℝ} {P : ℂ}
    (hP1 : 0 < ‖P - O2_sym a‖) (hP2 : ‖P - O2_sym a‖ < 1)
    (hQ1 : 0 < ‖chordMap (O2_sym a) P - O1_sym a‖) (hQ2 : ‖chordMap (O2_sym a) P - O1_sym a‖ < 1)
    (hPim : 0 < P.im) : 0 < (eqT a P).im := by
  have hu : 1 - 1/‖chordMap (O2_sym a) P - O1_sym a‖ < 0 := by
    have := one_lt_one_div hQ1 hQ2; linarith
  have hv : 1 - 1/‖P - O2_sym a‖ < 0 := by
    have := one_lt_one_div hP1 hP2; linarith
  have huv : 0 < (1 - 1/‖chordMap (O2_sym a) P - O1_sym a‖) * (1 - 1/‖P - O2_sym a‖) :=
    mul_pos_of_neg_of_neg hu hv
  have hkey : (1 - 1/‖chordMap (O2_sym a) P - O1_sym a‖) * ((1 - 1/‖P - O2_sym a‖) * P.im)
      = ((1 - 1/‖chordMap (O2_sym a) P - O1_sym a‖) * (1 - 1/‖P - O2_sym a‖)) * P.im := by ring
  rw [eqT_im_eq, hkey]
  exact mul_pos huv hPim

/-- The companion of `eqT_im_pos_of`: a point of the open lower half plane is sent into the open
lower half plane. -/
lemma eqT_im_neg_of {a : ℝ} {P : ℂ}
    (hP1 : 0 < ‖P - O2_sym a‖) (hP2 : ‖P - O2_sym a‖ < 1)
    (hQ1 : 0 < ‖chordMap (O2_sym a) P - O1_sym a‖) (hQ2 : ‖chordMap (O2_sym a) P - O1_sym a‖ < 1)
    (hPim : P.im < 0) : (eqT a P).im < 0 := by
  have hu : 1 - 1/‖chordMap (O2_sym a) P - O1_sym a‖ < 0 := by
    have := one_lt_one_div hQ1 hQ2; linarith
  have hv : 1 - 1/‖P - O2_sym a‖ < 0 := by
    have := one_lt_one_div hP1 hP2; linarith
  have huv : 0 < (1 - 1/‖chordMap (O2_sym a) P - O1_sym a‖) * (1 - 1/‖P - O2_sym a‖) :=
    mul_pos_of_neg_of_neg hu hv
  have hkey : (1 - 1/‖chordMap (O2_sym a) P - O1_sym a‖) * ((1 - 1/‖P - O2_sym a‖) * P.im)
      = ((1 - 1/‖chordMap (O2_sym a) P - O1_sym a‖) * (1 - 1/‖P - O2_sym a‖)) * P.im := by ring
  rw [eqT_im_eq, hkey]
  exact mul_neg_of_pos_of_neg huv hPim

/-- Every point of the curve is at distance in `(0,1)` from `O₂`, and its image under the chord
map about `O₂` is at distance in `(0,1)` from `O₁`. -/
lemma eqT_arc_bounds {a : ℝ} {ρ₁ ρ₂ : ℝ → ℝ}
    (hpos₁ : ∀ θ, 0 < ρ₁ θ) (hpos₂ : ∀ θ, 0 < ρ₂ θ)
    (hchord₁ : ∀ θ, ρ₁ θ + ρ₁ (θ + Real.pi) = 1)
    (hchord₂ : ∀ θ, ρ₂ θ + ρ₂ (θ + Real.pi) = 1)
    (hrange : Set.range (fun θ => polarPt (-(a / 2)) (ρ₁ θ) θ) =
      Set.range (fun θ => polarPt (a / 2) (ρ₂ θ) θ)) (θ : ℝ) :
    (0 < ‖polarPt (-(a/2)) (ρ₁ θ) θ - O2_sym a‖ ∧
        ‖polarPt (-(a/2)) (ρ₁ θ) θ - O2_sym a‖ < 1) ∧
      (0 < ‖chordMap (O2_sym a) (polarPt (-(a/2)) (ρ₁ θ) θ) - O1_sym a‖ ∧
        ‖chordMap (O2_sym a) (polarPt (-(a/2)) (ρ₁ θ) θ) - O1_sym a‖ < 1) := by
  have hO1val : O1_sym a = ((-(a/2) : ℝ) : ℂ) := by simp only [O1_sym]; push_cast; ring
  have hO2val : O2_sym a = (((a/2) : ℝ) : ℂ) := by rw [O2_sym]
  have hPmem2 : polarPt (-(a/2)) (ρ₁ θ) θ ∈ Set.range (fun θ => polarPt (a/2) (ρ₂ θ) θ) := by
    rw [← hrange]; exact Set.mem_range_self θ
  obtain ⟨φ, hφ⟩ := Set.mem_range.mp hPmem2
  have hnormP : ‖polarPt (-(a/2)) (ρ₁ θ) θ - O2_sym a‖ = ρ₂ φ := by
    rw [← hφ, hO2val]; exact nec_norm_polarPt_sub (hpos₂ φ)
  have hφlt : ρ₂ φ < 1 := by have := hchord₂ φ; linarith [hpos₂ (φ + Real.pi)]
  have hQmem : chordMap (O2_sym a) (polarPt (-(a/2)) (ρ₁ θ) θ) ∈
      Set.range (fun θ => polarPt (-(a/2)) (ρ₁ θ) θ) := by
    rw [← hφ, nec_chordMap_polarPt_O2 (a := a) hpos₂ hchord₂ φ, hrange]
    exact Set.mem_range_self (φ + Real.pi)
  obtain ⟨ψ, hψ⟩ := Set.mem_range.mp hQmem
  have hnormQ : ‖chordMap (O2_sym a) (polarPt (-(a/2)) (ρ₁ θ) θ) - O1_sym a‖ = ρ₁ ψ := by
    rw [← hψ, hO1val]; exact nec_norm_polarPt_sub (hpos₁ ψ)
  have hψlt : ρ₁ ψ < 1 := by have := hchord₁ ψ; linarith [hpos₁ (ψ + Real.pi)]
  exact ⟨⟨by rw [hnormP]; exact hpos₂ φ, by rw [hnormP]; exact hφlt⟩,
    ⟨by rw [hnormQ]; exact hpos₁ ψ, by rw [hnormQ]; exact hψlt⟩⟩

/-- `sin` is negative on `(π, 2π)`. -/
lemma sin_neg_of_pi_lt_of_lt_two_pi {θ : ℝ} (h1 : Real.pi < θ) (h2 : θ < 2 * Real.pi) :
    Real.sin θ < 0 := by
  have h0 : 0 < 2 * Real.pi - θ := by linarith
  have hπ : 2 * Real.pi - θ < Real.pi := by linarith
  have hpos := Real.sin_pos_of_pos_of_lt_pi h0 hπ
  have hsin : Real.sin θ = - Real.sin (2 * Real.pi - θ) := by
    rw [Real.sin_two_pi_sub]; ring
  rw [hsin]; linarith

/-- **The arc lemma.** On a normalised equichordal curve, `eqT a` preserves the sign of the
imaginary part of the point: on the open upper arc `0 < θ < π` the image again lies in the open
upper half plane, and on the lower arc `π < θ < 2π` the image lies in the open lower half
plane. -/
theorem eqT_im_arc {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {ρ₁ ρ₂ : ℝ → ℝ}
    (hC : NormEqCurve a ρ₁ ρ₂) :
    (∀ θ, 0 < θ → θ < Real.pi → 0 < (eqT a (polarPt (-(a/2)) (ρ₁ θ) θ)).im) ∧
    (∀ θ, Real.pi < θ → θ < 2 * Real.pi → (eqT a (polarPt (-(a/2)) (ρ₁ θ) θ)).im < 0) := by
  obtain ⟨hcont₁, hcont₂, hpos₁, hpos₂, hchord₁, hchord₂, hrange⟩ := hC
  constructor
  · intro θ hθ0 hθπ
    have hb := eqT_arc_bounds (a := a) hpos₁ hpos₂ hchord₁ hchord₂ hrange θ
    have hPim : 0 < (polarPt (-(a/2)) (ρ₁ θ) θ).im := by
      rw [nec_polarPt_im]
      exact mul_pos (hpos₁ θ) (Real.sin_pos_of_pos_of_lt_pi hθ0 hθπ)
    exact eqT_im_pos_of hb.1.1 hb.1.2 hb.2.1 hb.2.2 hPim
  · intro θ hθπ hθ2π
    have hb := eqT_arc_bounds (a := a) hpos₁ hpos₂ hchord₁ hchord₂ hrange θ
    have hPim : (polarPt (-(a/2)) (ρ₁ θ) θ).im < 0 := by
      rw [nec_polarPt_im]
      exact mul_neg_of_pos_of_neg (hpos₁ θ) (sin_neg_of_pi_lt_of_lt_two_pi hθπ hθ2π)
    exact eqT_im_neg_of hb.1.1 hb.1.2 hb.2.1 hb.2.2 hPim

end Work.EQ
