import Mathlib
import Submission.Work.EQ.normEqCurve_structure
import Submission.Work.EQ.polarPt_basic

/-!
# Continuity of the equichordal angle function on one period

`Work.EQ.eqT_continuousOn_D`: for a normalised two-point equichordal curve
(`NormEqCurve a ρ₁ ρ₂`, `0 < a < 1`) the map
`θ ↦ arccos (re (T(P(θ)) - O₁) / ‖T(P(θ)) - O₁‖)`, where `P(θ) = polarPt (-(a/2)) (ρ₁ θ) θ`
is the point of the curve at angle `θ` about `O₁` and `T = eqT a` is Rychlik's map, is
continuous on `[-π, 2π]`.

The function is continuous on all of `ℝ`: the parametrisation `θ ↦ P(θ)` is continuous, `eqT`
is continuous at every point of the curve (the two chord maps are applied at points at distance
`∈ (0,1)` from their centres, so neither singular value `c` is met), and the denominator
`T(P(θ)) - O₁` never vanishes because `T(P(θ))` is again a point of the curve, a positive
distance `< 1` from `O₁`; hence `w ↦ re w / ‖w‖` and `arccos` may be composed.
-/

namespace Work.EQ

theorem eqT_continuousOn_D {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {ρ₁ ρ₂ : ℝ → ℝ}
    (hC : NormEqCurve a ρ₁ ρ₂) :
    ContinuousOn (fun θ : ℝ =>
        Real.arccos ((eqT a (polarPt (-(a/2)) (ρ₁ θ) θ) - O1_sym a).re /
          ‖eqT a (polarPt (-(a/2)) (ρ₁ θ) θ) - O1_sym a‖))
      (Set.Icc (-Real.pi) (2 * Real.pi)) := by
  obtain ⟨hc1, hc2, hc3, hc4, hc5, hc6, hc7, hc8, hc9, hc10, hc11, hc12, hc13, hc14, hc15,
    hc16, hc17, hc18⟩ := normEqCurve_structure ha0 ha1 hC
  obtain ⟨hcont₁, hcont₂, hpos₁, hpos₂, hchord₁, hchord₂, hrange⟩ := hC
  have hO1 : O1_sym a = ((-(a/2) : ℝ) : ℂ) := by simp only [O1_sym]; push_cast; ring
  have hO2 : O2_sym a = (((a/2) : ℝ) : ℂ) := by rw [O2_sym]
  -- the polar parametrisation of the curve about `O₁` is continuous
  have hfcont : Continuous (fun θ : ℝ => polarPt (-(a/2)) (ρ₁ θ) θ) := by
    simp only [polarPt]
    fun_prop
  -- `chordMap c` is continuous at any point different from its centre
  have hcat : ∀ {c P : ℂ}, P ≠ c → ContinuousAt (chordMap c) P := by
    intro c P h
    have h2 : ‖P - c‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr h)
    have hc : ContinuousAt (fun P : ℂ => P - c) P := continuousAt_id.sub continuousAt_const
    have hn : ContinuousAt (fun P : ℂ => ‖P - c‖) P := continuous_norm.continuousAt.comp hc
    have hdiv : ContinuousAt (fun P : ℂ => (P - c) / ((‖P - c‖ : ℝ) : ℂ)) P :=
      hc.div (Complex.continuous_ofReal.continuousAt.comp hn) (by simpa using h2)
    change ContinuousAt (fun P : ℂ => P - (P - c) / ((‖P - c‖ : ℝ) : ℂ)) P
    exact continuousAt_id.sub hdiv
  -- the curve never passes through `O₂` (every curve point is at positive distance from `O₂`)
  have hfne : ∀ θ, polarPt (-(a/2)) (ρ₁ θ) θ ≠ O2_sym a := by
    intro θ h
    have hmem : O2_sym a ∈ Set.range (fun θ => polarPt (a/2) (ρ₂ θ) θ) := by
      rw [← hrange]; exact ⟨θ, h⟩
    obtain ⟨φ, hφ⟩ := hmem
    have hφ' : polarPt (a/2) (ρ₂ φ) φ = O2_sym a := hφ
    have hb := nec_norm_polarPt_sub (c := a/2) (r := ρ₂ φ) (θ := φ) (hpos₂ φ)
    rw [hφ', hO2] at hb
    simp at hb
    linarith [hpos₂ φ]
  -- every curve point is at distance in `(0,1)` from `O₁`
  have bound1 : ∀ X ∈ Set.range (fun θ => polarPt (-(a/2)) (ρ₁ θ) θ),
      0 < ‖X - O1_sym a‖ ∧ ‖X - O1_sym a‖ < 1 := by
    intro X hX
    obtain ⟨θ, rfl⟩ := hX
    have hval : ‖polarPt (-(a/2)) (ρ₁ θ) θ - O1_sym a‖ = ρ₁ θ := by
      rw [hO1]; exact nec_norm_polarPt_sub (hpos₁ θ)
    rw [hval]
    exact ⟨hpos₁ θ, by have := hchord₁ θ; linarith [hpos₁ (θ + Real.pi)]⟩
  have hQcont : Continuous (fun θ => chordMap (O2_sym a) (polarPt (-(a/2)) (ρ₁ θ) θ)) := by
    rw [continuous_iff_continuousAt]
    intro θ
    exact ContinuousAt.comp (f := fun θ => polarPt (-(a/2)) (ρ₁ θ) θ)
      (hcat (hfne θ)) hfcont.continuousAt
  have hQne : ∀ θ, chordMap (O2_sym a) (polarPt (-(a/2)) (ρ₁ θ) θ) ≠ O1_sym a := by
    intro θ h
    have hb := (bound1 _ (hc7 θ)).1
    rw [h] at hb
    simp at hb
  have hQ2cont : Continuous
      (fun θ => chordMap (O1_sym a) (chordMap (O2_sym a) (polarPt (-(a/2)) (ρ₁ θ) θ))) := by
    rw [continuous_iff_continuousAt]
    intro θ
    exact ContinuousAt.comp (f := fun θ => chordMap (O2_sym a) (polarPt (-(a/2)) (ρ₁ θ) θ))
      (hcat (hQne θ)) hQcont.continuousAt
  have hwcont : Continuous (fun θ => eqT a (polarPt (-(a/2)) (ρ₁ θ) θ) - O1_sym a) := by
    have hh : Continuous
        (fun θ => chordMap (O1_sym a) (chordMap (O2_sym a) (polarPt (-(a/2)) (ρ₁ θ) θ)) - O1_sym a) :=
      hQ2cont.sub (continuous_const : Continuous (fun _ : ℝ => O1_sym a))
    simpa only [eqT] using hh
  -- `T(P(θ)) - O₁` never vanishes
  have hwne : ∀ θ, eqT a (polarPt (-(a/2)) (ρ₁ θ) θ) - O1_sym a ≠ 0 := by
    intro θ
    have hb := bound1 _ (hc7 θ)
    have hform : eqT a (polarPt (-(a/2)) (ρ₁ θ) θ) - O1_sym a
        = ((1 - 1/‖chordMap (O2_sym a) (polarPt (-(a/2)) (ρ₁ θ) θ) - O1_sym a‖ : ℝ) : ℂ)
          * (chordMap (O2_sym a) (polarPt (-(a/2)) (ρ₁ θ) θ) - O1_sym a) := by
      simp only [eqT]
      exact nec_chordMap_sub (O1_sym a) _
    rw [hform]
    apply mul_ne_zero
    · simp only [Ne, Complex.ofReal_eq_zero]
      have : (1:ℝ) < 1/‖chordMap (O2_sym a) (polarPt (-(a/2)) (ρ₁ θ) θ) - O1_sym a‖ :=
        one_lt_one_div hb.1 hb.2
      linarith
    · exact norm_ne_zero_iff.mp (ne_of_gt hb.1)
  have hre : Continuous (fun θ => (eqT a (polarPt (-(a/2)) (ρ₁ θ) θ) - O1_sym a).re) :=
    Complex.continuous_re.comp hwcont
  have hn : Continuous (fun θ => ‖eqT a (polarPt (-(a/2)) (ρ₁ θ) θ) - O1_sym a‖) :=
    continuous_norm.comp hwcont
  have hratio : Continuous (fun θ => (eqT a (polarPt (-(a/2)) (ρ₁ θ) θ) - O1_sym a).re /
      ‖eqT a (polarPt (-(a/2)) (ρ₁ θ) θ) - O1_sym a‖) :=
    hre.div hn (fun θ => norm_ne_zero_iff.mpr (hwne θ))
  exact (Real.continuous_arccos.comp hratio).continuousOn

end Work.EQ
