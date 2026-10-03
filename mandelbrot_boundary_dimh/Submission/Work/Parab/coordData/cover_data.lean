import Mathlib
import Submission.Work.Interfaces.Parabolic
import Submission.Work.FatouCoord.Setup
import Submission.Work.Parab.Setup
import Submission.Work.Parab.coverCone.cover_cone_wedge

namespace Work.Parab.coordData

/-- The cone angle in `cover_cone_wedge` is `2π/3 - π/12 = π/2 + π/12`. -/
private lemma cone_angle : Real.pi / 2 + Real.pi / 12 = 2 * Real.pi / 3 - Real.pi / 12 := by
  ring

/-- `tau0` is an involution (with the junk value `tau0 0 = 0`). -/
private lemma tau0_tau0' (ζ : ℂ) : MandelDim.tau0 (MandelDim.tau0 ζ) = ζ := by
  simp only [MandelDim.tau0]
  by_cases h : ζ = 0
  · rw [h]; simp
  · field_simp

theorem cover_data {Φ : ℂ → ℂ} {L : Set ℂ} {M₀ M₁ : ℝ} {a b : ℂ}
    (hM₀ : 0 < M₀) (hM₁ : 0 < M₁)
    (hL : ∀ ζ : ℂ, ζ.re < -M₀ → ζ ∈ L)
    (hLim : ∀ ζ : ℂ, M₁ < |ζ.im| → ζ.re < 3 * |ζ.im| → ζ ∈ L)
    (hasym : ∀ ε > 0, ∃ R : ℝ, ∀ ζ ∈ L, R < ‖ζ‖ →
      ‖Φ ζ - (ζ - a * Complex.log (-ζ) - b)‖ < ε) :
    ∃ ξ₀ : ℝ, 0 < ξ₀ ∧ ∃ ρ : ℝ, 0 < ρ ∧ ∀ z : ℂ, 0 < ‖z‖ → ‖z‖ < ρ →
      |z.arg| ≤ Real.pi / 2 + Real.pi / 12 →
        MandelDim.tau0 z ∈ L ∧ Φ (MandelDim.tau0 z) ∈ MandelDim.QLeft ξ₀ := by
  obtain ⟨ξ₀, hξ₀, ρ, hρ, hcover⟩ :=
    Work.Parab.coverCone.cover_cone_wedge (Φ := Φ) (L := L) (M₀ := M₀) (M₁ := M₁)
      (a := a) (b := b) hM₀ hM₁ hL hLim hasym
  refine ⟨ξ₀, hξ₀, ρ, hρ, fun z hz0 hzρ hzarg => ?_⟩
  rw [cone_angle] at hzarg
  obtain ⟨w, hw, ζ, hζL, hΦζ, htau⟩ := hcover z hz0 hzρ hzarg
  have hz_eq : MandelDim.tau0 z = ζ := by
    rw [← htau]
    exact tau0_tau0' ζ
  rw [hz_eq]
  exact ⟨hζL, by rw [hΦζ]; exact hw⟩

end Work.Parab.coordData
