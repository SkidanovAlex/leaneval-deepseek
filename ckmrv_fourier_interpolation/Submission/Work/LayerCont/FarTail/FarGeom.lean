/-
# The far-side geometry of the two swept left rectangles

The classification `Work.LayerCont.ECS.exists_contour_left_data` says that the only `SL(2,ℤ)`
orbit points of `τ` inside the two closed left rectangles
`leftRect s₀ A₁ ξ₁`, `leftRect s₀⁻¹ A₂ ξ₂` are the pole `τ - 1` and the removable coincidence
`ST⁻¹τ`.  On the **far side** (`1 < τ.re`) neither of the two can actually occur in those
rectangles:

* `τ - 1` has real part `τ.re - 1 > 0`, whereas a left rectangle has `re ≤ 0`;
* the coincidence `ST⁻¹τ = -1/(τ-1)` has imaginary part `≈ 1/s₀`, which is *below* the rectangle
  `leftRect s₀ A₁ ξ₁` (whose heights lie in `[s₀-A₁, s₀+A₁]`) because of the separation
  `s₀⁻¹ + A₂ < s₀ - A₁` and `Work.LayerCont.FarTail.coinc_mem_openLeftRect_far`, which places the
  coincidence inside `leftRect s₀⁻¹ A₂ ξ₂` (`≈ 1/s₀`).

Hence, on the far side, the first rectangle is completely orbit-free, and in the second the only
possible orbit point is the coincidence itself — precisely the two hypotheses `hcl₁`, `hcl₂` of
`Work.LayerCont.Coinc.layerLowDouble_eq_layerLowAt_far`.
-/
import Mathlib
import Submission.Work.LayerCont.FarTail.Defs
import Submission.Work.LayerCont.Coinc.All

set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

noncomputable section

open UpperHalfPlane MeasureTheory Filter Topology
open scoped Topology Manifold

namespace Work.LayerCont.FarTail

open Work.Asymptotics Work.LayerCont.Coinc

/-- **The two far-side orbit exclusions.**  Given the classification `hclass` of the orbit points
of the two rectangles and the location `hcoinc` of the coincidence inside the second one, on the
far side the first rectangle carries *no* orbit point and the second carries only the
coincidence. -/
theorem far_orbit_rects {s₀ A₁ ξ₁ A₂ ξ₂ ε : ℝ} (hs₀ : 0 < s₀)
    (hsep : s₀⁻¹ + A₂ < s₀ - A₁)
    (hclass : ∀ τ : UpperHalfPlane, dist τ (Work.Asymptotics.onePlusI s₀ hs₀) < ε →
      ∀ (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (z : UpperHalfPlane),
        (Work.Asymptotics.leftRect s₀ A₁ ξ₁ z ∨ Work.Asymptotics.leftRect s₀⁻¹ A₂ ξ₂ z) →
          z = γ • τ → z = Work.Asymptotics.tauSubOne τ ∨ z = Work.Asymptotics.tauCoinc τ)
    (hcoinc : ∀ τ : UpperHalfPlane, dist τ (Work.Asymptotics.onePlusI s₀ hs₀) < ε → 1 < τ.re →
      Work.LayerCont.Coinc.coincℂ τ ∈ Work.Asymptotics.openLeftRectℂ s₀⁻¹ A₂ ξ₂) :
    (∀ τ : UpperHalfPlane, dist τ (Work.Asymptotics.onePlusI s₀ hs₀) < ε → 1 < τ.re →
      ∀ (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (z : UpperHalfPlane),
        Work.Asymptotics.leftRect s₀ A₁ ξ₁ z → z ≠ γ • τ) ∧
    (∀ τ : UpperHalfPlane, dist τ (Work.Asymptotics.onePlusI s₀ hs₀) < ε → 1 < τ.re →
      ∀ (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (z : UpperHalfPlane),
        Work.Asymptotics.leftRect s₀⁻¹ A₂ ξ₂ z →
          (z ≠ γ • τ ∨ z = ModularGroup.S • ((-1 : ℝ) +ᵥ τ))) := by
  have hcoincIm : ∀ τ : UpperHalfPlane, dist τ (Work.Asymptotics.onePlusI s₀ hs₀) < ε → 1 < τ.re →
      (Work.LayerCont.Coinc.coincℂ τ).im < s₀ - A₁ := by
    intro τ hτ hτre
    have h := hcoinc τ hτ hτre
    simp only [Work.Asymptotics.openLeftRectℂ, Set.mem_ofPred_eq] at h
    linarith [h.2.2, hsep]
  have htauCoinc : ∀ τ : UpperHalfPlane,
      Work.Asymptotics.tauCoinc τ = ModularGroup.S • ((-1 : ℝ) +ᵥ τ) := by
    intro τ
    rw [← Work.LayerCont.ECS.S_smul_tauSubOne τ]
  have hsubOne : ∀ τ : UpperHalfPlane, (Work.Asymptotics.tauSubOne τ).re = τ.re - 1 :=
    fun τ => Work.LayerCont.tauSubOne_re' τ
  constructor
  · intro τ hτ hτre γ z hz hzeq
    rw [Work.Asymptotics.leftRect] at hz
    rcases hclass τ hτ γ z (Or.inl hz) hzeq with h | h
    · rw [h, hsubOne τ] at hz
      linarith [hz.2.1, hτre]
    · have him : (Work.Asymptotics.tauCoinc τ).im
          = (Work.LayerCont.Coinc.coincℂ τ).im := by
        rw [htauCoinc τ]
        exact (UpperHalfPlane.coe_im (ModularGroup.S • ((-1 : ℝ) +ᵥ τ))).symm
      rw [h, him] at hz
      linarith [hz.2.2.1, hcoincIm τ hτ hτre]
  · intro τ hτ hτre γ z hz
    by_cases hzeq : z = γ • τ
    · right
      rw [Work.Asymptotics.leftRect] at hz
      rcases hclass τ hτ γ z (Or.inr hz) hzeq with h | h
      · exfalso
        rw [h, hsubOne τ] at hz
        linarith [hz.2.1, hτre]
      · rw [h, htauCoinc τ]
    · exact Or.inl hzeq


/-- **The two far-side orbit exclusions, reversed regime.**  Same statement as
`far_orbit_rects`, but with the pole rectangle (height `s₀`) *below* the coincidence rectangle
(height `s₀⁻¹`): the coincidence is then excluded from the lower rectangle by the *reversed*
separation `s₀ + A₁ ≤ s₀⁻¹ - A₂` (its height is `≈ s₀⁻¹ ≥ s₀ - A₁ + A₂`), and the pole
`τ - 1` has positive real part on the far side. -/
theorem far_orbit_rects_rev {s₀ A₁ ξ₁ A₂ ξ₂ ε : ℝ} (hs₀ : 0 < s₀)
    (hsep : s₀ + A₁ ≤ s₀⁻¹ - A₂)
    (hclass : ∀ τ : UpperHalfPlane, dist τ (Work.Asymptotics.onePlusI s₀ hs₀) < ε →
      ∀ (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (z : UpperHalfPlane),
        (Work.Asymptotics.leftRect s₀ A₁ ξ₁ z ∨ Work.Asymptotics.leftRect s₀⁻¹ A₂ ξ₂ z) →
          z = γ • τ → z = Work.Asymptotics.tauSubOne τ ∨ z = Work.Asymptotics.tauCoinc τ)
    (hcoinc : ∀ τ : UpperHalfPlane, dist τ (Work.Asymptotics.onePlusI s₀ hs₀) < ε → 1 < τ.re →
      Work.LayerCont.Coinc.coincℂ τ ∈ Work.Asymptotics.openLeftRectℂ s₀⁻¹ A₂ ξ₂) :
    (∀ τ : UpperHalfPlane, dist τ (Work.Asymptotics.onePlusI s₀ hs₀) < ε → 1 < τ.re →
      ∀ (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (z : UpperHalfPlane),
        Work.Asymptotics.leftRect s₀ A₁ ξ₁ z → z ≠ γ • τ) ∧
    (∀ τ : UpperHalfPlane, dist τ (Work.Asymptotics.onePlusI s₀ hs₀) < ε → 1 < τ.re →
      ∀ (γ : Matrix.SpecialLinearGroup (Fin 2) ℤ) (z : UpperHalfPlane),
        Work.Asymptotics.leftRect s₀⁻¹ A₂ ξ₂ z →
          (z ≠ γ • τ ∨ z = ModularGroup.S • ((-1 : ℝ) +ᵥ τ))) := by
  have hcoincIm : ∀ τ : UpperHalfPlane, dist τ (Work.Asymptotics.onePlusI s₀ hs₀) < ε → 1 < τ.re →
      s₀ + A₁ < (Work.LayerCont.Coinc.coincℂ τ).im := by
    intro τ hτ hτre
    have h := hcoinc τ hτ hτre
    simp only [Work.Asymptotics.openLeftRectℂ, Set.mem_ofPred_eq] at h
    linarith [h.2.2.1, hsep]
  have htauCoinc : ∀ τ : UpperHalfPlane,
      Work.Asymptotics.tauCoinc τ = ModularGroup.S • ((-1 : ℝ) +ᵥ τ) := by
    intro τ
    rw [← Work.LayerCont.ECS.S_smul_tauSubOne τ]
  have hsubOne : ∀ τ : UpperHalfPlane, (Work.Asymptotics.tauSubOne τ).re = τ.re - 1 :=
    fun τ => Work.LayerCont.tauSubOne_re' τ
  constructor
  · intro τ hτ hτre γ z hz hzeq
    rw [Work.Asymptotics.leftRect] at hz
    rcases hclass τ hτ γ z (Or.inl hz) hzeq with h | h
    · rw [h, hsubOne τ] at hz
      linarith [hz.2.1, hτre]
    · have him : (Work.Asymptotics.tauCoinc τ).im
          = (Work.LayerCont.Coinc.coincℂ τ).im := by
        rw [htauCoinc τ]
        exact (UpperHalfPlane.coe_im (ModularGroup.S • ((-1 : ℝ) +ᵥ τ))).symm
      rw [h, him] at hz
      linarith [hz.2.2.2, hcoincIm τ hτ hτre]
  · intro τ hτ hτre γ z hz
    by_cases hzeq : z = γ • τ
    · right
      rw [Work.Asymptotics.leftRect] at hz
      rcases hclass τ hτ γ z (Or.inr hz) hzeq with h | h
      · exfalso
        rw [h, hsubOne τ] at hz
        linarith [hz.2.1, hτre]
      · rw [h, htauCoinc τ]
    · exact Or.inl hzeq

end Work.LayerCont.FarTail
