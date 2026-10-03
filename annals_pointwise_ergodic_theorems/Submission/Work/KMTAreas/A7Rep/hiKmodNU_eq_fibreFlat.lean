import Mathlib
import Submission.Work.KMTAreas.A7.RepFibre
import Submission.Work.KMTAreas.A7.bump_support_realArc
import Submission.Work.KMTAreas.A7.cut_discharge

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTAreas.A7Rep

open MeasureTheory Polynomial Finset Filter

/-- The two cutoffs `m_*`, `m̃_*` may be dropped from the model integral once they are known to be
`1` on the supports of the bumps: pointwise, `m_*(θ) * φ_N(θ) = φ_N(θ)`. -/
private theorem mStarF_mul_varphiN_eq (N k₁ U : ℕ)
    (hcut : ∀ θ : ℝ, Work.KMTAreas.A7.varphiN N k₁ θ ≠ 0 →
      Work.KMTAreas.A7.mStarF U θ = 1) :
    ∀ θ : ℝ, Work.KMTAreas.A7.mStarF U θ * Work.KMTAreas.A7.varphiN N k₁ θ
      = Work.KMTAreas.A7.varphiN N k₁ θ := by
  intro θ
  by_cases h : Work.KMTAreas.A7.varphiN N k₁ θ = 0
  · rw [h, mul_zero]
  · rw [hcut θ h, one_mul]

/-- The same drop for the second cutoff. -/
private theorem mStargF_mul_varphitildeN_eq (d N k₂ U : ℕ)
    (hcut : ∀ θ : ℝ, Work.KMTAreas.A7.varphitildeN d N k₂ θ ≠ 0 →
      Work.KMTAreas.A7.mStargF d U θ = 1) :
    ∀ θ : ℝ, Work.KMTAreas.A7.mStargF d U θ * Work.KMTAreas.A7.varphitildeN d N k₂ θ
      = Work.KMTAreas.A7.varphitildeN d N k₂ θ := by
  intro θ
  by_cases h : Work.KMTAreas.A7.varphitildeN d N k₂ θ = 0
  · rw [h, mul_zero]
  · rw [hcut θ h, one_mul]

theorem hiKmodNU_eq_fibreFlat (ρ : ℝ) (P : Polynomial ℤ) (U N l₁ l₂ k₁ k₂ : ℕ) (j₁ j₂ : ℤ)
    (hdeg : 2 ≤ P.natDegree) (hl₁ : 1 ≤ l₁) (hl₂ : 1 ≤ l₂)
    (hband₁ : (k₁ : ℤ) + 2 * (U : ℤ) ≤ Work.Analysis.EndVar.logN N)
    (hband₂ : (k₂ : ℤ) + 2 * (U : ℤ) ≤ Work.Analysis.EndVar.logN N)
    (hna₁ : Work.Analysis.IonescuWainger.NonAliasing (1 - 2 * (U : ℤ))
      (Work.KMTAreas.A7.diffFreqs ρ l₁))
    (hna₂ : Work.Analysis.IonescuWainger.NonAliasing (1 - 2 * (U : ℤ))
      (Work.KMTAreas.A7.diffFreqs ρ l₂))
    (hcut₁ : ∀ θ : ℝ, Work.KMTAreas.A7.varphiN N k₁ θ ≠ 0 → Work.KMTAreas.A7.mStarF U θ = 1)
    (hcut₂ : ∀ θ : ℝ, Work.KMTAreas.A7.varphitildeN P.natDegree N k₂ θ ≠ 0 →
      Work.KMTAreas.A7.mStargF P.natDegree U θ = 1) :
    Work.KMTAreas.A7.hiKmodNU ρ P U N l₁ l₂ k₁ k₂ j₁ j₂
      = ∑ p ∈ (Work.KMTAreas.A7.diffFreqs ρ l₁).product (Work.KMTAreas.A7.diffFreqs ρ l₂),
          (fourier (T := 1) (-j₁)) p.1 * (fourier (T := 1) (-j₂)) p.2
            * Work.KMTAreas.A7.mZ P (Work.KMTAreas.A7.arithQ ρ (max l₁ l₂)) p.1 p.2
            * (∫ θ₁ : ℝ, ∫ θ₂ : ℝ,
                Work.KMTAreas.A7.varphiN N k₁ θ₁
                  * Work.KMTAreas.A7.varphitildeN P.natDegree N k₂ θ₂
                  * Work.KMTAreas.A7.mTilde P N θ₁ θ₂
                  * Work.KMTAreas.A7.ee (-((j₁ : ℝ) * θ₁ + (j₂ : ℝ) * θ₂))) := by
  -- 1. the fibre form of the model kernel, from the master identity
  obtain ⟨hs₁, hs₂⟩ :=
    Work.KMTAreas.A7.bump_support_realArc P hdeg N k₁ k₂ U hband₁ hband₂
  rw [Work.KMTAreas.A7.hiKmodNU_fibre ρ P U N l₁ l₂ k₁ k₂ j₁ j₂ hl₁ hl₂ hna₁ hna₂ hs₁ hs₂]
  -- 2. the cutoffs are `1` on the supports of the bumps, so they drop out
  have hφ := mStarF_mul_varphiN_eq N k₁ U hcut₁
  have hψ := mStargF_mul_varphitildeN_eq P.natDegree N k₂ U hcut₂
  rw [Work.KMTAreas.A7.hiFibreKer]
  refine Finset.sum_congr rfl (fun p _ => ?_)
  congr 1
  apply MeasureTheory.integral_congr_ae
  filter_upwards with θ₁
  apply MeasureTheory.integral_congr_ae
  filter_upwards with θ₂
  calc Work.KMTAreas.A7.mStarF U θ₁ * Work.KMTAreas.A7.mStargF P.natDegree U θ₂
        * Work.KMTAreas.A7.varphiN N k₁ θ₁
        * Work.KMTAreas.A7.varphitildeN P.natDegree N k₂ θ₂
        * Work.KMTAreas.A7.mTilde P N θ₁ θ₂
        * Work.KMTAreas.A7.ee (-((j₁ : ℝ) * θ₁ + (j₂ : ℝ) * θ₂))
      = (Work.KMTAreas.A7.mStarF U θ₁ * Work.KMTAreas.A7.varphiN N k₁ θ₁)
        * (Work.KMTAreas.A7.mStargF P.natDegree U θ₂
            * Work.KMTAreas.A7.varphitildeN P.natDegree N k₂ θ₂)
        * Work.KMTAreas.A7.mTilde P N θ₁ θ₂
        * Work.KMTAreas.A7.ee (-((j₁ : ℝ) * θ₁ + (j₂ : ℝ) * θ₂)) := by ring
    _ = Work.KMTAreas.A7.varphiN N k₁ θ₁
        * Work.KMTAreas.A7.varphitildeN P.natDegree N k₂ θ₂
        * Work.KMTAreas.A7.mTilde P N θ₁ θ₂
        * Work.KMTAreas.A7.ee (-((j₁ : ℝ) * θ₁ + (j₂ : ℝ) * θ₂)) := by rw [hφ θ₁, hψ θ₂]

end Work.KMTAreas.A7Rep
