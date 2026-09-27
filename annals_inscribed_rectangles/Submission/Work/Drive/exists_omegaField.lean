import Mathlib
import Submission.Work.Drive.planeChartDataAux
import Submission.Work.Drive.smoothUnit_eqOn_annulus_of_periodicArgument
import Submission.Work.Drive.periodicArgument_annulus_transport
import Submission.Work.Drive.bandLoop_periodic_argument

namespace Work.Drive

theorem exists_omegaField (γ : Circle → ℝ × ℝ)
    (hU : Submission.Drive.UmlaufProp) (hWrap : Work.Drive.WrapData γ)
    (hγ : Manifold.IsSmoothEmbedding (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
      (modelWithCornersSelf ℝ (ℝ × ℝ)) ((⊤ : ℕ∞) : WithTop ℕ∞) γ)
    (hγne : ∀ x : Circle, γ x ≠ 0)
    (M W : ℂ × ℝ → ℂ)
    (hMsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) M)
    (hWsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) W)
    (hMval : ∀ x : ℂ, ∀ τ : ℝ, 0 ≤ τ → ‖x‖ = 1 → M (x, τ) = Neutral.dataMid γ x (Real.sqrt τ))
    (hWval : ∀ x : ℂ, ∀ τ : ℝ, 0 ≤ τ → ‖x‖ = 1 → W (x, τ) = Neutral.dchW γ (x, Real.sqrt τ))
    (hMne0 : ∀ x : ℂ, ‖x‖ = 1 → M (x, 0) ≠ 0)
    (hWne0 : ∀ x : ℂ, ‖x‖ = 1 → W (x, 0) ≠ 0)
    (hM0 : ∀ x : ℂ, 1 / 4 ≤ ‖x‖ → ‖x‖ ≤ 1 → M (x, 0) ≠ 0)
    (hW0 : ∀ x : ℂ, 1 / 4 ≤ ‖x‖ → ‖x‖ ≤ 1 → W (x, 0) ≠ 0)
    (x : ℂ → ℂ) (τ : ℂ → ℝ)
    (hx1 : ∀ z : ℂ, 1 / 2 ≤ ‖z‖ → x z = z / ((‖z‖ : ℝ) : ℂ))
    (hτ1 : ∀ z : ℂ, 1 / 2 ≤ ‖z‖ → τ z = Real.pi ^ 2 / 2 * (‖z‖ - 1 / 2))
    {ρ₀ ρ₁ ρ₂ ρ₃ : ℝ} (hρ₀ : 0 < ρ₀) (h₀₁ : ρ₀ < ρ₁) (h₁₂ : ρ₁ < ρ₂) (h₂₃ : ρ₂ < ρ₃)
    (hρ₀half : ρ₀ < 1 / 2) (hhalf₃ : 1 / 2 ≤ ρ₃)
    (hwsm : ∀ z : ℂ, ρ₀ ≤ ‖z‖ → ‖z‖ ≤ ρ₃ →
      ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => pcW M W x τ z) z)
    (hwunit : ∀ z : ℂ, ρ₀ ≤ ‖z‖ → ‖z‖ ≤ ρ₃ → ‖pcW M W x τ z‖ = 1) :
    ∃ Ω : ℂ → ℂ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Ω ∧ (∀ z : ℂ, ‖Ω z‖ = 1) ∧
      (∀ z : ℂ, ρ₁ ≤ ‖z‖ → ‖z‖ ≤ ρ₂ → Ω z = pcW M W x τ z) := by
  -- The unit-circle loop of the band data has a continuous `2π`-periodic argument:
  -- the seam argument of `Work.Drive.seam_periodic_argument`, conjugated.
  have hMval0 : ∀ y : ℂ, ‖y‖ = 1 → M (y, 0) = Neutral.dataMid γ y 0 := fun y hy => by
    simpa using hMval y 0 le_rfl hy
  have hWval0 : ∀ y : ℂ, ‖y‖ = 1 → W (y, 0) = Neutral.dchW γ (y, 0) := fun y hy => by
    simpa using hWval y 0 le_rfl hy
  obtain ⟨θs, hθsc, hθsper, hθs⟩ :=
    seam_periodic_argument γ hγ hγne hU hWrap hMsm hWsm hMval0 hWval0 hMne0 hWne0
      (c := 1) (hc := by norm_num)
  have hθs' : ∀ σ : ℝ, Complex.exp (((θs σ : ℝ) : ℂ) * Complex.I)
      = star (dirDatum M W (Complex.exp (((σ : ℂ) * Complex.I)), 0)) := fun σ => by
    simpa using hθs σ
  -- negating the argument turns an argument of the conjugate loop into one of the loop itself
  have hθseam : ∀ σ : ℝ, Complex.exp (((-(θs σ) : ℝ) : ℂ) * Complex.I)
      = pcW M W x τ (((1 / 2 : ℝ) : ℂ) * Complex.exp (((σ : ℂ) * Complex.I))) := by
    intro σ
    rw [← star_exp_mul_I (θs σ), hθs' σ, star_star]
    exact (pcW_at_seam hx1 hτ1 hM0 hW0 σ).symm
  have hθper : Function.Periodic (fun σ : ℝ => -(θs σ)) (2 * Real.pi) := fun σ =>
    by simp only [hθsper σ]
  have hwsm' : ∀ z : ℂ, ρ₀ ≤ ‖z‖ → ‖z‖ ≤ 1 / 2 →
      ContDiffAt ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun z => pcW M W x τ z) z :=
    fun z h1 h2 => hwsm z h1 (le_trans h2 hhalf₃)
  have hwunit' : ∀ z : ℂ, ρ₀ ≤ ‖z‖ → ‖z‖ ≤ 1 / 2 → ‖pcW M W x τ z‖ = 1 :=
    fun z h1 h2 => hwunit z h1 (le_trans h2 hhalf₃)
  -- transport the argument from the seam circle `‖z‖ = 1/2` down to the inner circle `‖z‖ = ρ₀`
  obtain ⟨θρ, hθρc, hθρper, hθρ⟩ :=
    periodicArgument_annulus_transport (ρ := ρ₀) (ρ₂ := 1 / 2) hρ₀ hρ₀half hwsm' hwunit'
      hθsc.neg hθper hθseam
  -- a smooth unit-valued map with a periodic argument on the inner circle extends
  exact smoothUnit_eqOn_annulus_of_periodicArgument (ρ₀ := ρ₀) (ρ₁ := ρ₁) (ρ₂ := ρ₂) (ρ₃ := ρ₃)
    hρ₀ h₀₁ h₁₂ h₂₃ hwsm hwunit hθρc hθρper hθρ

end Work.Drive
