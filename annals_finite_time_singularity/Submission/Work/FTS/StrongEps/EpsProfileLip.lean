import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.StrongEps.PZeroScheme
import Submission.Work.FTS.StrongEps.EpsSlotLipP

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps

theorem EpsProfileLip {α T : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn} {g₀ : Work.FTS.Galerkin.Fn}
    {ε : ℕ → ℝ} {G : ℕ → Work.FTS.Galerkin.Fam}
    (hsol : ∀ n : ℕ, Work.FTS.StrongEps.IsEpsSolP α ρ (ε n) T Φs E g₀ (G n))
    (hcont : ∀ n : ℕ, ∀ p : ℝ × ℝ, p ∈ Work.FTS.EllipticEst.Q0 →
      ContinuousOn (fun s : ℝ => Work.FTS.StrongEps.epsRHSP α ρ (ε n) Φs E (G n) s p.1 p.2)
        (Set.Icc (0 : ℝ) T))
    (hbdd : ∀ K : Set (ℝ × ℝ), IsCompact K → K ⊆ Work.FTS.EllipticEst.Q0 →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ p ∈ K,
        |Work.FTS.StrongEps.epsRHSP α ρ (ε n) Φs E (G n) s p.1 p.2| ≤ C) :
    ∀ K : Set (ℝ × ℝ), IsCompact K → K ⊆ Work.FTS.EllipticEst.Q0 →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, ∀ p ∈ K, ∀ τ ∈ Set.Icc (0 : ℝ) T,
        ∀ τ' ∈ Set.Icc (0 : ℝ) T,
          |Work.FTS.Galerkin.slice (G n) τ p.1 p.2 - Work.FTS.Galerkin.slice (G n) τ' p.1 p.2|
            ≤ C * |τ - τ'| := by
  intro K hK hKQ
  obtain ⟨C₀, hC₀nn, hC₀⟩ := hbdd K hK hKQ
  refine ⟨C₀, hC₀nn, ?_⟩
  intro n p hp τ hτ τ' hτ'
  have hQ : (p.1, p.2) ∈ Work.FTS.EllipticEst.Q0 := hKQ hp
  have hFcont : ContinuousOn
      (fun s : ℝ => Work.FTS.StrongEps.epsRHSP α ρ (ε n) Φs E (G n) s p.1 p.2)
      (Set.Icc (0 : ℝ) T) := hcont n p hQ
  have hFbd : ∀ s ∈ Set.Icc (0 : ℝ) T,
      |Work.FTS.StrongEps.epsRHSP α ρ (ε n) Φs E (G n) s p.1 p.2| ≤ C₀ :=
    fun s hs => hC₀ n s hs p hp
  -- the integral form of the two slices and the resulting difference identity
  have key : ∀ σ σ' : ℝ, σ ∈ Set.Icc (0 : ℝ) T → σ' ∈ Set.Icc (0 : ℝ) T → σ' ≤ σ →
      |Work.FTS.Galerkin.slice (G n) σ p.1 p.2 - Work.FTS.Galerkin.slice (G n) σ' p.1 p.2|
        ≤ C₀ * |σ - σ'| := by
    intro σ σ' hσ hσ' hle
    have h1 := Work.FTS.StrongEps.epsSol_eq_integralP (hsol n)
      (fun z θ hzθ => hcont n (z, θ) hzθ) p.1 p.2 σ hQ hσ
    have h2 := Work.FTS.StrongEps.epsSol_eq_integralP (hsol n)
      (fun z θ hzθ => hcont n (z, θ) hzθ) p.1 p.2 σ' hQ hσ'
    have hi1 : IntervalIntegrable
        (fun s : ℝ => Work.FTS.StrongEps.epsRHSP α ρ (ε n) Φs E (G n) s p.1 p.2)
        MeasureTheory.volume (0 : ℝ) σ' :=
      ContinuousOn.intervalIntegrable_of_Icc hσ'.1
        (hFcont.mono (Set.Icc_subset_Icc le_rfl hσ'.2))
    have hi2 : IntervalIntegrable
        (fun s : ℝ => Work.FTS.StrongEps.epsRHSP α ρ (ε n) Φs E (G n) s p.1 p.2)
        MeasureTheory.volume σ' σ :=
      ContinuousOn.intervalIntegrable_of_Icc hle (hFcont.mono (Set.Icc_subset_Icc hσ'.1 hσ.2))
    have hadj := intervalIntegral.integral_add_adjacent_intervals hi1 hi2
    have hdiff : Work.FTS.Galerkin.slice (G n) σ p.1 p.2
          - Work.FTS.Galerkin.slice (G n) σ' p.1 p.2
        = ∫ s in σ'..σ, Work.FTS.StrongEps.epsRHSP α ρ (ε n) Φs E (G n) s p.1 p.2 := by
      show (G n) p.1 p.2 σ - (G n) p.1 p.2 σ' = _
      rw [h1, h2]
      linarith
    rw [hdiff]
    have hnorm : ‖∫ s in σ'..σ,
          Work.FTS.StrongEps.epsRHSP α ρ (ε n) Φs E (G n) s p.1 p.2‖
        ≤ C₀ * |σ - σ'| := by
      refine intervalIntegral.norm_integral_le_of_norm_le_const fun x hx => ?_
      rw [Set.uIoc_of_le hle] at hx
      rw [Real.norm_eq_abs]
      exact hFbd x ⟨le_trans hσ'.1 hx.1.le, le_trans hx.2 hσ.2⟩
    simpa only [Real.norm_eq_abs] using hnorm
  rcases le_total τ' τ with hle | hle
  · exact key τ τ' hτ hτ' hle
  · have h := key τ' τ hτ' hτ hle
    rw [abs_sub_comm (Work.FTS.Galerkin.slice (G n) τ p.1 p.2)
          (Work.FTS.Galerkin.slice (G n) τ' p.1 p.2), abs_sub_comm τ τ']
    exact h

end Work.FTS.StrongEps
