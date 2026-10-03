import Mathlib
import Submission.Work.KMTPlan.A6.M0_iteratedDeriv
import Submission.Work.KMTPlan.A6.SymToolbox

namespace Work.KMTAreas.A7

/-- The mixed iterated `ξ`-derivative `dp j₁ j₂ σ x y` expands definitionally as
`iteratedDeriv j₁ (fun t => iteratedDeriv j₂ (fun s => σ t s) y) x`. -/
lemma dp_apply (j₁ j₂ : ℕ) (σ : ℝ → ℝ → ℂ) (x y : ℝ) :
    Work.KMTPlan.A6.dp j₁ j₂ σ x y
      = iteratedDeriv j₁ (fun t : ℝ => iteratedDeriv j₂ (fun s : ℝ => σ t s) y) x := rfl

/-- **The iterated `ξ`-derivatives of the halved discrete average.**
`∂^{j₁}_{ξ₁}∂^{j₂}_{ξ₂} weylAvg = N⁻¹ ∑_{n ∈ (N/2,N]} ∂^{j₁}_{ξ₁}∂^{j₂}_{ξ₂} momPhase(n)`,
i.e. differentiating the finite sum of characters just brings down the factors
`(2πi n)^{j₁}(2πiP(n))^{j₂}` on each summand. -/
theorem dp_weylAvg_eq_sum_momPhaseDeriv (P : Polynomial ℤ) (N : ℕ) (α₁ α₂ : Work.Analysis.IonescuWainger.Circle) (x y : ℝ) (j₁ j₂ : ℕ) : Work.KMTPlan.A6.dp j₁ j₂ (fun a b => Work.KMTAreas.A7.weylAvg P N α₁ α₂ a b) x y = ((N : ℂ))⁻¹ * ∑ n ∈ Finset.Ioc (N / 2) N, Work.KMTAreas.A7.momPhaseDeriv P N α₁ α₂ x y (n : ℤ) j₁ j₂ := by
  rw [dp_apply]
  have hinner : (fun t : ℝ => iteratedDeriv j₂
        (fun s : ℝ => Work.KMTAreas.A7.weylAvg P N α₁ α₂ t s) y)
      = fun t : ℝ => ((N : ℂ))⁻¹ * ∑ n ∈ Finset.Ioc (N / 2) N,
          Work.KMTAreas.A7.momPhaseDeriv P N α₁ α₂ t y (n : ℤ) 0 j₂ := by
    funext t
    rw [iteratedDeriv_eq_iterate, Work.KMTPlan.A6.M0Aux.iterate_deriv_weylAvg]
  rw [hinner, iteratedDeriv_eq_iterate, Work.KMTPlan.A6.M0Aux.iterate_deriv_weylAvgSum_fst]

end Work.KMTAreas.A7
