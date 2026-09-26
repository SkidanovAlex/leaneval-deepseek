import Submission.Work.FunctionalEquations.DifferenceExpansionFtilde
import Submission.Work.CKFinal.Shadow.Util
import Submission.Work.CKFinal.Shadow.Basic

open scoped ContDiff
set_option linter.dupNamespace false

namespace Work.CKFinal.Shadow

namespace Work.FunctionalEquations
export _root_.Work.FunctionalEquations (FtildeDiff_periodicStripBound)
end Work.FunctionalEquations
namespace Work.FunctionalEquations
export _root_.Work.FunctionalEquations (FtildeDiff_dirichletExpansionIciOne)
end Work.FunctionalEquations

namespace Work.FunctionalEquations

open LeanEval.Analysis.CKMRVInterpolation Work.Core Work.FE Filter Topology
open scoped FourierTransform SchwartzMap

noncomputable section

/-- **Dirichlet expansion of the first difference of `F̃`** (CKMRV Theorem 3.1, cf. (3.2)).
For a solution `S` of the functional equations and any `x`, the periodic function
`τ ↦ F̃ (τ + 1) x - F̃ τ x` is a Dirichlet series with frequencies `m ≥ 1` on the upper half
plane, and its coefficients are the Fourier coefficients of the values on any horizontal
line `Im = y`, `y > 0`. -/
theorem DifferenceExpansionFtilde {n : ℕ} [NeZero n]
    (S : Work.FE.FunctionalEquationSolution n) (x : Work.FE.E n) :
    ∃ c : Set.Ici (1 : ℕ) → ℂ,
      (∀ τ : ℂ, 0 < τ.im → HasSum (fun m : Set.Ici (1 : ℕ) =>
          c m * Work.FE.dirichletTerm m.1 τ)
        (S.Ftilde (τ + 1) x - S.Ftilde τ x)) ∧
      (∀ (m : Set.Ici (1 : ℕ)) (y : ℝ), 0 < y →
        c m = ∫ t in (0 : ℝ)..1, (S.Ftilde ((t : ℂ) + (y : ℂ) * Complex.I + 1) x
            - S.Ftilde ((t : ℂ) + (y : ℂ) * Complex.I) x) *
          Complex.exp (-(2 * (Real.pi : ℂ) * Complex.I * (m.1 : ℂ)
            * ((t : ℂ) + (y : ℂ) * Complex.I)))) := by
  obtain ⟨α, β, hα, hβ, hunif⟩ := S.uniform_Ftilde
  -- the difference is periodic of period `1` (second difference equation)
  have hper : ∀ τ : ℂ, 0 < τ.im →
      (fun τ : ℂ => S.Ftilde (τ + 1) x - S.Ftilde τ x) (τ + 1)
        = (fun τ : ℂ => S.Ftilde (τ + 1) x - S.Ftilde τ x) τ := by
    intro τ hτ
    change S.Ftilde (τ + 1 + 1) x - S.Ftilde (τ + 1) x = S.Ftilde (τ + 1) x - S.Ftilde τ x
    have h2 : τ + 1 + 1 = τ + 2 := by ring
    rw [h2]
    have hr := S.recur_Ftilde τ x hτ
    linear_combination hr
  -- strip bound for the difference, from the uniform bound for `F̃`
  have hstrip : ∀ τ : ℂ, 0 < τ.im → -1 ≤ τ.re → τ.re ≤ 0 →
      ‖(fun τ : ℂ => S.Ftilde (τ + 1) x - S.Ftilde τ x) τ‖ ≤ (2 * α) * τ.im ^ (-β) := by
    intro τ hτ h1 h2
    have hτ1 : 0 < (τ + 1).im := by simpa using hτ
    have hre1 : -1 ≤ (τ + 1).re := by
      simp only [Complex.add_re, Complex.one_re]
      linarith
    have hre2 : (τ + 1).re ≤ 1 := by
      simp only [Complex.add_re, Complex.one_re]
      linarith
    have hb1 := hunif (τ + 1) x hτ1 hre1 hre2
    have hb0 := hunif τ x hτ h1 (by linarith)
    have him1 : (τ + 1).im = τ.im := by simp
    rw [him1] at hb1
    calc ‖S.Ftilde (τ + 1) x - S.Ftilde τ x‖
        ≤ ‖S.Ftilde (τ + 1) x‖ + ‖S.Ftilde τ x‖ := norm_sub_le _ _
      _ ≤ α * τ.im ^ (-β) + α * τ.im ^ (-β) := add_le_add hb1 hb0
      _ = (2 * α) * τ.im ^ (-β) := by ring
  obtain ⟨M, hM, hMbound, hMdecay⟩ :=
    FtildeDiff_periodicStripBound (2 * α) β (by linarith) hβ hper hstrip
  have hhol : DifferentiableOn ℂ
      (fun τ : ℂ => S.Ftilde (τ + 1) x - S.Ftilde τ x) {τ : ℂ | 0 < τ.im} := by
    have hmaps : Set.MapsTo (fun τ : ℂ => τ + 1) {τ : ℂ | 0 < τ.im} {τ : ℂ | 0 < τ.im} := by
      intro τ hτ
      simpa using hτ
    have h1 : DifferentiableOn ℂ (fun τ : ℂ => S.Ftilde (τ + 1) x) {τ : ℂ | 0 < τ.im} :=
      (S.holomorphic_Ftilde x).comp (differentiableOn_id.add_const (1 : ℂ)) hmaps
    exact h1.sub (S.holomorphic_Ftilde x)
  obtain ⟨c, hc1, hc2⟩ := FtildeDiff_dirichletExpansionIciOne
    (fun τ : ℂ => S.Ftilde (τ + 1) x - S.Ftilde τ x) hper hhol M hM hMbound hMdecay
  exact ⟨c, hc1, hc2⟩

end

end Work.FunctionalEquations


end Work.CKFinal.Shadow
