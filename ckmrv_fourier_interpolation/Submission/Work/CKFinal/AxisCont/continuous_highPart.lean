import Mathlib
import Submission.Work.LayerCont.GcuspHolomorphic

/-!
# Continuity of the high (closed form) part of the CKMRV layer

The closed form `highPart G τ r` of `4 sin²(πr²/2) ∫_1^∞ 𝒢(τ,it)e^{-πr²t}dt` is (see
`Work.Asymptotics.highPart`) the linear combination

  `λ ψ(λ) e^{-λ} G₀₀ τ + i ψ(λ)(λ+1) e^{-λ} G₀₁ τ
     + μ ψ(μ) e^{-μ} G₁₀ τ + i ψ(μ)(μ+1) e^{-μ} G₁₁ τ`

of the four coefficient functions `G i j`, with `λ = πr²`, `μ = πr² - 2π` and the regularising
factor `ψ = psi1` depending on `r` only.  Hence for `G = Gcusp ℓ d` (the CKMRV cusp coefficients,
which are holomorphic, in particular continuous, in `τ` by
`Work.LayerCont.mdifferentiable_Gcusp`) the map `τ ↦ highPart (Gcusp ℓ d) τ r` is continuous.
-/

namespace Work.CKFinal.AxisCont

/-- **Continuity of the high part in `τ`.**  The coefficients of the linear combination
defining `highPart` depend only on `r`; each `Gcusp ℓ d i j` is holomorphic, hence continuous. -/
theorem continuous_highPart (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (r : ℝ) :
    Continuous (fun τ : UpperHalfPlane =>
      Work.Asymptotics.highPart (Work.Asymptotics.Gcusp ℓ d) τ r) := by
  have hGc : ∀ i j : Fin 2,
      Continuous (fun τ : UpperHalfPlane => Work.Asymptotics.Gcusp ℓ d i j τ) :=
    fun i j => (Work.LayerCont.mdifferentiable_Gcusp ℓ d hd i j).continuous
  simp only [Work.Asymptotics.highPart]
  fun_prop

end Work.CKFinal.AxisCont
