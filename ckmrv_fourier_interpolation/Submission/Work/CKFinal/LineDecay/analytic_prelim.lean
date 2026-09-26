import Mathlib
import Submission.Work.CKFinal.LineDecay.LamDefs
import Submission.Work.CKFinal.LineDecay.lam_analytic_pieces

namespace Work.CKFinal.LineDecay

/-- **The elementary entire functions of the `λ = π r²` picture.**

`lamS z = 2 - e^{iz} - e^{-iz}` is entire, `psi1C z = 2 ∫_0^1 (1-s) cos (s z) ds` is entire (a
parametric integral over the compact interval `[0,1]`, bounded on every ball), and
for every coefficient family `G : Fin 2 → Fin 2 → UpperHalfPlane → ℂ` and every
`τ : UpperHalfPlane` the function `z ↦ highPartC G τ z` — a finite sum of products of `z`,
`psi1C z`, `psi1C (z - 2π)`, `exp (-z)`, `exp (-(z - 2π))` with the constants `G i j τ` — is
entire. -/
theorem analytic_prelim :
    AnalyticOnNhd ℂ Work.CKFinal.lamS Set.univ
    ∧ AnalyticOnNhd ℂ Work.CKFinal.psi1C Set.univ
    ∧ (∀ (G : Fin 2 → Fin 2 → UpperHalfPlane → ℂ) (τ : UpperHalfPlane),
        AnalyticOnNhd ℂ (fun z : ℂ => Work.CKFinal.highPartC G τ z) Set.univ) :=
  ⟨analyticOnNhd_lamS, analyticOnNhd_psi1C, fun G τ => analyticOnNhd_highPartC G τ⟩

end Work.CKFinal.LineDecay
