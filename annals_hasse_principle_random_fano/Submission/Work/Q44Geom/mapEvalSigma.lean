import Mathlib
import Submission.Work.Q44Geom.defs
import Submission.Work.Q44Geom.taylorDefs

set_option autoImplicit false
noncomputable section

open MvPolynomial

namespace Work.Q44Geom

theorem mapEvalSigma (w : Fin 3 → Fin 5 → ℚ) (b₁ b₂ : Fin 5 → ℚ)
    (f : MvPolynomial (Fin 5) ℚ) (p : Fin 3 → ℚ) :
    MvPolynomial.map (MvPolynomial.eval p) (Work.Q44Geom.sigma w b₁ b₂ f)
      = Work.Q44Geom.taylorHom (Work.Q44Geom.substPoint w b₁ b₂ p 0) b₁ b₂ f := by
  have h : (MvPolynomial.mapAlgHom (MvPolynomial.aeval (R := ℚ) p)).comp (sigma w b₁ b₂)
      = taylorHom (substPoint w b₁ b₂ p 0) b₁ b₂ := by
    rw [sigma, taylorHom, MvPolynomial.comp_aeval]
    congr 1
    funext i
    have hsub : substPoint w b₁ b₂ p 0 i = ∑ a : Fin 3, p a * w a i := by
      simp [substPoint]
    rw [MvPolynomial.mapAlgHom_apply]
    rw [show (↑(MvPolynomial.aeval (R := ℚ) p) : MvPolynomial (Fin 3) ℚ →+* ℚ)
        = MvPolynomial.eval p from rfl]
    simp only [taylorSubst, map_add, map_mul, map_C, map_X, hsub, MvPolynomial.eval_C,
      Work.Q44Geom.eval_linForm]
  calc (MvPolynomial.map (MvPolynomial.eval p)) (sigma w b₁ b₂ f)
      = ((MvPolynomial.mapAlgHom (MvPolynomial.aeval (R := ℚ) p)).comp (sigma w b₁ b₂)) f := rfl
    _ = (taylorHom (substPoint w b₁ b₂ p 0) b₁ b₂) f := by rw [h]

end Work.Q44Geom
