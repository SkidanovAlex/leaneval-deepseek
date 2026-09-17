import Mathlib
import Submission.Commons.LinearAlgebra.Matrix.Cartan.E8_wact_sign
import Submission.Commons.LinearAlgebra.Matrix.Cartan.E8_weyl_stab_rho_trivial

namespace Commons.LinearAlgebra.Matrix.Cartan

/-- The mirror form of `wact_reverse`: `wact L` inverts `wact L.reverse` on the other side. -/
lemma wact_reverse_wact (L : List (Fin 8)) (v : Fin 8 → ℤ) :
    wact L (wact L.reverse v) = v := by
  have h := wact_reverse L.reverse v
  rwa [List.reverse_reverse] at h

/-- If two words of simple reflections agree on the Weyl vector `ρ`, whose stabiliser is trivial,
they define the same linear map on `ℤ⁸`. -/
lemma wact_eq_of_wact_rho_eq {L₁ L₂ : List (Fin 8)}
    (h : wact L₁ rhoZ = wact L₂ rhoZ) : ∀ v : Fin 8 → ℤ, wact L₁ v = wact L₂ v := by
  have hM : wact (L₁ ++ L₂.reverse) rhoZ = rhoZ := by
    rw [wact_append, h, wact_reverse]
  have hfun : ∀ v : Fin 8 → ℤ, wact (L₁ ++ L₂.reverse) v = v :=
    wact_stab_rho_trivial _ hM
  intro v
  have h1 : wact L₂.reverse (wact L₁ v) = v := by
    have hv := hfun v
    rwa [wact_append] at hv
  calc wact L₁ v = wact L₂ (wact L₂.reverse (wact L₁ v)) := (wact_reverse_wact L₂ (wact L₁ v)).symm
    _ = wact L₂ v := by rw [h1]

/-- **The sign `ε(w)` is well defined on the Weyl orbit of `ρ`.**  If two words `L₁`, `L₂` of simple
reflections take the Weyl vector `ρ = ω₀ + ⋯ + ω₇` to the same weight, then they have the same length
parity.  (Consequently the sign `(-1)^{ℓ(w)}` is a function of the weight `wρ` alone.) -/
theorem E8_wact_sign_rho {L₁ L₂ : List (Fin 8)}
    (h : Commons.LinearAlgebra.Matrix.Cartan.wact L₁ Commons.LinearAlgebra.Matrix.Cartan.rhoZ
       = Commons.LinearAlgebra.Matrix.Cartan.wact L₂ Commons.LinearAlgebra.Matrix.Cartan.rhoZ) :
    (-1 : ℤ) ^ L₁.length = (-1 : ℤ) ^ L₂.length :=
  E8_wact_sign (wact_eq_of_wact_rho_eq h)

end Commons.LinearAlgebra.Matrix.Cartan
