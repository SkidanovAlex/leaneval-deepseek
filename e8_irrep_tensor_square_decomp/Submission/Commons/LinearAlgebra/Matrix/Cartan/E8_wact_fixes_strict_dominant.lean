import Mathlib
import Submission.Commons.LinearAlgebra.Matrix.Cartan.E8_weyl_stab_rho_trivial
import Submission.Commons.LinearAlgebra.Matrix.Cartan.E8_dominant_unique

namespace Commons.LinearAlgebra.Matrix.Cartan

/-- **A strictly dominant weight has trivial stabiliser in the Weyl group.**  If a word `L` of
simple reflections fixes a weight `x` all of whose fundamental-weight coordinates are `≥ 1`, then
`wact L` is the identity endomorphism of `ℤ⁸`. -/
theorem E8_wact_fixes_strict_dominant {L : List (Fin 8)} {x : Fin 8 → ℤ} (hx : ∀ i, 1 ≤ x i)
    (h : Commons.LinearAlgebra.Matrix.Cartan.wact L x = x) (v : Fin 8 → ℤ) :
    Commons.LinearAlgebra.Matrix.Cartan.wact L v = v := by
  by_cases hrho : wact L rhoZ = rhoZ
  · exact wact_stab_rho_trivial L hrho v
  · exfalso
    obtain ⟨i, hi⟩ := weyl_descent_self L hrho
    have hpair : bil x (wact L (alpha i)) = x i := by
      have h1 : bil (wact L x) (wact L (alpha i)) = bil x (alpha i) := bil_wact L x (alpha i)
      rw [h] at h1
      rw [h1, bil_alpha_right]
    have hle : bil x (wact L (alpha i)) ≤ 0 := by
      simp only [bil, dotProduct]
      exact Finset.sum_nonpos (fun j _ =>
        mul_nonpos_of_nonneg_of_nonpos (by linarith [hx j]) (hi j))
    have hxi : 1 ≤ x i := hx i
    omega

end Commons.LinearAlgebra.Matrix.Cartan
