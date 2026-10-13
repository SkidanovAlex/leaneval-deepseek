import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.H2.ModalSolR.RGWeakAux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.H2.ModalSolR.RGWeak

open Work.EllipticEst.ModalSolution.RadGreenWeak

theorem Fgen_algebra {α : ℝ} (hα : 0 < α) (m : ℕ) {c ψ : ℝ → ℝ} :
    ∀ t : ℝ, 0 < t →
      Work.EllipticEst.ModalSolution.RadGreenWeak.srcM α m c t *
          Work.FTS.H2.ModalSolR.RGWeak.Fgen α (Work.EllipticEst.ModalSolution.RadGreenWeak.sM α m) ψ t
        - Work.EllipticEst.ModalSolution.RadGreenWeak.srcP α m c t *
          Work.FTS.H2.ModalSolR.RGWeak.Fgen α (Work.EllipticEst.ModalSolution.RadGreenWeak.sP α m) ψ t
      = α * (4 * (m : ℝ) + 5) *
          (c t * ψ t * Work.EllipticEst.ModalSolution.RadGreenWeak.wgt α t) := by
  intro t ht
  have hα0 : α ≠ 0 := ne_of_gt hα
  -- The two indicial exponents, as opaque atoms (so that `ring` can reassociate products;
  -- it cannot see through the division by `α`), together with their values `-(2m+5)/α`, `2m/α`.
  set M : ℝ := -(2 * (m : ℝ) + 5) / α with hM
  set P : ℝ := 2 * (m : ℝ) / α with hP
  have hsM : sM α m = M := by rw [hM]; rfl
  have hsP : sP α m = P := by rw [hP]; rfl
  -- `srcM`, `srcP` in terms of `M`, `P`: the exponents `(2m+5)/α = -M`, `-(2m)/α = -P`.
  have hsrcM : srcM α m c t = c t * t ^ (-M - 1) := by
    simp only [srcM]
    rw [show (2 * (m : ℝ) + 5) / α - 1 = -M - 1 from by rw [hM]; ring]
  have hsrcP : srcP α m c t = c t * t ^ (-P - 1) := by
    simp only [srcP]
    rw [show -(2 * (m : ℝ) / α) - 1 = -P - 1 from by rw [hP]]
  -- Merging the powers of `t`: `t^{-R-1}·(t^R·X - R·t^{R-1}·Y) = X/t - R·Y/t²`.
  have hcomb (R : ℝ) : t ^ (-R - 1) * (t ^ R * deriv ψ t - R * t ^ (R - 1) * ψ t)
      = deriv ψ t * t ^ (-1:ℝ) - R * ψ t * t ^ (-2:ℝ) := by
    rw [mul_sub]
    rw [show t ^ (-R - 1) * (t ^ R * deriv ψ t)
          = deriv ψ t * (t ^ (-R - 1) * t ^ R) from by ring,
        show t ^ (-R - 1) * (R * t ^ (R - 1) * ψ t)
          = R * ψ t * (t ^ (-R - 1) * t ^ (R - 1)) from by ring]
    rw [show t ^ (-R - 1) * t ^ R = t ^ (-1:ℝ) from by rw [← Real.rpow_add ht]; congr 1; ring,
        show t ^ (-R - 1) * t ^ (R - 1) = t ^ (-2:ℝ) from by rw [← Real.rpow_add ht]; congr 1; ring]
  have htermM : srcM α m c t * Fgen α M ψ t
      = c t * pwt α t * (deriv ψ t * t ^ (-1:ℝ) - M * ψ t * t ^ (-2:ℝ)) := by
    rw [hsrcM, Fgen]
    rw [show (c t * t ^ (-M - 1)) * (pwt α t * (t ^ M * deriv ψ t - M * t ^ (M - 1) * ψ t))
        = c t * pwt α t
            * (t ^ (-M - 1) * (t ^ M * deriv ψ t - M * t ^ (M - 1) * ψ t)) from by ring]
    rw [hcomb M]
  have htermP : srcP α m c t * Fgen α P ψ t
      = c t * pwt α t * (deriv ψ t * t ^ (-1:ℝ) - P * ψ t * t ^ (-2:ℝ)) := by
    rw [hsrcP, Fgen]
    rw [show (c t * t ^ (-P - 1)) * (pwt α t * (t ^ P * deriv ψ t - P * t ^ (P - 1) * ψ t))
        = c t * pwt α t
            * (t ^ (-P - 1) * (t ^ P * deriv ψ t - P * t ^ (P - 1) * ψ t)) from by ring]
    rw [hcomb P]
  -- The difference of the two brackets kills the `deriv ψ t` terms and leaves `(P - M)ψ t/t²`.
  have hdiff : (deriv ψ t * t ^ (-1:ℝ) - M * ψ t * t ^ (-2:ℝ))
      - (deriv ψ t * t ^ (-1:ℝ) - P * ψ t * t ^ (-2:ℝ))
      = (P - M) * ψ t * t ^ (-2:ℝ) := by ring
  set D : ℝ := (4 * (m : ℝ) + 5) / α with hD
  have hPM : P - M = D := by rw [hP, hM, hD]; field_simp; ring
  have hαD : α ^ 2 * D = α * (4 * (m : ℝ) + 5) := by rw [hD]; field_simp
  have ht2 : t ^ 2 * t ^ (-2:ℝ) = 1 := by
    rw [show t ^ (-2:ℝ) = (t ^ (2:ℕ))⁻¹ by
          rw [Real.rpow_neg (le_of_lt ht), Real.rpow_two]]
    exact mul_inv_cancel₀ (pow_ne_zero 2 (ne_of_gt ht))
  calc srcM α m c t * Fgen α (sM α m) ψ t - srcP α m c t * Fgen α (sP α m) ψ t
      = c t * pwt α t *
          ((deriv ψ t * t ^ (-1:ℝ) - M * ψ t * t ^ (-2:ℝ))
            - (deriv ψ t * t ^ (-1:ℝ) - P * ψ t * t ^ (-2:ℝ))) := by
        rw [hsM, hsP, htermM, htermP, ← mul_sub]
    _ = c t * pwt α t * ((P - M) * ψ t * t ^ (-2:ℝ)) := by rw [hdiff]
    _ = α * (4 * (m : ℝ) + 5) * (c t * ψ t * wgt α t) := by
        rw [hPM, pwt]
        calc c t * (α ^ 2 * (t ^ 2 * wgt α t)) * (D * ψ t * t ^ (-2:ℝ))
            = (α ^ 2 * D) * (t ^ 2 * t ^ (-2:ℝ)) * (c t * ψ t * wgt α t) := by ring
          _ = (α * (4 * (m : ℝ) + 5)) * 1 * (c t * ψ t * wgt α t) := by rw [hαD, ht2]
          _ = α * (4 * (m : ℝ) + 5) * (c t * ψ t * wgt α t) := by ring

end Work.FTS.H2.ModalSolR.RGWeak
