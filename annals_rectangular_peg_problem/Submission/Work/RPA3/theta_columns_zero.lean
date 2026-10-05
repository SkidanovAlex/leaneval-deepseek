import Mathlib
import Submission.Work.RPA3.theta_columns_defs
import Submission.Work.RPA3.Symp

namespace Work.RPA3

/-- **D2, independence of the four columns at `ξ = 0`.**  At `ξ = 0` the tubular map is
`θ(τ,x,t,0) = ℓ τ (x,t)`, so the four columns are the four vectors
`∂_xℓ, ∂_tℓ, J ∂_xℓ, J ∂_tℓ`, where `∂_xℓ = deriv (fun y => ℓ τ (y,t)) x` and
`∂_tℓ = deriv (fun s => ℓ τ (x,s)) t`.  Those are linearly independent by the hypotheses
`LagFamilyAll.imm` (the two slice derivatives are independent) and `LagFamilyAll.lag`
(the family is Lagrangian), via `Work.RPA3.lagrangian_independent` in
`Submission/Work/RPA3/Symp.lean`.  There is no restriction on `(τ,x,t)`.

Proof sketch: unfold `ColumnsIndependent`.  For the first two columns, `theta_zero` (`simp`)
identifies `θ(τ,x,t,0)` with `ℓ τ (x,t)`, so the `deriv`s are `∂_xℓ`, `∂_tℓ` verbatim.  For the
third column, `θ(τ,x,t,(u,0)) = ℓ τ (x,t) + u • J(∂_xℓ)` (using `J_add`, `J_smul`, `J_zero` and
`zero_smul`), whose `deriv` at `u = 0` is `J(∂_xℓ)`; the fourth column is analogous.  Then finish
with `lagrangian_independent`. -/
theorem theta_columns_zero (L : Work.RPA3.LagFamilyAll) (τ x t : ℝ) :
    Work.RPA3.ColumnsIndependent L τ x t 0 := by
  show ColumnsIndependent L τ x t ((0 : ℝ), (0 : ℝ))
  intro a b c d h
  -- the first two columns are `∂_xℓ` and `∂_tℓ`, since `θ(τ,·,·,0) = ℓ τ`
  have h1 : deriv (fun y => theta L τ y t (0, 0)) x = deriv (fun y => L.ℓ τ (y, t)) x := by
    simp only [theta_zero]
  have h2 : deriv (fun s => theta L τ x s (0, 0)) t = deriv (fun s => L.ℓ τ (x, s)) t := by
    simp only [theta_zero]
  -- the third column is `J ∂_xℓ`: `u ↦ θ(τ,x,t,(u,0)) = ℓ τ (x,t) + u • J ∂_xℓ`
  have h3 : deriv (fun u => theta L τ x t (u, (0 : ℝ))) 0
      = J (deriv (fun y => L.ℓ τ (y, t)) x) := by
    have hfun : (fun u : ℝ => theta L τ x t (u, 0))
        = fun u : ℝ => L.ℓ τ (x, t) + u • J (deriv (fun y => L.ℓ τ (y, t)) x) := by
      funext u
      simp only [theta, zero_smul, add_zero, J_smul]
    rw [hfun, deriv_const_add, deriv_smul_const differentiableAt_id]
    simp
  -- the fourth column is `J ∂_tℓ`
  have h4 : deriv (fun u => theta L τ x t ((0 : ℝ), u)) 0
      = J (deriv (fun s => L.ℓ τ (x, s)) t) := by
    have hfun : (fun u : ℝ => theta L τ x t (0, u))
        = fun u : ℝ => L.ℓ τ (x, t) + u • J (deriv (fun s => L.ℓ τ (x, s)) t) := by
      funext u
      simp only [theta, zero_smul, zero_add, J_smul]
    rw [hfun, deriv_const_add, deriv_smul_const differentiableAt_id]
    simp
  rw [h1, h2, h3, h4] at h
  exact lagrangian_independent _ _ (L.imm τ x t) (L.lag τ x t) a b c d h

end Work.RPA3
