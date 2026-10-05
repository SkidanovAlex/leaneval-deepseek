import Mathlib
import Submission.Work.RPA3.TubularDefs
import Submission.Work.RPA3.Symp

/-!
# RPA3: the tubular map in the standard region

For `|x| ≥ X₀` the Lagrangian family is the zero section, `ℓ τ (x,t) = stdZ x t = ((x,t),(0,0))`.
The tubular map is
`θ(τ,x,t,ξ) = ℓ τ (x,t) + J (ξ₁ ∂_xℓ + ξ₂ ∂_tℓ)`,
and in the standard region the two slice derivatives are the constant vectors `∂_xℓ = (1,0,0,0)`
and `∂_tℓ = (0,1,0,0)`, so `θ = ((x,t),(-ξ₁,-ξ₂))`.

The only non-elementary point is that `std` only pins `ℓ` down on the closed region `{|x| ≥ X₀}`,
so at a boundary point `x = ±X₀` the derivative cannot be read off from an eventual equality:
there we use that the slice is differentiable (it is `C⁸`) and that the derivative is unique on the
one-sided region (`Ici x` or `Iic x`), which is uniquely differentiable at `x`.
-/

open scoped ContDiff Topology

set_option autoImplicit false
noncomputable section

namespace Work.RPA3

/-- `∂_x stdZ(·,t) = (1,0,0,0)`. -/
theorem hasDerivAt_stdZ_x (x t : ℝ) :
    HasDerivAt (fun y : ℝ => stdZ y t) (((1 : ℝ), 0), (0, 0)) x :=
  HasDerivAt.prodMk (HasDerivAt.prodMk (hasDerivAt_id x) (hasDerivAt_const x t))
    (hasDerivAt_const x (0 : ℝ × ℝ))

/-- `∂_t stdZ(x,·) = (0,1,0,0)`. -/
theorem hasDerivAt_stdZ_t (x t : ℝ) :
    HasDerivAt (fun s : ℝ => stdZ x s) ((0, (1 : ℝ)), (0, 0)) t :=
  HasDerivAt.prodMk (HasDerivAt.prodMk (hasDerivAt_const t x) (hasDerivAt_id t))
    (hasDerivAt_const t (0 : ℝ × ℝ))

/-- In the standard region, `∂_xℓ = (1,0,0,0)`. -/
theorem deriv_slice_x (L : LagFamilyAll) (τ t x : ℝ) (hx : L.X0 ≤ |x|) :
    deriv (fun y : ℝ => L.ℓ τ (y, t)) x = ((1, 0), (0, 0)) := by
  have hFdiff : DifferentiableAt ℝ (fun y : ℝ => L.ℓ τ (y, t)) x := by
    have h1 : ContDiff ℝ 8 (fun y : ℝ => (τ, (y, t))) := by fun_prop
    have h2 := L.smooth.comp h1
    exact h2.differentiable (by norm_num) |>.differentiableAt
  have hSx : HasDerivAt (fun y : ℝ => stdZ y t) (((1 : ℝ), 0), (0, 0)) x := hasDerivAt_stdZ_x x t
  rcases lt_or_ge L.X0 |x| with hlt | hle
  · -- `|x| > X₀` is an open condition, so `ℓ` equals `stdZ` near `x`.
    have hnhds : (fun y : ℝ => |y|) ⁻¹' (Set.Ioi L.X0) ∈ 𝓝 x :=
      (continuous_abs.continuousAt).preimage_mem_nhds (isOpen_Ioi.mem_nhds (Set.mem_Ioi.mpr hlt))
    have heq : (fun y : ℝ => L.ℓ τ (y, t)) =ᶠ[𝓝 x] (fun y : ℝ => stdZ y t) :=
      Filter.eventually_of_mem hnhds (fun y hy => L.std τ y t (le_of_lt hy))
    rw [heq.deriv_eq, hSx.deriv]
  · -- boundary case: `|x| = X₀`, and one of `Ici x`, `Iic x` lies in the standard region.
    have hxeq : |x| = L.X0 := le_antisymm hle hx
    by_cases hx0 : 0 ≤ x
    · have hxX0 : x = L.X0 := by rw [← abs_of_nonneg hx0]; exact hxeq
      have hsd : UniqueDiffWithinAt ℝ (Set.Ici x) x := uniqueDiffWithinAt_Ici x
      have hFw : HasDerivWithinAt (fun y : ℝ => L.ℓ τ (y, t))
          (deriv (fun y : ℝ => L.ℓ τ (y, t)) x) (Set.Ici x) x :=
        hFdiff.hasDerivAt.hasDerivWithinAt
      have hSw : HasDerivWithinAt (fun y : ℝ => L.ℓ τ (y, t)) ((1, 0), (0, 0)) (Set.Ici x) x := by
        refine hSx.hasDerivWithinAt.congr ?_ ?_
        · intro y hy
          have hyx : x ≤ y := hy
          have hy' : L.X0 ≤ |y| := by
            rw [abs_of_nonneg (le_trans hx0 hyx)]
            calc L.X0 = x := hxX0.symm
              _ ≤ y := hyx
          exact L.std τ y t hy'
        · exact L.std τ x t hx
      exact UniqueDiffWithinAt.eq_deriv _ hsd hFw hSw
    · have hyneg : x < 0 := lt_of_not_ge hx0
      have hxX0 : x = -L.X0 := by
        have := abs_of_neg hyneg
        linarith [hxeq, this]
      have hsd : UniqueDiffWithinAt ℝ (Set.Iic x) x := uniqueDiffWithinAt_Iic x
      have hFw : HasDerivWithinAt (fun y : ℝ => L.ℓ τ (y, t))
          (deriv (fun y : ℝ => L.ℓ τ (y, t)) x) (Set.Iic x) x :=
        hFdiff.hasDerivAt.hasDerivWithinAt
      have hSw : HasDerivWithinAt (fun y : ℝ => L.ℓ τ (y, t)) ((1, 0), (0, 0)) (Set.Iic x) x := by
        refine hSx.hasDerivWithinAt.congr ?_ ?_
        · intro y hy
          have hyx : y ≤ x := hy
          have hyne : y < 0 := lt_of_le_of_lt hyx hyneg
          have hy' : L.X0 ≤ |y| := by
            rw [abs_of_neg hyne]
            have hLX : L.X0 = -x := by rw [← hxeq, abs_of_neg hyneg]
            linarith
          exact L.std τ y t hy'
        · exact L.std τ x t hx
      exact UniqueDiffWithinAt.eq_deriv _ hsd hFw hSw

/-- In the standard region, `∂_tℓ = (0,1,0,0)`. -/
theorem deriv_slice_t (L : LagFamilyAll) (τ x t : ℝ) (hx : L.X0 ≤ |x|) :
    deriv (fun s : ℝ => L.ℓ τ (x, s)) t = ((0, 1), (0, 0)) := by
  have hS : HasDerivAt (fun s : ℝ => stdZ x s) ((0, (1 : ℝ)), (0, 0)) t := hasDerivAt_stdZ_t x t
  have heq : (fun s : ℝ => L.ℓ τ (x, s)) =ᶠ[𝓝 t] (fun s : ℝ => stdZ x s) :=
    Filter.Eventually.of_forall (fun s => L.std τ x s hx)
  rw [heq.deriv_eq, hS.deriv]

/-- In the standard region `|x| ≥ X₀` the family is `stdZ` and the tubular map is the explicit
translation `((x,t),(-ξ₁,-ξ₂))`: `∂_xθ = (1,0,0,0)` and `∂_tθ = (0,1,0,0)` are constant there, so
`θ = ((x,t),(0,0)) + J(ξ₁(1,0,0,0) + ξ₂(0,1,0,0)) = ((x,t),(-ξ₁,-ξ₂))`. -/
theorem theta_std (L : Work.RPA3.LagFamilyAll) (τ x t : ℝ) (ξ : ℝ × ℝ) (hx : L.X0 ≤ |x|) :
    Work.RPA3.theta L τ x t ξ = ((x, t), (-ξ.1, -ξ.2)) := by
  have hdx := deriv_slice_x L τ t x hx
  have hdt := deriv_slice_t L τ x t hx
  simp only [theta, L.std τ x t hx, hdx, hdt]
  ext <;> simp [stdZ, J]

end Work.RPA3
