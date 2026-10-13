import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.ConstructionInstance.Defs
import Submission.Work.ConstructionInstance.exists_sqrt_two_mul_rpow
import Submission.Work.ConstructionInstance.omegaSz_ray_quad
import Submission.Work.ConstructionInstance.profile_abs_lower_one

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The profile's lower bound at a prescribed self-similar scale

The reference profile `F_* = p·(Γ(θ)/c(p))·F_{*,rad}(z)` is maximal in the self-similar variable
at `z = 1`, where `F_{*,rad}(1) = 2·1/(1+1)² = 1/2`, and is maximal in the angle at `θ = π/4`,
where `Γ(π/4) = (sin(π/4)cos²(π/4))^{p/3} > 0`.  Hence at `(z,θ) = (1,π/4)`

  `F_*(1,π/4) = p·Γ(π/4)/(2c(p))`,

and a perturbation `g` with `|g(1,π/4)| ≤ Cg ≤ p·Γ(π/4)/(4c(p))` can lower the absolute value
only down to `p·Γ(π/4)/(4c(p))`.

This file transfers that pointwise bound to the physical vorticity: the ray `x = (t,0,t)`,
`t > 0`, has `ρ(x) = √2·t`, `θ(x) = π/4` and `e_θ(x) = e₁`, so choosing `t` with `(√2 t)^p = s`
(which exists by `exists_sqrt_two_mul_rpow`) gives a point whose self-similar variable is exactly
`ρ(x)^p/s = 1`, where the profile bound applies:

  `p·Γ(π/4)/(4c(p)) ≤ ‖omegaSz p g (ρ(x)^p/s) x‖`.
-/

noncomputable section

open scoped Matrix

namespace Work.ConstructionInstance

/-- **The profile's lower bound at a point, at any prescribed scale**: taking the direction
`θ = π/4` and the scale `z = 1` (`F_*(1,π/4) = p·Γ(π/4)/(2c)`, `FM.Fstar 1 = 1/2`), the
perturbation can shift the value by at most `Cg`, so `|F| ≥ pΓ(π/4)/(4c)` whenever
`Cg ≤ pΓ(π/4)/(4c)`.  The point `x` is chosen so that `ρ(x)^p/s = 1` and `θ(x) = π/4`. -/
theorem exists_omegaSz_low {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) {g : ℝ → ℝ → ℝ} {Cg : ℝ}
    (hgbdd : ∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ → |g z θ| ≤ Cg)
    (hsmall : Cg ≤ p * Work.Spaces.Gam p (Real.pi / 4) / (4 * Work.Spaces.c p))
    {s : ℝ} (hs : 0 < s) :
    ∃ x : Work.ConstructionInstance.R3,
      p * Work.Spaces.Gam p (Real.pi / 4) / (4 * Work.Spaces.c p)
        ≤ ‖Work.ConstructionInstance.omegaSz p g (Work.Cyl.rho x ^ p / s) x‖ := by
  -- The scale `t` with `(√2 t)^p = s`, i.e. `ρ(t,0,t)^p = s`.
  obtain ⟨t, ht, htp⟩ := exists_sqrt_two_mul_rpow (p := p) (s := s) hp hs
  refine ⟨!₂[t, 0, t], ?_⟩
  -- `ρ(t,0,t) = √(t² + t²) = √2 · t`.
  have hrho : Work.Cyl.rho (!₂[t, 0, t] : R3) = Real.sqrt 2 * t := by
    rw [Work.Cyl.rho, Work.Cyl.radSq, Work.Cyl.axial]
    simp
    rw [show t ^ 2 + t ^ 2 = 2 * t ^ 2 by ring, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2),
      Real.sqrt_sq ht.le]
  -- the self-similar variable of that point is `1`.
  have hz : Work.Cyl.rho (!₂[t, 0, t] : R3) ^ p / s = 1 := by
    rw [hrho, htp, div_self (ne_of_gt hs)]
  -- the value of the vorticity on the ray: `F(1,π/4) • e₁`, and `‖e₁‖ = 1`.
  have hray := omegaSz_ray_quad (p := p) (z := 1) (t := t) ht g
  have he1 : ‖(!₂[0, 1, 0] : R3)‖ = 1 := by
    rw [EuclideanSpace.norm_eq]
    simp only [Fin.sum_univ_three]
    norm_num
  have hnorm : ‖omegaSz p g (Work.Cyl.rho (!₂[t, 0, t] : R3) ^ p / s)
        (!₂[t, 0, t] : R3)‖ = |profile p g 1 (Real.pi / 4)| := by
    rw [hz, hray, norm_smul, Real.norm_eq_abs, he1, mul_one]
  calc p * Work.Spaces.Gam p (Real.pi / 4) / (4 * Work.Spaces.c p)
      ≤ |profile p g 1 (Real.pi / 4)| := profile_abs_lower_one hp hp1 hgbdd hsmall
    _ = ‖omegaSz p g (Work.Cyl.rho (!₂[t, 0, t] : R3) ^ p / s) (!₂[t, 0, t] : R3)‖ :=
        hnorm.symm

end Work.ConstructionInstance
