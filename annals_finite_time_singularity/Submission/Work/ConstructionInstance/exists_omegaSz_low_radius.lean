import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.ConstructionInstance.exists_omegaSz_low

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.ConstructionInstance

/-!
# The profile's lower bound at a prescribed self-similar scale, inside a ball of radius `L`

This is the radius-refined companion of `exists_omegaSz_low`: there we produced *some* point with
self-similar variable `1`; here we must additionally keep that point inside the cylinder of
radius `L`.  The witness is again on the ray `x = (t,0,t)` with `(√2 t)^p = s`, for which
`ρ(x) = √2 t = s^{1/p}`; the hypothesis `s^{1/p} ≤ L` is exactly the requirement `ρ(x) ≤ L`.
-/

theorem exists_omegaSz_low_radius {p L s : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) {g : ℝ → ℝ → ℝ}
    {Cg : ℝ} (hgbdd : ∀ z θ : ℝ, 0 ≤ z → θ ∈ Work.Spaces.Iθ → |g z θ| ≤ Cg)
    (hsmall : Cg ≤ p * Work.Spaces.Gam p (Real.pi / 4) / (4 * Work.Spaces.c p))
    (hs : 0 < s) (hsL : s ^ (1 / p) ≤ L) :
    ∃ x : Work.ConstructionInstance.R3, Work.Cyl.rho x ≤ L ∧
      p * Work.Spaces.Gam p (Real.pi / 4) / (4 * Work.Spaces.c p)
        ≤ ‖Work.ConstructionInstance.omegaSz p g (Work.Cyl.rho x ^ p / s) x‖ := by
  -- The scale `t` with `√2 · t = s^{1/p}` (hence `(√2 t)^p = s`).
  have hspos : 0 < s ^ (1 / p) := Real.rpow_pos_of_pos hs (1 / p)
  have hsqrt2 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  set t : ℝ := s ^ (1 / p) / Real.sqrt 2 with htdef
  have ht : 0 < t := by rw [htdef]; exact div_pos hspos hsqrt2
  have hbase : Real.sqrt 2 * t = s ^ (1 / p) := by
    rw [htdef]; field_simp
  -- `(√2 t)^p = s`.
  have htp : (Real.sqrt 2 * t) ^ p = s := by
    rw [hbase, ← Real.rpow_mul (le_of_lt hs) (1 / p) p, one_div,
      inv_mul_cancel₀ (ne_of_gt hp), Real.rpow_one]
  -- `ρ(t,0,t) = √2 · t = s^{1/p} ≤ L`.
  have hrho : Work.Cyl.rho (!₂[t, 0, t] : R3) = Real.sqrt 2 * t := by
    rw [Work.Cyl.rho, Work.Cyl.radSq, Work.Cyl.axial]
    simp
    rw [show t ^ 2 + t ^ 2 = 2 * t ^ 2 by ring, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2),
      Real.sqrt_sq ht.le]
  refine ⟨!₂[t, 0, t], ?_, ?_⟩
  · rw [hrho, hbase]; exact hsL
  · -- The self-similar variable of that point is `1`.
    have hz : Work.Cyl.rho (!₂[t, 0, t] : R3) ^ p / s = 1 := by
      rw [hrho, htp, div_self (ne_of_gt hs)]
    -- The value of the vorticity on the ray: `F(1,π/4) • e₁`, and `‖e₁‖ = 1`.
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
