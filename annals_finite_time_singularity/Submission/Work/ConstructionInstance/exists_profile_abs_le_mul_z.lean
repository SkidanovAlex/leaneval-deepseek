import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.ConstructionInstance.SelfSim
import Submission.Work.ConstructionInstance.Defs
import Submission.Work.ConstructionInstance.g_z_linear_bound
import Submission.Work.ConstructionInstance.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.ConstructionInstance

/-- **The `F_*` part of the profile is `O(z)`**: for `0 < p ≤ 1`, `z ≥ 0` and `θ ∈ [0,π/2]`,

  `|F_*(z,θ)| ≤ 20 z`.

Indeed `F_*(z,θ) = p·(Γ(θ)/c(p))·2z/(1+z)²` with `Γ(θ) ≤ 1`, `c(p) ≥ 1/10` and
`2z/(1+z)² ≤ 2z` for `z ≥ 0`. -/
theorem Fstar_abs_le_mul_z {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) {z : ℝ} (hz : 0 ≤ z)
    {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    |Work.Construction.Fstar p z θ| ≤ 20 * z := by
  have hc := (Work.Spaces.c_bounds p hp hp1).1
  have hcpos : 0 < Work.Spaces.c p := by linarith
  have hG := Work.Spaces.Gam_bounds p θ hp hθ
  have hden : (0 : ℝ) < (1 + z) ^ 2 := by positivity
  have hq0 : 0 ≤ Work.Spaces.Gam p θ / Work.Spaces.c p := div_nonneg hG.1 hcpos.le
  have hq1 : Work.Spaces.Gam p θ / Work.Spaces.c p ≤ 10 := by
    rw [div_le_iff₀ hcpos]; nlinarith [hG.2]
  have hfrac0 : 0 ≤ 2 * z / (1 + z) ^ 2 := by positivity
  have hfrac1 : 2 * z / (1 + z) ^ 2 ≤ 2 * z := by
    rw [div_le_iff₀ hden]
    nlinarith [sq_nonneg z, hz, sq_nonneg (1 + z)]
  have hpc : p * (Work.Spaces.Gam p θ / Work.Spaces.c p) ≤ 10 := by
    have := mul_le_mul hp1 hq1 hq0 (by norm_num : (0 : ℝ) ≤ 1)
    linarith
  have hval : Work.Construction.Fstar p z θ
      = p * (Work.Spaces.Gam p θ / Work.Spaces.c p) * (2 * z / (1 + z) ^ 2) := by
    rw [Work.Construction.Fstar, Work.FM.Fstar]
  rw [hval, abs_of_nonneg (mul_nonneg (mul_nonneg hp.le hq0) hfrac0)]
  calc p * (Work.Spaces.Gam p θ / Work.Spaces.c p) * (2 * z / (1 + z) ^ 2)
      ≤ 10 * (2 * z) := mul_le_mul hpc hfrac1 hfrac0 (by norm_num)
    _ = 20 * z := by ring

theorem exists_profile_abs_le_mul_z {p : ℝ} (hp : 0 < p) (hp1 : p ≤ 1) {g : ℝ → ℝ → ℝ}
    (hquad0 : ∀ θ : ℝ, g 0 θ = 0) (hsmooth : Work.Spaces.SmoothNbhd g) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ z : ℝ, z ∈ Set.Icc (0 : ℝ) 1 → ∀ θ : ℝ,
      |θ| ≤ Real.pi / 2 → |Work.ConstructionInstance.profile p g z θ| ≤ K * z := by
  have hsm2 : ContDiffOn ℝ 2 (Function.uncurry g)
      (Set.Ioi (-1) ×ˢ Set.Ioo (-1) (Real.pi / 2 + 1)) := hsmooth.of_le (by norm_num)
  obtain ⟨K1, hK1, hK1b⟩ := g_z_linear_bound hquad0 hsm2
  refine ⟨K1 + 20, by linarith, ?_⟩
  intro z hz θ hθ
  have hz0 : 0 ≤ z := hz.1
  have hsplit : (K1 + 20) * z = K1 * z + 20 * z := by ring
  rw [hsplit]
  have hkey : ∀ φ : ℝ, φ ∈ Work.Spaces.Iθ →
      |Work.Construction.Fstar p z φ + g z φ| ≤ K1 * z + 20 * z := by
    intro φ hφ
    calc |Work.Construction.Fstar p z φ + g z φ|
        ≤ |Work.Construction.Fstar p z φ| + |g z φ| := abs_add_le _ _
      _ ≤ 20 * z + K1 * z :=
          add_le_add (Fstar_abs_le_mul_z hp hp1 hz0 hφ) (hK1b φ hφ z hz)
      _ = K1 * z + 20 * z := by ring
  rcases le_or_gt 0 θ with hθ0 | hθ0
  · have hθmem : θ ∈ Work.Spaces.Iθ :=
      ⟨hθ0, by rw [abs_of_nonneg hθ0] at hθ; exact hθ⟩
    rw [profile_of_nonneg hθ0]
    exact hkey θ hθmem
  · have hθmem : -θ ∈ Work.Spaces.Iθ :=
      ⟨by linarith, by rw [abs_of_neg hθ0] at hθ; exact hθ⟩
    rw [profile_of_neg (not_le.mpr hθ0), abs_neg]
    exact hkey (-θ) hθmem

end Work.ConstructionInstance
