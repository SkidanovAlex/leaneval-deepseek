import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.Nonlinear.Pieces.RNP.row15aux.Gam_deriv_bounds
import Submission.Work.Spaces.mixed_mul_le
import Submission.Work.FTS.LocData.SmoothQuad_Fstar
import Submission.Work.FTS.LocData.SmoothChain
import Submission.Work.Spaces.c_bounds
import Submission.Work.FTS.Nonlinear.Pieces.RNP.row15aux.mixedSepDecomp
import Submission.Work.FTS.Nonlinear.Pieces.RNP.row15aux.sinTwoInvBound

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.Nonlinear.Pieces.RNP.row15aux

/-!
# `row15_PthFstarMixed`: the mixed-derivative bound for `∂_θ F_*`

Row 15 of the nonlinear estimates needs a pointwise bound on the mixed derivatives
`D_z^l D_θ^m (∂_θF_*)` of the angular derivative of the profile
`F_*(z,θ) = α (Γ(θ)/c(α)) · F̲(z)` (`Work.Construction.Fstar`, `F̲ = Work.FM.Fstar`),
because `N₂^{ss} = -2·U(Φ̃_*)·∂_θF_*`.

The whole estimate rests on the **separation of variables**: `∂_θF_*` is the product of an
angular factor and a radial one,

  `∂_θF_*(z,θ) = (α/c(α)) · Γ'(θ) · F̲(z)`   (`Work.Construction.pth_Fstar_eq`),

and the two operators `D_θ = sin(2θ)∂_θ` and `D_z = z∂_z` act on their own factor
(`mixedSepDecomp`):

  `D_z^l D_θ^m (∂_θF_*)(z,θ)
     = (α/c(α)) · (D_θ^m Γ')(θ) · ((OpZ)^l F̲)(z)`.

So it remains to bound the angular factor, which is exactly the first half of
`Gam_deriv_bounds` (`|D_θ^m Γ'| ≤ C α Γ (cot θ + tan θ + 1)`, `m ≤ 4`), together with the
elementary `cot θ + tan θ + 1 ≤ 3/sin(2θ)` (`sinTwoInvBound`) and `1/c(α) ≤ 10`
(`c_bounds`).
-/

theorem row15_PthFstarMixed : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ), 0 < α → α ≤ 1 → ∀ (z : ℝ), 0 < z → ∀ (θ : ℝ), 0 < θ → θ < Real.pi / 2 → ∀ (m l : ℕ), m + l ≤ 4 → |Work.Spaces.mixed l m (Work.Spaces.pth (Work.Construction.Fstar α)) z θ| ≤ C * α ^ 2 * Work.Spaces.Gam α θ * (Real.sin (2 * θ))⁻¹ * |(Work.Spaces.OpZ^[l]) Work.FM.Fstar z| := by
  obtain ⟨Cg, hCgpos, hCg⟩ := Gam_deriv_bounds.1
  refine ⟨30 * Cg, by positivity, ?_⟩
  intro α hα hα1 z hz θ hθ0 hθ1 m l hml
  have hGam0 : 0 ≤ Work.Spaces.Gam α θ :=
    (Work.Spaces.Gam_bounds α θ hα ⟨le_of_lt hθ0, le_of_lt hθ1⟩).1
  have hc : 0 < Work.Spaces.c α := by
    have h := (Work.Spaces.c_bounds α hα hα1).1
    linarith
  -- the prefactor `α/c(α)` is at most `10 α`
  have hk : |α * (Work.Spaces.c α)⁻¹| ≤ 10 * α := by
    rw [abs_of_nonneg (mul_nonneg (le_of_lt hα) (inv_nonneg.mpr (le_of_lt hc)))]
    have hinv : (Work.Spaces.c α)⁻¹ ≤ 10 := by
      rw [inv_eq_one_div, div_le_iff₀ hc]
      linarith [(Work.Spaces.c_bounds α hα hα1).1]
    nlinarith [hα, hinv]
  -- the angular jet bound on `Γ'`
  have hdth : |Work.Spaces.dthU^[m] (fun t => deriv (fun s => Work.Spaces.Gam α s) t) θ|
      ≤ Cg * α * Work.Spaces.Gam α θ
          * (Real.cos θ / Real.sin θ + Real.sin θ / Real.cos θ + 1) :=
    hCg α θ hα hα1 ⟨hθ0, hθ1⟩ m (by omega)
  -- separation of variables of `∂_θF_*`
  have hpth : Work.Spaces.pth (Work.Construction.Fstar α)
      = fun z θ => ((α * (Work.Spaces.c α)⁻¹) * deriv (fun s => Work.Spaces.Gam α s) θ)
          * Work.FM.Fstar z := by
    funext z θ
    rw [Work.Construction.pth_Fstar_eq hα, div_eq_mul_inv]
    ring
  have h1 := mixedSepDecomp l m
    (fun θ => (α * (Work.Spaces.c α)⁻¹) * deriv (fun s => Work.Spaces.Gam α s) θ)
    Work.FM.Fstar z θ
  rw [Work.Spaces.dthU_iter_const_mul] at h1
  have hfac : Work.Spaces.mixed l m (Work.Spaces.pth (Work.Construction.Fstar α)) z θ
      = ((α * (Work.Spaces.c α)⁻¹)
          * Work.Spaces.dthU^[m] (fun t => deriv (fun s => Work.Spaces.Gam α s) t) θ)
        * Work.Spaces.OpZ^[l] Work.FM.Fstar z := by
    rw [hpth, h1]
  calc |Work.Spaces.mixed l m (Work.Spaces.pth (Work.Construction.Fstar α)) z θ|
      = |α * (Work.Spaces.c α)⁻¹| *
          |Work.Spaces.dthU^[m] (fun t => deriv (fun s => Work.Spaces.Gam α s) t) θ| *
          |Work.Spaces.OpZ^[l] Work.FM.Fstar z| := by
        rw [hfac, abs_mul, abs_mul]
    _ ≤ (10 * α) * (Cg * α * Work.Spaces.Gam α θ
            * (Real.cos θ / Real.sin θ + Real.sin θ / Real.cos θ + 1)) *
          |Work.Spaces.OpZ^[l] Work.FM.Fstar z| := by
        refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
        exact mul_le_mul hk hdth (abs_nonneg _) (by positivity)
    _ ≤ (10 * α) * (Cg * α * Work.Spaces.Gam α θ * (3 * (Real.sin (2 * θ))⁻¹)) *
          |Work.Spaces.OpZ^[l] Work.FM.Fstar z| := by
        refine mul_le_mul_of_nonneg_right ?_ (abs_nonneg _)
        refine mul_le_mul_of_nonneg_left ?_ (by positivity : (0:ℝ) ≤ 10 * α)
        exact mul_le_mul_of_nonneg_left (sinTwoInvBound hθ0 hθ1)
          (mul_nonneg (mul_nonneg (le_of_lt hCgpos) (le_of_lt hα)) hGam0)
    _ = (30 * Cg) * α ^ 2 * Work.Spaces.Gam α θ * (Real.sin (2 * θ))⁻¹ *
          |Work.Spaces.OpZ^[l] Work.FM.Fstar z| := by ring

end Work.FTS.Nonlinear.Pieces.RNP.row15aux
