/-
# `Work.FTS.PhiStar.Series.eFam_zero_moment` — the `m = 0` mode of the source vanishes

The `m = 0` eigenfunction of `Lzero` is `e_0 = 3 sin θ cos θ = (3/2) sin 2θ`, with eigenvalue
`lam 0 = 0`, and the self-adjoint weight is `cos θ dθ`.  Hence

  `∫_θ F(z,θ)·e_0(θ)·cos θ dθ = 3·∫_θ F(z,θ)·sin θ cos² θ dθ = 3·Fstar F z`,

so the moment condition `Fstar F ≡ 0` (a hypothesis of `bslOp_sol_exists`) says exactly that the
`m = 0` coefficient `cmode 0 F z` of the source vanishes identically.  Consequently the `m = 0`
term of the mode series `psiSeries` is `radGreen α 0 (cmode 0 F) · e_0 = 0`, which is why the
solution automatically satisfies `Fstar Ψ ≡ 0` without any correction (the kernel direction
`z^{-5/α} sin 2θ` is excluded by `HkMem`, so there is no other way to adjust the moment).

The identity is *unconditional*: no integrability hypothesis is needed, because the Bochner
integral is a total function and the chain (interval integral = set integral over `Ioc`, pointwise
rewriting of the integrand, distribution of the constant `3`, `Ioc` vs `Icc` on a null set) uses
only unconditional rewrite rules.
-/
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.PhiStar.Series.Defs
import Submission.Work.Elliptic.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology BigOperators
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Series

set_option autoImplicit false

/-- The `m = 0` Dirichlet eigenfunction of `Lzero`: `e_0(θ) = 3 sin θ cos θ = (3/2) sin (2θ)`. -/
lemma eFam_zero_apply (θ : ℝ) :
    Work.FTS.PhiStar.Gegenbauer.eFam 0 θ = 3 * (Real.sin θ * Real.cos θ) := by
  rw [Work.FTS.PhiStar.Gegenbauer.eFam]
  simp only [Work.FTS.PhiStar.Gegenbauer.gC]
  ring

/-- The `m = 0` coefficient of the slice is `3·Fstar` divided by the (nonzero) normalisation:
in particular it vanishes as soon as the source moment does. -/
theorem eFam_zero_moment (F : ℝ → ℝ → ℝ) {z : ℝ} (h : Work.Elliptic.Fstar F z = 0) :
    Work.FTS.PhiStar.Series.cmode 0 F z = 0 := by
  have hpoint : ∀ θ : ℝ, F z θ * Work.FTS.PhiStar.Gegenbauer.eFam 0 θ * Real.cos θ
      = 3 * (F z θ * Work.Elliptic.sinCos2 θ) := by
    intro θ
    rw [eFam_zero_apply]
    simp only [Work.Elliptic.sinCos2]
    ring
  have hnum : (∫ θ in (0 : ℝ)..(Real.pi / 2),
        F z θ * Work.FTS.PhiStar.Gegenbauer.eFam 0 θ * Real.cos θ)
      = 3 * Work.Elliptic.Fstar F z := by
    rw [intervalIntegral.integral_of_le (by linarith [Real.pi_pos])]
    rw [show (∫ θ in Set.Ioc (0 : ℝ) (Real.pi / 2),
          F z θ * Work.FTS.PhiStar.Gegenbauer.eFam 0 θ * Real.cos θ)
        = ∫ θ in Set.Ioc (0 : ℝ) (Real.pi / 2), 3 * (F z θ * Work.Elliptic.sinCos2 θ) from
      MeasureTheory.setIntegral_congr_fun measurableSet_Ioc (fun θ _ => hpoint θ)]
    rw [MeasureTheory.integral_const_mul]
    congr 1
    simp only [Work.Elliptic.Fstar, Work.Spaces.Iθ]
    exact (MeasureTheory.integral_Icc_eq_integral_Ioc).symm
  rw [Work.FTS.PhiStar.Series.cmode, hnum, h, mul_zero, zero_div]

/-- The radial Green's function of the zero source vanishes. -/
theorem radGreen_zero (α : ℝ) (m : ℕ) (z : ℝ) :
    Work.FTS.PhiStar.Radial.radGreen α m (fun _ => 0) z = 0 := by
  simp [Work.FTS.PhiStar.Radial.radGreen]

end Work.FTS.PhiStar.Series
