import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.Nonlinear.Defs
import Submission.Work.FTS.H2.LinfQ
import Submission.Work.FTS.H2.HQ.Glue
import Submission.Work.FTS.H2.HQ.LinfQpt

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.Nonlinear.Pieces.rl1Tools

set_option maxHeartbeats 1600000

/-!
# `gPt` — the pointwise size of the perturbation's elliptic outputs

The elliptic package `Work.FTS.Nonlin.EllPkgG α Ce g Φg` of the perturbation `g` bounds the
`ℋ⁴`-norms of the three coefficients

`ℛ(Φ̃_g)`, `𝒰(Φ̃_g)/sin(2θ)`, `𝒱(Φ̃_g)`   (`Φ̃_g = Work.FTS.Nonlin.PhiTg α g Φg`)

of the nonlinearity by `Ce·|g|_{ℋ⁴}`.  The nonlinear estimates of §8 of the paper need these
coefficients not only in `L²` but *pointwise* inside the quadrant, and this file supplies that:
the interior `L^∞`-`ℋ⁴` trade-off (Elgindi's Corollary `SecondDerivativesBounded`, in the
`RegQ`-form `Work.FTS.H2.LinfQ.mixed_supAbsO_le`, constant `10`),

  `|u(z,θ)| ≤ 10/√(γ-1)·|u|_{ℋ⁴} = 10·√(10/α)·|u|_{ℋ⁴}`   (`z > 0`, `0 < θ < π/2`),

because `γ - 1 = α/10`.  Composing with the `EllPkgG`-bounds and replacing `Ce` by `max Ce 0`
gives the three estimates of `gPt`.
-/

open scoped Real Topology
open MeasureTheory Set Filter

/-- **The interior `L^∞` bound with the explicit constant `10`.**

For `RegQ α 4 f` (`= SmoothQuad f ∧ HkMem α 4 f ∧ BdryTraces α 4 f`, the interior class of
`Submission/Work/FTS/Vocab.lean`) and `0 < α ≤ 1`, the function itself is bounded on the open
quadrant by `10/√(γ-1)·|f|_{ℋ⁴}`.

The bound `supAbsO f ≤ 10/√(γ-1)·|f|_{ℋ⁴}` with the explicit constant `10` is
`Work.FTS.H2.mixed_supAbsO_le` (the `(b,a) = (0,0)` instance); the passage from the interior
*suppremum* to the *pointwise* statement is `Work.FTS.H2.le_supAbsO`, which needs a uniform
bound on the quadrant only in order to know that `supAbsO` is not the junk value attached to an
unbounded set.  Such a bound is available from the pointwise form
`Work.FTS.H2.HQ.LinfQpt` of the same trade-off (with its two one-dimensional Hardy ingredients
`Work.FTS.H2.HardyThetaO` and `Work.FTS.H2.hardyZ_open`), whose constant is unknown but
positive; that is all that is needed. -/
theorem abs_le_ten_sqrt_gam {α : ℝ} {f : ℝ → ℝ → ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hreg : Work.FTS.Nonlin.RegQ α 4 f) :
    ∀ z, 0 < z → ∀ θ, 0 < θ → θ < Real.pi / 2 →
      |f z θ| ≤ 10 / Real.sqrt (Work.Spaces.gam α - 1) * Work.FTS.Nonlin.Xn α f := by
  obtain ⟨C, _hCpos, hL⟩ := Work.FTS.H2.HQ.LinfQpt
  -- the two one-dimensional Hardy inequalities, in the shapes `LinfQpt` asks them for
  have hAng : ∀ (u : ℝ → ℝ → ℝ) (z : ℝ), Work.FTS.LocData.SmoothQuad u →
      z ∈ Set.Ioi (-1) → Tendsto (fun θ => u z θ) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) →
      IntegrableOn (fun σ => (Work.Spaces.pth u z σ) ^ 2
        * Real.sin (2 * σ) ^ (2 - Work.Spaces.gam α)) Work.Spaces.Iθ →
      ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), u z θ ^ 2
        ≤ 100 / (Work.Spaces.gam α - 1) * ∫ σ in Work.Spaces.Iθ,
            Work.Spaces.pth u z σ ^ 2 * Real.sin (2 * σ) ^ (2 - Work.Spaces.gam α) :=
    fun u z hu hz h0 hint => Work.FTS.H2.HardyThetaO α hα hα1 u z hu hz h0 hint
  have hRad : ∀ (v : ℝ → ℝ), ContDiffOn ℝ 1 v (Set.Ioi 0) → Tendsto v atTop (nhds 0) →
      IntegrableOn (fun s => (s * deriv v s) ^ 2 * Work.Spaces.w s ^ 2) Work.Spaces.Iz →
      ∀ z ∈ Set.Ioi 0, v z ^ 2
        ≤ ∫ s in Work.Spaces.Iz, (s * deriv v s) ^ 2 * Work.Spaces.w s ^ 2 :=
    fun v hcd hdec hint => Work.FTS.H2.hardyZ_open hcd hdec hint
  -- a uniform (but numerically unknown) bound on the open quadrant
  have hglobal : ∀ z' θ', 0 < z' → 0 < θ' → θ' < Real.pi / 2 →
      |f z' θ'| ≤ C / Real.sqrt (Work.Spaces.gam α - 1) * Work.FTS.Nonlin.Xn α f := by
    intro z' θ' hz' hθ' hθ''
    have h := hL α f 0 0 hα hα1 (by norm_num) hreg hAng hRad z' hz' θ' hθ' hθ''
    simpa only [Work.Spaces.mixed_zero_left, Work.Spaces.DthIter_zero] using h
  intro z hz θ hθ0 hθ1
  have hsup : |f z θ| ≤ Work.FTS.H2.supAbsO f :=
    Work.FTS.H2.le_supAbsO hz hθ0 hθ1 hglobal
  have hsupb : Work.FTS.H2.supAbsO f ≤ 10 / Real.sqrt (Work.Spaces.gam α - 1)
      * Work.FTS.Nonlin.Xn α f := by
    have h := Work.FTS.H2.mixed_supAbsO_le α f hα hα1 hreg.1 hreg.2.1 hreg.2.2 0 0
      (by norm_num)
    simpa only [Work.Spaces.mixed_zero_left, Work.Spaces.DthIter_zero] using h
  exact le_trans hsup hsupb

/-- `γ - 1 = α/10`, so `10/√(γ-1) = 10·√(10/α)` for `α > 0`. -/
theorem ten_div_sqrt_gam {α : ℝ} (hα : 0 < α) :
    10 / Real.sqrt (Work.Spaces.gam α - 1) = 10 * Real.sqrt (10 / α) := by
  have hαn : 0 < Real.sqrt α := Real.sqrt_pos.mpr hα
  have h10 : 0 < Real.sqrt (10 : ℝ) := Real.sqrt_pos.mpr (by norm_num)
  rw [Work.Spaces.gam_sub_one α,
    Real.sqrt_div (le_of_lt hα) 10,
    Real.sqrt_div (by norm_num : (0 : ℝ) ≤ 10) α]
  field_simp

theorem gPt {α Ce : ℝ} {g Φg : Work.FTS.Galerkin.Fn}
    (hα : 0 < α) (hα1 : α ≤ 1) (hell : Work.FTS.Nonlin.EllPkgG α Ce g Φg) :
    (∀ z, 0 < z → ∀ θ, 0 < θ → θ < Real.pi / 2 →
      |Work.Construction.Rop α (Work.FTS.Nonlin.PhiTg α g Φg) z θ|
        ≤ 10 * Real.sqrt (10 / α) * max Ce 0 * Work.FTS.Nonlin.Xn α g) ∧
    (∀ z, 0 < z → ∀ θ, 0 < θ → θ < Real.pi / 2 →
      |Work.Construction.Uop α (Work.FTS.Nonlin.PhiTg α g Φg) z θ / Work.Construction.s2 θ|
        ≤ 10 * Real.sqrt (10 / α) * max Ce 0 * Work.FTS.Nonlin.Xn α g) ∧
    (∀ z, 0 < z → ∀ θ, 0 < θ → θ < Real.pi / 2 →
      |Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α g Φg) z θ|
        ≤ 10 * Real.sqrt (10 / α) * max Ce 0 * Work.FTS.Nonlin.Xn α g) := by
  obtain ⟨hRreg, hRbd⟩ := hell.R
  obtain ⟨hUreg, hUbd⟩ := hell.U
  obtain ⟨hVreg, hVbd⟩ := hell.V
  have hXg : 0 ≤ Work.FTS.Nonlin.Xn α g := Work.Spaces.HkNorm_nonneg α 4 g
  have hCemax : Ce ≤ max Ce 0 := le_max_left Ce 0
  have hcoef : 0 ≤ 10 / Real.sqrt (Work.Spaces.gam α - 1) :=
    div_nonneg (by norm_num) (Real.sqrt_nonneg _)
  -- the common shape of the three estimates
  have key : ∀ {f : ℝ → ℝ → ℝ}, Work.FTS.Nonlin.RegQ α 4 f →
      Work.FTS.Nonlin.Xn α f ≤ Ce * Work.FTS.Nonlin.Xn α g →
      ∀ z, 0 < z → ∀ θ, 0 < θ → θ < Real.pi / 2 →
        |f z θ| ≤ 10 * Real.sqrt (10 / α) * max Ce 0 * Work.FTS.Nonlin.Xn α g := by
    intro f hreg hbd z hz θ hθ0 hθ1
    have h1 := abs_le_ten_sqrt_gam hα hα1 hreg z hz θ hθ0 hθ1
    have h2 : Work.FTS.Nonlin.Xn α f ≤ max Ce 0 * Work.FTS.Nonlin.Xn α g :=
      le_trans hbd (mul_le_mul_of_nonneg_right hCemax hXg)
    calc |f z θ| ≤ 10 / Real.sqrt (Work.Spaces.gam α - 1) * Work.FTS.Nonlin.Xn α f := h1
      _ ≤ 10 / Real.sqrt (Work.Spaces.gam α - 1)
            * (max Ce 0 * Work.FTS.Nonlin.Xn α g) := mul_le_mul_of_nonneg_left h2 hcoef
      _ = 10 * Real.sqrt (10 / α) * max Ce 0 * Work.FTS.Nonlin.Xn α g := by
          rw [ten_div_sqrt_gam hα]; ring
  exact ⟨key hRreg hRbd, key hUreg hUbd, key hVreg hVbd⟩

end Work.FTS.Nonlinear.Pieces.rl1Tools
