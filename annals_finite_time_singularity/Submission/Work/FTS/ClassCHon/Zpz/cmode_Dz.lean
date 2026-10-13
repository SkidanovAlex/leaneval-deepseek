/-
Copyright: work module for the Elgindi finite-time singularity project.

# `cmode_Dz` — compatibility of the mode coefficients with `D_z = z ∂_z`

The theorem proved here is

  `cmode m (D_z F) z = z · d/dz (cmode m F) z`   for `z > 0`,

for a source `F` which is `C^∞` on the open quadrant and honest in `ℋ²`
(`Work.FTS.EllipticEst.SmoothOpen`, `Work.Spaces.HkMem α 2 F`).

Since `cmode m G z = numW m G z / D_m` with `D_m = (2m+2)(2m+3)/(4m+5) > 0`
(`Zpz/Basic.lean`) and `numW m (D_z F) z = z · pwF m F z`, the statement reduces to the
differentiation under the `θ`-integral sign of `numW m F`, whose derivative is
`pwF m F z = ∫_θ ∂_zF(z,θ)·φ_m(θ) dθ`.

The mathematical work is distributed over the modules of this directory:

* `Zpz/Defs.lean` — the vocabulary `phiW`, `numW`, `pwF`, `Hsq`;
* `Zpz/Basic.lean` — `cmode` in terms of `numW`, and `numW_Dz`;
* `Zpz/Ftc.lean` — the two-fold `z`-fundamental-theorem bound;
* `Zpz/Slope.lean` — the difference-quotient bound `slope_bound`;
* `Zpz/Deriv.lean` — `numW_hasDerivAt`, the limit of the slope;
* `Zpz/Aux/*.lean` — the four slice statements extracted from `SmoothOpen F` and
  `HkMem α 2 F`: the `L¹`-ness of `τ ↦ ∫_θ √(HkIntegrand α 2 F τ θ)`, the pointwise second-order
  slice bound, its Tonelli product-integrability, and the `L¹`-ness of the `φ_m`-weighted slices.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.PhiStar.Series.Defs
import Submission.Work.FTS.PhiStar.Honesty.cmode_variation_le
import Submission.Work.FTS.PhiStar.Honesty.continuousOn_cmode_of_hkMem_one
import Submission.Work.FTS.PhiStar.Honesty.pz_abs_slice_le_sqrt_Hk
import Submission.Work.FTS.PhiStar.Honesty.integral_swap_pz_abs
import Submission.Work.FTS.PhiStar.Honesty.slice_abs_integrable
import Submission.Work.FTS.OpenPkg.Basic
import Submission.Work.FTS.ClassCHon.Zpz.Defs
import Submission.Work.FTS.ClassCHon.Zpz.Basic
import Submission.Work.FTS.ClassCHon.Zpz.Deriv
import Submission.Work.FTS.ClassCHon.Zpz.Auxiliary.sqrtHk_integrable
import Submission.Work.FTS.ClassCHon.Zpz.Auxiliary.abs_pzIter2_le_sqrt
import Submission.Work.FTS.ClassCHon.Zpz.Auxiliary.integrable_and_swap_abs_pzIter2
import Submission.Work.FTS.ClassCHon.Zpz.Auxiliary.slice_mul_phiW_integrable

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.ClassCHon.Zpz

theorem cmode_Dz {α : ℝ} {F : ℝ → ℝ → ℝ} (m : ℕ)
    (hsm : Work.FTS.EllipticEst.SmoothOpen F) (hF : Work.Spaces.HkMem α 2 F) :
    ∀ z : ℝ, 0 < z → Work.FTS.PhiStar.Series.cmode m (Work.Spaces.Dz F) z
      = z * deriv (fun t => Work.FTS.PhiStar.Series.cmode m F t) z := by
  intro z hz
  have hF1 : Work.Spaces.HkMem α 1 F :=
    Work.FTS.OpenPkg.HkMem_mono_open hsm 1 (by norm_num) hF
  obtain ⟨hsl, hout⟩ := Aux.sqrtHk_integrable hsm hF
  have hpt2 : ∀ τ θ : ℝ, 0 < τ → θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) →
      |Work.Spaces.pzIter 2 F τ θ|
        ≤ (2 / τ ^ 2) * Real.sqrt (Work.Spaces.HkIntegrand α 2 F τ θ) :=
    fun τ θ hτ hθ => Aux.abs_pzIter2_le_sqrt hsm hτ hθ
  have hswap : ∀ {z₀ x : ℝ}, 0 < z₀ → 0 < x →
      MeasureTheory.Integrable (Function.uncurry (fun τ θ : ℝ => |Work.Spaces.pzIter 2 F τ θ|))
          ((MeasureTheory.volume.restrict (Set.uIoc z₀ x)).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ)) ∧
        (∫ θ in Work.Spaces.Iθ, (∫ τ in Set.uIoc z₀ x, |Work.Spaces.pzIter 2 F τ θ|))
          = ∫ τ in Set.uIoc z₀ x,
              (∫ θ in Work.Spaces.Iθ, |Work.Spaces.pzIter 2 F τ θ|) := by
    intro z₀ x hz₀ hx
    exact Aux.integrable_and_swap_abs_pzIter2 hsm hpt2 hsl hout hz₀ hx
  have hphi : ∀ w : ℝ, 0 < w →
      MeasureTheory.IntegrableOn (fun θ : ℝ => F w θ * phiW m θ) Work.Spaces.Iθ ∧
      MeasureTheory.IntegrableOn (fun θ : ℝ => Work.Spaces.pz F w θ * phiW m θ)
        Work.Spaces.Iθ :=
    fun w hw => Aux.slice_mul_phiW_integrable m hsm hF1 hw
  have habs : ∀ w : ℝ, 0 < w →
      MeasureTheory.IntegrableOn (fun θ : ℝ => |F w θ|) Work.Spaces.Iθ ∧
      MeasureTheory.IntegrableOn (fun θ : ℝ => |Work.Spaces.pz F w θ|) Work.Spaces.Iθ :=
    fun w hw => Work.FTS.PhiStar.Honesty.slice_abs_integrable hsm hF1 hw
  have hderiv : HasDerivAt (numW m F) (pwF m F z) z :=
    numW_hasDerivAt m hsm hphi habs hpt2 hsl hout hswap hz
  -- the mode normalisation constant
  set D : ℝ := ((2 * (m : ℝ) + 2) * (2 * (m : ℝ) + 3)) / (4 * (m : ℝ) + 5) with hD
  have hcmode : ∀ (G : ℝ → ℝ → ℝ) (t : ℝ),
      Work.FTS.PhiStar.Series.cmode m G t = numW m G t / D := by
    intro G t
    rw [cmode_eq_numW_div m G t, hD]
  have hder : deriv (Work.FTS.PhiStar.Series.cmode m F) z = pwF m F z / D := by
    have hfun : Work.FTS.PhiStar.Series.cmode m F = fun t => numW m F t / D :=
      funext fun t => hcmode F t
    rw [hfun, deriv_div_const, hderiv.deriv]
  rw [hcmode (Work.Spaces.Dz F) z, numW_Dz m F z, hder]
  ring

end Work.FTS.ClassCHon.Zpz
