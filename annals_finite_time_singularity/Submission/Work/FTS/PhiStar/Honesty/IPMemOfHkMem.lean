import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.EllipticEst.AngSecond.Defs
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `HkMem α 0 F ⟹ IPMem F F`

At level `k = 0` the `H^k`-integrand `Work.Spaces.HkIntegrand α 0 F` collapses to the single
square `(F z θ · w z / sin(2θ)^{η/2})²` (the `D_z`-sum has the one term `i = 0` and the mixed
double sum is empty), while the weighted pairing integrand of `AngSecond.IPMem F F` is
`F z θ · F z θ · w z² · σ θ` with `σ θ = sin(2θ)^{-η}`.  The two agree pointwise on `Iθ`
(`AngSecond.sq_mul_W`, whose endpoint case `sin(2θ) = 0` is handled by `Real.zero_rpow`), so the
honesty of the first transfers verbatim to the honesty of the second, both slicewise in `θ` and
then in `z`.

This is the level-`0` bridge `HkMem α 0 F → IPMem F F` used by the `PhiStar/Honesty` layer; a
sibling statement `Work.FTS.EllipticEst.AngClean.HkMem_zero_IPMem` proves the same fact in the
`AngClean` namespace.
-/

namespace Work.FTS.PhiStar.Honesty

open MeasureTheory

/-- At `k = 0` the `H^k`-integrand collapses to a single square: the `D_z`-sum has the one term
`i = 0` and the mixed double sum is empty. -/
private lemma HkIntegrand_zero_eq (α : ℝ) (F : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.HkIntegrand α 0 F z θ
      = (F z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
  simp [Work.Spaces.HkIntegrand]

/-- **The level-`0` bridge**: `HkMem α 0 F` says that `HkIntegrand α 0 F` is honest, and on `Iθ`
that integrand *is* the integrand of the weighted pairing `IP F F`. -/
theorem IPMemOfHkMem {α : ℝ} {F : ℝ → ℝ → ℝ} (h : Work.Spaces.HkMem α 0 F) :
    Work.FTS.EllipticEst.AngSecond.IPMem F F := by
  -- The integrand of `IP F F` is the `k = 0` `Hk`-integrand, on the whole of `Iθ`.
  have hsq : ∀ z θ, θ ∈ Work.Spaces.Iθ → Work.Spaces.HkIntegrand α 0 F z θ
      = F z θ * F z θ * Work.FTS.EllipticEst.AngSecond.w2 z
          * Work.FTS.EllipticEst.AngSecond.sig θ :=
    fun z θ hθ => by
      rw [HkIntegrand_zero_eq α F z θ,
        Work.FTS.EllipticEst.AngSecond.sq_mul_W F hθ]
  -- The `θ`-slice of `IP F F` at a fixed `z`, written as an integral of the `Hk`-integrand.
  have hslice : ∀ z, (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 F z θ)
      = ∫ θ in Work.Spaces.Iθ, F z θ * F z θ * Work.FTS.EllipticEst.AngSecond.w2 z
          * Work.FTS.EllipticEst.AngSecond.sig θ :=
    fun z => setIntegral_congr_fun measurableSet_Icc (fun θ hθ => hsq z θ hθ)
  constructor
  · -- Slicewise honesty in `θ`.
    intro z hz
    exact MeasureTheory.IntegrableOn.congr_fun (h.1 z hz)
      (fun θ hθ => hsq z θ hθ) measurableSet_Icc
  · -- Outer honesty in `z`.
    exact MeasureTheory.IntegrableOn.congr_fun h.2 (fun z _ => hslice z) measurableSet_Ici

end Work.FTS.PhiStar.Honesty
