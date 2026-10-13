import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.Elliptic.Defs
import Submission.Work.Elliptic.GsingFuncs
import Submission.Work.Elliptic.Gsing_algebra

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.Elliptic

set_option autoImplicit false
set_option linter.unusedSimpArgs false

open scoped Real Topology
open MeasureTheory Set Filter

/-! ## Derivative facts for the pieces of `Gsing` -/

/-- `Abar` has derivative `DAbar`. -/
private lemma hasDerivAt_Abar (α : ℝ) {z : ℝ} (hz : 0 < z) :
    HasDerivAt (Abar α) (DAbar α z) z := by
  have hzne : z ≠ 0 := ne_of_gt hz
  have hp : HasDerivAt (fun y : ℝ => y ^ (-(5 / α))) ((-(5 / α)) * z ^ (-(5 / α) - 1)) z :=
    Real.hasDerivAt_rpow_const (Or.inl hzne)
  have h := hp.const_mul (-(3 / (4 * α)))
  convert h using 1
  · ext y; rfl
  · show (-(3 / (4 * α)) * (-(5 / α))) * z ^ (-(5 / α) - 1)
        = -(3 / (4 * α)) * (-(5 / α) * z ^ (-(5 / α) - 1))
    ring

/-- `DAbar` has derivative `DDAbar`. -/
private lemma hasDerivAt_DAbar (α : ℝ) {z : ℝ} (hz : 0 < z) :
    HasDerivAt (DAbar α) (DDAbar α z) z := by
  have hzne : z ≠ 0 := ne_of_gt hz
  have hp : HasDerivAt (fun y : ℝ => y ^ (-(5 / α) - 1))
      ((-(5 / α) - 1) * z ^ (-(5 / α) - 1 - 1)) z :=
    Real.hasDerivAt_rpow_const (Or.inl hzne)
  have h := hp.const_mul ((-(3 / (4 * α))) * (-(5 / α)))
  have hfun : (fun y : ℝ => ((-(3 / (4 * α))) * (-(5 / α))) * y ^ (-(5 / α) - 1))
      = DAbar α := rfl
  rw [hfun] at h
  simpa only [DDAbar] using h

/-- `Gstar` has derivative `DGstar`. -/
private lemma hasDerivAt_Gstar (α : ℝ) (F : ℝ → ℝ → ℝ) {z : ℝ}
    (hL12 : HasDerivAt (L12 F) (-(3 * Fstar F z / z)) z) :
    HasDerivAt (Gstar α F) (DGstar α F z) z := by
  have h := hL12.const_mul (-(1 / (4 * α)))
  have hfun : (fun y : ℝ => -(1 / (4 * α)) * L12 F y) = Gstar α F := rfl
  rw [hfun] at h
  simpa only [DGstar] using h

/-- `Gbar` has derivative `DGbar`. -/
private lemma hasDerivAt_Gbar (α : ℝ) (F : ℝ → ℝ → ℝ) {z : ℝ} (hz : 0 < z)
    (hJ : HasDerivAt (Jfun α F) (z ^ ((5 - α) / α) * Fstar F z) z) :
    HasDerivAt (Gbar α F) (DGbar α F z) z := by
  have hA : HasDerivAt (Abar α) (DAbar α z) z := hasDerivAt_Abar α hz
  have h := hA.mul hJ
  have hfun : (Abar α * Jfun α F) = Gbar α F := rfl
  rw [hfun] at h
  simpa only [DGbar] using h

/-- `DGstar` has derivative `DDGstar`. -/
private lemma hasDerivAt_DGstar (α : ℝ) (F : ℝ → ℝ → ℝ) {z : ℝ} (hz : 0 < z)
    (hFc : HasDerivAt (Fstar F) (deriv (Fstar F) z) z) :
    HasDerivAt (DGstar α F) (DDGstar α F z) z := by
  have hzne : z ≠ 0 := ne_of_gt hz
  have hnum : HasDerivAt (fun y : ℝ => 3 * Fstar F y) (3 * deriv (Fstar F) z) z :=
    hFc.const_mul 3
  have hden : HasDerivAt (fun y : ℝ => y) (1 : ℝ) z := hasDerivAt_id z
  have hquot : HasDerivAt (fun y : ℝ => 3 * Fstar F y / y)
      (((3 * deriv (Fstar F) z) * z - (3 * Fstar F z) * 1) / z ^ 2) z :=
    hnum.div hden hzne
  have hneg : HasDerivAt (fun y : ℝ => -(3 * Fstar F y / y))
      (-(((3 * deriv (Fstar F) z) * z - (3 * Fstar F z) * 1) / z ^ 2)) z := hquot.neg
  have h := hneg.const_mul (-(1 / (4 * α)))
  have hfun : (fun y : ℝ => -(1 / (4 * α)) * (-(3 * Fstar F y / y))) = DGstar α F := rfl
  rw [hfun] at h
  simpa only [DDGstar, mul_one] using h

/-- The function `y ↦ y^{(5-α)/α} F_*(y)` has derivative
`((5-α)/α) z^{(5-α)/α-1} F_*(z) + z^{(5-α)/α} F_*'(z)`. -/
private lemma hasDerivAt_rpow_mul_Fstar (α : ℝ) (F : ℝ → ℝ → ℝ) {z : ℝ} (hz : 0 < z)
    (hFc : HasDerivAt (Fstar F) (deriv (Fstar F) z) z) :
    HasDerivAt (fun y : ℝ => y ^ ((5 - α) / α) * Fstar F y)
      (((5 - α) / α) * z ^ ((5 - α) / α - 1) * Fstar F z
        + z ^ ((5 - α) / α) * deriv (Fstar F) z) z := by
  have hzne : z ≠ 0 := ne_of_gt hz
  have hp : HasDerivAt (fun y : ℝ => y ^ ((5 - α) / α))
      (((5 - α) / α) * z ^ ((5 - α) / α - 1)) z :=
    Real.hasDerivAt_rpow_const (Or.inl hzne)
  have h := hp.mul hFc
  have hfun : ((fun y : ℝ => y ^ ((5 - α) / α)) * Fstar F)
      = (fun y : ℝ => y ^ ((5 - α) / α) * Fstar F y) := rfl
  rw [hfun] at h
  exact h

/-- `DGbar` has derivative `DDGbar`. -/
private lemma hasDerivAt_DGbar (α : ℝ) (F : ℝ → ℝ → ℝ) {z : ℝ} (hz : 0 < z)
    (hFc : HasDerivAt (Fstar F) (deriv (Fstar F) z) z)
    (hJ : HasDerivAt (Jfun α F) (z ^ ((5 - α) / α) * Fstar F z) z) :
    HasDerivAt (DGbar α F) (DDGbar α F z) z := by
  have hA : HasDerivAt (Abar α) (DAbar α z) z := hasDerivAt_Abar α hz
  have hA' : HasDerivAt (DAbar α) (DDAbar α z) z := hasDerivAt_DAbar α hz
  have hFq := hasDerivAt_rpow_mul_Fstar α F hz hFc
  have h1 : HasDerivAt (fun y : ℝ => DAbar α y * Jfun α F y)
      (DDAbar α z * Jfun α F z + DAbar α z * (z ^ ((5 - α) / α) * Fstar F z)) z :=
    hA'.mul hJ
  have h2 : HasDerivAt (fun y : ℝ => Abar α y * (y ^ ((5 - α) / α) * Fstar F y))
      (DAbar α z * (z ^ ((5 - α) / α) * Fstar F z)
        + Abar α z * (((5 - α) / α) * z ^ ((5 - α) / α - 1) * Fstar F z
            + z ^ ((5 - α) / α) * deriv (Fstar F) z)) z :=
    hA.mul hFq
  have h := h1.add h2
  have hfun : ((fun y : ℝ => DAbar α y * Jfun α F y)
      + (fun y : ℝ => Abar α y * (y ^ ((5 - α) / α) * Fstar F y))) = DGbar α F := rfl
  rw [hfun] at h
  have hval : DDAbar α z * Jfun α F z + DAbar α z * (z ^ ((5 - α) / α) * Fstar F z)
      + (DAbar α z * (z ^ ((5 - α) / α) * Fstar F z)
        + Abar α z * (((5 - α) / α) * z ^ ((5 - α) / α - 1) * Fstar F z
            + z ^ ((5 - α) / α) * deriv (Fstar F) z)) = DDGbar α F z := by
    rw [DDGbar]; ring
  rw [hval] at h
  exact h

theorem Gsing_ode (α : ℝ) (F : ℝ → ℝ → ℝ) (hα : 0 < α)
    (hL12 : ∀ z ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (fun z' => Work.Elliptic.L12 F z') (-(3 * Work.Elliptic.Fstar F z / z)) z)
    (hFc : ∀ z ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (Work.Elliptic.Fstar F) (deriv (Work.Elliptic.Fstar F) z) z)
    (hJ : ∀ z ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (fun z' => ∫ s in (0 : ℝ)..z', s ^ ((5 - α) / α) * Work.Elliptic.Fstar F s)
        (z ^ ((5 - α) / α) * Work.Elliptic.Fstar F z) z) :
    ∀ z ∈ Set.Ioi (0 : ℝ),
      α ^ 2 * z ^ 2 * deriv (fun z' => deriv (Work.Elliptic.Gsing α F) z') z
        + α * (5 + α) * z * deriv (Work.Elliptic.Gsing α F) z
        = (15 / 4) * Work.Elliptic.Fstar F z := by
  intro z hz
  have hzpos : 0 < z := hz
  have hFcz : HasDerivAt (Fstar F) (deriv (Fstar F) z) z := hFc z hz
  have hJz : HasDerivAt (Jfun α F) (z ^ ((5 - α) / α) * Fstar F z) z := by
    have h := hJ z hz
    have hfun : (fun z' => ∫ s in (0 : ℝ)..z', s ^ ((5 - α) / α) * Fstar F s) = Jfun α F := rfl
    rw [hfun] at h
    exact h
  -- `Gsing` has derivative `DGstar + DGbar`
  have hGsing : HasDerivAt (Gsing α F) (DGstar α F z + DGbar α F z) z := by
    have h1 : HasDerivAt (Gstar α F) (DGstar α F z) z := hasDerivAt_Gstar α F (hL12 z hz)
    have h2 : HasDerivAt (Gbar α F) (DGbar α F z) z := hasDerivAt_Gbar α F hzpos hJz
    have h := h1.add h2
    have hfun : ((Gstar α F) + (Gbar α F)) = Gsing α F := rfl
    rw [hfun] at h
    exact h
  -- `deriv (Gsing α F)` agrees with `DGstar + DGbar` near `z`
  have hderiv_eq : deriv (Gsing α F) =ᶠ[𝓝 z] (DGstar α F + DGbar α F) := by
    have hmem : ∀ᶠ w in 𝓝 z, w ∈ Set.Ioi (0 : ℝ) :=
      Filter.eventually_mem_set.mpr (isOpen_Ioi.mem_nhds hz)
    refine hmem.mono ?_
    intro w hw
    have h1 : HasDerivAt (Gstar α F) (DGstar α F w) w := hasDerivAt_Gstar α F (hL12 w hw)
    have h2 : HasDerivAt (Gbar α F) (DGbar α F w) w :=
      hasDerivAt_Gbar α F hw (by
        have h := hJ w hw
        have hfun : (fun z' => ∫ s in (0 : ℝ)..z', s ^ ((5 - α) / α) * Fstar F s) = Jfun α F := rfl
        rw [hfun] at h
        exact h)
    have h3 : HasDerivAt (Gsing α F) (DGstar α F w + DGbar α F w) w := by
      have h := h1.add h2
      have hfun : ((Gstar α F) + (Gbar α F)) = Gsing α F := rfl
      rw [hfun] at h
      exact h
    exact h3.deriv
  -- second derivative
  have hDG : HasDerivAt (DGstar α F + DGbar α F) (DDGstar α F z + DDGbar α F z) z := by
    have h1 : HasDerivAt (DGstar α F) (DDGstar α F z) z := hasDerivAt_DGstar α F hzpos hFcz
    have h2 : HasDerivAt (DGbar α F) (DDGbar α F z) z := hasDerivAt_DGbar α F hzpos hFcz hJz
    exact h1.add h2
  have hderiv2 : HasDerivAt (deriv (Gsing α F)) (DDGstar α F z + DDGbar α F z) z :=
    hDG.congr_of_eventuallyEq hderiv_eq
  have e1 : deriv (fun z' => deriv (Gsing α F) z') z = DDGstar α F z + DDGbar α F z :=
    hderiv2.deriv
  have e2 : deriv (Gsing α F) z = DGstar α F z + DGbar α F z := hGsing.deriv
  rw [e1, e2]
  exact Gsing_algebra α F z hα hzpos

end Work.Elliptic
