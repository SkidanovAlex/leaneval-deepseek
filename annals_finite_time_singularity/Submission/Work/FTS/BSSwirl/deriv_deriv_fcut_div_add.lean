import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.BSSwirl.inv_norm_cut

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open scoped Topology Filter

namespace Work.FTS.BSSwirl

/-- The radial part of the Laplacian applied to the cutoff potential `fcut(r/ε)/r`:
writing `g(s) = fcut(s/ε) · s⁻¹`, one has `g''(r) + 2 g'(r)/r = fcut''(r/ε)/(ε² r)`.

This is the elementary computation needed when writing
`Δ(fcut(‖z‖/ε)/‖z‖)` in polar coordinates. -/
theorem deriv_deriv_fcut_div_add (ε : ℝ) (hε : 0 < ε) {r : ℝ} (hr : 0 < r) :
    deriv (deriv (fun s : ℝ => Work.FTS.BSSwirl.fcut (s / ε) * s⁻¹)) r
      + 2 * deriv (fun s : ℝ => Work.FTS.BSSwirl.fcut (s / ε) * s⁻¹) r / r
      = deriv (deriv Work.FTS.BSSwirl.fcut) (r / ε) / (ε ^ 2 * r) := by
  have hr0 : r ≠ 0 := ne_of_gt hr
  have hε0 : ε ≠ 0 := ne_of_gt hε
  -- smoothness of `fcut` and of `deriv fcut`
  have hd1 : Differentiable ℝ fcut := (contDiff_fcut 1).differentiable one_ne_zero
  have hd2 : Differentiable ℝ (deriv fcut) := ((contDiff_fcut 2).deriv').differentiable one_ne_zero
  have hfc : ∀ y : ℝ, HasDerivAt fcut (deriv fcut y) y := fun y => (hd1 y).hasDerivAt
  have hdfc : ∀ y : ℝ, HasDerivAt (deriv fcut) (deriv (deriv fcut) y) y := fun y => (hd2 y).hasDerivAt
  -- the derivatives of `s ↦ fcut (s / ε)` and `s ↦ deriv fcut (s / ε)`
  have hu : ∀ s : ℝ, HasDerivAt (fun s : ℝ => fcut (s / ε)) (deriv fcut (s / ε) * (1/ε)) s := by
    intro s
    have h1 : HasDerivAt (fun y : ℝ => y / ε) (1 / ε) s := (hasDerivAt_id s).div_const ε
    have h2 := (hfc (s/ε)).comp s h1
    simpa [Function.comp_def] using h2
  have hdu : ∀ s : ℝ,
      HasDerivAt (fun s : ℝ => deriv fcut (s / ε)) (deriv (deriv fcut) (s / ε) * (1/ε)) s := by
    intro s
    have h1 : HasDerivAt (fun y : ℝ => y / ε) (1 / ε) s := (hasDerivAt_id s).div_const ε
    have h2 := (hdfc (s/ε)).comp s h1
    simpa [Function.comp_def] using h2
  -- the first derivative of `g s = fcut (s/ε) * s⁻¹` at `r`
  have hgr : deriv (fun s : ℝ => fcut (s / ε) * s⁻¹) r
      = deriv fcut (r / ε) * (1/ε) * r⁻¹ + fcut (r / ε) * (-(r^2)⁻¹) := by
    have h : HasDerivAt (fun s : ℝ => fcut (s / ε) * s⁻¹)
        (deriv fcut (r / ε) * (1/ε) * r⁻¹ + fcut (r / ε) * (-(r^2)⁻¹)) r :=
      (hu r).mul (hasDerivAt_inv hr0)
    exact h.deriv
  -- the derivative of `s ↦ -(s^2)⁻¹` at `r`
  have hq : HasDerivAt (fun s : ℝ => -(s^2)⁻¹) (2 / r^3) r := by
    have h1 : HasDerivAt (fun s : ℝ => s^2) (2 * r) r := by
      simpa using hasDerivAt_pow 2 r
    have h2 : HasDerivAt (fun s : ℝ => (s^2)⁻¹) (-(2*r) / (r^2)^2) r := h1.inv (pow_ne_zero 2 hr0)
    have h3 : HasDerivAt (fun s : ℝ => -((s^2)⁻¹)) (-(-(2*r)/(r^2)^2)) r := h2.neg
    have hv : -(-(2*r)/(r^2)^2) = 2/r^3 := by field_simp
    rw [hv] at h3
    exact h3
  -- the two halves of `deriv g` are differentiable, with the derivatives below
  have hF1 : HasDerivAt (fun s : ℝ => deriv fcut (s / ε) * (1/ε) * s⁻¹)
      ((deriv (deriv fcut) (r / ε) * (1/ε)) * (1/ε) * r⁻¹ + (deriv fcut (r / ε) * (1/ε)) * (-(r^2)⁻¹)) r := by
    have ha : HasDerivAt (fun s : ℝ => deriv fcut (s / ε) * (1/ε))
        (deriv (deriv fcut) (r/ε) * (1/ε) * (1/ε)) r := by
      have h : HasDerivAt (fun s : ℝ => deriv fcut (s / ε) * (1/ε))
          ((deriv (deriv fcut) (r/ε) * (1/ε)) * (1/ε)) r :=
        (hdu r).mul_const (1/ε)
      exact h
    have h : HasDerivAt (fun s : ℝ => deriv fcut (s / ε) * (1/ε) * s⁻¹)
        ((deriv (deriv fcut) (r/ε) * (1/ε) * (1/ε)) * r⁻¹ + (deriv fcut (r/ε) * (1/ε)) * (-(r^2)⁻¹)) r :=
      ha.mul (hasDerivAt_inv hr0)
    exact h
  have hF2 : HasDerivAt (fun s : ℝ => fcut (s / ε) * (-(s^2)⁻¹))
      ((deriv fcut (r/ε) * (1/ε)) * (-(r^2)⁻¹) + fcut (r/ε) * (2/r^3)) r := by
    have h : HasDerivAt (fun s : ℝ => fcut (s / ε) * (-(s^2)⁻¹))
        ((deriv fcut (r/ε) * (1/ε)) * (-(r^2)⁻¹) + fcut (r/ε) * (2/r^3)) r :=
      (hu r).mul hq
    exact h
  have hF : HasDerivAt (fun s : ℝ => deriv fcut (s / ε) * (1/ε) * s⁻¹ + fcut (s / ε) * (-(s^2)⁻¹))
      (((deriv (deriv fcut) (r/ε) * (1/ε)) * (1/ε)) * r⁻¹ + (deriv fcut (r/ε) * (1/ε)) * (-(r^2)⁻¹)
        + ((deriv fcut (r/ε) * (1/ε)) * (-(r^2)⁻¹) + fcut (r/ε) * (2/r^3))) r := hF1.add hF2
  -- `deriv g` is, near `r`, the explicit function `F`
  have hev : deriv (fun s : ℝ => fcut (s / ε) * s⁻¹) =ᶠ[𝓝 r]
      (fun s : ℝ => deriv fcut (s / ε) * (1/ε) * s⁻¹ + fcut (s / ε) * (-(s^2)⁻¹)) := by
    filter_upwards [isOpen_Ioi.mem_nhds hr] with s hs
    have h : HasDerivAt (fun s : ℝ => fcut (s / ε) * s⁻¹)
        (deriv fcut (s / ε) * (1/ε) * s⁻¹ + fcut (s / ε) * (-(s^2)⁻¹)) s :=
      (hu s).mul (hasDerivAt_inv (ne_of_gt hs))
    exact h.deriv
  have hsec : deriv (deriv (fun s : ℝ => fcut (s / ε) * s⁻¹)) r
      = ((deriv (deriv fcut) (r / ε) * (1/ε)) * (1/ε)) * r⁻¹ + (deriv fcut (r/ε) * (1/ε)) * (-(r^2)⁻¹)
        + ((deriv fcut (r/ε) * (1/ε)) * (-(r^2)⁻¹) + fcut (r/ε) * (2/r^3)) := by
    rw [hev.deriv_eq, hF.deriv]
  rw [hsec, hgr]
  field_simp
  ring

end Work.FTS.BSSwirl
