/-
# `Work.FTS.PhiStar.RadGreenSupport.radGreen_ode_weak`

The radial Green's function `Work.FTS.PhiStar.Radial.radGreen α m c` (the decaying solution of the
mode-`m` Euler equation `-α²z²a'' - α(5+α)z a' + λ_m a = c`, `λ_m = 2m(2m+5)`) satisfies that
equation at every `z > 0`, under the *weak* hypothesis set: `c` continuous on `(0,∞)`,
`c t·t^{(2m+5)/α-1}` integrable on `(0,1)` and `c t·t^{-2m/α-1}` integrable on `(1,∞)`.

The sibling theorem `Work.FTS.PhiStar.Radial.radGreen_solves` proves the same identity with one
extra hypothesis (`IntegrableOn (c t·t^{-2m/α-1}) (Ioo 0 1)`), which its proof never uses: the
first-derivative computation needs only the fundamental theorem of calculus for the interval
integral `∫₀^z` (governed by `h0`) and for the tail `∫_{Ioi z}` (governed by `hinf`), while the
second-derivative computation is pure algebra plus the differentiability of the two integrals.
Here the identity is proved from `hc`, `h0`, `hinf` alone.

The first-order differentiability machinery is reused (publicly) from
`Submission/Work/FTS/PhiStar/Series/radGreenI_differentiableAt.lean` (`rgiA`, `rgiB`, `rgiF1`,
`rgiF2`, `rgiSn`, `rgiSp`, `rgiK`, `rgiD1`, `rgiA_hasDerivAt`, `rgiB_hasDerivAt`,
`hasDerivAt_radGreenI`, `radGreenI_eq_rgi`); the only new analytic input is the differentiability
of `rgiD1` with its explicit derivative `rgD2` below.  Note `radGreen α m c` is *definitionally*
`radGreenI α m c`.
-/
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.PhiStar.Radial.Defs
import Submission.Work.FTS.PhiStar.Radial.radGreenIntended
import Submission.Work.FTS.PhiStar.Radial.intervalIntegrable_of_Ioi_Ioo
import Submission.Work.FTS.PhiStar.Radial.integrableOn_Ioi_of_Ioi_Ioo
import Submission.Work.FTS.PhiStar.Radial.hasDerivAt_integral_Ioi
import Submission.Work.FTS.PhiStar.Series.radGreenI_differentiableAt

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.RadGreenSupport

set_option autoImplicit false

open Work.FTS.PhiStar.Series (rgiK rgiSn rgiSp rgiF1 rgiF2 rgiA rgiB rgiD1
  rgiA_hasDerivAt rgiB_hasDerivAt hasDerivAt_radGreenI radGreenI_eq_rgi)

/-- The second derivative of the radial Green's function `radGreenI α m c`, in explicit form:
the derivative of `rgiD1` (which is the derivative of `radGreenI`). -/
private def rgD2 (α : ℝ) (m : ℕ) (c : ℝ → ℝ) (y : ℝ) : ℝ :=
  rgiK α m * (((rgiSn α m * ((rgiSn α m - 1) * y ^ (rgiSn α m - 2))) * rgiA α m c y
            + (rgiSn α m * y ^ (rgiSn α m - 1)) * rgiF1 α m c y)
          + ((rgiSp α m * ((rgiSp α m - 1) * y ^ (rgiSp α m - 2))) * rgiB α m c y
            + (rgiSp α m * y ^ (rgiSp α m - 1)) * (-(rgiF2 α m c y))))

/-- **The derivative `rgiD1` of `radGreenI` is differentiable on `(0,∞)`**, with the explicit
derivative `rgD2`; uses only the interval-integral FTC (`h0`) and the tail-integral FTC (`hinf`). -/
private lemma rgD1_hasDerivAt {α : ℝ} {m : ℕ} {c : ℝ → ℝ}
    (hc : ContinuousOn c (Set.Ioi 0))
    (h0 : MeasureTheory.IntegrableOn (fun t => c t * t ^ ((2 * (m : ℝ) + 5) / α - 1))
      (Set.Ioo 0 1))
    (hinf : MeasureTheory.IntegrableOn (fun t => c t * t ^ (-(2 * (m : ℝ) / α) - 1))
      (Set.Ioi 1)) :
    ∀ z ∈ Set.Ioi (0 : ℝ), HasDerivAt (rgiD1 α m c) (rgD2 α m c z) z := by
  intro z hz
  have hzne : z ≠ 0 := ne_of_gt hz
  have hA := rgiA_hasDerivAt (α := α) (m := m) (c := c) hc h0 z hz
  have hB := rgiB_hasDerivAt (α := α) (m := m) (c := c) hc hinf z hz
  have hp1 : HasDerivAt (fun t : ℝ => rgiSn α m * t ^ (rgiSn α m - 1))
      (rgiSn α m * ((rgiSn α m - 1) * z ^ (rgiSn α m - 2))) z := by
    have h := (Real.hasDerivAt_rpow_const (x := z) (p := rgiSn α m - 1)
      (Or.inl hzne)).const_mul (rgiSn α m)
    rwa [show (rgiSn α m - 1) - 1 = rgiSn α m - 2 from by ring] at h
  have hp2 : HasDerivAt (fun t : ℝ => rgiSp α m * t ^ (rgiSp α m - 1))
      (rgiSp α m * ((rgiSp α m - 1) * z ^ (rgiSp α m - 2))) z := by
    have h := (Real.hasDerivAt_rpow_const (x := z) (p := rgiSp α m - 1)
      (Or.inl hzne)).const_mul (rgiSp α m)
    rwa [show (rgiSp α m - 1) - 1 = rgiSp α m - 2 from by ring] at h
  exact ((hp1.mul hA).add (hp2.mul hB)).const_mul (rgiK α m)

theorem radGreen_ode_weak {α : ℝ} (hα : 0 < α) (m : ℕ) {c : ℝ → ℝ}
    (hc : ContinuousOn c (Set.Ioi 0))
    (h0 : MeasureTheory.IntegrableOn (fun t => c t * t ^ ((2 * (m : ℝ) + 5) / α - 1)) (Set.Ioo 0 1))
    (hinf : MeasureTheory.IntegrableOn (fun t => c t * t ^ (-(2 * (m : ℝ) / α) - 1)) (Set.Ioi 1)) :
    ∀ z, 0 < z →
      -α ^ 2 * z ^ 2 * deriv (deriv (Work.FTS.PhiStar.Radial.radGreen α m c)) z
        - α * (5 + α) * z * deriv (Work.FTS.PhiStar.Radial.radGreen α m c) z
        + Work.FTS.PhiStar.Radial.lamR m * Work.FTS.PhiStar.Radial.radGreen α m c z = c z := by
  have hαne : α ≠ 0 := ne_of_gt hα
  have hG : Work.FTS.PhiStar.Radial.radGreen α m c = Work.FTS.PhiStar.Radial.radGreenI α m c := rfl
  intro z hz
  rw [hG]
  -- First and second derivative of `radGreenI`.
  have hd1 : HasDerivAt (Work.FTS.PhiStar.Radial.radGreenI α m c) (rgiD1 α m c z) z :=
    hasDerivAt_radGreenI (α := α) (m := m) (c := c) hc h0 hinf z hz
  have heq : deriv (Work.FTS.PhiStar.Radial.radGreenI α m c) =ᶠ[𝓝 z] rgiD1 α m c :=
    eventually_of_mem (Ioi_mem_nhds hz)
      (fun y hy => (hasDerivAt_radGreenI (α := α) (m := m) (c := c) hc h0 hinf y hy).deriv)
  have hdd : deriv (deriv (Work.FTS.PhiStar.Radial.radGreenI α m c)) z = rgD2 α m c z := by
    rw [heq.deriv_eq, (rgD1_hasDerivAt (α := α) (m := m) (c := c) hc h0 hinf z hz).deriv]
  have hd1z : deriv (Work.FTS.PhiStar.Radial.radGreenI α m c) z = rgiD1 α m c z := hd1.deriv
  have hgz : Work.FTS.PhiStar.Radial.radGreenI α m c z
      = rgiK α m * (z ^ (rgiSn α m) * rgiA α m c z + z ^ (rgiSp α m) * rgiB α m c z) :=
    congrFun (radGreenI_eq_rgi α m c) z
  rw [hdd, hd1z, hgz]
  -- The `rpow` clearing identities.
  have hzs1 : z * z ^ (rgiSn α m - 1) = z ^ (rgiSn α m) := by
    nth_rewrite 1 [← Real.rpow_one z]
    rw [← Real.rpow_add hz]
    congr 1
    ring
  have hzs2 : z ^ 2 * z ^ (rgiSn α m - 2) = z ^ (rgiSn α m) := by
    rw [← Real.rpow_two z, ← Real.rpow_add hz]
    congr 1
    ring
  have hzp1 : z * z ^ (rgiSp α m - 1) = z ^ (rgiSp α m) := by
    nth_rewrite 1 [← Real.rpow_one z]
    rw [← Real.rpow_add hz]
    congr 1
    ring
  have hzp2 : z ^ 2 * z ^ (rgiSp α m - 2) = z ^ (rgiSp α m) := by
    rw [← Real.rpow_two z, ← Real.rpow_add hz]
    congr 1
    ring
  have hc1 : z ^ 2 * z ^ (rgiSn α m - 1) * rgiF1 α m c z = c z := by
    have he : (2 * (m : ℝ) + 5) / α - 1 = -1 - (-(2 * (m : ℝ) + 5) / α) := by ring
    have hf : rgiF1 α m c z = c z * z ^ (-1 - rgiSn α m) := by
      simp only [rgiF1, rgiSn]; rw [he]
    have h2 : z ^ 2 * z ^ (rgiSn α m - 1) = z ^ (rgiSn α m + 1) := by
      rw [← Real.rpow_two z, ← Real.rpow_add hz]; congr 1; ring
    have hE : (rgiSn α m + 1) + (-1 - rgiSn α m) = 0 := by ring
    have hcomb : z ^ 2 * z ^ (rgiSn α m - 1) * z ^ (-1 - rgiSn α m) = 1 := by
      rw [h2, ← Real.rpow_add hz, hE, Real.rpow_zero]
    calc z ^ 2 * z ^ (rgiSn α m - 1) * rgiF1 α m c z
        = z ^ 2 * z ^ (rgiSn α m - 1) * (c z * z ^ (-1 - rgiSn α m)) := by rw [hf]
      _ = c z * (z ^ 2 * z ^ (rgiSn α m - 1) * z ^ (-1 - rgiSn α m)) := by ring
      _ = c z * 1 := by rw [hcomb]
      _ = c z := by ring
  have hc2 : z ^ 2 * z ^ (rgiSp α m - 1) * rgiF2 α m c z = c z := by
    have he : -(2 * (m : ℝ) / α) - 1 = -1 - (2 * (m : ℝ) / α) := by ring
    have hf : rgiF2 α m c z = c z * z ^ (-1 - rgiSp α m) := by
      simp only [rgiF2, rgiSp]; rw [he]
    have h2 : z ^ 2 * z ^ (rgiSp α m - 1) = z ^ (rgiSp α m + 1) := by
      rw [← Real.rpow_two z, ← Real.rpow_add hz]; congr 1; ring
    have hE : (rgiSp α m + 1) + (-1 - rgiSp α m) = 0 := by ring
    have hcomb : z ^ 2 * z ^ (rgiSp α m - 1) * z ^ (-1 - rgiSp α m) = 1 := by
      rw [h2, ← Real.rpow_add hz, hE, Real.rpow_zero]
    calc z ^ 2 * z ^ (rgiSp α m - 1) * rgiF2 α m c z
        = z ^ 2 * z ^ (rgiSp α m - 1) * (c z * z ^ (-1 - rgiSp α m)) := by rw [hf]
      _ = c z * (z ^ 2 * z ^ (rgiSp α m - 1) * z ^ (-1 - rgiSp α m)) := by ring
      _ = c z * 1 := by rw [hcomb]
      _ = c z := by ring
  have hzA1 : z * rgiD1 α m c z = rgiK α m * (rgiSn α m * (z ^ (rgiSn α m) * rgiA α m c z)
      + rgiSp α m * (z ^ (rgiSp α m) * rgiB α m c z)) := by
    simp only [rgiD1]
    linear_combination (rgiK α m * rgiSn α m * rgiA α m c z) * hzs1
      + (rgiK α m * rgiSp α m * rgiB α m c z) * hzp1
  have hzA2 : z ^ 2 * rgD2 α m c z
      = rgiK α m * (rgiSn α m * (rgiSn α m - 1) * (z ^ (rgiSn α m) * rgiA α m c z)
        + rgiSp α m * (rgiSp α m - 1) * (z ^ (rgiSp α m) * rgiB α m c z)
        + (rgiSn α m - rgiSp α m) * c z) := by
    simp only [rgD2]
    linear_combination (rgiK α m * rgiSn α m * (rgiSn α m - 1) * rgiA α m c z) * hzs2
      + (rgiK α m * rgiSp α m * (rgiSp α m - 1) * rgiB α m c z) * hzp2
      + (rgiK α m * rgiSn α m) * hc1 - (rgiK α m * rgiSp α m) * hc2
  have hind1 : -α ^ 2 * rgiSn α m * (rgiSn α m - 1) - α * (5 + α) * rgiSn α m
      + Work.FTS.PhiStar.Radial.lamR m = 0 := by
    simp only [rgiSn, Work.FTS.PhiStar.Radial.lamR]
    field_simp
    ring
  have hind2 : -α ^ 2 * rgiSp α m * (rgiSp α m - 1) - α * (5 + α) * rgiSp α m
      + Work.FTS.PhiStar.Radial.lamR m = 0 := by
    simp only [rgiSp, Work.FTS.PhiStar.Radial.lamR]
    field_simp
    ring
  have hK : α ^ 2 * rgiK α m * (rgiSp α m - rgiSn α m) = 1 := by
    simp only [rgiK, rgiSp, rgiSn]
    field_simp
    ring
  linear_combination (-(α ^ 2)) * hzA2 - (α * (5 + α)) * hzA1
    + (rgiK α m * (z ^ (rgiSn α m) * rgiA α m c z)) * hind1
    + (rgiK α m * (z ^ (rgiSp α m) * rgiB α m c z)) * hind2 + (c z) * hK

end Work.FTS.PhiStar.RadGreenSupport
