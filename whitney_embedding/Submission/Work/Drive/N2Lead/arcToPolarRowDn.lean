import Mathlib
import Submission.Work.Drive.N2Lead.mobiusUpperCoreKit

/-!
# `arcToPolarRowDn`: the nondegeneracy row of the lower arc transfers to the polar picture

The two curve families of the twisted Möbius picture are related by

  `polarPic r Dp εp ε (Θ (tauL u)) = dnCurve ηs Dp εp ε u`   (`u ∈ Icc (-m) m`),

which is the content of the hypotheses `hThetal` (the polar angle of the lower arc is
`3π/2 + arctan (u/ηs)/2`) and `hpolarL` (the polar point of that angle is `star (arcZ ηs u)`)
together with the definition of the three pictures in `mobiusUpperCoreKit`.

The row that has to be transferred is the *radial nondegeneracy* of the picture at the point: for a
planar curve `γ` the quantity `(star (γ t) * deriv γ t).im` is (minus) the determinant of
`(γ t, γ' t)`, so it vanishes exactly when the curve is tangent to the radial direction.  Since
`w` lies in the *open* interval `Ioo (-m) m`, the identity above holds on a whole neighbourhood of
`w`, so the chain rule gives

  `deriv (dnCurve ·) w = deriv (polarPic ·) (Θ (tauL w)) * deriv (Θ ∘ tauL) w`.

The only algebra then needed is `Im (z * (c : ℂ)) = c * Im z` for real `c`: the imaginary part of
the lower-arc product is the polar product's imaginary part *times* `deriv (Θ ∘ tauL) w`, so the
former can only be nonzero if the latter is.  (In particular no hypothesis on `deriv Θ` is needed:
the nondegeneracy of `deriv tauL` is what makes `Θ ∘ tauL` a genuine reparametrisation, and the
conclusion already follows without ever inverting it.)
-/

namespace Work.Drive.N2Lead

open scoped Manifold ContDiff Topology
open Set Filter

noncomputable section

/-- **Transfer of the radial nondegeneracy row along a reparametrisation.**  If `F ∘ f` agrees with
`G` near `x` and `G` is radially nondegenerate at `x`, then `F` is radially nondegenerate at
`f x`.  No hypothesis on `deriv f x` (in particular none of nonvanishing) is needed: the chain rule
`deriv G x = deriv F (f x) * deriv f x` together with `Im (z * (c : ℂ)) = c * Im z` for real `c`
already forces both real factors to be nonzero. -/
lemma im_star_mul_deriv_ne_zero_of_eventuallyEq {F G : ℝ → ℂ} {f : ℝ → ℝ} {x : ℝ}
    (hF : DifferentiableAt ℝ F (f x)) (hf : DifferentiableAt ℝ f x)
    (hev : (fun y => F (f y)) =ᶠ[𝓝 x] G)
    (hG : (star (G x) * deriv G x).im ≠ 0) :
    (star (F (f x)) * deriv F (f x)).im ≠ 0 := by
  have hFG : F (f x) = G x := hev.eq_of_nhds
  have hcomp : deriv (fun y => F (f y)) x = deriv F (f x) * deriv f x := by
    have h := deriv.scomp (𝕜 := ℝ) (𝕜' := ℝ) (F := ℂ) (h := f) (g₁ := F) x hF hf
    simpa [Function.comp_def, smul_eq_mul, mul_comm] using h
  have hderivG : deriv G x = deriv F (f x) * deriv f x := by
    rw [← hev.deriv_eq]
    exact hcomp
  intro hzero
  apply hG
  rw [← hFG, hderivG]
  have hcast : star (F (f x)) * (deriv F (f x) * ((deriv f x : ℝ) : ℂ))
      = (star (F (f x)) * deriv F (f x)) * ((deriv f x : ℝ) : ℂ) := by ring
  rw [hcast, Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re, hzero]
  ring

theorem arcToPolarRowDn {ηs m ε εp Dp : ℝ} {r Θ tauL : ℝ → ℝ}
    (hηs : 0 < ηs) (hm : 0 < m) (hε : 0 < ε) (hεp : 0 < εp) (hDp : 0 ≤ Dp)
    (hrsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) r)
    (hΘsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Θ)
    (hThetal : ∀ u ∈ Set.Icc (-m) m, Θ (tauL u) = 3 * Real.pi / 2 + (1 / 2) * Real.arctan (u / ηs))
    (hpolarL : ∀ u ∈ Set.Icc (-m) m,
      (r (Θ (tauL u)) : ℂ) * Complex.exp (((Θ (tauL u) : ℝ) : ℂ) * Complex.I)
        = star (Work.Drive.N2Lead.arcZ ηs u))
    {w : ℝ} (hw : w ∈ Set.Ioo (-m) m)
    (hτl : DifferentiableAt ℝ tauL w ∧ deriv tauL w ≠ 0)
    (hcurve : (star (Work.Drive.N2Lead.dnCurve ηs Dp εp ε w)
        * deriv (Work.Drive.N2Lead.dnCurve ηs Dp εp ε) w).im ≠ 0) :
    (star (Work.Drive.N2Lead.polarPic r Dp εp ε (Θ (tauL w)))
        * deriv (Work.Drive.N2Lead.polarPic r Dp εp ε) (Θ (tauL w))).im ≠ 0 := by
  -- the two pictures agree on the whole closed interval, hence near `w`
  have hident : ∀ u ∈ Set.Icc (-m) m,
      polarPic r Dp εp ε (Θ (tauL u)) = dnCurve ηs Dp εp ε u := by
    intro u hu
    have h1 := hpolarL u hu
    simp only [polarPic, dnCurve, h1]
  have hev : (fun y : ℝ => polarPic r Dp εp ε (Θ (tauL y))) =ᶠ[𝓝 w] dnCurve ηs Dp εp ε :=
    Filter.eventually_of_mem
      (Filter.mem_of_superset (isOpen_Ioo.mem_nhds hw) Set.Ioo_subset_Icc_self) hident
  -- transfer the row
  exact im_star_mul_deriv_ne_zero_of_eventuallyEq
    (F := polarPic r Dp εp ε) (G := dnCurve ηs Dp εp ε) (f := fun y : ℝ => Θ (tauL y)) (x := w)
    ((contDiff_polarPic hrsm Dp εp ε).differentiable (by simp)).differentiableAt
    (((hΘsm.differentiable (by simp)).differentiableAt).comp w hτl.1) hev hcurve

end

end Work.Drive.N2Lead
