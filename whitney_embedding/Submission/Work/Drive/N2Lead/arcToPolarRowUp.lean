import Mathlib
import Submission.Work.Drive.N2Lead.mobiusUpperCoreKit

/-!
# The transfer of the "star row" from the upper arc to the polar curve

The rows of the twisted Möbius upper picture are stated for three curve families, related on the pin
interval by
`polarPic r Dp εp ε (Θ (tauU u)) = upCurve ηs Dp εp ε u`
(`Work.Drive.N2Lead.polarPic`, `Work.Drive.N2Lead.upCurve`; the identity is `hpolarU`).

This file proves the transfer of the *non-degeneracy of the "star row"*
`(star z * z').im ≠ 0` along such a change of parameter: if the upper arc picture has non-vanishing
star row at `w`, and the two curves agree on a neighbourhood of `w` up to the reparametrisation
`u ↦ Θ (tauU u)`, then the polar picture has non-vanishing star row at `Θ (tauU w)`.

The point is the elementary identity
`(star z * (z' * L)).im = (star z * z').im * L` for a *real* scalar `L = deriv (Θ ∘ tauU) w`
(the imaginary part of `star z * z'` is the signed area rate `|z|² φ'`, which scales by the change of
variable): a non-zero value cannot become zero by multiplication with a real number, whatever that
number is (in particular one does not need `deriv (Θ ∘ tauU) w ≠ 0`).
-/

namespace Work.Drive.N2Lead

open scoped Manifold ContDiff Topology
open Set Filter

noncomputable section

/-- The elementary scaling identity behind the transfer: multiplying by a real scalar multiplies the
imaginary part of `star z * z'` by that scalar. -/
private lemma im_star_mul_real (z z' : ℂ) (L : ℝ) :
    (star z * (z' * (L : ℂ))).im = (star z * z').im * L := by
  have h : star z * (z' * (L : ℂ)) = (L : ℂ) * (star z * z') := by ring
  rw [h, Complex.mul_im]
  simp
  ring

/-- **The transfer of the star row along a reparametrisation.**  If the curve `G` agrees near `a`
with the reparametrised curve `F ∘ t`, and the star row of `G` does not vanish at `a`, then the star
row of `F` does not vanish at `t a`. -/
private lemma im_star_deriv_ne_zero_of_eventuallyEq_comp {F G : ℝ → ℂ} {t : ℝ → ℝ} {a : ℝ}
    (hFG : G =ᶠ[𝓝 a] F ∘ t)
    (hF : DifferentiableAt ℝ F (t a))
    (ht : DifferentiableAt ℝ t a)
    (hG : (star (G a) * deriv G a).im ≠ 0) :
    (star (F (t a)) * deriv F (t a)).im ≠ 0 := by
  have hGa : G a = F (t a) := hFG.eq_of_nhds
  have hderiv : deriv G a = deriv F (t a) * deriv t a := by
    rw [hFG.deriv_eq, deriv.scomp a hF ht, Complex.real_smul, mul_comm]
  have hkey : (star (F (t a)) * (deriv F (t a) * deriv t a)).im
      = (star (F (t a)) * deriv F (t a)).im * deriv t a := im_star_mul_real _ _ _
  intro h0
  apply hG
  rw [hGa, hderiv, hkey, h0, zero_mul]

theorem arcToPolarRowUp {ηs m ε εp Dp : ℝ} {r Θ tauU : ℝ → ℝ}
    (hηs : 0 < ηs) (hm : 0 < m) (hε : 0 < ε) (hεp : 0 < εp) (hDp : 0 ≤ Dp)
    (hrsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) r)
    (hΘsm : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) Θ)
    (hThetau : ∀ u ∈ Set.Icc (-m) m, Θ (tauU u) = Real.pi / 2 - (1 / 2) * Real.arctan (u / ηs))
    (hpolarU : ∀ u ∈ Set.Icc (-m) m,
      (r (Θ (tauU u)) : ℂ) * Complex.exp (((Θ (tauU u) : ℝ) : ℂ) * Complex.I)
        = Work.Drive.N2Lead.arcZ ηs u)
    {w : ℝ} (hw : w ∈ Set.Ioo (-m) m)
    (hτu : DifferentiableAt ℝ tauU w ∧ deriv tauU w ≠ 0)
    (hcurve : (star (Work.Drive.N2Lead.upCurve ηs Dp εp ε w)
        * deriv (Work.Drive.N2Lead.upCurve ηs Dp εp ε) w).im ≠ 0) :
    (star (Work.Drive.N2Lead.polarPic r Dp εp ε (Θ (tauU w)))
        * deriv (Work.Drive.N2Lead.polarPic r Dp εp ε) (Θ (tauU w))).im ≠ 0 := by
  have hFdiff : DifferentiableAt ℝ (polarPic r Dp εp ε) (Θ (tauU w)) :=
    ((contDiff_polarPic hrsm Dp εp ε).differentiable (by simp)).differentiableAt
  have hΘdiff : DifferentiableAt ℝ Θ (tauU w) :=
    (hΘsm.differentiable (by simp)).differentiableAt
  have htdiff : DifferentiableAt ℝ (fun u : ℝ => Θ (tauU u)) w :=
    hΘdiff.comp w hτu.1
  have hIcc : ∀ᶠ u in 𝓝 w, u ∈ Set.Icc (-m) m :=
    Filter.eventually_of_mem (isOpen_Ioo.mem_nhds hw) (fun u hu => Set.Ioo_subset_Icc_self hu)
  have hFG : (upCurve ηs Dp εp ε) =ᶠ[𝓝 w]
      polarPic r Dp εp ε ∘ (fun u : ℝ => Θ (tauU u)) := by
    filter_upwards [hIcc] with u hu
    simp only [Function.comp_apply, upCurve, polarPic]
    rw [hpolarU u hu]
  exact im_star_deriv_ne_zero_of_eventuallyEq_comp (F := polarPic r Dp εp ε)
    (G := upCurve ηs Dp εp ε) (t := fun u : ℝ => Θ (tauU u)) (a := w) hFG hFdiff htdiff hcurve

end

end Work.Drive.N2Lead
