import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Order.CompletePartialOrder
import Submission.Work.EllipticEst.ModalSolution.RGW.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open MeasureTheory Set Filter
open scoped Real Topology

namespace Work.EllipticEst.ModalSolution.RGW

open Work.EllipticEst.ModalSolution.RadGreenWeak (Lneg pwt wgt qW)

/-!
# The Lagrange identity (Green's formula) for the radial operator `Lneg`

`Lneg α u z = -(α²z²u''(z) + α(5+α)zu'(z))` is, on `(0,∞)`, in divergence form with respect to
the weight `wgt α z = z^q`, `q = (5-α)/α`:

`(v · Lneg ψ - Lneg v · ψ) · z^q = (pwt · (v'ψ - vψ'))'`   with  `pwt α z = α²z²z^q`.

The key algebraic fact is `α²(q + 2) = α(5 + α)`, which is exactly the choice `q = (5-α)/α`.
Integrating over `[c,d] ⊂ (0,∞)` gives the stated boundary formula.
-/

/-- The Lagrange coefficient `pwt α z = α²z²z^q` is differentiable on `(0,∞)`, with derivative
`α(5+α) z z^q`.  (This is where `q = (5-α)/α` enters: `α²(q+2) = α(5+α)`.) -/
theorem pwt_hasDerivAt (α : ℝ) {z : ℝ} (hz : 0 < z) :
    HasDerivAt (pwt α) (α * (5 + α) * z * wgt α z) z := by
  have hz' : z ≠ 0 := ne_of_gt hz
  have hq : HasDerivAt (fun t : ℝ => t ^ (qW α)) (qW α * z ^ (qW α - 1)) z :=
    Real.hasDerivAt_rpow_const (Or.inl hz')
  have hp : HasDerivAt (fun t : ℝ => t ^ 2) (2 * z) z := by
    simpa using hasDerivAt_pow 2 z
  have hmul : HasDerivAt (fun t : ℝ => t ^ 2 * t ^ (qW α))
      (2 * z * z ^ qW α + z ^ 2 * (qW α * z ^ (qW α - 1))) z := hp.mul hq
  have hcm := hmul.const_mul (α ^ 2)
  have hfun : (fun y : ℝ => α ^ 2 * (y ^ 2 * y ^ (qW α))) = pwt α := by
    funext y; simp [pwt, wgt]
  rw [hfun] at hcm
  have h2'' : z * z ^ (qW α - 1) = z ^ qW α := by
    calc z * z ^ (qW α - 1) = z ^ (1:ℝ) * z ^ (qW α - 1) := by rw [Real.rpow_one]
      _ = z ^ ((1:ℝ) + (qW α - 1)) := by rw [Real.rpow_add hz]
      _ = z ^ qW α := by congr 1; ring
  have hsq : z ^ 2 * z ^ (qW α - 1) = z * z ^ qW α := by
    rw [pow_two, mul_assoc, h2'']
  have hkey : α ^ 2 * (qW α + 2) = α * (5 + α) := by
    rcases eq_or_ne α 0 with h | h
    · subst h; norm_num [qW]
    · rw [qW]; field_simp; ring
  have heq : α ^ 2 * (2 * z * z ^ qW α + z ^ 2 * (qW α * z ^ (qW α - 1)))
      = α * (5 + α) * z * wgt α z := by
    have h2 : z ^ 2 * (qW α * z ^ (qW α - 1)) = z ^ 2 * z ^ (qW α - 1) * qW α := by ring
    rw [h2, hsq, wgt]
    have h3 : α ^ 2 * (2 * z * z ^ qW α + z * z ^ qW α * qW α)
        = (α ^ 2 * (qW α + 2)) * (z * z ^ qW α) := by ring
    rw [h3, hkey]
    ring
  rwa [heq] at hcm

/-- A `C²` function on `(0,∞)` has a differentiable first derivative there, with derivative given
by `deriv (deriv u)`. -/
theorem hasDerivAt_deriv_of_contDiffOn {u : ℝ → ℝ} (hu : ContDiffOn ℝ 2 u (Set.Ioi 0))
    {z : ℝ} (hz : 0 < z) :
    HasDerivAt (deriv u) (deriv (deriv u) z) z := by
  have h1 : ContDiffOn ℝ 1 (deriv u) (Set.Ioi 0) := hu.deriv_of_isOpen isOpen_Ioi (by norm_num)
  exact ((h1.contDiffAt (isOpen_Ioi.mem_nhds hz)).differentiableAt (by norm_num)).hasDerivAt

/-- A `C²` function on `(0,∞)` is differentiable there, with derivative `deriv u`. -/
theorem hasDerivAt_of_contDiffOn {u : ℝ → ℝ} (hu : ContDiffOn ℝ 2 u (Set.Ioi 0))
    {z : ℝ} (hz : 0 < z) :
    HasDerivAt u (deriv u z) z :=
  ((hu.contDiffAt (isOpen_Ioi.mem_nhds hz)).differentiableAt (by norm_num)).hasDerivAt

/-- `Lneg α u` is continuous on `(0,∞)` as soon as `u` is `C²` there. -/
theorem Lneg_continuousOn (α : ℝ) {u : ℝ → ℝ} (hu : ContDiffOn ℝ 2 u (Set.Ioi 0)) :
    ContinuousOn (fun z => Lneg α u z) (Set.Ioi 0) := by
  have h1 : ContDiffOn ℝ 1 (deriv u) (Set.Ioi 0) := hu.deriv_of_isOpen isOpen_Ioi (by norm_num)
  have hddu : ContinuousOn (deriv (deriv u)) (Set.Ioi 0) :=
    h1.continuousOn_deriv_of_isOpen isOpen_Ioi (by norm_num)
  have hdu : ContinuousOn (deriv u) (Set.Ioi 0) :=
    hu.continuousOn_deriv_of_isOpen isOpen_Ioi (by norm_num)
  unfold Lneg
  fun_prop

/-- Pointwise form of the Lagrange identity: on `(0,∞)` the function `pwt · (v'ψ - vψ')` is an
antiderivative of `(v · Lneg ψ - Lneg v · ψ) · wgt`. -/
theorem hasDerivAt_lagrange (α : ℝ) {v ψ : ℝ → ℝ}
    (hv : ContDiffOn ℝ 2 v (Set.Ioi 0)) (hψ : ContDiffOn ℝ 2 ψ (Set.Ioi 0)) :
    ∀ z : ℝ, 0 < z →
      HasDerivAt (fun y => pwt α y * (deriv v y * ψ y - v y * deriv ψ y))
        ((v z * Lneg α ψ z - Lneg α v z * ψ z) * wgt α z) z := by
  intro z hz
  have hP : HasDerivAt (fun y => deriv v y * ψ y - v y * deriv ψ y)
      (deriv (deriv v) z * ψ z - v z * deriv (deriv ψ) z) z := by
    have h1 : HasDerivAt (fun y => deriv v y * ψ y)
        (deriv (deriv v) z * ψ z + deriv v z * deriv ψ z) z :=
      (hasDerivAt_deriv_of_contDiffOn hv hz).mul (hasDerivAt_of_contDiffOn hψ hz)
    have h2 : HasDerivAt (fun y => v y * deriv ψ y)
        (deriv v z * deriv ψ z + v z * deriv (deriv ψ) z) z :=
      (hasDerivAt_of_contDiffOn hv hz).mul (hasDerivAt_deriv_of_contDiffOn hψ hz)
    exact (h1.sub h2).congr_deriv (by ring)
  have hm : HasDerivAt (fun y => pwt α y * (deriv v y * ψ y - v y * deriv ψ y))
      (α * (5 + α) * z * wgt α z * (deriv v z * ψ z - v z * deriv ψ z)
        + pwt α z * (deriv (deriv v) z * ψ z - v z * deriv (deriv ψ) z)) z :=
    (pwt_hasDerivAt α hz).mul hP
  refine hm.congr_deriv ?_
  simp only [Lneg, pwt, wgt]
  ring

theorem lagrange_ibp (α : ℝ) {v ψ : ℝ → ℝ} {c d : ℝ} (hc : 0 < c) (hcd : c ≤ d)
    (hv : ContDiffOn ℝ 2 v (Set.Ioi 0)) (hψ : ContDiffOn ℝ 2 ψ (Set.Ioi 0)) :
    ∫ z in Set.Icc c d,
        (v z * Work.EllipticEst.ModalSolution.RadGreenWeak.Lneg α ψ z
          - Work.EllipticEst.ModalSolution.RadGreenWeak.Lneg α v z * ψ z)
          * Work.EllipticEst.ModalSolution.RadGreenWeak.wgt α z
      = Work.EllipticEst.ModalSolution.RadGreenWeak.pwt α d * (deriv v d * ψ d - v d * deriv ψ d)
        - Work.EllipticEst.ModalSolution.RadGreenWeak.pwt α c * (deriv v c * ψ c - v c * deriv ψ c) := by
  have hderiv : ∀ z ∈ Set.Icc c d,
      HasDerivAt (fun y => pwt α y * (deriv v y * ψ y - v y * deriv ψ y))
        ((v z * Lneg α ψ z - Lneg α v z * ψ z) * wgt α z) z := by
    intro z hz
    exact hasDerivAt_lagrange α hv hψ z (lt_of_lt_of_le hc hz.1)
  have hcont : ContinuousOn (fun z => (v z * Lneg α ψ z - Lneg α v z * ψ z) * wgt α z)
      (Set.Icc c d) := by
    have hsub : Set.Icc c d ⊆ Set.Ioi 0 := fun z hz => lt_of_lt_of_le hc hz.1
    have hb : ContinuousOn (fun z => v z * Lneg α ψ z - Lneg α v z * ψ z) (Set.Ioi 0) :=
      (hv.continuousOn.mul (Lneg_continuousOn α hψ)).sub
        ((Lneg_continuousOn α hv).mul hψ.continuousOn)
    have hw : ContinuousOn (wgt α) (Set.Ioi 0) := fun z hz =>
      (Real.continuousAt_rpow_const z (qW α) (Or.inl (ne_of_gt hz))).continuousWithinAt
    exact (hb.mono hsub).mul (hw.mono hsub)
  have hint : IntervalIntegrable
      (fun z => (v z * Lneg α ψ z - Lneg α v z * ψ z) * wgt α z) volume c d :=
    hcont.intervalIntegrable_of_Icc hcd
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun y => pwt α y * (deriv v y * ψ y - v y * deriv ψ y))
    (f' := fun z => (v z * Lneg α ψ z - Lneg α v z * ψ z) * wgt α z)
    (fun z hz => hderiv z (by rw [Set.uIcc_of_le hcd] at hz; exact hz)) hint
  have hIcc : (∫ z in Set.Icc c d, (v z * Lneg α ψ z - Lneg α v z * ψ z) * wgt α z)
      = ∫ z in c..d, (v z * Lneg α ψ z - Lneg α v z * ψ z) * wgt α z := by
    rw [integral_Icc_eq_integral_Ioc, intervalIntegral.integral_of_le hcd]
  rw [hIcc, hFTC]

end Work.EllipticEst.ModalSolution.RGW
