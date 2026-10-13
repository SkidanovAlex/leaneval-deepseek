/-
Copyright: work module for the Elgindi finite-time singularity project.

# `H2W/Ae/AngSliceBound` — the angular first-order bound from the second-order one

In the almost-everywhere class `AeData` the *second* angular derivative `∂_θθ u` is honest
(`AeData.memAng2`), while the first one is not directly controlled.  This module proves that the
first one follows from the second by the elementary one-dimensional chain

  `f'(θ) = f'(θ₀) + ∫_{θ₀}^{θ} f''`   (Rolle: `f'(θ₀) = 0` since `f(0) = f(π/2) = 0`),
  `(f'(θ))² ≤ (∫_{Iθ} |f''|)² ≤ (∫_{Iθ} (f'')² σ) · (∫_{Iθ} σ^{-1})`  (Cauchy–Schwarz),

with `σ = sin(2θ)^{-η}` and `∫_{Iθ} σ^{-1} = ∫_{Iθ} sin(2θ)^η ≤ π/2`.  Hence, uniformly on the
fibre, `(f')² ≤ (π/2)² ∫_{Iθ} (f'')² σ`, and integrating against `w(z)²` in `z`,

```
L2Mem (fun z θ => pth u z θ * w z) ∧
L2Sq (fun z θ => pth u z θ * w z) ≤ (π/2)^2 * HkSq α 0 (pthIter 2 u).
```

This replaces the `|∂_θΨ w| ≤ |F w|` step of the paper's Step 1 (`prop:H2`): the angular half of
Step 1 is reduced to the *single* statement `HkSq α 0 (∂_θθ u) ≤ C HkSq α 0 G`, with no
truncated energy identity involved.
-/
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.LocalExtr.Rolle
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Order.CompletePartialOrder
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.ProductTools
import Submission.Work.Spaces.cs_integral
import Submission.Work.FTS.EllipticEst.Defs
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.FTS.EllipticEst.ThetaPoincareDefs
import Submission.Work.FTS.EllipticEst.Honest.Basic
import Submission.Work.FTS.EllipticEst.H2W.Ae.Defs
import Submission.Work.FTS.EllipticEst.Endpt.sliceBdd_of_hmB
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Spaces.aesm_slice_of_continuousOn_Qd
import Submission.Work.FTS.H2.Transport3Aux.num_int_1d_aux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.H2W.Ae

set_option autoImplicit false

open Work.FTS.EllipticEst (sEta thEta)

/-! ## Cauchy–Schwarz with the `σ`-weight, on the open interval -/

/-- `(x ^ a) ^ 2 = x ^ (2 * a)` for `x > 0` (`rpow_sq_of_pos` of `slice_cs_weighted`, which is
`private` there). -/
private lemma rpow_sq_of_pos (x a : ℝ) (hx : 0 < x) : (x ^ a) ^ 2 = x ^ (2 * a) := by
  rw [← Real.rpow_mul_natCast hx.le a 2]
  ring_nf

/-- **The weighted Cauchy–Schwarz of `slice_cs_weighted`, with the continuity hypothesis on the
open interval only.**  For `g` continuous on `(0, π/2)` whose `σ`-weighted square is integrable,

`(∫_{Iθ} |g|)² ≤ (∫_{Iθ} g² σ) · (∫_{Iθ} σ^{-1})`,   `σ^{-1} = sin(2θ)^η`. -/
theorem cs_weighted_open {g : ℝ → ℝ}
    (hg : ContinuousOn g (Set.Ioo 0 (Real.pi / 2)))
    (hint : IntegrableOn (fun θ => (g θ) ^ 2 * sEta θ) Work.Spaces.Iθ) :
    (∫ θ in Work.Spaces.Iθ, |g θ|) ^ 2
      ≤ (∫ θ in Work.Spaces.Iθ, (g θ) ^ 2 * sEta θ)
        * (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (Work.Spaces.eta)) := by
  have hIoomeas : MeasurableSet (Set.Ioo (0 : ℝ) (Real.pi / 2)) := measurableSet_Ioo
  have hsub : Set.Ioo (0 : ℝ) (Real.pi / 2) ⊆ Work.Spaces.Iθ := by
    intro x hx
    rw [Work.Spaces.Iθ, Set.mem_Icc]
    exact ⟨le_of_lt hx.1, le_of_lt hx.2⟩
  have hsinpos : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), 0 < Real.sin (2 * θ) :=
    fun θ hθ => Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
      (by linarith [hθ.2, Real.pi_pos])
  have hsincont : ContinuousOn (fun θ : ℝ => Real.sin (2 * θ))
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    Real.continuous_sin.comp_continuousOn ((continuous_const.mul continuous_id).continuousOn)
  have hwcont : ContinuousOn
      (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta / 2)))
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    hsincont.rpow_const (fun θ hθ => Or.inl (ne_of_gt (hsinpos θ hθ)))
  have hvcont : ContinuousOn
      (fun θ : ℝ => (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    hsincont.rpow_const (fun θ hθ => Or.inr (by rw [Work.Spaces.eta]; norm_num))
  have hucont : ContinuousOn
      (fun θ : ℝ => |g θ| * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta / 2)))
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) := hg.abs.mul hwcont
  have huaesm : AEStronglyMeasurable
      (fun θ : ℝ => |g θ| * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta / 2)))
      (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) :=
    hucont.aestronglyMeasurable hIoomeas
  have hvaesm : AEStronglyMeasurable
      (fun θ : ℝ => (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))
      (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) :=
    hvcont.aestronglyMeasurable hIoomeas
  have hEq1 : Set.EqOn (fun θ : ℝ => (g θ) ^ 2 * sEta θ)
      (fun θ : ℝ => (|g θ| * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta / 2))) ^ 2)
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    intro θ hθ
    have hx : 0 < Real.sin (2 * θ) := hsinpos θ hθ
    show (g θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))
      = (|g θ| * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta / 2))) ^ 2
    rw [mul_pow, sq_abs, rpow_sq_of_pos _ _ hx,
      show 2 * (-(Work.Spaces.eta / 2)) = -(Work.Spaces.eta) by ring]
  have hEq2 : Set.EqOn (fun θ : ℝ => (Real.sin (2 * θ)) ^ (Work.Spaces.eta))
      (fun θ : ℝ => ((Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2)
      (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    intro θ hθ
    show (Real.sin (2 * θ)) ^ (Work.Spaces.eta)
      = ((Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2
    rw [rpow_sq_of_pos _ _ (hsinpos θ hθ),
      show 2 * (Work.Spaces.eta / 2) = Work.Spaces.eta by ring]
  have hu2int : MeasureTheory.Integrable
      (fun θ : ℝ => (|g θ| * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta / 2))) ^ 2)
      (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) :=
    (hint.mono_set hsub).congr_fun hEq1 hIoomeas
  have hv2int : MeasureTheory.Integrable
      (fun θ : ℝ => ((Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) ^ 2)
      (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) :=
    ((Work.FTS.EllipticEst.integrableOn_sin_two_rpow
      Work.Spaces.eta_nonneg).1.mono_set hsub).congr_fun hEq2 hIoomeas
  have humem : MeasureTheory.MemLp
      (fun θ : ℝ => |g θ| * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta / 2))) 2
      (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) :=
    (MeasureTheory.memLp_two_iff_integrable_sq huaesm).mpr hu2int
  have hvmems : MeasureTheory.MemLp
      (fun θ : ℝ => (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)) 2
      (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) :=
    (MeasureTheory.memLp_two_iff_integrable_sq hvaesm).mpr hv2int
  have hcs := Work.Spaces.cs_integral humem hvmems
  have e1 : (∫ x in Set.Ioo (0 : ℝ) (Real.pi / 2),
        (|g x| * (Real.sin (2 * x)) ^ (-(Work.Spaces.eta / 2)))
          * (Real.sin (2 * x)) ^ (Work.Spaces.eta / 2))
      = ∫ x in Set.Ioo (0 : ℝ) (Real.pi / 2), |g x| := by
    refine MeasureTheory.setIntegral_congr_fun hIoomeas ?_
    intro x hx
    have hx' : 0 < Real.sin (2 * x) := hsinpos x hx
    show (|g x| * (Real.sin (2 * x)) ^ (-(Work.Spaces.eta / 2)))
        * (Real.sin (2 * x)) ^ (Work.Spaces.eta / 2) = |g x|
    rw [mul_assoc, ← Real.rpow_add hx',
      show -(Work.Spaces.eta / 2) + Work.Spaces.eta / 2 = 0 by ring, Real.rpow_zero,
      mul_one]
  have e2 : (∫ x in Set.Ioo (0 : ℝ) (Real.pi / 2),
        (|g x| * (Real.sin (2 * x)) ^ (-(Work.Spaces.eta / 2))) ^ 2)
      = ∫ x in Set.Ioo (0 : ℝ) (Real.pi / 2), (g x) ^ 2 * sEta x := by
    refine MeasureTheory.setIntegral_congr_fun hIoomeas ?_
    intro x hx
    have hx' : 0 < Real.sin (2 * x) := hsinpos x hx
    show (|g x| * (Real.sin (2 * x)) ^ (-(Work.Spaces.eta / 2))) ^ 2
      = (g x) ^ 2 * (Real.sin (2 * x)) ^ (-(Work.Spaces.eta))
    rw [mul_pow, sq_abs, rpow_sq_of_pos _ _ hx',
      show 2 * (-(Work.Spaces.eta / 2)) = -(Work.Spaces.eta) by ring]
  have e3 : (∫ x in Set.Ioo (0 : ℝ) (Real.pi / 2),
        ((Real.sin (2 * x)) ^ (Work.Spaces.eta / 2)) ^ 2)
      = ∫ x in Set.Ioo (0 : ℝ) (Real.pi / 2), (Real.sin (2 * x)) ^ (Work.Spaces.eta) := by
    refine MeasureTheory.setIntegral_congr_fun hIoomeas ?_
    intro x hx
    show ((Real.sin (2 * x)) ^ (Work.Spaces.eta / 2)) ^ 2
      = (Real.sin (2 * x)) ^ (Work.Spaces.eta)
    rw [rpow_sq_of_pos _ _ (hsinpos x hx),
      show 2 * (Work.Spaces.eta / 2) = Work.Spaces.eta by ring]
  rw [e1, e2, e3] at hcs
  -- transfer the three integrals from `Ioo 0 (π/2)` to `Iθ`
  have ht1 : (∫ x in Work.Spaces.Iθ, |g x|)
      = ∫ x in Set.Ioo (0 : ℝ) (Real.pi / 2), |g x| :=
    MeasureTheory.setIntegral_congr_set
      (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume)).symm
  have ht2 : (∫ x in Work.Spaces.Iθ, (g x) ^ 2 * sEta x)
      = ∫ x in Set.Ioo (0 : ℝ) (Real.pi / 2), (g x) ^ 2 * sEta x :=
    MeasureTheory.setIntegral_congr_set
      (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume)).symm
  have ht3 : (∫ x in Work.Spaces.Iθ, (Real.sin (2 * x)) ^ (Work.Spaces.eta))
      = ∫ x in Set.Ioo (0 : ℝ) (Real.pi / 2), (Real.sin (2 * x)) ^ (Work.Spaces.eta) :=
    MeasureTheory.setIntegral_congr_set
      (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume)).symm
  rw [ht1, ht2, ht3]
  exact hcs


/-! ## The one-dimensional slice bound -/

/-- **The `σ`-Newton–Leibniz bound on a fibre.**  For a fibre `f` of class `C²` on `(0, π/2)`,
continuous on `[0, π/2]` with `f 0 = f (π/2) = 0`, whose second derivative is
square-integrable against `σ = sin(2θ)^{-η}`:

`(f'(θ))² ≤ (π/2) · ∫_θ (f'')² σ`   for `θ` in the *open* angular interval

(the two endpoints of `Iθ` carry no mass and are irrelevant). -/
theorem slice_pth_sq_le_pointwise (f : ℝ → ℝ)
    (hcd : ContDiffOn ℝ 2 f (Set.Ioo 0 (Real.pi / 2)))
    (hcont : ContinuousOn f (Set.Icc 0 (Real.pi / 2)))
    (h0 : f 0 = 0) (h1 : f (Real.pi / 2) = 0)
    (hint : IntegrableOn (fun θ => (deriv (deriv f) θ) ^ 2 * sEta θ) Work.Spaces.Iθ) :
    ∀ θ ∈ Set.Ioo 0 (Real.pi / 2), (deriv f θ) ^ 2
      ≤ (Real.pi / 2) * (∫ θ in Work.Spaces.Iθ,
          (deriv (deriv f) θ) ^ 2 * sEta θ) := by
  have hpi : (0 : ℝ) < Real.pi / 2 := by positivity
  have hIoo : IsOpen (Set.Ioo (0 : ℝ) (Real.pi / 2)) := isOpen_Ioo
  -- Rolle: a point with vanishing first derivative
  obtain ⟨θ₀, hθ₀mem, hθ₀⟩ := exists_deriv_eq_zero hpi hcont (by rw [h0, h1])
  have hθ₀0 : 0 < θ₀ := hθ₀mem.1
  have hθ₀1 : θ₀ < Real.pi / 2 := hθ₀mem.2
  -- the second derivative is continuous on the open interval
  have hd1 : ContDiffOn ℝ 1 (deriv f) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    hcd.deriv_of_isOpen hIoo (m := 1) (by norm_num)
  have hcont2 : ContinuousOn (fun θ => deriv (deriv f) θ) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    hd1.continuousOn_deriv_of_isOpen hIoo (le_refl 1)
  -- the weighted second-derivative mass
  set A : ℝ := ∫ θ in Work.Spaces.Iθ, (deriv (deriv f) θ) ^ 2 * sEta θ with hA
  have hA0 : 0 ≤ A := by
    rw [hA]
    exact MeasureTheory.setIntegral_nonneg measurableSet_Icc fun θ hθ =>
      mul_nonneg (sq_nonneg _)
        (Real.rpow_nonneg (Work.FTS.EllipticEst.Honest.sin_two_nonneg_of_mem_Iθ hθ) _)
  -- `σ ≥ 1` on the open interval
  have hsig : ∀ x ∈ Set.Ioo (0 : ℝ) (Real.pi / 2), (1 : ℝ) ≤ sEta x := by
    intro x hx
    have hs0 : 0 < Real.sin (2 * x) :=
      Real.sin_pos_of_pos_of_lt_pi (by linarith [hx.1]) (by linarith [hx.2, Real.pi_pos])
    have hs1 : Real.sin (2 * x) ≤ 1 := Real.sin_le_one _
    have hz : -(Work.Spaces.eta) ≤ 0 := by have := Work.Spaces.eta_nonneg; linarith
    exact Real.one_le_rpow_of_pos_of_le_one_of_nonpos hs0 hs1 hz
  -- `σ` is continuous on the open interval
  have hsEta_cont : ContinuousOn (fun x => sEta x) (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
    have hs : ContinuousOn (fun x : ℝ => Real.sin (2 * x)) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
      Real.continuous_sin.comp_continuousOn
        ((continuous_const.mul continuous_id).continuousOn)
    refine hs.rpow_const fun x hx => Or.inl (ne_of_gt ?_)
    exact Real.sin_pos_of_pos_of_lt_pi (by linarith [hx.1]) (by linarith [hx.2, Real.pi_pos])
  -- the `σ`-weighted mass of a sub-interval of `(0, π/2)` is dominated by `A`
  have hIntσ : ∀ a b : ℝ, Set.uIcc a b ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) → a ≤ b →
      (∫ x in a..b, (deriv (deriv f) x) ^ 2 * sEta x) ≤ A := by
    intro a b hab hle
    rw [hA, intervalIntegral.integral_of_le hle]
    have hfnn : 0 ≤ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
        (fun x => (deriv (deriv f) x) ^ 2 * sEta x) := by
      change ∀ᵐ x ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
        0 ≤ (deriv (deriv f) x) ^ 2 * sEta x
      rw [show Work.Spaces.Iθ = Set.Icc (0 : ℝ) (Real.pi / 2) from rfl,
        MeasureTheory.ae_restrict_iff' measurableSet_Icc]
      exact Filter.Eventually.of_forall fun x hx =>
        mul_nonneg (sq_nonneg _)
          (Real.rpow_nonneg (Work.FTS.EllipticEst.Honest.sin_two_nonneg_of_mem_Iθ hx) _)
    refine MeasureTheory.setIntegral_mono_set hint hfnn ?_
    refine Filter.Eventually.of_forall fun x hx => ?_
    have hx' : x ∈ Set.uIcc a b :=
      Set.mem_uIcc.mpr (Or.inl ⟨le_of_lt hx.1, hx.2⟩)
    exact ⟨(hab hx').1.le, (hab hx').2.le⟩
  -- the unweighted mass is dominated by the weighted one, then by `A`
  have hmono : ∀ a b : ℝ, a ≤ b → Set.uIcc a b ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) →
      (∫ x in a..b, (deriv (deriv f) x) ^ 2) ≤ A := by
    intro a b hle hab
    have hc := hcont2.mono hab
    have hI2 : IntervalIntegrable (fun x => (deriv (deriv f) x) ^ 2) volume a b :=
      (hc.pow 2).intervalIntegrable
    have hI3 : IntervalIntegrable (fun x => (deriv (deriv f) x) ^ 2 * sEta x) volume a b :=
      ((hc.pow 2).mul (hsEta_cont.mono hab)).intervalIntegrable
    refine le_trans (intervalIntegral.integral_mono_on_of_le_Ioo hle hI2 hI3 ?_)
      (hIntσ a b hab hle)
    intro x hx
    have h1 : (1 : ℝ) ≤ sEta x :=
      hsig x (hab (Set.mem_uIcc.mpr (Or.inl ⟨le_of_lt hx.1, le_of_lt hx.2⟩)))
    calc (deriv (deriv f) x) ^ 2 = (deriv (deriv f) x) ^ 2 * 1 := by ring
      _ ≤ (deriv (deriv f) x) ^ 2 * sEta x := mul_le_mul_of_nonneg_left h1 (sq_nonneg _)
  intro θ hθ
  -- the fundamental theorem of calculus from the Rolle point
  have huIcc : Set.uIcc θ₀ θ ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
    intro x hx
    rw [Set.mem_uIcc] at hx
    rcases hx with ⟨hx1, hx2⟩ | ⟨hx1, hx2⟩
    · exact ⟨lt_of_lt_of_le hθ₀0 hx1, lt_of_le_of_lt hx2 hθ.2⟩
    · exact ⟨lt_of_lt_of_le hθ.1 hx1, lt_of_le_of_lt hx2 hθ₀1⟩
  have hInt1 : IntervalIntegrable (fun x => deriv (deriv f) x) volume θ₀ θ :=
    (hcont2.mono huIcc).intervalIntegrable
  have hInt2 : IntervalIntegrable (fun x => (deriv (deriv f) x) ^ 2) volume θ₀ θ :=
    ((hcont2.mono huIcc).pow 2).intervalIntegrable
  have hderiv_eq : deriv f θ = ∫ x in θ₀..θ, deriv (deriv f) x := by
    rw [← sub_zero (deriv f θ), ← hθ₀]
    exact (intervalIntegral.integral_deriv_eq_sub
      (fun x hx => (hd1.differentiableOn (by norm_num) x (huIcc hx)).differentiableAt
        (hIoo.mem_nhds (huIcc hx))) hInt1).symm
  rw [hderiv_eq]
  rcases le_total θ₀ θ with hle | hle
  · have h1 := Work.FTS.H2.Transport3Aux.sq_integral_le hle hInt1 hInt2
    have h2 := hmono θ₀ θ hle huIcc
    have h3 : θ - θ₀ ≤ Real.pi / 2 := by linarith [hθ.2, hθ₀0]
    nlinarith [h1, h2, hA0, h3]
  · have hs : (∫ x in θ₀..θ, deriv (deriv f) x) = -(∫ x in θ..θ₀, deriv (deriv f) x) :=
      intervalIntegral.integral_symm θ θ₀ (f := fun x => deriv (deriv f) x) (μ := volume)
    rw [hs]
    have hsneg : (-(∫ x in θ..θ₀, deriv (deriv f) x)) ^ 2
        = (∫ x in θ..θ₀, deriv (deriv f) x) ^ 2 := by ring
    have huIcc' : Set.uIcc θ θ₀ ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
      intro x hx
      rw [Set.mem_uIcc] at hx
      rcases hx with ⟨hx1, hx2⟩ | ⟨hx1, hx2⟩
      · exact ⟨lt_of_lt_of_le hθ.1 hx1, lt_of_le_of_lt hx2 hθ₀1⟩
      · exact ⟨lt_of_lt_of_le hθ₀0 hx1, lt_of_le_of_lt hx2 hθ.2⟩
    have hc' := hcont2.mono huIcc'
    have h1 := Work.FTS.H2.Transport3Aux.sq_integral_le hle
      hc'.intervalIntegrable (hc'.pow 2).intervalIntegrable
    have h2 := hmono θ θ₀ hle huIcc'
    have h3 : θ₀ - θ ≤ Real.pi / 2 := by linarith [hθ₀1, hθ.1]
    nlinarith [h1, h2, hA0, h3]

/-! ## The identification of the level-`0` integrand -/

/-- `(w / s^{η/2})² = w² s^{-η}` for `s > 0`. -/
private lemma div_rpow_sq (w s : ℝ) (hs : 0 < s) (η : ℝ) :
    (w / s ^ (η / 2)) ^ 2 = w ^ 2 * s ^ (-η) := by
  have h2 : (s ^ (η / 2)) ^ 2 = s ^ η := by
    rw [← Real.rpow_mul_natCast hs.le (η / 2) 2]
    ring_nf
  rw [div_pow, h2, Real.rpow_neg hs.le]
  ring

/-- **The level-`0` `ℋ`-integrand of a function is `(g·w)²·σ` on `Iθ`.** -/
theorem hkIntegrand_zero_eq_wsq (α : ℝ) (g : ℝ → ℝ → ℝ) {z : ℝ} {θ : ℝ}
    (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.Spaces.HkIntegrand α 0 g z θ
      = (g z θ) ^ 2 * (Work.Spaces.w z) ^ 2 * sEta θ := by
  rw [Work.FTS.EllipticEst.Honest.HkIntegrand_zero_eq]
  rw [Work.Spaces.Iθ, Set.mem_Icc] at hθ
  have hsE : sEta 0 = 0 := by
    show (Real.sin (2 * (0:ℝ))) ^ (-(Work.Spaces.eta)) = 0
    rw [show 2 * (0:ℝ) = 0 by ring, Real.sin_zero, Real.zero_rpow]
    rw [Work.Spaces.eta]; norm_num
  have hsEpi : sEta (Real.pi / 2) = 0 := by
    show (Real.sin (2 * (Real.pi / 2))) ^ (-(Work.Spaces.eta)) = 0
    rw [show 2 * (Real.pi / 2) = Real.pi by ring, Real.sin_pi, Real.zero_rpow]
    rw [Work.Spaces.eta]; norm_num
  rcases lt_or_eq_of_le hθ.1 with hθ0 | hθ0
  · rcases lt_or_eq_of_le hθ.2 with hθpi | hθpi
    · have hs : 0 < Real.sin (2 * θ) :=
        Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
      rw [mul_pow, div_rpow_sq (Work.Spaces.w z) (Real.sin (2 * θ)) hs Work.Spaces.eta]
      show (g z θ) ^ 2 * ((Work.Spaces.w z) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
        = (g z θ) ^ 2 * (Work.Spaces.w z) ^ 2 * sEta θ
      rw [show sEta θ = (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) from rfl]
      ring
    · subst hθpi
      have hsin : Real.sin (2 * (Real.pi / 2)) = 0 := by
        rw [show 2 * (Real.pi / 2) = Real.pi by ring, Real.sin_pi]
      rw [hsin,
        Real.zero_rpow (by rw [Work.Spaces.eta]; norm_num : Work.Spaces.eta / 2 ≠ 0),
        div_zero, mul_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), hsEpi]
      ring
  · subst hθ0
    have hsin : Real.sin (2 * (0 : ℝ)) = 0 := by
      rw [show 2 * (0 : ℝ) = 0 by ring, Real.sin_zero]
    rw [hsin,
      Real.zero_rpow (by rw [Work.Spaces.eta]; norm_num : Work.Spaces.eta / 2 ≠ 0),
      div_zero, mul_zero, zero_pow (by norm_num : (2 : ℕ) ≠ 0), hsE]
    ring

/-! ## The a.e. slice bound and the global estimate -/

/-- The interval integral over `0..π/2` is the set integral over `Iθ`. -/
private lemma intervalIntegral_eq_Iθ (f : ℝ → ℝ) :
    (∫ x in (0 : ℝ)..(Real.pi / 2), f x) = ∫ x in Work.Spaces.Iθ, f x := by
  have hpi : (0 : ℝ) ≤ Real.pi / 2 := by positivity
  rw [intervalIntegral.integral_of_le hpi,
    MeasureTheory.setIntegral_congr_set
      (MeasureTheory.Ioc_ae_eq_Icc (μ := MeasureTheory.volume))]
  rfl

/-- **The angular slice bound, almost everywhere in `z`.**  For a datum of the weak class whose
angular fibres are continuous on `[0, π/2]` for a.e. `z`,

`∫_θ (∂_θu(z,θ)·w z)² ≤ (π/2)² ∫_θ HkIntegrand α 0 (∂_θθu) z θ`

for a.e. `z`. -/
theorem aeData_ang_slice_bound (α : ℝ) (u G : ℝ → ℝ → ℝ) (h : AeData α u G)
    (hC : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      ContinuousOn (fun θ => u z θ) (Set.Icc 0 (Real.pi / 2))) :
    ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pth u z θ * Work.Spaces.w z) ^ 2)
        ≤ (Real.pi / 2) ^ 2 * (∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α 0 (Work.Spaces.pthIter 2 u) z θ) := by
  filter_upwards [hC, MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with z hCz hz
  have hzpos : 0 < z := hz
  have hzmem : z ∈ Work.Spaces.Iz := by rw [Work.Spaces.Iz]; exact le_of_lt hzpos
  -- the fibre is `C²` on the open interval
  have hzc : ContDiffOn ℝ 2 (fun θ => u z θ) (Set.Ioo 0 (Real.pi / 2)) := by
    have h1 : ContDiffOn ℝ 2 (Function.uncurry u)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := h.smooth 2
    have h2 := h1.comp (contDiff_prodMk_right z).contDiffOn (fun θ hθ => ⟨hzpos, hθ⟩)
    simpa [Function.comp_def] using h2
  -- the integrability of the `σ`-weighted second derivative, from `AeData.memAng2`
  set g : ℝ → ℝ := fun θ => (deriv (deriv (fun θ => u z θ)) θ) ^ 2 * sEta θ with hg
  have hbase : IntegrableOn (fun θ => (Work.Spaces.w z) ^ 2 * g θ) Work.Spaces.Iθ := by
    refine (h.memAng2.1 z hzmem).congr_fun_ae ?_
    filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Icc] with θ hθ
    rw [hkIntegrand_zero_eq_wsq α (Work.Spaces.pthIter 2 u) hθ]
    simp only [Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero, Work.Spaces.pth, hg]
    ring
  have hint : IntegrableOn g Work.Spaces.Iθ := by
    have hw : (Work.Spaces.w z) ^ 2 ≠ 0 := by
      have hw0 : Work.Spaces.w z ≠ 0 := by
        rw [Work.Spaces.w]
        exact div_ne_zero (pow_ne_zero 2 (by linarith)) (pow_ne_zero 2 hzpos.ne')
      exact pow_ne_zero 2 hw0
    have h1 := Integrable.const_mul hbase (((Work.Spaces.w z) ^ 2)⁻¹)
    have h2 : (fun θ => ((Work.Spaces.w z) ^ 2)⁻¹ * (((Work.Spaces.w z) ^ 2) * g θ)) = g := by
      funext θ
      exact inv_mul_cancel_left₀ hw (g θ)
    rw [h2] at h1
    exact h1
  -- the pointwise bound on the fibre
  have hpt := slice_pth_sq_le_pointwise (fun θ => u z θ) hzc hCz (h.dirZero z) (h.dirPi z) hint
  -- the fibre integral bound
  set M : ℝ := ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pthIter 2 u z θ) ^ 2 * sEta θ with hM
  have hM0 : 0 ≤ M := by
    rw [hM]
    exact MeasureTheory.setIntegral_nonneg measurableSet_Icc fun θ hθ =>
      mul_nonneg (sq_nonneg _)
        (Real.rpow_nonneg (Work.FTS.EllipticEst.Honest.sin_two_nonneg_of_mem_Iθ hθ) _)
  have hA : (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pth u z θ) ^ 2) ≤ (Real.pi / 2) ^ 2 * M := by
    have hle : (fun θ => (Work.Spaces.pth u z θ) ^ 2)
        ≤ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ] fun _ => (Real.pi / 2) * M := by
      have hmeas : MeasureTheory.volume.restrict Work.Spaces.Iθ
          = MeasureTheory.volume.restrict (Set.Ioo 0 (Real.pi / 2)) :=
        MeasureTheory.Measure.restrict_congr_set
          (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume)).symm
      rw [hmeas]
      filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioo] with θ hθ
      exact hpt θ hθ
    have hconst : Integrable (fun _ : ℝ => (Real.pi / 2) * M)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
      MeasureTheory.integrableOn_const (hs := by
        rw [show Work.Spaces.Iθ = Set.Icc (0 : ℝ) (Real.pi / 2) from rfl]
        exact (isCompact_Icc.measure_lt_top).ne) (C := (Real.pi / 2) * M)
    have hmono := MeasureTheory.integral_mono_of_nonneg
      (μ := MeasureTheory.volume.restrict Work.Spaces.Iθ)
      (Filter.Eventually.of_forall fun θ => sq_nonneg _) hconst hle
    rw [← intervalIntegral_eq_Iθ (fun θ => (Work.Spaces.pth u z θ) ^ 2),
      ← intervalIntegral_eq_Iθ (fun _ : ℝ => (Real.pi / 2) * M)] at hmono
    rw [intervalIntegral.integral_const] at hmono
    simp only [smul_eq_mul, sub_zero] at hmono
    have hmono' : (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pth u z θ) ^ 2)
        ≤ (Real.pi / 2) * ((Real.pi / 2) * M) := by
      rw [← intervalIntegral_eq_Iθ (fun θ => (Work.Spaces.pth u z θ) ^ 2)]
      exact hmono
    calc (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pth u z θ) ^ 2)
        ≤ (Real.pi / 2) * ((Real.pi / 2) * M) := hmono'
      _ = (Real.pi / 2) ^ 2 * M := by ring
  -- combine with the identification of the integrand
  have heq1 : (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pth u z θ * Work.Spaces.w z) ^ 2)
      = (Work.Spaces.w z) ^ 2 * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pth u z θ) ^ 2) := by
    rw [← MeasureTheory.integral_const_mul]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun θ _ => ?_
    ring
  have heq2 : (∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α 0 (Work.Spaces.pthIter 2 u) z θ)
      = (Work.Spaces.w z) ^ 2 * M := by
    rw [hM, ← MeasureTheory.integral_const_mul]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc fun θ hθ => ?_
    rw [hkIntegrand_zero_eq_wsq α (Work.Spaces.pthIter 2 u) hθ]
    ring
  rw [heq1, heq2]
  have hw2 : 0 ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _
  nlinarith [hA, hw2, hM0]

/-! ## The global estimate -/

/-- **The angular half of Step 1 in the weak class.**  For `AeData α u G` whose angular fibres
are continuous on `[0, π/2]` for a.e. `z`,

`L2Sq (∂_θu · w) ≤ (π/2)² · HkSq α 0 (∂_θθu)`. -/
theorem L2Sq_pth_w_le (α : ℝ) (u G : ℝ → ℝ → ℝ) (h : AeData α u G)
    (hC : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      ContinuousOn (fun θ => u z θ) (Set.Icc 0 (Real.pi / 2))) :
    Work.Spaces.L2Sq (fun z θ => Work.Spaces.pth u z θ * Work.Spaces.w z)
      ≤ (Real.pi / 2) ^ 2 * Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 u) := by
  have hbase := aeData_ang_slice_bound α u G h hC
  -- transfer the a.e. statement from `Ioi 0` to `Iz = Ici 0`
  have hIz : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pth u z θ * Work.Spaces.w z) ^ 2)
        ≤ (Real.pi / 2) ^ 2 * (∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α 0 (Work.Spaces.pthIter 2 u) z θ) := by
    change ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ici 0)), _
    rw [MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := 0)).symm]
    exact hbase
  have hRHS : Integrable (fun z => (Real.pi / 2) ^ 2 * (∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α 0 (Work.Spaces.pthIter 2 u) z θ))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
    Integrable.const_mul h.memAng2.2 ((Real.pi / 2) ^ 2)
  have hnn : 0 ≤ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iz]
      (fun z => ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pth u z θ * Work.Spaces.w z) ^ 2) :=
    Filter.Eventually.of_forall fun z => integral_nonneg fun θ => sq_nonneg _
  have hmain := MeasureTheory.integral_mono_of_nonneg
    (μ := MeasureTheory.volume.restrict Work.Spaces.Iz) hnn hRHS hIz
  rw [MeasureTheory.integral_const_mul] at hmain
  exact hmain

/-! ## The `L²`-membership of `∂_θu · w` -/

/-- **`L2Mem` for the angular first derivative.**  Together with `L2Sq_pth_w_le` this is the
whole angular content of `aeFirstEnergy` (and the hypothesis `aeSigmaUp` consumes).  The
a.e.-continuity hypothesis on the fibres is the one supplied in tree by
`AeProof/AeSliceLeftTendstoAe` + `AeProof/AeGapSlices.ae_continuousOn_slice`. -/
theorem L2Mem_pth_w (α : ℝ) (u G : ℝ → ℝ → ℝ) (h : AeData α u G)
    (hC : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      ContinuousOn (fun θ => u z θ) (Set.Icc 0 (Real.pi / 2))) :
    Work.Spaces.L2Mem (fun z θ => Work.Spaces.pth u z θ * Work.Spaces.w z) := by
  have hso : Work.FTS.EllipticEst.SmoothOpen u :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  -- the joint a.e.-strong measurability of the uncurried integrand
  have hwcont : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.w p.1)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
    have hw : ContinuousOn Work.Spaces.w (Set.Ioi (0 : ℝ)) := by
      have h : Work.Spaces.w = fun z : ℝ => (1 + z) ^ 2 / z ^ 2 := rfl
      rw [h]
      refine ContinuousOn.div (by fun_prop) (by fun_prop) fun z hz => ?_
      exact pow_ne_zero 2 (ne_of_gt hz)
    exact hw.comp continuous_fst.continuousOn fun p hp => hp.1
  have haesm : AEStronglyMeasurable
      (Function.uncurry (fun z θ => (Work.Spaces.pth u z θ * Work.Spaces.w z) ^ 2))
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    Work.Spaces.aesm_of_continuousOn_Qd _
      (ContinuousOn.pow ((Work.FTS.EllipticEst.SmoothOpen.pth hso).continuousOn.mul hwcont) 2)
  refine ⟨fun z hz => ?_, ?_⟩
  · -- slicewise integrability
    rcases eq_or_lt_of_le (Set.mem_Ici.mp hz) with hz0 | hzpos
    · subst hz0
      have hw0 : Work.Spaces.w 0 = 0 := by
        show (1 + (0 : ℝ)) ^ 2 / (0 : ℝ) ^ 2 = 0
        norm_num
      have hzero : (fun θ => (Work.Spaces.pth u 0 θ * Work.Spaces.w 0) ^ 2)
          = fun _ => (0 : ℝ) := by
        funext θ
        rw [hw0]
        ring
      rw [hzero]
      exact MeasureTheory.integrableOn_zero
    · -- `z > 0`: the slice of `∂_θu` is bounded
      obtain ⟨C, hCpos, hCbdd⟩ :=
        Work.FTS.EllipticEst.Endpt.sliceBdd_of_hmB (α := α) h.smooth h.memAng2 hzpos
      haveI : IsFiniteMeasure (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
        ⟨by rw [MeasureTheory.Measure.restrict_apply_univ]
            exact isCompact_Icc.measure_lt_top⟩
      have hIoo : IsOpen (Set.Ioo (0 : ℝ) (Real.pi / 2)) := isOpen_Ioo
      have hcd1 : ContDiffOn ℝ 1 (fun θ => u z θ) (Set.Ioo (0 : ℝ) (Real.pi / 2)) := by
        have h1 : ContDiffOn ℝ 1 (Function.uncurry u)
            (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := h.smooth 1
        have h2 := h1.comp (contDiff_prodMk_right z).contDiffOn (fun θ hθ => ⟨hzpos, hθ⟩)
        simpa [Function.comp_def] using h2
      have hcont : ContinuousOn (fun θ => deriv (fun θ' => u z θ') θ)
          (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
        hcd1.continuousOn_deriv_of_isOpen hIoo (le_refl 1)
      have hmeas : AEStronglyMeasurable
          (fun θ => (Work.Spaces.pth u z θ) ^ 2) (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
        have h1 : AEStronglyMeasurable (fun θ => (deriv (fun θ' => u z θ') θ) ^ 2)
            (MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))) :=
          (hcont.pow 2).aestronglyMeasurable measurableSet_Ioo
        rw [show MeasureTheory.volume.restrict Work.Spaces.Iθ
            = MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)) from
          (MeasureTheory.Measure.restrict_congr_set
            (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume))).symm]
        exact h1
      have hbdd : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
          ‖(Work.Spaces.pth u z θ) ^ 2‖ ≤ C ^ 2 := by
        have h1 : ∀ᵐ θ ∂(MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2))),
            ‖(Work.Spaces.pth u z θ) ^ 2‖ ≤ C ^ 2 :=
          by
            filter_upwards [MeasureTheory.self_mem_ae_restrict measurableSet_Ioo] with θ hθ
            rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
            simpa only [Work.Spaces.pth, sq_abs] using
              pow_le_pow_left₀ (abs_nonneg _) (hCbdd θ hθ).2 2
        rw [show MeasureTheory.volume.restrict Work.Spaces.Iθ
            = MeasureTheory.volume.restrict (Set.Ioo (0 : ℝ) (Real.pi / 2)) from
          (MeasureTheory.Measure.restrict_congr_set
            (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume))).symm]
        exact h1
      have hunit : Integrable (fun θ => (Work.Spaces.pth u z θ) ^ 2)
          (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
        (MeasureTheory.MemLp.of_bound (p := 1) hmeas (C ^ 2) hbdd).integrable le_rfl
      have hwz : (fun θ => (Work.Spaces.pth u z θ * Work.Spaces.w z) ^ 2)
          = fun θ => (Work.Spaces.w z) ^ 2 * (Work.Spaces.pth u z θ) ^ 2 := by
        funext θ; ring
      rw [hwz]
      exact hunit.const_mul _
  · -- the `z`-integral
    have hdom : Integrable (fun z => (Real.pi / 2) ^ 2 * (∫ θ in Work.Spaces.Iθ,
          Work.Spaces.HkIntegrand α 0 (Work.Spaces.pthIter 2 u) z θ))
        (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
      Integrable.const_mul h.memAng2.2 _
    have haesm2 : AEStronglyMeasurable
        (fun z => ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pth u z θ * Work.Spaces.w z) ^ 2)
        (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
      haesm.integral_prod_right'
    have hb : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
        ‖∫ θ in Work.Spaces.Iθ, (Work.Spaces.pth u z θ * Work.Spaces.w z) ^ 2‖
          ≤ (Real.pi / 2) ^ 2 * (∫ θ in Work.Spaces.Iθ,
              Work.Spaces.HkIntegrand α 0 (Work.Spaces.pthIter 2 u) z θ) := by
      have hbase := aeData_ang_slice_bound α u G h hC
      change ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ici 0)), _
      rw [MeasureTheory.Measure.restrict_congr_set
        (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := 0)).symm]
      filter_upwards [hbase] with z hz
      rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun θ => sq_nonneg _)]
      exact hz
    exact MeasureTheory.Integrable.mono' hdom haesm2 hb

end Work.FTS.EllipticEst.H2W.Ae
