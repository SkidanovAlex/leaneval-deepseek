/-
Copyright: work module for the Elgindi finite-time singularity project.

# `H2W.step3Open` — Step 3 of `prop:H2` in the *open* (`C^∞`-on-the-open-quadrant) class

Target: for `U`, `S` solving `bslOp α U = S` on the open quadrant, with the six `η`-weighted
pairings `IP (z²∂_zzU) (z²∂_zzU)`, `IP (z∂_zU) (z∂_zU)`, `IP (∂_θθU) (∂_θθU)`, `IP U U`,
`IP S S`, `IP (∂_θ(tan θ · U)) (∂_θ(tan θ · U))` honest,

  `α⁴ · IP (z²∂_zzU) (z²∂_zzU) ≤ 16 · (IP S S + IP (∂_θθU) (∂_θθU)
     + IP (∂_θ(tan θ · U)) (∂_θ(tan θ · U)) + 36 · IP U U + (α(5+α))² · IP (z∂_zU) (z∂_zU))`.

## The route

On the open quadrant `bslOp α U = S` unfolds (`Work.Elliptic.bslOp_apply`,
`Work.Elliptic.Lzero`) to

  `α² z² ∂_zzU = -S - α(5+α)(z∂_zU) - ∂_θθU + ∂_θ(tan θ·U) - 6U`,

so that `|α²z²∂_zzU| ≤ |S| + |α(5+α)z∂_zU| + |∂_θθU| + |∂_θ(tan θ·U)| + |6U|` pointwise, and
the five-term Cauchy–Schwarz (`Honest.HkIntegrand_zero_le_five`, constant `5`) dominates the
level-`0` integrand of `α²z²∂_zzU` by `5` times the sum of the integrands of the five summands
on the whole closed quadrant.  The pointwise domination integrates
(`Honest.HkSq_zero_le_sum_five`) into

  `HkSq α 0 (α²z²∂_zzU) ≤ 5 (HkSq α 0 S + HkSq α 0 (∂_θθU) + HkSq α 0 (∂_θ(tan θ·U))
     + HkSq α 0 (6U) + HkSq α 0 (α(5+α)z∂_zU))`,

and the `HkSq`-functionals are the same as the `IP`-pairings (`Honest.IP_self_eq_HkSq`); the
scaling `HkSq α 0 (c·g) = c² HkSq α 0 g` (`Honest.HkSq_zero_const_mul`) pulls out the constants
`6` and `α(5+α)`, and the factor `α⁴` on the left is `(α²)²`, so it is absorbed into the
constant of `α²z²∂_zzU`.  `5 ≤ 16` finishes.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.AngSecond.Defs
import Submission.Work.FTS.EllipticEst.Honest.HkSqAssembly
import Submission.Work.FTS.EllipticEst.Honest.Basic
import Submission.Work.FTS.LocData.HkMem_const_mul

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.H2W

set_option linter.unusedVariables false

/-! ## Two elementary helpers -/

/-- The five-term triangle inequality `|a+b+c+d+e| ≤ |a|+|b|+|c|+|d|+|e|`. -/
private theorem abs_five_step3 (a b c d e : ℝ) :
    |a + b + c + d + e| ≤ |a| + |b| + |c| + |d| + |e| := by
  have h1 := abs_add_le (a + b + c + d) e
  have h2 := abs_add_le (a + b + c) d
  have h3 := abs_add_le (a + b) c
  have h4 := abs_add_le a b
  have n1 : 0 ≤ |a + b + c + d| := abs_nonneg _
  have n2 : 0 ≤ |a + b + c| := abs_nonneg _
  have n3 : 0 ≤ |a + b| := abs_nonneg _
  linarith [abs_nonneg a, abs_nonneg b, abs_nonneg c, abs_nonneg d, abs_nonneg e]

/-- **The bridge `IPMem g g ⟹ HkMem α 0 g`**, the converse of
`AngClean.HkMem_zero_IPMem`: at level `0` the `Hk`-integrand of `g` is the `IP`-integrand of
`g` with itself (`AngSecond.sq_mul_W`), so the two honesty conditions coincide. -/
private theorem hkMem_of_ipMem_self {α : ℝ} {g : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.AngSecond.IPMem g g) : Work.Spaces.HkMem α 0 g := by
  have heq : ∀ z θ, θ ∈ Work.Spaces.Iθ →
      g z θ * g z θ * Work.FTS.EllipticEst.AngSecond.w2 z
            * Work.FTS.EllipticEst.AngSecond.sig θ = Work.Spaces.HkIntegrand α 0 g z θ :=
    fun z θ hθ => by
      rw [Work.FTS.EllipticEst.Honest.HkIntegrand_zero_eq,
        Work.FTS.EllipticEst.AngSecond.sq_mul_W g hθ]
  constructor
  · intro z hz
    exact (h.1 z hz).congr_fun (fun θ hθ => heq z θ hθ) measurableSet_Icc
  · exact h.2.congr (Eventually.of_forall fun z =>
      setIntegral_congr_fun measurableSet_Icc fun θ hθ => heq z θ hθ)

/-! ## The lemma -/

theorem step3Open (α : ℝ) (U S : ℝ → ℝ → ℝ) (hα : 0 < α) (hα4 : α ≤ 1 / 4)
    (hEq : ∀ z, 0 < z → ∀ θ, 0 < θ → θ < Real.pi / 2 →
      Work.Elliptic.bslOp α U z θ = S z θ)
    (h0 : ∀ z, U z 0 = 0) (hpi : ∀ z, U z (Real.pi / 2) = 0)
    (hdec : ∀ θ ∈ Work.Spaces.Iθ, Filter.Tendsto (fun z => U z θ) Filter.atTop (nhds 0))
    (hQF : Work.FTS.EllipticEst.AngSecond.IPMem
      (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 U z θ) (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 U z θ))
    (hGF : Work.FTS.EllipticEst.AngSecond.IPMem (fun z θ => z * Work.Spaces.pz U z θ)
      (fun z θ => z * Work.Spaces.pz U z θ))
    (hPhiF : Work.FTS.EllipticEst.AngSecond.IPMem (Work.Spaces.pthIter 2 U)
      (Work.Spaces.pthIter 2 U))
    (hPsF : Work.FTS.EllipticEst.AngSecond.IPMem U U)
    (hSF : Work.FTS.EllipticEst.AngSecond.IPMem S S)
    (hTF : Work.FTS.EllipticEst.AngSecond.IPMem (Work.Spaces.pth (fun z θ => Real.tan θ * U z θ))
      (Work.Spaces.pth (fun z θ => Real.tan θ * U z θ))) :
    α ^ 4 * Work.FTS.EllipticEst.AngSecond.IP (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 U z θ)
        (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 U z θ)
      ≤ 16 * (Work.FTS.EllipticEst.AngSecond.IP S S
          + Work.FTS.EllipticEst.AngSecond.IP (Work.Spaces.pthIter 2 U)
              (Work.Spaces.pthIter 2 U)
          + Work.FTS.EllipticEst.AngSecond.IP (Work.Spaces.pth (fun z θ => Real.tan θ * U z θ))
              (Work.Spaces.pth (fun z θ => Real.tan θ * U z θ))
          + 36 * Work.FTS.EllipticEst.AngSecond.IP U U
          + (α * (5 + α)) ^ 2 * Work.FTS.EllipticEst.AngSecond.IP
              (fun z θ => z * Work.Spaces.pz U z θ) (fun z θ => z * Work.Spaces.pz U z θ)) := by
  -- **Step 1.** The equation, solved for `α² z² ∂_zzU`, and the triangular bound.
  have habs : ∀ z, 0 < z → ∀ θ, 0 < θ → θ < Real.pi / 2 →
      |α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 U z θ)|
        ≤ |S z θ| + |Work.Spaces.pthIter 2 U z θ|
          + |Work.Spaces.pth (fun z θ => Real.tan θ * U z θ) z θ|
          + |6 * U z θ| + |(α * (5 + α)) * (z * Work.Spaces.pz U z θ)| := by
    intro z hz θ hθ0 hθ1
    have h := hEq z hz θ hθ0 hθ1
    rw [Work.Elliptic.bslOp_apply, Work.Elliptic.Lzero] at h
    have hid : α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 U z θ)
        = -S z θ - (α * (5 + α) * z) * Work.Spaces.pz U z θ
          - Work.Spaces.pthIter 2 U z θ
          + Work.Spaces.pth (fun z θ => Real.tan θ * U z θ) z θ - 6 * U z θ := by
      linarith [h]
    rw [hid]
    have e : -S z θ - (α * (5 + α) * z) * Work.Spaces.pz U z θ
        - Work.Spaces.pthIter 2 U z θ + Work.Spaces.pth (fun z θ => Real.tan θ * U z θ) z θ
        - 6 * U z θ
        = (-(S z θ)) + (-((α * (5 + α)) * (z * Work.Spaces.pz U z θ)))
          + (-(Work.Spaces.pthIter 2 U z θ))
          + (Work.Spaces.pth (fun z θ => Real.tan θ * U z θ) z θ) + (-(6 * U z θ)) := by ring
    rw [e]
    have h5 := abs_five_step3 (-(S z θ)) (-((α * (5 + α)) * (z * Work.Spaces.pz U z θ)))
        (-(Work.Spaces.pthIter 2 U z θ)) (Work.Spaces.pth (fun z θ => Real.tan θ * U z θ) z θ)
        (-(6 * U z θ))
    rw [abs_neg, abs_neg, abs_neg, abs_neg] at h5
    linarith [h5]
  -- **Step 2.** Honesty of the five majorants.
  have hmemS : Work.Spaces.HkMem α 0 S := hkMem_of_ipMem_self hSF
  have hmemPhi : Work.Spaces.HkMem α 0 (Work.Spaces.pthIter 2 U) := hkMem_of_ipMem_self hPhiF
  have hmemTan : Work.Spaces.HkMem α 0 (Work.Spaces.pth (fun z θ => Real.tan θ * U z θ)) :=
    hkMem_of_ipMem_self hTF
  have hmemU : Work.Spaces.HkMem α 0 U := hkMem_of_ipMem_self hPsF
  have hmemG : Work.Spaces.HkMem α 0 (fun z θ => z * Work.Spaces.pz U z θ) := hkMem_of_ipMem_self hGF
  have hmem6U : Work.Spaces.HkMem α 0 (fun z θ => 6 * U z θ) :=
    Work.FTS.LocData.HkMem_const_mul α 0 6 hmemU
  have hmem5G : Work.Spaces.HkMem α 0 (fun z θ => (α * (5 + α)) * (z * Work.Spaces.pz U z θ)) :=
    Work.FTS.LocData.HkMem_const_mul α 0 (α * (5 + α)) hmemG
  -- **Step 3.** The pointwise five-term domination of the `HkIntegrand`s.
  have hpt := Work.FTS.EllipticEst.Honest.HkIntegrand_zero_le_five
      (α := α) (u := fun z θ => α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 U z θ))
      (g1 := S) (g2 := Work.Spaces.pthIter 2 U)
      (g3 := Work.Spaces.pth (fun z θ => Real.tan θ * U z θ))
      (g4 := fun z θ => 6 * U z θ)
      (g5 := fun z θ => (α * (5 + α)) * (z * Work.Spaces.pz U z θ)) habs
  have h5 := Work.FTS.EllipticEst.Honest.HkSq_zero_le_sum_five (C := 5) (by norm_num)
      hmemS hmemPhi hmemTan hmem6U hmem5G hpt
  -- **Step 4.** Pull the constants `6` and `α(5+α)` out of the `HkSq`-functionals.
  have h5' : Work.Spaces.HkSq α 0 (fun z θ => α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 U z θ))
      ≤ 5 * (Work.Spaces.HkSq α 0 S + Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 U)
          + Work.Spaces.HkSq α 0 (Work.Spaces.pth (fun z θ => Real.tan θ * U z θ))
          + 36 * Work.Spaces.HkSq α 0 U
          + (α * (5 + α)) ^ 2 * Work.Spaces.HkSq α 0 (fun z θ => z * Work.Spaces.pz U z θ)) := by
    rw [Work.FTS.EllipticEst.Honest.HkSq_zero_const_mul α 6 U,
        Work.FTS.EllipticEst.Honest.HkSq_zero_const_mul α (α * (5 + α))
          (fun z θ => z * Work.Spaces.pz U z θ)] at h5
    norm_num at h5
    exact h5
  have hsum : 0 ≤ Work.Spaces.HkSq α 0 S + Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 U)
      + Work.Spaces.HkSq α 0 (Work.Spaces.pth (fun z θ => Real.tan θ * U z θ))
      + 36 * Work.Spaces.HkSq α 0 U
      + (α * (5 + α)) ^ 2 * Work.Spaces.HkSq α 0 (fun z θ => z * Work.Spaces.pz U z θ) := by
    have h1 := Work.FTS.EllipticEst.Honest.HkSq_zero_nonneg α S
    have h2 := Work.FTS.EllipticEst.Honest.HkSq_zero_nonneg α (Work.Spaces.pthIter 2 U)
    have h3 := Work.FTS.EllipticEst.Honest.HkSq_zero_nonneg α
      (Work.Spaces.pth (fun z θ => Real.tan θ * U z θ))
    have h4 := Work.FTS.EllipticEst.Honest.HkSq_zero_nonneg α U
    have h5n := Work.FTS.EllipticEst.Honest.HkSq_zero_nonneg α (fun z θ => z * Work.Spaces.pz U z θ)
    nlinarith [sq_nonneg (α * (5 + α)), sq_nonneg (6 : ℝ)]
  have hkey : Work.Spaces.HkSq α 0 (fun z θ => α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 U z θ))
      ≤ 16 * (Work.Spaces.HkSq α 0 S + Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 U)
          + Work.Spaces.HkSq α 0 (Work.Spaces.pth (fun z θ => Real.tan θ * U z θ))
          + 36 * Work.Spaces.HkSq α 0 U
          + (α * (5 + α)) ^ 2 * Work.Spaces.HkSq α 0 (fun z θ => z * Work.Spaces.pz U z θ)) :=
    le_trans h5' (by linarith [hsum])
  -- **Step 5.** Absorb `α⁴ = (α²)²` and pass back to the `IP`-pairings.
  calc α ^ 4 * Work.FTS.EllipticEst.AngSecond.IP (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 U z θ)
          (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 U z θ)
      = α ^ 4 * Work.Spaces.HkSq α 0 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 U z θ) := by
        rw [Work.FTS.EllipticEst.Honest.IP_self_eq_HkSq α]
    _ = Work.Spaces.HkSq α 0 (fun z θ => α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 U z θ)) := by
        rw [Work.FTS.EllipticEst.Honest.HkSq_zero_const_mul α (α ^ 2)
          (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 U z θ)]
        ring
    _ ≤ 16 * (Work.Spaces.HkSq α 0 S + Work.Spaces.HkSq α 0 (Work.Spaces.pthIter 2 U)
          + Work.Spaces.HkSq α 0 (Work.Spaces.pth (fun z θ => Real.tan θ * U z θ))
          + 36 * Work.Spaces.HkSq α 0 U
          + (α * (5 + α)) ^ 2 * Work.Spaces.HkSq α 0 (fun z θ => z * Work.Spaces.pz U z θ)) := hkey
    _ = 16 * (Work.FTS.EllipticEst.AngSecond.IP S S
          + Work.FTS.EllipticEst.AngSecond.IP (Work.Spaces.pthIter 2 U)
              (Work.Spaces.pthIter 2 U)
          + Work.FTS.EllipticEst.AngSecond.IP (Work.Spaces.pth (fun z θ => Real.tan θ * U z θ))
              (Work.Spaces.pth (fun z θ => Real.tan θ * U z θ))
          + 36 * Work.FTS.EllipticEst.AngSecond.IP U U
          + (α * (5 + α)) ^ 2 * Work.FTS.EllipticEst.AngSecond.IP
              (fun z θ => z * Work.Spaces.pz U z θ) (fun z θ => z * Work.Spaces.pz U z θ)) := by
        rw [Work.FTS.EllipticEst.Honest.IP_self_eq_HkSq α S,
            Work.FTS.EllipticEst.Honest.IP_self_eq_HkSq α (Work.Spaces.pthIter 2 U),
            Work.FTS.EllipticEst.Honest.IP_self_eq_HkSq α
              (Work.Spaces.pth (fun z θ => Real.tan θ * U z θ)),
            Work.FTS.EllipticEst.Honest.IP_self_eq_HkSq α U,
            Work.FTS.EllipticEst.Honest.IP_self_eq_HkSq α (fun z θ => z * Work.Spaces.pz U z θ)]

end Work.FTS.EllipticEst.H2W
