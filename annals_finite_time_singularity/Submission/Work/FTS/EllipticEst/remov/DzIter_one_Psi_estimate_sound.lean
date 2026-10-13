/-
Copyright: work module for the Elgindi finite-time singularity project.

# `remov.DzIter_one_Psi_estimate_sound`: the `|B| ≤ (K + π/2)·√hh` estimate for the
angular moment of `∂_zΨ`

Let `Ψ` be a datum of the weak class `TT.EllWeakPos α k F Ψ` (`k ≥ 1`), and write
`sinCos2 θ = sinθ·cos²θ`, `w z = (1+z)²/z²`, `eta = 99/100`.  For every `z₀ > 0` with
`θ ↦ ∂_zΨ(z₀,θ)·sinCos2 θ` integrable on `Iθ`, and every `hh ∈ (0,z₀)`,

`|∫_θ ∂_zΨ(z₀,θ)·sinCos2 θ| ≤ ((∫_z ∫_θ ((z²∂_z²Ψ)·w/sin(2θ)^{η/2})²)/z₀⁴ + π/2)·√hh`.

This is the key `√h`-estimate of the first-order moment chain (Steps 1–2 of the paper's §H2
proof of `prop:H2`): it is what forces `F_*(∂_zΨ) = 0` by letting `hh → 0`
(`remov.Fstar_DzIter_one_Psi`).

## Why this file exists

The identical statement is proved in `remov/DzIter_one_Psi_estimate.lean`.  That proof was
originally written against the helper `pzMulSinCos2RectIntegrable`, which is **false** as stated
(its hypotheses are phrased with Bochner integrals of nonnegative functions and hence carry no
information — see `remov/NOTES_pzMulSinCos2RectIntegrable_FALSE.md` and
`remov/PzMulSinCos2RectCounterexample.lean`); it has since been repaired so that the joint
integrability of `∂_zΨ·sinCos2` is obtained from the honest rectangle-integrability lemma
`remov.pzSinCos2_rectIntegrable` (whose hypotheses `hsl`, `hFint` are genuine integrability
statements).  This file is a **self-contained copy of that repaired proof** which does *not*
import `DzIter_one_Psi_estimate`, so that a consumer can depend on the estimate without depending
on that module.

## Route

* `hkMemW0L2` gives the honest weighted `L²` slice of `A = z²∂_z²Ψ`, its integrability in `z`,
  and the Cauchy–Schwarz bound
  `∫_θ |∂_z²Ψ|·sinCos2 ≤ z⁻²·√(π/2)·√(∫_θ (A·w/sin^{η/2})²)` for `z > 0`.
* `hkMemSliceAbsIntegrable` gives the honest slice and rectangle integrability of
  `|∂_z²Ψ|·sinCos2`; `aeSliceFtcPzIter2` gives the a.e.-in-`θ` fundamental theorem of calculus
  `∫_{z₀}^{ρ} ∂_z²Ψ = ∂_zΨ(ρ) - ∂_zΨ(z₀)` along the slices; `pzSinCos2_rectIntegrable` upgrades
  the slice hypotheses to joint integrability of `∂_zΨ·sinCos2` on `(z₀, z₀+hh] × Iθ`, which is
  what makes the Fubini steps legal.
* `pzSliceFubiniZero` gives both the swap of the two integrals and the vanishing of the average
  moment; the latter comes from the moment condition `F_*Ψ = 0` at `z₀` and `z₀ + hh`, together
  with the slice integrability of `Ψ·sinCos2` (`hPsi`).
* The pointwise estimate is then the double-primitive bound, Cauchy–Schwarz in `s`, and the AM–GM
  inequality `√(ab) ≤ a/2 + b/2` at the end.

Everything here is `sorry`-free and rests only on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS.EllipticEst.TT.WeakDefs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Elliptic.Defs
import Submission.Work.Spaces.cs_integral
import Submission.Work.FTS.EllipticEst.remov.hkMemW0L2
import Submission.Work.FTS.EllipticEst.remov.hkMemSliceAbsIntegrable
import Submission.Work.FTS.EllipticEst.remov.aeSliceFtcPzIter2
import Submission.Work.FTS.EllipticEst.remov.pzSliceFubiniZero
import Submission.Work.FTS.EllipticEst.remov.pzSinCos2_rectIntegrable

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.remov

set_option autoImplicit false
set_option maxHeartbeats 4000000

/-! ## The reusable core estimate and its `θ`-measure-theoretic helpers

These are placed in the sub-namespace `DzIterOneSound` so that importing this module together
with `remov.DzIter_one_Psi_estimate` (which carries the same helper names) cannot produce a name
clash. -/

namespace DzIterOneSound

/-! ## Small general helpers -/

/-- `sinθcos²θ ≥ 0` on `Iθ`. -/
lemma sinCos2_nonneg_Iθ_est {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) : 0 ≤ Work.Elliptic.sinCos2 θ := by
  obtain ⟨h0, h1⟩ := hθ
  have hs : 0 ≤ Real.sin θ := Real.sin_nonneg_of_nonneg_of_le_pi h0 (by linarith [Real.pi_pos])
  have hc : 0 ≤ Real.cos θ := Real.cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith) h1
  rw [Work.Elliptic.sinCos2]
  positivity

/-- An `Iθ`-integral of `|f|·sinθcos²θ` is nonnegative. -/
lemma integral_abs_mul_sinCos2_nonneg_est (f : ℝ → ℝ) :
    0 ≤ ∫ θ in Work.Spaces.Iθ, |f θ| * Work.Elliptic.sinCos2 θ := by
  refine MeasureTheory.integral_nonneg_of_ae ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
  exact mul_nonneg (abs_nonneg _) (sinCos2_nonneg_Iθ_est hθ)

/-- **Slice integrability of an interval integral.** -/
lemma integrable_Iθ_intervalIntegral_of_integrable_prod_est {h : ℝ → ℝ → ℝ} {a z₁ : ℝ}
    (hab : a ≤ z₁)
    (hint : MeasureTheory.Integrable (Function.uncurry h)
      ((MeasureTheory.volume.restrict (Set.uIoc a z₁)).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
    {ρ : ℝ} (hρ : ρ ∈ Set.Icc a z₁) :
    MeasureTheory.Integrable (fun θ : ℝ => ∫ s in a..ρ, h s θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
  have hρa : a ≤ ρ := hρ.1
  have hρz : ρ ≤ z₁ := hρ.2
  have hdom : MeasureTheory.Integrable
      (fun θ : ℝ => ∫ s in Set.uIoc a z₁, ‖h s θ‖)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    have h := hint.integral_norm_prod_right
    simpa only [Function.uncurry_apply_pair] using h
  have hslice : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      MeasureTheory.IntegrableOn (fun s : ℝ => h s θ) (Set.uIoc a z₁) := by
    have h := hint.prod_left_ae
    filter_upwards [h] with θ hθ
    simpa only [Function.uncurry_apply_pair, MeasureTheory.IntegrableOn] using hθ
  have hsub : Set.uIoc a ρ ⊆ Set.uIoc a z₁ := by
    rw [Set.uIoc_of_le hρa, Set.uIoc_of_le hab]
    exact Set.Ioc_subset_Ioc le_rfl hρz
  have hsmall : MeasureTheory.Integrable (Function.uncurry h)
      ((MeasureTheory.volume.restrict (Set.uIoc a ρ)).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    hint.mono_measure
      (MeasureTheory.Measure.prod_mono (MeasureTheory.Measure.restrict_mono hsub le_rfl) le_rfl)
  have hmeas : MeasureTheory.AEStronglyMeasurable
      (fun θ : ℝ => ∫ s in a..ρ, h s θ) (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    have hsw : MeasureTheory.AEStronglyMeasurable
        (fun z : ℝ × ℝ => h z.2 z.1)
        ((MeasureTheory.volume.restrict Work.Spaces.Iθ).prod
          (MeasureTheory.volume.restrict (Set.uIoc a ρ))) :=
      hsmall.aestronglyMeasurable.prod_swap
    have h2 := hsw.integral_prod_right'
    refine h2.congr ?_
    filter_upwards with θ
    rw [intervalIntegral.integral_of_le hρa, ← Set.uIoc_of_le hρa]
  refine hdom.mono' hmeas ?_
  filter_upwards [hslice] with θ hθ
  rw [Real.norm_eq_abs, intervalIntegral.integral_of_le hρa]
  refine le_trans (MeasureTheory.norm_integral_le_integral_norm
    (μ := MeasureTheory.volume.restrict (Set.Ioc a ρ)) (fun s => h s θ)) ?_
  exact MeasureTheory.setIntegral_mono_set hθ.norm
    (Filter.Eventually.of_forall fun s => norm_nonneg _)
    (Filter.Eventually.of_forall fun s hs =>
      hsub (by simpa only [Set.uIoc_of_le hρa] using hs))

/-- **The `θ`–`s` swap for the interval integral.** -/
lemma intervalIntegral_swap_right_est {h : ℝ → ℝ → ℝ} {a z₁ ρ : ℝ}
    (hint : MeasureTheory.Integrable (Function.uncurry h)
      ((MeasureTheory.volume.restrict (Set.uIoc a z₁)).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
    (hρ : ρ ∈ Set.Icc a z₁) :
    (∫ θ in Work.Spaces.Iθ, ∫ s in a..ρ, h s θ)
      = ∫ s in a..ρ, ∫ θ in Work.Spaces.Iθ, h s θ := by
  have hρa : a ≤ ρ := hρ.1
  have hsub : Set.uIoc a ρ ⊆ Set.uIoc a z₁ := by
    rw [Set.uIoc_of_le hρa, Set.uIoc_of_le (le_trans hρa hρ.2)]
    exact Set.Ioc_subset_Ioc le_rfl hρ.2
  have h' : MeasureTheory.Integrable (Function.uncurry h)
      ((MeasureTheory.volume.restrict (Set.uIoc a ρ)).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
    hint.mono_measure
      (MeasureTheory.Measure.prod_mono (MeasureTheory.Measure.restrict_mono hsub le_rfl) le_rfl)
  exact (MeasureTheory.intervalIntegral_integral_swap h').symm

/-- **Interval integrability of the primitive.** -/
lemma intervalIntegrable_primitive_of_integrableOn_est {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hf : MeasureTheory.IntegrableOn f (Set.Icc a b)) :
    IntervalIntegrable (fun ρ : ℝ => ∫ s in a..ρ, f s) MeasureTheory.volume a b := by
  have hcont : ContinuousOn (fun ρ : ℝ => ∫ s in a..ρ, f s) (Set.uIcc a b) :=
    intervalIntegral.continuousOn_primitive_interval (by rwa [Set.uIcc_of_le hab])
  exact hcont.intervalIntegrable

/-- **Cauchy–Schwarz for an interval integral**: `(∫_a^b f)² ≤ (b-a) ∫_a^b f²`. -/
lemma sq_intervalIntegral_le_est {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hfae : MeasureTheory.AEStronglyMeasurable f
      (MeasureTheory.volume.restrict (Set.uIoc a b)))
    (hf : MeasureTheory.IntegrableOn (fun x => f x ^ 2) (Set.uIoc a b)) :
    (∫ x in a..b, f x) ^ 2 ≤ (b - a) * (∫ x in a..b, (f x) ^ 2) := by
  haveI : IsFiniteMeasure (MeasureTheory.volume.restrict (Set.uIoc a b)) := ⟨by
    rw [MeasureTheory.Measure.restrict_apply MeasurableSet.univ, Set.univ_inter, Real.volume_uIoc]
    exact ENNReal.ofReal_lt_top⟩
  have hmem1 : MeasureTheory.MemLp (fun _ : ℝ => (1 : ℝ)) 2
      (MeasureTheory.volume.restrict (Set.uIoc a b)) := MeasureTheory.memLp_const 1
  have hmem2 : MeasureTheory.MemLp f 2 (MeasureTheory.volume.restrict (Set.uIoc a b)) := by
    rw [MeasureTheory.memLp_two_iff_integrable_sq hfae]
    exact hf
  have hcs := Work.Spaces.cs_integral hmem1 hmem2
  simp only [one_mul, one_pow] at hcs
  have hconv : (∫ x in a..b, f x) = ∫ x in Set.uIoc a b, f x := by
    rw [intervalIntegral.integral_of_le hab, Set.uIoc_of_le hab]
  have hconv2 : (∫ x in a..b, (f x) ^ 2) = ∫ x in Set.uIoc a b, (f x) ^ 2 := by
    rw [intervalIntegral.integral_of_le hab, Set.uIoc_of_le hab]
  rw [hconv, hconv2]
  have hconst : (∫ x in Set.uIoc a b, (1 : ℝ)) = b - a := by
    rw [Set.uIoc_of_le hab, MeasureTheory.setIntegral_const]
    simp only [smul_eq_mul, mul_one, MeasureTheory.Measure.real, Real.volume_Ioc,
      ENNReal.toReal_ofReal (sub_nonneg.mpr hab)]
  rw [hconst] at hcs
  exact hcs

/-! ## The core estimate -/

/-- **The core estimate.** -/
theorem coreBound {Ψ : ℝ → ℝ → ℝ} {z₀ hh : ℝ}
    (hz₀ : 0 < z₀) (hhpos : 0 < hh) (hhlt : hh < z₀)
    (hB : MeasureTheory.Integrable
      (fun θ : ℝ => Work.Spaces.pz Ψ z₀ θ * Work.Elliptic.sinCos2 θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ))
    (hQJ : MeasureTheory.IntegrableOn
      (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
        ((z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
          * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2)
      Work.Spaces.Iz)
    (hCs : ∀ z ∈ Set.Icc z₀ (z₀ + hh), ∫ θ in Work.Spaces.Iθ,
        |Work.Spaces.pzIter 2 Ψ z θ| * Work.Elliptic.sinCos2 θ
      ≤ (1 / z ^ 2) * Real.sqrt (Real.pi / 2) * Real.sqrt
          (∫ θ in Work.Spaces.Iθ,
            ((z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
              * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2))
    (hFint : MeasureTheory.IntegrableOn
      (fun s : ℝ => ∫ θ in Work.Spaces.Iθ,
        |Work.Spaces.pzIter 2 Ψ s θ| * Work.Elliptic.sinCos2 θ) (Set.Icc z₀ (z₀ + hh)))
    (hrectAbs : MeasureTheory.Integrable
      (Function.uncurry (fun s θ : ℝ =>
        |Work.Spaces.pzIter 2 Ψ s θ| * Work.Elliptic.sinCos2 θ))
      ((MeasureTheory.volume.restrict (Set.uIoc z₀ (z₀ + hh))).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
    (hFtc : ∀ᵐ θ ∂(MeasureTheory.volume.restrict Work.Spaces.Iθ),
      ∀ ρ ∈ Set.Icc z₀ (z₀ + hh),
        IntervalIntegrable (fun s : ℝ => Work.Spaces.pzIter 2 Ψ s θ)
          MeasureTheory.volume z₀ ρ ∧
        (∫ s in z₀..ρ, Work.Spaces.pzIter 2 Ψ s θ)
          = Work.Spaces.pz Ψ ρ θ - Work.Spaces.pz Ψ z₀ θ)
    (hrect : MeasureTheory.Integrable
      (Function.uncurry (fun z θ : ℝ => Work.Spaces.pz Ψ z θ * Work.Elliptic.sinCos2 θ))
      ((MeasureTheory.volume.restrict (Set.Ioc z₀ (z₀ + hh))).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)))
    (hswap : (∫ z in z₀..(z₀ + hh), (∫ θ in Work.Spaces.Iθ,
          Work.Spaces.pz Ψ z θ * Work.Elliptic.sinCos2 θ))
        = (∫ θ in Work.Spaces.Iθ, ∫ z in z₀..(z₀ + hh),
          Work.Spaces.pz Ψ z θ * Work.Elliptic.sinCos2 θ))
    (hzero : (∫ θ in Work.Spaces.Iθ, ∫ z in z₀..(z₀ + hh),
          Work.Spaces.pz Ψ z θ * Work.Elliptic.sinCos2 θ) = 0) :
    |∫ θ in Work.Spaces.Iθ, Work.Spaces.pz Ψ z₀ θ * Work.Elliptic.sinCos2 θ|
      ≤ ((∫ z in Work.Spaces.Iz, ∫ θ in Work.Spaces.Iθ,
            ((z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
              * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2)
          / z₀ ^ 4 + Real.pi / 2) * Real.sqrt hh := by
  have hzle : z₀ ≤ z₀ + hh := by linarith
  set Q : ℝ → ℝ := fun z => ∫ θ in Work.Spaces.Iθ,
      ((z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
        * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2 with hQdef
  set Fint : ℝ → ℝ := fun s => ∫ θ in Work.Spaces.Iθ,
      |Work.Spaces.pzIter 2 Ψ s θ| * Work.Elliptic.sinCos2 θ with hFdef
  set B : ℝ := ∫ θ in Work.Spaces.Iθ, Work.Spaces.pz Ψ z₀ θ * Work.Elliptic.sinCos2 θ
    with hBdef
  have hQJ' : MeasureTheory.IntegrableOn Q Work.Spaces.Iz := by
    simpa only [hQdef] using hQJ
  have hFint' : MeasureTheory.IntegrableOn Fint (Set.Icc z₀ (z₀ + hh)) := by
    simpa only [hFdef] using hFint
  have hCs' : ∀ z ∈ Set.Icc z₀ (z₀ + hh), Fint z
      ≤ (1 / z ^ 2) * Real.sqrt (Real.pi / 2) * Real.sqrt (Q z) := by
    intro z hz
    simpa only [hFdef, hQdef] using hCs z hz
  have hQnn : ∀ z : ℝ, 0 ≤ Q z := fun z => by
    rw [hQdef]; exact MeasureTheory.integral_nonneg fun θ => sq_nonneg _
  have hFnn : ∀ s : ℝ, 0 ≤ Fint s := by
    intro s; rw [hFdef]; exact integral_abs_mul_sinCos2_nonneg_est _
  -- ### Step 1: the a.e. pointwise bound
  have hpt : ∀ᵐ ρ ∂(MeasureTheory.volume.restrict (Set.Ioc z₀ (z₀ + hh))),
      |B - (∫ θ in Work.Spaces.Iθ, Work.Spaces.pz Ψ ρ θ * Work.Elliptic.sinCos2 θ)|
        ≤ ∫ s in z₀..ρ, Fint s := by
    filter_upwards [hrect.prod_right_ae,
      MeasureTheory.ae_restrict_mem measurableSet_Ioc] with ρ hρint hρmem
    have hρIcc : ρ ∈ Set.Icc z₀ (z₀ + hh) := ⟨le_of_lt hρmem.1, hρmem.2⟩
    have hle : z₀ ≤ ρ := le_of_lt hρmem.1
    have hρint' : MeasureTheory.Integrable
        (fun θ : ℝ => Work.Spaces.pz Ψ ρ θ * Work.Elliptic.sinCos2 θ)
        (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
      simpa only [Function.uncurry_apply_pair] using hρint
    have hA : B - (∫ θ in Work.Spaces.Iθ, Work.Spaces.pz Ψ ρ θ * Work.Elliptic.sinCos2 θ)
        = ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pz Ψ z₀ θ - Work.Spaces.pz Ψ ρ θ)
            * Work.Elliptic.sinCos2 θ := by
      rw [hBdef, ← MeasureTheory.integral_sub hB hρint']
      exact MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => by ring)
    rw [hA]
    refine le_trans (MeasureTheory.norm_integral_le_integral_norm
      (μ := MeasureTheory.volume.restrict Work.Spaces.Iθ)
      (fun θ => (Work.Spaces.pz Ψ z₀ θ - Work.Spaces.pz Ψ ρ θ)
        * Work.Elliptic.sinCos2 θ)) ?_
    simp only [Real.norm_eq_abs]
    have hptθ : (fun θ : ℝ => |(Work.Spaces.pz Ψ z₀ θ - Work.Spaces.pz Ψ ρ θ)
          * Work.Elliptic.sinCos2 θ|)
        ≤ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iθ]
        (fun θ : ℝ => (∫ s in z₀..ρ, |Work.Spaces.pzIter 2 Ψ s θ|)
          * Work.Elliptic.sinCos2 θ) := by
      filter_upwards [hFtc, MeasureTheory.ae_restrict_mem measurableSet_Icc]
        with θ hθftc hθmem
      obtain ⟨-, heq⟩ := hθftc ρ hρIcc
      have hσ := sinCos2_nonneg_Iθ_est hθmem
      have h1 : Work.Spaces.pz Ψ z₀ θ - Work.Spaces.pz Ψ ρ θ
          = -(∫ s in z₀..ρ, Work.Spaces.pzIter 2 Ψ s θ) := by linarith
      rw [h1, abs_mul, abs_neg, abs_of_nonneg hσ]
      exact mul_le_mul_of_nonneg_right
        (intervalIntegral.abs_integral_le_integral_abs hle) hσ
    have hRint : MeasureTheory.Integrable
        (fun θ : ℝ => (∫ s in z₀..ρ, |Work.Spaces.pzIter 2 Ψ s θ|)
          * Work.Elliptic.sinCos2 θ) (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
      have h0 := integrable_Iθ_intervalIntegral_of_integrable_prod_est hzle hrectAbs hρIcc
      refine h0.congr ?_
      filter_upwards with θ
      rw [intervalIntegral.integral_mul_const]
    have hLint : MeasureTheory.Integrable
        (fun θ : ℝ => |(Work.Spaces.pz Ψ z₀ θ - Work.Spaces.pz Ψ ρ θ)
          * Work.Elliptic.sinCos2 θ|) (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
      refine hRint.mono' ?_ ?_
      · have h1 : MeasureTheory.AEStronglyMeasurable
            (fun θ : ℝ => Work.Spaces.pz Ψ z₀ θ * Work.Elliptic.sinCos2 θ
              - Work.Spaces.pz Ψ ρ θ * Work.Elliptic.sinCos2 θ)
            (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
          hB.aestronglyMeasurable.sub hρint'.aestronglyMeasurable
        have h2 : MeasureTheory.AEStronglyMeasurable
            (fun θ : ℝ => (Work.Spaces.pz Ψ z₀ θ - Work.Spaces.pz Ψ ρ θ)
              * Work.Elliptic.sinCos2 θ) (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
          h1.congr (Filter.Eventually.of_forall fun θ => by ring)
        simpa only [Real.norm_eq_abs] using h2.norm
      · filter_upwards [hptθ] with θ hθ
        simpa only [Real.norm_eq_abs, abs_abs] using hθ
    have hmono := MeasureTheory.integral_mono_ae hLint hRint hptθ
    have hswapR : (∫ θ in Work.Spaces.Iθ,
          (∫ s in z₀..ρ, |Work.Spaces.pzIter 2 Ψ s θ|) * Work.Elliptic.sinCos2 θ)
        = ∫ s in z₀..ρ, Fint s := by
      have h0 := intervalIntegral_swap_right_est (h := fun s θ =>
        |Work.Spaces.pzIter 2 Ψ s θ| * Work.Elliptic.sinCos2 θ) hrectAbs hρIcc
      rw [← h0]
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards with θ
      rw [intervalIntegral.integral_mul_const]
    rw [hswapR] at hmono
    exact hmono
  -- ### Step 2: the average identity
  have hBint : IntervalIntegrable
      (fun ρ : ℝ => ∫ θ in Work.Spaces.Iθ,
        Work.Spaces.pz Ψ ρ θ * Work.Elliptic.sinCos2 θ) MeasureTheory.volume z₀ (z₀ + hh) := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hzle]
    have habs : MeasureTheory.Integrable
        (Function.uncurry (fun z θ : ℝ => |Work.Spaces.pz Ψ z θ| * Work.Elliptic.sinCos2 θ))
        ((MeasureTheory.volume.restrict (Set.Ioc z₀ (z₀ + hh))).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
      refine hrect.abs.congr ?_
      rw [MeasureTheory.Measure.prod_restrict]
      refine MeasureTheory.ae_restrict_of_forall_mem
        (measurableSet_Ioc.prod measurableSet_Icc) ?_
      rintro ⟨z, θ⟩ ⟨-, hθ⟩
      simp only [Function.uncurry_apply_pair, Real.norm_eq_abs, abs_mul,
        abs_of_nonneg (sinCos2_nonneg_Iθ_est hθ)]
    have hdom := habs.integral_norm_prod_left
    have hdom' : MeasureTheory.Integrable
        (fun ρ : ℝ => ∫ θ in Work.Spaces.Iθ,
          |Work.Spaces.pz Ψ ρ θ| * Work.Elliptic.sinCos2 θ)
        (MeasureTheory.volume.restrict (Set.Ioc z₀ (z₀ + hh))) := by
      refine hdom.congr ?_
      filter_upwards with ρ
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
      simp only [Real.norm_eq_abs, Function.uncurry_apply_pair]
      rw [abs_mul, abs_of_nonneg (abs_nonneg _), abs_of_nonneg (sinCos2_nonneg_Iθ_est hθ)]
    refine hdom'.mono' ?_ ?_
    · exact (hrect.aestronglyMeasurable.integral_prod_right')
    · filter_upwards with ρ
      refine le_trans (MeasureTheory.norm_integral_le_integral_norm
        (μ := MeasureTheory.volume.restrict Work.Spaces.Iθ)
        (fun θ => Work.Spaces.pz Ψ ρ θ * Work.Elliptic.sinCos2 θ)) ?_
      simp only [Real.norm_eq_abs]
      exact le_of_eq (MeasureTheory.integral_congr_ae (by
        filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
        simp only [abs_mul, abs_of_nonneg (abs_nonneg _),
          abs_of_nonneg (sinCos2_nonneg_Iθ_est hθ)]))
  have havg : hh * B = ∫ ρ in z₀..(z₀ + hh),
      (B - (∫ θ in Work.Spaces.Iθ, Work.Spaces.pz Ψ ρ θ * Work.Elliptic.sinCos2 θ)) := by
    have hzero' : (∫ ρ in z₀..(z₀ + hh),
        (∫ θ in Work.Spaces.Iθ, Work.Spaces.pz Ψ ρ θ * Work.Elliptic.sinCos2 θ)) = 0 := by
      rw [hswap, hzero]
    have hconst : IntervalIntegrable (fun _ : ℝ => B) MeasureTheory.volume z₀ (z₀ + hh) :=
      intervalIntegrable_const
    have h1 : (∫ ρ in z₀..(z₀ + hh),
          (B - (∫ θ in Work.Spaces.Iθ, Work.Spaces.pz Ψ ρ θ * Work.Elliptic.sinCos2 θ)))
        = (∫ ρ in z₀..(z₀ + hh), B)
          - (∫ ρ in z₀..(z₀ + hh),
              (∫ θ in Work.Spaces.Iθ, Work.Spaces.pz Ψ ρ θ * Work.Elliptic.sinCos2 θ)) :=
      intervalIntegral.integral_sub hconst hBint
    rw [h1, hzero', sub_zero, intervalIntegral.integral_const]
    ring
  -- the pointwise bound on `(Fint s)²`
  have hFint2bd : ∀ s ∈ Set.Icc z₀ (z₀ + hh),
      (Fint s) ^ 2 ≤ (Real.pi / 2) / z₀ ^ 4 * Q s := by
    intro s hs
    have hs1 : 0 < s := lt_of_lt_of_le hz₀ hs.1
    have hs4 : 0 < s ^ 4 := by positivity
    have hz4 : 0 < z₀ ^ 4 := by positivity
    have hle : 1 / s ^ 4 ≤ 1 / z₀ ^ 4 :=
      one_div_le_one_div_of_le hz4 (pow_le_pow_left₀ (le_of_lt hz₀) hs.1 4)
    have hb := hCs' s hs
    have hsqrt : 0 ≤ Real.sqrt (Q s) := Real.sqrt_nonneg _
    have h1 : (Fint s) ^ 2 ≤ ((1 / s ^ 2) * Real.sqrt (Real.pi / 2) * Real.sqrt (Q s)) ^ 2 :=
      pow_le_pow_left₀ (hFnn s) hb 2
    have h2 : ((1 / s ^ 2) * Real.sqrt (Real.pi / 2) * Real.sqrt (Q s)) ^ 2
        = (1 / s ^ 4) * (Real.pi / 2) * Q s := by
      rw [mul_pow, mul_pow, Real.sq_sqrt (by positivity), Real.sq_sqrt (hQnn s),
        div_pow, one_pow]
      ring
    have h3 : (1 / s ^ 4) * (Real.pi / 2) * Q s ≤ (1 / z₀ ^ 4) * (Real.pi / 2) * Q s := by
      have := mul_le_mul_of_nonneg_right hle (by positivity : (0:ℝ) ≤ Real.pi / 2)
      exact mul_le_mul_of_nonneg_right this (hQnn s)
    calc (Fint s) ^ 2 ≤ ((1 / s ^ 2) * Real.sqrt (Real.pi / 2) * Real.sqrt (Q s)) ^ 2 := h1
      _ = (1 / s ^ 4) * (Real.pi / 2) * Q s := h2
      _ ≤ (1 / z₀ ^ 4) * (Real.pi / 2) * Q s := h3
      _ = (Real.pi / 2) / z₀ ^ 4 * Q s := by ring
  -- ### Step 3: Cauchy–Schwarz in `s`
  have hCS : ∀ ρ ∈ Set.Icc z₀ (z₀ + hh),
      (∫ s in z₀..ρ, Fint s) ^ 2 ≤ (ρ - z₀) * (∫ s in z₀..ρ, (Fint s) ^ 2) := by
    intro ρ hρ
    have hle : z₀ ≤ ρ := hρ.1
    have hsub : Set.uIoc z₀ ρ ⊆ Set.Icc z₀ (z₀ + hh) := by
      intro x hx
      rw [Set.uIoc_of_le hle] at hx
      exact ⟨le_of_lt hx.1, le_trans hx.2 hρ.2⟩
    have hae : MeasureTheory.AEStronglyMeasurable Fint
        (MeasureTheory.volume.restrict (Set.uIoc z₀ ρ)) :=
      hFint'.aestronglyMeasurable.mono_measure (MeasureTheory.Measure.restrict_mono hsub le_rfl)
    have hf2 : MeasureTheory.IntegrableOn (fun x => (Fint x) ^ 2) (Set.uIoc z₀ ρ) := by
      have hQsub : MeasureTheory.IntegrableOn Q (Set.uIoc z₀ ρ) :=
        hQJ'.mono_set (fun x hx => by
          rw [Set.uIoc_of_le hle] at hx
          exact le_trans (le_of_lt hz₀) (le_of_lt hx.1))
      have hdom : MeasureTheory.IntegrableOn (fun x => (Real.pi / 2) / z₀ ^ 4 * Q x) (Set.uIoc z₀ ρ) :=
        hQsub.const_mul _
      refine hdom.mono' ?_ ?_
      · exact hae.pow 2
      · filter_upwards [MeasureTheory.ae_restrict_mem (measurableSet_uIoc)] with x hx
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact hFint2bd x (hsub hx)
    exact sq_intervalIntegral_le_est hle hae hf2
  -- ### Step 4: the `L²` bound over the interval
  have hF2 : ∀ ρ ∈ Set.Icc z₀ (z₀ + hh),
      (∫ s in z₀..ρ, (Fint s) ^ 2)
        ≤ (Real.pi / 2) / z₀ ^ 4 * (∫ z in Work.Spaces.Iz, Q z) := by
    intro ρ hρ
    have hle : z₀ ≤ ρ := hρ.1
    have hTnn : 0 ≤ ∫ z in Work.Spaces.Iz, Q z := MeasureTheory.integral_nonneg hQnn
    have hsub : Set.uIoc z₀ ρ ⊆ Set.Icc z₀ (z₀ + hh) := by
      intro x hx
      rw [Set.uIoc_of_le hle] at hx
      exact ⟨le_of_lt hx.1, le_trans hx.2 hρ.2⟩
    have hsub2 : Set.Icc z₀ ρ ⊆ Set.Icc z₀ (z₀ + hh) := fun x hx => ⟨hx.1, le_trans hx.2 hρ.2⟩
    have hf2 : IntervalIntegrable (fun x => (Fint x) ^ 2) MeasureTheory.volume z₀ ρ := by
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hle]
      have hQsub : MeasureTheory.IntegrableOn Q (Set.Ioc z₀ ρ) :=
        hQJ'.mono_set (fun x hx => le_trans (le_of_lt hz₀) (le_of_lt hx.1))
      refine (hQsub.const_mul ((Real.pi / 2) / z₀ ^ 4)).mono' ?_ ?_
      · have hae' : MeasureTheory.AEStronglyMeasurable Fint
            (MeasureTheory.volume.restrict (Set.Ioc z₀ ρ)) :=
          hFint'.aestronglyMeasurable.mono_measure
            (MeasureTheory.Measure.restrict_mono (Set.Ioc_subset_uIoc.trans hsub) le_rfl)
        exact hae'.pow 2
      · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with x hx
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact hFint2bd x (hsub (Set.Ioc_subset_uIoc hx))
    have hQint : IntervalIntegrable Q MeasureTheory.volume z₀ ρ := by
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hle]
      exact hQJ'.mono_set (fun x hx => le_trans (le_of_lt hz₀) (le_of_lt hx.1))
    have h1 : (∫ s in z₀..ρ, (Fint s) ^ 2) ≤ ∫ s in z₀..ρ, (Real.pi / 2) / z₀ ^ 4 * Q s := by
      refine intervalIntegral.integral_mono_on hle hf2 (hQint.const_mul _) ?_
      intro s hs
      exact hFint2bd s (hsub2 hs)
    have h2 : (∫ s in z₀..ρ, (Real.pi / 2) / z₀ ^ 4 * Q s)
        = (Real.pi / 2) / z₀ ^ 4 * (∫ s in z₀..ρ, Q s) :=
      intervalIntegral.integral_const_mul _ _
    have h3 : (∫ s in z₀..ρ, Q s) ≤ ∫ z in Work.Spaces.Iz, Q z := by
      rw [intervalIntegral.integral_of_le hle]
      refine MeasureTheory.setIntegral_mono_set hQJ' (Filter.Eventually.of_forall hQnn) ?_
      filter_upwards with x hx
      exact le_trans (le_of_lt hz₀) (le_of_lt hx.1)
    have h4 : (Real.pi / 2) / z₀ ^ 4 * (∫ s in z₀..ρ, Q s)
        ≤ (Real.pi / 2) / z₀ ^ 4 * (∫ z in Work.Spaces.Iz, Q z) :=
      mul_le_mul_of_nonneg_left h3 (by positivity)
    calc (∫ s in z₀..ρ, (Fint s) ^ 2)
        ≤ ∫ s in z₀..ρ, (Real.pi / 2) / z₀ ^ 4 * Q s := h1
      _ = (Real.pi / 2) / z₀ ^ 4 * (∫ s in z₀..ρ, Q s) := h2
      _ ≤ (Real.pi / 2) / z₀ ^ 4 * (∫ z in Work.Spaces.Iz, Q z) := h4
  -- ### Step 5: the `√hh` bound
  have hstep5 : ∀ ρ ∈ Set.Icc z₀ (z₀ + hh),
      ∫ s in z₀..ρ, Fint s
        ≤ Real.sqrt hh * Real.sqrt ((Real.pi / 2) / z₀ ^ 4 * (∫ z in Work.Spaces.Iz, Q z)) := by
    intro ρ hρ
    have hTnn : 0 ≤ ∫ z in Work.Spaces.Iz, Q z := MeasureTheory.integral_nonneg hQnn
    have h4 : 0 ≤ (Real.pi / 2) / z₀ ^ 4 * (∫ z in Work.Spaces.Iz, Q z) := by positivity
    have h1 : (∫ s in z₀..ρ, Fint s) ^ 2
        ≤ hh * ((Real.pi / 2) / z₀ ^ 4 * (∫ z in Work.Spaces.Iz, Q z)) := by
      have hc := hCS ρ hρ
      have h2 := hF2 ρ hρ
      have h3 : ρ - z₀ ≤ hh := by linarith [hρ.2]
      have h5 : 0 ≤ ρ - z₀ := sub_nonneg.mpr hρ.1
      have h6 : 0 ≤ ∫ s in z₀..ρ, (Fint s) ^ 2 :=
        intervalIntegral.integral_nonneg hρ.1 (fun s _ => sq_nonneg _)
      have h7 := mul_le_mul h3 h2 h6 (le_of_lt hhpos)
      linarith [hc, h7, h4]
    have h5 : 0 ≤ ∫ s in z₀..ρ, Fint s :=
      intervalIntegral.integral_nonneg hρ.1 (fun s _ => hFnn s)
    calc ∫ s in z₀..ρ, Fint s = Real.sqrt ((∫ s in z₀..ρ, Fint s) ^ 2) :=
          (Real.sqrt_sq h5).symm
      _ ≤ Real.sqrt (hh * ((Real.pi / 2) / z₀ ^ 4 * (∫ z in Work.Spaces.Iz, Q z))) :=
          Real.sqrt_le_sqrt h1
      _ = Real.sqrt hh * Real.sqrt ((Real.pi / 2) / z₀ ^ 4 * (∫ z in Work.Spaces.Iz, Q z)) :=
          Real.sqrt_mul (le_of_lt hhpos) _
  -- ### Step 6
  have hmain : |hh * B| ≤ hh * Real.sqrt hh
      * Real.sqrt ((Real.pi / 2) / z₀ ^ 4 * (∫ z in Work.Spaces.Iz, Q z)) := by
    have h1 : |hh * B| ≤ ∫ ρ in z₀..(z₀ + hh),
        |B - (∫ θ in Work.Spaces.Iθ, Work.Spaces.pz Ψ ρ θ * Work.Elliptic.sinCos2 θ)| := by
      rw [havg]
      exact intervalIntegral.abs_integral_le_integral_abs hzle
    have h2 : (∫ ρ in z₀..(z₀ + hh),
          |B - (∫ θ in Work.Spaces.Iθ, Work.Spaces.pz Ψ ρ θ * Work.Elliptic.sinCos2 θ)|)
        ≤ ∫ ρ in z₀..(z₀ + hh), (∫ s in z₀..ρ, Fint s) := by
      rw [intervalIntegral.integral_of_le hzle, intervalIntegral.integral_of_le hzle]
      refine MeasureTheory.integral_mono_ae ?_ ?_ hpt
      · have hc : MeasureTheory.IntegrableOn (fun _ : ℝ => B) (Set.Ioc z₀ (z₀ + hh)) :=
          MeasureTheory.integrableOn_const (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_ne_top)
        have h' : MeasureTheory.IntegrableOn
            (fun ρ : ℝ => B - (∫ θ in Work.Spaces.Iθ, Work.Spaces.pz Ψ ρ θ * Work.Elliptic.sinCos2 θ))
            (Set.Ioc z₀ (z₀ + hh)) := hc.sub hBint.1
        simpa only [Real.norm_eq_abs, Pi.sub_apply] using h'.abs
      · exact (intervalIntegrable_primitive_of_integrableOn_est hzle hFint').1
    have h3 : (∫ ρ in z₀..(z₀ + hh), (∫ s in z₀..ρ, Fint s))
        ≤ ∫ ρ in z₀..(z₀ + hh),
            (Real.sqrt hh * Real.sqrt ((Real.pi / 2) / z₀ ^ 4 * (∫ z in Work.Spaces.Iz, Q z))) := by
      refine intervalIntegral.integral_mono_on hzle
        (intervalIntegrable_primitive_of_integrableOn_est hzle hFint') intervalIntegrable_const ?_
      intro ρ hρ
      exact hstep5 ρ hρ
    have h4 : (∫ ρ in z₀..(z₀ + hh),
          (Real.sqrt hh * Real.sqrt ((Real.pi / 2) / z₀ ^ 4 * (∫ z in Work.Spaces.Iz, Q z))))
        = hh * Real.sqrt hh * Real.sqrt ((Real.pi / 2) / z₀ ^ 4 * (∫ z in Work.Spaces.Iz, Q z)) := by
      rw [intervalIntegral.integral_const]
      ring
    linarith [h1, h2, h3, le_of_eq h4]
  -- ### Step 7: divide by `hh` and apply AM–GM
  have hBbound : |B| ≤ Real.sqrt hh
      * Real.sqrt ((Real.pi / 2) / z₀ ^ 4 * (∫ z in Work.Spaces.Iz, Q z)) := by
    have h := hmain
    rw [abs_mul, abs_of_pos hhpos] at h
    have h' : hh * |B| ≤ hh * (Real.sqrt hh
        * Real.sqrt ((Real.pi / 2) / z₀ ^ 4 * (∫ z in Work.Spaces.Iz, Q z))) := by
      calc hh * |B| ≤ hh * Real.sqrt hh
            * Real.sqrt ((Real.pi / 2) / z₀ ^ 4 * (∫ z in Work.Spaces.Iz, Q z)) := h
        _ = hh * (Real.sqrt hh
            * Real.sqrt ((Real.pi / 2) / z₀ ^ 4 * (∫ z in Work.Spaces.Iz, Q z))) := by ring
    exact le_of_mul_le_mul_left h' hhpos
  have hAMGM : Real.sqrt ((Real.pi / 2) / z₀ ^ 4 * (∫ z in Work.Spaces.Iz, Q z))
      ≤ (∫ z in Work.Spaces.Iz, Q z) / z₀ ^ 4 + Real.pi / 2 := by
    have hTnn : 0 ≤ ∫ z in Work.Spaces.Iz, Q z := MeasureTheory.integral_nonneg hQnn
    have hz4 : 0 < z₀ ^ 4 := by positivity
    have harg : 0 ≤ (Real.pi / 2) / z₀ ^ 4 * (∫ z in Work.Spaces.Iz, Q z) := by positivity
    have hRnn : 0 ≤ (∫ z in Work.Spaces.Iz, Q z) / z₀ ^ 4 + Real.pi / 2 := by positivity
    have hsq : (Real.sqrt ((Real.pi / 2) / z₀ ^ 4 * (∫ z in Work.Spaces.Iz, Q z))) ^ 2
        ≤ ((∫ z in Work.Spaces.Iz, Q z) / z₀ ^ 4 + Real.pi / 2) ^ 2 := by
      rw [Real.sq_sqrt harg]
      set T := ∫ z in Work.Spaces.Iz, Q z with hTdef
      have ha : (Real.pi / 2) / z₀ ^ 4 * T = (T / z₀ ^ 4) * (Real.pi / 2) := by ring
      have hb : (T / z₀ ^ 4 + Real.pi / 2) ^ 2
          = (T / z₀ ^ 4) ^ 2 + 2 * (T / z₀ ^ 4) * (Real.pi / 2) + (Real.pi / 2) ^ 2 := by ring
      rw [ha, hb]
      nlinarith [sq_nonneg (T / z₀ ^ 4), sq_nonneg (Real.pi / 2), hTnn, hz4]
    have := (sq_le_sq.mp hsq)
    rwa [abs_of_nonneg (Real.sqrt_nonneg _), abs_of_nonneg hRnn] at this
  have hgoal : |B| ≤ ((∫ z in Work.Spaces.Iz, Q z) / z₀ ^ 4 + Real.pi / 2) * Real.sqrt hh :=
    calc |B| ≤ Real.sqrt hh * Real.sqrt ((Real.pi / 2) / z₀ ^ 4 * (∫ z in Work.Spaces.Iz, Q z)) :=
          hBbound
      _ ≤ Real.sqrt hh * ((∫ z in Work.Spaces.Iz, Q z) / z₀ ^ 4 + Real.pi / 2) :=
          mul_le_mul_of_nonneg_left hAMGM (Real.sqrt_nonneg _)
      _ = ((∫ z in Work.Spaces.Iz, Q z) / z₀ ^ 4 + Real.pi / 2) * Real.sqrt hh := by ring
  rw [hBdef] at hgoal ⊢
  rw [hQdef] at hgoal
  simpa only [hQdef] using hgoal

end DzIterOneSound

theorem DzIter_one_Psi_estimate_sound {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ}
    (hk : 1 ≤ k) (h : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ)
    (hPsi : ∀ z, 0 < z → MeasureTheory.Integrable
      (fun θ : ℝ => Ψ z θ * Work.Elliptic.sinCos2 θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ))
    (z₀ : ℝ) (hz₀ : 0 < z₀)
    (hB : MeasureTheory.Integrable
      (fun θ : ℝ => Work.Spaces.pz Ψ z₀ θ * Work.Elliptic.sinCos2 θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :
    ∀ hh ∈ Set.Ioo (0 : ℝ) z₀,
      |∫ θ in Work.Spaces.Iθ, Work.Spaces.pz Ψ z₀ θ * Work.Elliptic.sinCos2 θ|
        ≤ ((∫ z in Work.Spaces.Iz,
              ∫ θ in Work.Spaces.Iθ,
                ((z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
                  * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2)
              / z₀ ^ 4
            + Real.pi / 2) * Real.sqrt hh := by
  intro hh hhh
  obtain ⟨hhpos, hhlt⟩ := hhh
  have hzlt : z₀ < z₀ + hh := by linarith
  have hsm : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  -- the `ℋ⁰`-integrability of the weighted `z²∂_z²Ψ`
  have hA := hkMemW0L2 hk h
  have hQJ : MeasureTheory.IntegrableOn
      (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
        ((z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
          * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2)
      Work.Spaces.Iz := hA.2.1
  have hCsall := hA.2.2
  -- the absolute-value integrability package
  have hF := hkMemSliceAbsIntegrable hk h hz₀ hzlt
  have hFint : MeasureTheory.IntegrableOn
      (fun s : ℝ => ∫ θ in Work.Spaces.Iθ,
        |Work.Spaces.pzIter 2 Ψ s θ| * Work.Elliptic.sinCos2 θ) (Set.Icc z₀ (z₀ + hh)) :=
    hF.2.1
  have hrectAbs : MeasureTheory.Integrable
      (Function.uncurry (fun s θ : ℝ =>
        |Work.Spaces.pzIter 2 Ψ s θ| * Work.Elliptic.sinCos2 θ))
      ((MeasureTheory.volume.restrict (Set.uIoc z₀ (z₀ + hh))).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := hF.2.2.1
  -- the fundamental theorem of calculus along the slices
  have hFtc := aeSliceFtcPzIter2 hk h hz₀ (le_of_lt hzlt)
  -- the restricted data
  have hCs : ∀ z ∈ Set.Icc z₀ (z₀ + hh), ∫ θ in Work.Spaces.Iθ,
      |Work.Spaces.pzIter 2 Ψ z θ| * Work.Elliptic.sinCos2 θ
      ≤ (1 / z ^ 2) * Real.sqrt (Real.pi / 2) * Real.sqrt
          (∫ θ in Work.Spaces.Iθ,
            ((z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
              * (Work.Spaces.w z / Real.sin (2 * θ) ^ (Work.Spaces.eta / 2))) ^ 2) :=
    fun z hz => hCsall z (lt_of_lt_of_le hz₀ hz.1)
  have hsl : ∀ z ∈ Set.Icc z₀ (z₀ + hh), MeasureTheory.IntegrableOn
      (fun θ : ℝ => |Work.Spaces.pzIter 2 Ψ z θ| * Work.Elliptic.sinCos2 θ)
      Work.Spaces.Iθ :=
    fun z hz => hF.1 z (lt_of_lt_of_le hz₀ hz.1)
  -- the joint integrability on the rectangle
  have hrect := pzSinCos2_rectIntegrable hsm hz₀ hzlt hB hsl hFint
  -- Fubini and the vanishing of the average
  have hfub := pzSliceFubiniZero hsm hz₀ hzlt (hPsi z₀ hz₀)
    (hPsi (z₀ + hh) (by linarith)) (h.orthPsi z₀ hz₀) (h.orthPsi (z₀ + hh) (by linarith))
    hrect
  exact DzIterOneSound.coreBound hz₀ hhpos hhlt hB hQJ hCs hFint hrectAbs hFtc hrect hfub.1 hfub.2

end Work.FTS.EllipticEst.remov
