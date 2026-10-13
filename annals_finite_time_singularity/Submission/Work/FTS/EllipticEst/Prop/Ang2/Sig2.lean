import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Order.CompletePartialOrder
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.Defs
import Submission.Work.FTS.EllipticEst.Defs
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.FTS.EllipticEst.AeStepOneAux.Defs
import Submission.Work.FTS.EllipticEst.H2W.Ae.Defs
import Submission.Work.FTS.EllipticEst.H2W.AeProof.AeSigma.AeHkMemU
import Submission.Work.FTS.EllipticEst.H2W.AeProof.AeSigma.AeSliceFacts
import Submission.Work.FTS.EllipticEst.Mine.zcutFam
import Submission.Work.FTS.EllipticEst.Honest.omegaW_deriv_bounds
import Submission.Work.FTS.EllipticEst.AeStepOneAux.sliceCoerciveAe
import Submission.Work.FTS.EllipticEst.Dispatch.truncRadialIbpTheta

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `AeStepOneAux/aeDzNormSig` — the `σ`-weighted first-order radial bound from `SigmaCoercive`

For data in the almost-everywhere class `Work.FTS.EllipticEst.H2W.Ae.AeData α u G` with
`HkMem α 0 (z∂_zu)` and the a.e. vanishing of the slices at `θ = 0⁺`, and with the
`σ`-coercivity `SigmaCoercive` of the angular operator `Lzero1` available as a hypothesis,

  `α · nrm α (grad u) ≤ C(M) · nrm α G`   whenever `nrm α u ≤ M · nrm α G`,

where `nrm α f = √(HkSq α 0 f)`, `grad u = z ∂_zu`, `σ θ = sin(2θ)^{-η}` and
`HkSq α 0 f = ∫_z (w z)² ∫_θ f² σ`, `w z = (1+z)²/z²`.

## Route

Write `ρ = w²σ`, `Du = z∂_zu`, and truncate radially by a smooth cut-off `χ n`
(`Work.FTS.EllipticEst.Mine.zcutFam`: `χ n = 0` near `0` and for `z ≥ 2(n+1)`, `= 1` on
`[2/(n+1), n+1]`, with `|z χ n'| ≤ C₁` and `|z(z χ n')'| ≤ C₂` *uniformly in* `n`), setting
`ω z = (w z)² χ n z`.

* `truncRadialIbpSigma` (the compactly supported per-`θ` radial IBP
  `Work.FTS.EllipticEst.Honest.zIBP_compact`, integrated in `θ` against `σ`) gives
  `∫_z ω ∫_θ σ (Pu)u = -α²∫_z ω∫_θ σ (Du)² + (α²/2)∫_z (z²ω)''∫_θ σ u²
     - (α(5+α)/2)∫_z (zω)'∫_θ σ u²`, where `Pu = α²z²∂_zzu + α(5+α)z∂_zu`.
* On the open quadrant `Lzero u = G + Pu`, so `∫_zω∫_θσ(Pu)u = ∫_zω∫_θσ(Lzero u)u - ∫_zω∫_θσGu`.
* The slicewise `σ`-coercivity (`sliceCoerciveAe`, from `SigmaCoercive`) bounds the first term
  from below by `-K∫_z ω∫_θ σ u²`; the source pairing is bounded by AM–GM; the transfer terms by
  `Work.FTS.EllipticEst.Honest.omegaW_deriv_bounds`.  All of it is `≤ C(M) HkSq α 0 G`, using
  `nrm α u ≤ M nrm α G` and `HkMem α 0 u` (`Work.FTS.EllipticEst.H2W.AeProof.AeSigma.AeHkMemU`).
* Letting `n → ∞` (`χ n ↑ 1` with `|χ n| ≤ 1`, dominated convergence) gives
  `α² HkSq α 0 (grad u) ≤ C(M)² HkSq α 0 G`, and taking square roots the claim.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllipticEst.AeStepOneAux.Sig2

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-! ## The `σ`-weighted truncated radial integration by parts

This is the (previously missing) leaf of the argument below.  Its *equation* conjunct is the
proved `Work.FTS.EllipticEst.Dispatch.truncRadialIbpTheta` (`|ω| ≤ w²` in place of
`0 ≤ ω ≤ w²`), and the `IntegrableOn` conjunct is the `z`-integral of the joint integrability
proved there (`Dispatch.tRibp_integrablePair` + `Integrable.integral_prod_left`).  -/

/-- **The `σ`-weighted truncated radial integration by parts.**  Identical to
`Work.FTS.EllipticEst.AeStepOneAux.truncRadialIbpSigma` (whose only proof in the tree is a
`sorry`), derived here from the *proved* `Dispatch.truncRadialIbpTheta`. -/
theorem truncRadialIbpSigma (α : ℝ) (u : ℝ → ℝ → ℝ)
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry u)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hgrad : Work.Spaces.HkMem α 0 (fun z θ => z * Work.Spaces.pz u z θ))
    (hrad2 : Work.Spaces.HkMem α 0 (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 u z θ))
    (hu : Work.Spaces.HkMem α 0 u)
    (ω : ℝ → ℝ) (hωd : ContDiffOn ℝ 2 ω (Set.Ioi 0))
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (hωsupp : ∀ z, z ∉ Set.Icc a b → ω z = 0)
    (hωnn : ∀ z, 0 ≤ ω z) (hωle : ∀ z, ω z ≤ (Work.Spaces.w z) ^ 2) :
    (MeasureTheory.IntegrableOn (fun z => ω z * (∫ θ in Work.Spaces.Iθ,
        Work.FTS.EllipticEst.sEta θ *
          ((α ^ 2 * z ^ 2 * Work.Spaces.pzIter 2 u z θ
            + (α * (5 + α) * z) * Work.Spaces.pz u z θ) * u z θ))) (Set.Ioi 0))
    ∧ (∫ z in Set.Ioi 0, ω z * (∫ θ in Work.Spaces.Iθ,
        Work.FTS.EllipticEst.sEta θ *
          ((α ^ 2 * z ^ 2 * Work.Spaces.pzIter 2 u z θ
            + (α * (5 + α) * z) * Work.Spaces.pz u z θ) * u z θ)))
      = -α ^ 2 * (∫ z in Set.Ioi 0, ω z * (∫ θ in Work.Spaces.Iθ,
            Work.FTS.EllipticEst.sEta θ * (z * Work.Spaces.pz u z θ) ^ 2))
        + (α ^ 2 / 2) * (∫ z in Set.Ioi 0, deriv (deriv (fun y : ℝ => y ^ 2 * ω y)) z *
            (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.sEta θ * (u z θ) ^ 2))
        - (α * (5 + α) / 2) * (∫ z in Set.Ioi 0, deriv (fun y : ℝ => y * ω y) z *
            (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.sEta θ * (u z θ) ^ 2)) := by
  have hbdd : ∀ z, |ω z| ≤ (Work.Spaces.w z) ^ 2 := fun z => by
    rw [abs_of_nonneg (hωnn z)]
    exact hωle z
  obtain ⟨hIntL, -⟩ :=
    Work.FTS.EllipticEst.Dispatch.tRibp_integrablePair (α := α) (u := u) ω
      ha hab hsm hgrad hrad2 hu hωd hωsupp hbdd
  refine ⟨?_, Work.FTS.EllipticEst.Dispatch.truncRadialIbpTheta (α := α) (u := u) ω
    ha hab hsm hgrad hrad2 hu hωd hωsupp hbdd⟩
  have hprod := hIntL.integral_prod_left
  refine hprod.congr (Filter.Eventually.of_forall fun z => ?_)
  exact MeasureTheory.integral_const_mul (ω z) (fun θ => Work.FTS.EllipticEst.sEta θ *
    ((α ^ 2 * z ^ 2 * Work.Spaces.pzIter 2 u z θ
      + (α * (5 + α) * z) * Work.Spaces.pz u z θ) * u z θ))

/-! ## Elementary facts about the radial weight `φ z = w z ^ 2` -/

/-- The square of the radial weight is nonnegative. -/
theorem w_sq_nonneg (z : ℝ) : 0 ≤ (Work.Spaces.w z) ^ 2 := sq_nonneg _

/-- On the open half-line the square of the radial weight is positive: `w z = (1+z)²/z²`. -/
theorem w_sq_pos {z : ℝ} (hz : 0 < z) : 0 < (Work.Spaces.w z) ^ 2 := by
  rw [Work.Spaces.w]
  exact pow_pos (div_pos (pow_pos (by linarith) 2) (pow_pos hz 2)) 2

/-- The set integrals over `Ioi 0` and over `Iz = [0,∞)` agree (they differ by `{0}`). -/
theorem setIntegral_Ioi_eq_Iz (f : ℝ → ℝ) :
    (∫ z in Set.Ioi 0, f z) = ∫ z in Work.Spaces.Iz, f z := by
  rw [Work.Spaces.Iz]
  exact MeasureTheory.setIntegral_congr_set (f := f)
    (MeasureTheory.Ioi_ae_eq_Ici (μ := (MeasureTheory.volume : Measure ℝ)) (a := 0))

/-- `HkSq α 0` in the `w²σ`-weighted form. -/
theorem HkSq_zero_eq_phi_mul (α : ℝ) (f : ℝ → ℝ → ℝ) :
    Work.Spaces.HkSq α 0 f
      = ∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 *
          (∫ θ in Work.Spaces.Iθ, (f z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) := by
  rw [Work.Spaces.HkSq]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ici (fun z _ => ?_)
  exact Work.FTS.EllipticEst.H2W.AeProof.AeSigma.integral_hkIntegrand_w α f z

/-- The outer `w²`-weighted slice integral of an `ℋ⁰`-element is integrable. -/
theorem integrableOn_phi_mul_slice {α : ℝ} {f : ℝ → ℝ → ℝ} (hf : Work.Spaces.HkMem α 0 f) :
    MeasureTheory.IntegrableOn (fun z => (Work.Spaces.w z) ^ 2 *
      (∫ θ in Work.Spaces.Iθ, (f z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ))
      Work.Spaces.Iz :=
  hf.2.congr_fun
    (fun z _ => Work.FTS.EllipticEst.H2W.AeProof.AeSigma.integral_hkIntegrand_w α f z)
    measurableSet_Ici

/-! ## Measurability of the slice integrals -/

/-- The square of the radial weight is measurable. -/
theorem w_pos {z : ℝ} (hz : 0 < z) : 0 < Work.Spaces.w z := by
  rw [Work.Spaces.w]
  exact div_pos (pow_pos (by linarith) 2) (pow_pos hz 2)

theorem measurable_w_sq : Measurable (fun z : ℝ => (Work.Spaces.w z) ^ 2) := by
  unfold Work.Spaces.w
  fun_prop

/-- `AEStronglyMeasurable` of a function whose `w²`-weighted version is `AEStronglyMeasurable`
(the weight is nonvanishing on `(0,∞)`). -/
theorem aesm_div_phi {A : ℝ → ℝ}
    (h : MeasureTheory.AEStronglyMeasurable (fun z => (Work.Spaces.w z) ^ 2 * A z)
      (MeasureTheory.volume.restrict (Set.Ioi 0))) :
    MeasureTheory.AEStronglyMeasurable A (MeasureTheory.volume.restrict (Set.Ioi 0)) := by
  have hdiv : AEMeasurable
      (fun z => ((Work.Spaces.w z) ^ 2 * A z) / ((Work.Spaces.w z) ^ 2))
      (MeasureTheory.volume.restrict (Set.Ioi 0)) :=
    h.aemeasurable.div measurable_w_sq.aemeasurable
  refine (aestronglyMeasurable_iff_aemeasurable.mpr hdiv).congr ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz
  have hne : (Work.Spaces.w z) ^ 2 ≠ 0 := ne_of_gt (w_sq_pos hz)
  exact mul_div_cancel_left₀ (A z) hne

/-- Restricting an `AEStronglyMeasurable` function from `Iz = [0,∞)` to `(0,∞)`. -/
theorem aesm_restrict_Ioi_of_Iz {g : ℝ → ℝ}
    (h : MeasureTheory.AEStronglyMeasurable g (MeasureTheory.volume.restrict Work.Spaces.Iz)) :
    MeasureTheory.AEStronglyMeasurable g (MeasureTheory.volume.restrict (Set.Ioi 0)) := by
  have h1 : MeasureTheory.AEStronglyMeasurable g
      ((MeasureTheory.volume.restrict Work.Spaces.Iz).restrict (Set.Ioi 0)) := h.restrict
  have h2 : (MeasureTheory.volume.restrict Work.Spaces.Iz).restrict (Set.Ioi 0)
      = MeasureTheory.volume.restrict (Set.Ioi 0) := by
    rw [Work.Spaces.Iz, MeasureTheory.Measure.restrict_restrict measurableSet_Ioi]
    congr 1
    ext z
    simp only [Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Ici]
    exact ⟨fun h => h.1, fun h => ⟨h, le_of_lt h⟩⟩
  rwa [h2] at h1

/-- The `w²`-weighted slice integral of an `ℋ⁰`-element is `AEStronglyMeasurable`. -/
theorem aesm_phi_mul_slice {α : ℝ} {f : ℝ → ℝ → ℝ} (hf : Work.Spaces.HkMem α 0 f) :
    MeasureTheory.AEStronglyMeasurable (fun z => (Work.Spaces.w z) ^ 2 *
      (∫ θ in Work.Spaces.Iθ, (f z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ))
      (MeasureTheory.volume.restrict (Set.Ioi 0)) :=
  (aesm_restrict_Ioi_of_Iz hf.2.aestronglyMeasurable).congr
    (Filter.Eventually.of_forall fun z =>
      Work.FTS.EllipticEst.H2W.AeProof.AeSigma.integral_hkIntegrand_w α f z)

/-- The slice integral `z ↦ ∫_θ f² σ` of an `ℋ⁰`-element is `AEStronglyMeasurable`. -/
theorem aesm_slice_sq {α : ℝ} {f : ℝ → ℝ → ℝ} (hf : Work.Spaces.HkMem α 0 f) :
    MeasureTheory.AEStronglyMeasurable
      (fun z => ∫ θ in Work.Spaces.Iθ, (f z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      (MeasureTheory.volume.restrict (Set.Ioi 0)) :=
  aesm_div_phi (aesm_phi_mul_slice hf)

/-! ## Domination of truncated pairings -/

/-- **Domination of a truncated pairing by the `w²`-weighted one.**  If `0 ≤ ω ≤ w²`, `A ≥ 0`
and `z ↦ (w z)² A z` is integrable on `Iz`, then `z ↦ ω z A z` is integrable on `(0,∞)`. -/
theorem integrableOn_omega_mul {ω A : ℝ → ℝ}
    (hint : MeasureTheory.IntegrableOn (fun z => (Work.Spaces.w z) ^ 2 * A z) Work.Spaces.Iz)
    (hωm : Measurable ω) (hω0 : ∀ z, 0 ≤ ω z) (hωle : ∀ z, ω z ≤ (Work.Spaces.w z) ^ 2)
    (hA0 : ∀ z, 0 ≤ A z)
    (hA : MeasureTheory.AEStronglyMeasurable A (MeasureTheory.volume.restrict (Set.Ioi 0))) :
    MeasureTheory.IntegrableOn (fun z => ω z * A z) (Set.Ioi 0) := by
  refine MeasureTheory.Integrable.mono' (hint.mono_set Set.Ioi_subset_Ici_self)
    (hωm.aestronglyMeasurable.mul hA) ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z _hz
  rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hω0 z) (hA0 z))]
  exact mul_le_mul_of_nonneg_right (hωle z) (hA0 z)

/-- The integral of a truncated pairing is dominated by the `w²`-weighted integral. -/
theorem integral_omega_mul_le {ω A : ℝ → ℝ}
    (hint : MeasureTheory.IntegrableOn (fun z => (Work.Spaces.w z) ^ 2 * A z) Work.Spaces.Iz)
    (hωm : Measurable ω) (hω0 : ∀ z, 0 ≤ ω z) (hωle : ∀ z, ω z ≤ (Work.Spaces.w z) ^ 2)
    (hA0 : ∀ z, 0 ≤ A z)
    (hA : MeasureTheory.AEStronglyMeasurable A (MeasureTheory.volume.restrict (Set.Ioi 0))) :
    (∫ z in Set.Ioi 0, ω z * A z)
      ≤ ∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 * A z := by
  have h1 := integrableOn_omega_mul hint hωm hω0 hωle hA0 hA
  have h2 : (∫ z in Set.Ioi 0, ω z * A z)
      ≤ ∫ z in Set.Ioi 0, (Work.Spaces.w z) ^ 2 * A z := by
    refine MeasureTheory.integral_mono_ae h1 (hint.mono_set Set.Ioi_subset_Ici_self) ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z _hz
    exact mul_le_mul_of_nonneg_right (hωle z) (hA0 z)
  exact h2.trans_eq (setIntegral_Ioi_eq_Iz _)

/-- **Domination of a pairing with a bounded coefficient.**  If `|c z| ≤ C (w z)²` on `(0,∞)`,
`A ≥ 0` and `z ↦ (w z)² A z` is integrable on `Iz`, then `z ↦ c z A z` is integrable on `(0,∞)`
and `|∫_z c A| ≤ C ∫_z (w z)² A z`. -/
theorem integrableOn_coef_mul_le {c A : ℝ → ℝ} {C : ℝ}
    (hint : MeasureTheory.IntegrableOn (fun z => (Work.Spaces.w z) ^ 2 * A z) Work.Spaces.Iz)
    (hC : 0 ≤ C) (hbound : ∀ z, 0 < z → |c z| ≤ C * (Work.Spaces.w z) ^ 2)
    (hA0 : ∀ z, 0 ≤ A z)
    (hc : MeasureTheory.AEStronglyMeasurable c (MeasureTheory.volume.restrict (Set.Ioi 0)))
    (hA : MeasureTheory.AEStronglyMeasurable A (MeasureTheory.volume.restrict (Set.Ioi 0))) :
    MeasureTheory.IntegrableOn (fun z => c z * A z) (Set.Ioi 0) ∧
      |∫ z in Set.Ioi 0, c z * A z|
        ≤ C * (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 * A z) := by
  have hmain : MeasureTheory.IntegrableOn (fun z => c z * A z) (Set.Ioi 0) := by
    refine MeasureTheory.Integrable.mono'
      ((hint.mono_set Set.Ioi_subset_Ici_self).const_mul C) (hc.mul hA) ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz
    have h := hbound z hz
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hA0 z)]
    calc |c z| * A z ≤ (C * (Work.Spaces.w z) ^ 2) * A z :=
          mul_le_mul_of_nonneg_right h (hA0 z)
      _ = C * ((Work.Spaces.w z) ^ 2 * A z) := by ring
  refine ⟨hmain, ?_⟩
  have h1 : |∫ z in Set.Ioi 0, c z * A z| ≤ ∫ z in Set.Ioi 0, |c z * A z| :=
    abs_integral_le_integral_abs
  have h2 : (∫ z in Set.Ioi 0, |c z * A z|)
      ≤ ∫ z in Set.Ioi 0, C * ((Work.Spaces.w z) ^ 2 * A z) := by
    refine MeasureTheory.integral_mono_ae hmain.abs ?_ ?_
    · exact (hint.mono_set Set.Ioi_subset_Ici_self).const_mul C
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz
      have h := hbound z hz
      rw [abs_mul, abs_of_nonneg (hA0 z)]
      calc |c z| * A z ≤ (C * (Work.Spaces.w z) ^ 2) * A z :=
            mul_le_mul_of_nonneg_right h (hA0 z)
        _ = C * ((Work.Spaces.w z) ^ 2 * A z) := by ring
  have h3 : (∫ z in Set.Ioi 0, C * ((Work.Spaces.w z) ^ 2 * A z))
      = C * (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 * A z) := by
    rw [MeasureTheory.integral_const_mul, setIntegral_Ioi_eq_Iz]
  linarith [h1, h2, h3]


/-! ## The `θ`-slice functionals of the first-order estimate -/

/-- `R u z = ∫_θ σ θ · u(z,θ)²`. -/
def Rslice (u : ℝ → ℝ → ℝ) (z : ℝ) : ℝ :=
  ∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.sEta θ * (u z θ) ^ 2

/-- `Z u z = ∫_θ σ θ · (z ∂_z u(z,θ))²`. -/
def Zslice (u : ℝ → ℝ → ℝ) (z : ℝ) : ℝ :=
  ∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.sEta θ * (z * Work.Spaces.pz u z θ) ^ 2

/-- `Gslice G z = ∫_θ σ θ · G(z,θ)²`. -/
def Gslice (G : ℝ → ℝ → ℝ) (z : ℝ) : ℝ :=
  ∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.sEta θ * (G z θ) ^ 2

/-- `Sslice G u z = ∫_θ σ θ · G(z,θ) · u(z,θ)`. -/
def Sslice (G u : ℝ → ℝ → ℝ) (z : ℝ) : ℝ :=
  ∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.sEta θ * (G z θ * u z θ)

/-- `Pslice α u z = ∫_θ σ θ · (α²z²∂_z²u + α(5+α)z∂_z u)(z,θ) · u(z,θ)`. -/
def Pslice (α : ℝ) (u : ℝ → ℝ → ℝ) (z : ℝ) : ℝ :=
  ∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.sEta θ *
    ((α ^ 2 * z ^ 2 * Work.Spaces.pzIter 2 u z θ
      + (α * (5 + α) * z) * Work.Spaces.pz u z θ) * u z θ)

/-- `Lslice u z = ∫_θ Lzero1(u z ·) θ · u z θ · σ θ`. -/
def Lslice (u : ℝ → ℝ → ℝ) (z : ℝ) : ℝ :=
  ∫ θ in Work.Spaces.Iθ,
    Work.FTS.EllipticEst.Lzero1 (fun θ' => u z θ') θ * u z θ * Work.FTS.EllipticEst.sEta θ

/-- The angular weight vanishes at `θ = 0`. -/
theorem sEta_zero : Work.FTS.EllipticEst.sEta 0 = 0 := by
  rw [Work.FTS.EllipticEst.sEta, show 2 * (0 : ℝ) = 0 by ring, Real.sin_zero]
  exact Real.zero_rpow (by norm_num [Work.Spaces.eta])

/-- The angular weight vanishes at `θ = π/2`. -/
theorem sEta_pi_div_two : Work.FTS.EllipticEst.sEta (Real.pi / 2) = 0 := by
  rw [Work.FTS.EllipticEst.sEta, show 2 * (Real.pi / 2) = Real.pi by ring, Real.sin_pi]
  exact Real.zero_rpow (by norm_num [Work.Spaces.eta])

/-- `HkSq α 0 u` in terms of `Rslice`. -/
theorem HkSq_zero_eq_Rslice (α : ℝ) (u : ℝ → ℝ → ℝ) :
    Work.Spaces.HkSq α 0 u = ∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 * Rslice u z := by
  rw [HkSq_zero_eq_phi_mul]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ici (fun z _ => ?_)
  rw [Rslice]
  congr 1
  exact MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => mul_comm _ _)

/-- `HkSq α 0 (grad u)` in terms of `Zslice`. -/
theorem HkSq_grad_eq_Zslice (α : ℝ) (u : ℝ → ℝ → ℝ) :
    Work.Spaces.HkSq α 0 (fun z θ => z * Work.Spaces.pz u z θ)
      = ∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 * Zslice u z := by
  rw [HkSq_zero_eq_phi_mul]
  refine MeasureTheory.setIntegral_congr_fun measurableSet_Ici (fun z _ => ?_)
  rw [Zslice]
  congr 1
  exact MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => mul_comm _ _)

/-- The commutation `∫_θ f g = ∫_θ g f` on the angular interval. -/
theorem setIntegral_mul_comm (f g : ℝ → ℝ) :
    (∫ θ in Work.Spaces.Iθ, f θ * g θ) = ∫ θ in Work.Spaces.Iθ, g θ * f θ :=
  MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => mul_comm _ _)

/-- `Rslice` written with the square first. -/
theorem Rslice_eq_integral (u : ℝ → ℝ → ℝ) (z : ℝ) :
    Rslice u z = ∫ θ in Work.Spaces.Iθ, (u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ := by
  rw [Rslice]
  exact setIntegral_mul_comm (fun θ => Work.FTS.EllipticEst.sEta θ) (fun θ => (u z θ) ^ 2)

/-- `Zslice` written with the square first. -/
theorem Zslice_eq_integral (u : ℝ → ℝ → ℝ) (z : ℝ) :
    Zslice u z = ∫ θ in Work.Spaces.Iθ, (z * Work.Spaces.pz u z θ) ^ 2
      * Work.FTS.EllipticEst.sEta θ := by
  rw [Zslice]
  exact setIntegral_mul_comm (fun θ => Work.FTS.EllipticEst.sEta θ)
    (fun θ => (z * Work.Spaces.pz u z θ) ^ 2)

/-- `Gslice` written with the square first. -/
theorem Gslice_eq_integral (G : ℝ → ℝ → ℝ) (z : ℝ) :
    Gslice G z = ∫ θ in Work.Spaces.Iθ, (G z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ := by
  rw [Gslice]
  exact setIntegral_mul_comm (fun θ => Work.FTS.EllipticEst.sEta θ) (fun θ => (G z θ) ^ 2)

/-- The `AeData`-slice of `Rslice` is `σ`-integrable. -/
theorem integrableOn_Rslice {α : ℝ} {u G : ℝ → ℝ → ℝ} (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G) {z : ℝ}
    (hz : 0 < z) :
    MeasureTheory.IntegrableOn (fun θ => Work.FTS.EllipticEst.sEta θ * (u z θ) ^ 2)
      Work.Spaces.Iθ :=
  ((Work.FTS.EllipticEst.H2W.AeProof.AeSigma.aeSliceSigmaInt α u G h z hz).1).congr_fun
    (fun θ _ => by ring) measurableSet_Icc

/-- The `AeData`-slice of `Gslice` is `σ`-integrable. -/
theorem integrableOn_Gslice {α : ℝ} {u G : ℝ → ℝ → ℝ} (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G) {z : ℝ}
    (hz : 0 < z) :
    MeasureTheory.IntegrableOn (fun θ => Work.FTS.EllipticEst.sEta θ * (G z θ) ^ 2)
      Work.Spaces.Iθ :=
  (Work.FTS.EllipticEst.H2W.AeProof.AeSigma.integrableOn_sq_mul_sEtaR_of_HkMem h.memG
    hz).congr_fun (fun θ _ => by ring) measurableSet_Icc

/-- The `AeData`-slice of `Pslice` is `σ`-integrable. -/
theorem integrableOn_Pslice {α : ℝ} {u G : ℝ → ℝ → ℝ} (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G) {z : ℝ}
    (hz : 0 < z) :
    MeasureTheory.IntegrableOn (fun θ => Work.FTS.EllipticEst.sEta θ *
      ((α ^ 2 * z ^ 2 * Work.Spaces.pzIter 2 u z θ
        + (α * (5 + α) * z) * Work.Spaces.pz u z θ) * u z θ)) Work.Spaces.Iθ := by
  obtain ⟨-, -, h3, h4, -⟩ :=
    Work.FTS.EllipticEst.H2W.AeProof.AeSigma.aeSliceSigmaInt α u G h z hz
  have ha : MeasureTheory.IntegrableOn (fun θ => (α ^ 2 * z ^ 2) *
      (Work.FTS.EllipticEst.sEta θ * (Work.Spaces.pzIter 2 u z θ * u z θ))) Work.Spaces.Iθ :=
    (h4.const_mul (α ^ 2 * z ^ 2)).congr (Filter.Eventually.of_forall (fun θ => by ring))
  have hb : MeasureTheory.IntegrableOn (fun θ => (α * (5 + α) * z) *
      (Work.FTS.EllipticEst.sEta θ * (Work.Spaces.pz u z θ * u z θ))) Work.Spaces.Iθ :=
    (h3.const_mul (α * (5 + α) * z)).congr (Filter.Eventually.of_forall (fun θ => by ring))
  refine (ha.add hb).congr_fun (fun θ _ => ?_) measurableSet_Icc
  simp only [Pi.add_apply]
  ring

/-- The `AeData`-slice of `Sslice` is `σ`-integrable (AM–GM against `G² + u²`). -/
theorem integrableOn_Sslice {α : ℝ} {u G : ℝ → ℝ → ℝ} (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G) {z : ℝ}
    (hz : 0 < z) :
    MeasureTheory.IntegrableOn (fun θ => Work.FTS.EllipticEst.sEta θ * (G z θ * u z θ))
      Work.Spaces.Iθ := by
  have hu2 := integrableOn_Rslice h hz
  have hg2 := integrableOn_Gslice h hz
  have hsum : MeasureTheory.IntegrableOn (fun θ =>
      (1 / 2) * (Work.FTS.EllipticEst.sEta θ * (G z θ) ^ 2
        + Work.FTS.EllipticEst.sEta θ * (u z θ) ^ 2)) Work.Spaces.Iθ :=
    (hg2.add hu2).const_mul (1 / 2)
  have hsmG : MeasureTheory.AEStronglyMeasurable (fun θ => G z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    Work.FTS.EllipticEst.H2W.AeProof.AeSigma.aesm_slice_G h hz
  have hsmU : MeasureTheory.AEStronglyMeasurable (fun θ => u z θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    Work.FTS.EllipticEst.H2W.AeProof.AeSigma.aesm_of_contOn_Ioo
      (Work.FTS.EllipticEst.H2W.AeProof.AeSigma.contOn_slice h hz)
  have hsmσ : MeasureTheory.AEStronglyMeasurable (fun θ => Work.FTS.EllipticEst.sEta θ)
      (MeasureTheory.volume.restrict Work.Spaces.Iθ) :=
    Work.FTS.EllipticEst.H2W.AeProof.AeSigma.measurable_sEtaR.aestronglyMeasurable
  refine MeasureTheory.Integrable.mono' hsum (hsmσ.mul (hsmG.mul hsmU)) ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
  have hσ : 0 ≤ Work.FTS.EllipticEst.sEta θ :=
    Work.FTS.EllipticEst.H2W.AeProof.AeSigma.sEtaR_nonneg hθ
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hσ, abs_mul]
  have h2 : 2 * (|G z θ| * |u z θ|) ≤ (G z θ) ^ 2 + (u z θ) ^ 2 := by
    nlinarith [sq_nonneg (|G z θ| - |u z θ|), sq_abs (G z θ), sq_abs (u z θ)]
  calc Work.FTS.EllipticEst.sEta θ * (|G z θ| * |u z θ|)
      = (1 / 2) * (Work.FTS.EllipticEst.sEta θ * (2 * (|G z θ| * |u z θ|))) := by ring
    _ ≤ (1 / 2) * (Work.FTS.EllipticEst.sEta θ * ((G z θ) ^ 2 + (u z θ) ^ 2)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 hσ) (by norm_num)
    _ = (1 / 2) * (Work.FTS.EllipticEst.sEta θ * (G z θ) ^ 2
          + Work.FTS.EllipticEst.sEta θ * (u z θ) ^ 2) := by ring

/-- `Lslice` is the sum of `Pslice` and `Sslice` (the equation on the open quadrant). -/
theorem Lslice_eq_Pslice_add_Sslice {α : ℝ} {u G : ℝ → ℝ → ℝ} (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G) {z : ℝ}
    (hz : 0 < z) :
    Lslice u z = Pslice α u z + Sslice G u z := by
  have hpt : ∀ θ ∈ Work.Spaces.Iθ,
      Work.FTS.EllipticEst.Lzero1 (fun θ' => u z θ') θ * u z θ * Work.FTS.EllipticEst.sEta θ
        = Work.FTS.EllipticEst.sEta θ *
            ((α ^ 2 * z ^ 2 * Work.Spaces.pzIter 2 u z θ
              + (α * (5 + α) * z) * Work.Spaces.pz u z θ) * u z θ)
          + Work.FTS.EllipticEst.sEta θ * (G z θ * u z θ) := by
    intro θ hθ
    rcases lt_or_eq_of_le hθ.1 with hθ0 | hθ0
    · rcases lt_or_eq_of_le hθ.2 with hθ1 | hθ1
      · have hbsl := h.eq z hz θ hθ0 hθ1
        have hL : Work.FTS.EllipticEst.Lzero1 (fun θ' => u z θ') θ
            = Work.Elliptic.Lzero u z θ := by
          have h1 : Work.FTS.EllipticEst.Lzero1 (fun θ' => u z θ') θ
              = Work.Elliptic.Lzero (fun _ θ' : ℝ => u z θ') z θ :=
            congrFun (Work.FTS.EllipticEst.Lzero1_eq_Lzero (fun θ' => u z θ') z) θ
          have h2 : Work.Elliptic.Lzero (fun _ θ' : ℝ => u z θ') z θ
              = Work.Elliptic.Lzero u z θ := by
            rw [Work.Elliptic.Lzero_eq_deriv, Work.Elliptic.Lzero_eq_deriv]
          rw [h1, h2]
        rw [hL]
        have hkey : Work.Elliptic.Lzero u z θ
            = G z θ + (α ^ 2 * z ^ 2 * Work.Spaces.pzIter 2 u z θ
                + (α * (5 + α) * z) * Work.Spaces.pz u z θ) := by
          rw [Work.Elliptic.bslOp_apply] at hbsl
          linarith [hbsl]
        rw [hkey]; ring
      · subst hθ1
        rw [sEta_pi_div_two]; ring
    · subst hθ0
      rw [sEta_zero]; ring
  rw [Lslice, Pslice, Sslice, Work.Spaces.Iθ]
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Icc hpt]
  exact MeasureTheory.integral_add (integrableOn_Pslice h hz) (integrableOn_Sslice h hz)

/-! ## Smoothness of the radial weight and the coefficient bounds of the cut-off -/

/-- `z ↦ (w z)²` is `C²` on `(0,∞)`. -/
theorem contDiffOn_w_sq_two : ContDiffOn ℝ 2 (fun z : ℝ => (Work.Spaces.w z) ^ 2) (Set.Ioi 0) := by
  have hnum : ContDiffOn ℝ 2 (fun z : ℝ => (1 + z) ^ 2) (Set.Ioi 0) :=
    (contDiffOn_const.add contDiffOn_id).pow 2
  have hden : ContDiffOn ℝ 2 (fun z : ℝ => z ^ 2) (Set.Ioi 0) := contDiffOn_id.pow 2
  have hne : ∀ z ∈ Set.Ioi (0 : ℝ), z ^ 2 ≠ 0 := fun z hz => pow_ne_zero 2 (ne_of_gt hz)
  have hdiv : ContDiffOn ℝ 2 (fun z : ℝ => (1 + z) ^ 2 / z ^ 2) (Set.Ioi 0) :=
    hnum.div hden hne
  have hsq : ContDiffOn ℝ 2 (fun z : ℝ => ((1 + z) ^ 2 / z ^ 2) ^ 2) (Set.Ioi 0) := hdiv.pow 2
  refine hsq.congr (fun z _ => ?_)
  rw [Work.Spaces.w]

/-- From the two logarithmic derivative bounds of `χ` one gets `|z²χ''| ≤ C₂ + C₁`. -/
theorem chi_second_le {χ : ℝ → ℝ} (hχ : ContDiff ℝ 2 χ) {C₁ C₂ : ℝ}
    (h1 : ∀ z, |z * deriv χ z| ≤ C₁)
    (h2 : ∀ z, |z * deriv (fun w : ℝ => w * deriv χ w) z| ≤ C₂) :
    ∀ z, |z ^ 2 * deriv (deriv χ) z| ≤ C₂ + C₁ := by
  intro z
  have hd : DifferentiableAt ℝ χ z := (hχ.differentiable (by norm_num)) z
  have hd' : DifferentiableAt ℝ (deriv χ) z := (hχ.differentiable_deriv_two) z
  have hderiv : deriv (fun w : ℝ => w * deriv χ w) z = deriv χ z + z * deriv (deriv χ) z := by
    have h : HasDerivAt (fun w : ℝ => w * deriv χ w)
        (1 * deriv χ z + z * deriv (deriv χ) z) z :=
      (hasDerivAt_id z).mul hd'.hasDerivAt
    simpa using h.deriv
  have hkey : z ^ 2 * deriv (deriv χ) z
      = z * deriv (fun w : ℝ => w * deriv χ w) z - z * deriv χ z := by
    rw [hderiv]; ring
  rw [hkey]
  calc |z * deriv (fun w : ℝ => w * deriv χ w) z - z * deriv χ z|
      ≤ |z * deriv (fun w : ℝ => w * deriv χ w) z| + |z * deriv χ z| := abs_sub _ _
    _ ≤ C₂ + C₁ := add_le_add (h2 z) (h1 z)

/-! ## Measurability and domination helpers used by the main argument -/

/-- A property holding for every `z > 0` holds a.e. on `Iz = [0,∞)`. -/
theorem ae_restrict_Iz_of_pos {p : ℝ → Prop} (h : ∀ z : ℝ, 0 < z → p z) :
    ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz), p z := by
  have h1 : MeasureTheory.volume.restrict Work.Spaces.Iz
      = MeasureTheory.volume.restrict (Set.Ioi 0) := by
    rw [Work.Spaces.Iz]
    exact (MeasureTheory.Measure.restrict_congr_set
      (MeasureTheory.Ioi_ae_eq_Ici (μ := (MeasureTheory.volume : Measure ℝ)) (a := 0))).symm
  rw [h1]
  exact MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi h

/-- The angular weight is continuous on `(0,π/2)`. -/
theorem continuousOn_sEta : ContinuousOn (fun θ : ℝ => Work.FTS.EllipticEst.sEta θ)
    (Set.Ioo 0 (Real.pi / 2)) := by
  have hsin : ContinuousOn (fun θ : ℝ => Real.sin (2 * θ)) (Set.Ioo 0 (Real.pi / 2)) :=
    (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn
  exact hsin.rpow_const (fun θ hθ => Or.inl (ne_of_gt (Real.sin_pos_of_pos_of_lt_pi
    (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos]))))

/-- **Measurability of the source pairing `z ↦ ∫_θ σ θ · G z θ · u z θ`** in the `AeData` class:
for `z > 0` the source `G` agrees with the smooth `bslOp α u`, so the integrand is continuous on
the open quadrant. -/
theorem aesm_Sslice {α : ℝ} {u G : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G) :
    MeasureTheory.AEStronglyMeasurable (Sslice G u)
      (MeasureTheory.volume.restrict (Set.Ioi 0)) := by
  have hsm : Work.FTS.EllipticEst.SmoothOpen u :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hbsl : Work.FTS.EllipticEst.SmoothOpen (Work.Elliptic.bslOp α u) :=
    Work.FTS.EllipticEst.remov.SmoothOpen_bslOp_of_smoothOpen hsm
  have hσc : ContinuousOn (fun p : ℝ × ℝ => Work.FTS.EllipticEst.sEta p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    continuousOn_sEta.comp (continuous_snd.continuousOn) (fun p hp => hp.2)
  have hcont : ContinuousOn (fun p : ℝ × ℝ => Work.FTS.EllipticEst.sEta p.2 *
      (Work.Elliptic.bslOp α u p.1 p.2 * u p.1 p.2))
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
    hσc.mul (((hbsl.forall 0).continuousOn).mul ((hsm.forall 0).continuousOn))
  have haesm : MeasureTheory.AEStronglyMeasurable
      (fun z => ∫ θ in Work.Spaces.Iθ,
        Work.FTS.EllipticEst.sEta θ * (Work.Elliptic.bslOp α u z θ * u z θ))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
    (Work.Spaces.aesm_of_continuousOn_Qd _ hcont).integral_prod_right'
  have h1 : MeasureTheory.AEStronglyMeasurable
      (fun z => ∫ θ in Work.Spaces.Iθ,
        Work.FTS.EllipticEst.sEta θ * (G z θ * u z θ))
      (MeasureTheory.volume.restrict Work.Spaces.Iz) :=
    haesm.congr (ae_restrict_Iz_of_pos (fun z hz => by
      have h1 : (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.sEta θ *
            (Work.Elliptic.bslOp α u z θ * u z θ))
          = ∫ θ in Set.Ioo 0 (Real.pi / 2), Work.FTS.EllipticEst.sEta θ *
              (Work.Elliptic.bslOp α u z θ * u z θ) :=
        (MeasureTheory.setIntegral_congr_set
          (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := 0)
            (b := Real.pi / 2))).symm
      have h2 : (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.sEta θ * (G z θ * u z θ))
          = ∫ θ in Set.Ioo 0 (Real.pi / 2),
              Work.FTS.EllipticEst.sEta θ * (G z θ * u z θ) :=
        (MeasureTheory.setIntegral_congr_set
          (MeasureTheory.Ioo_ae_eq_Icc (μ := MeasureTheory.volume) (a := 0)
            (b := Real.pi / 2))).symm
      show (∫ θ in Work.Spaces.Iθ,
            Work.FTS.EllipticEst.sEta θ * (Work.Elliptic.bslOp α u z θ * u z θ))
          = ∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.sEta θ * (G z θ * u z θ)
      rw [h1, h2]
      exact MeasureTheory.setIntegral_congr_fun measurableSet_Ioo
        (fun θ hθ => by rw [h.eq z hz θ hθ.1 hθ.2])))
  exact aesm_restrict_Ioi_of_Iz h1

theorem aeDzNormSig (hK : Work.FTS.EllipticEst.AeStepOneAux.SigmaCoercive) (M : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (u G : ℝ → ℝ → ℝ),
      Work.FTS.EllipticEst.H2W.Ae.AeData α u G →
      Work.Spaces.HkMem α 0 (Work.FTS.EllipticEst.H2W.Ae.grad u) →
      (∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
        Filter.Tendsto (fun θ => u z θ) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0)) →
      Work.FTS.EllipticEst.H2W.Ae.nrm α u ≤ M * Work.FTS.EllipticEst.H2W.Ae.nrm α G →
      α * Work.FTS.EllipticEst.H2W.Ae.nrm α (Work.FTS.EllipticEst.H2W.Ae.grad u)
        ≤ C * Work.FTS.EllipticEst.H2W.Ae.nrm α G := by
  obtain ⟨K, hKpos, hKslice⟩ := Work.FTS.EllipticEst.AeStepOneAux.sliceCoerciveAe hK
  obtain ⟨χ, C₁, C₂, hC₁pos, hC₂pos, hχsm, hχrange, hχleft, hχmid, hχright, hχd1, hχd2,
    hχlim⟩ := Work.FTS.EllipticEst.Mine.zcutFam
  have hC₁nn : 0 ≤ C₁ := le_of_lt hC₁pos
  have hC₂nn : 0 ≤ C₂ := le_of_lt hC₂pos
  set D₁ : ℝ := 3 + C₁ with hD₁def
  set D₂ : ℝ := 6 + 4 * C₁ + (C₂ + C₁) with hD₂def
  have hD₁nn : 0 ≤ D₁ := by rw [hD₁def]; linarith
  have hD₂nn : 0 ≤ D₂ := by rw [hD₂def]; linarith
  set Λ : ℝ := (1 / 32) * D₂ + (21 / 32) * D₁ with hΛdef
  have hΛnn : 0 ≤ Λ := by rw [hΛdef]; positivity
  set Λ₀ : ℝ := K * M ^ 2 + (1 + M ^ 2) / 2 + Λ * M ^ 2 with hΛ₀def
  have hΛ₀pos : 0 < Λ₀ := by rw [hΛ₀def]; nlinarith [sq_nonneg M]
  refine ⟨Real.sqrt Λ₀, Real.sqrt_pos.mpr hΛ₀pos, ?_⟩
  intro α u G hAe hgrad hLeft hMu
  have hα : 0 < α := hAe.hα
  have hα4 : α ≤ 1 / 4 := hAe.hα4
  have hU : Work.Spaces.HkMem α 0 u :=
    Work.FTS.EllipticEst.H2W.AeProof.AeSigma.AeHkMemU α u G hAe
  have hUle : Work.Spaces.HkSq α 0 u ≤ M ^ 2 * Work.Spaces.HkSq α 0 G := by
    have h2 : Real.sqrt (Work.Spaces.HkSq α 0 u)
        ≤ |M| * Real.sqrt (Work.Spaces.HkSq α 0 G) :=
      hMu.trans (mul_le_mul_of_nonneg_right (le_abs_self M) (Real.sqrt_nonneg _))
    have h3 := pow_le_pow_left₀ (Real.sqrt_nonneg _) h2 2
    rwa [Real.sq_sqrt (Work.Spaces.HkSq_nonneg α 0 u), mul_pow, sq_abs,
      Real.sq_sqrt (Work.Spaces.HkSq_nonneg α 0 G)] at h3
  have hRphi : MeasureTheory.IntegrableOn
      (fun z => (Work.Spaces.w z) ^ 2 * Rslice u z) Work.Spaces.Iz :=
    (integrableOn_phi_mul_slice hU).congr_fun (fun z _ => by
      simp only [Rslice_eq_integral]) measurableSet_Ici
  have hZphi : MeasureTheory.IntegrableOn
      (fun z => (Work.Spaces.w z) ^ 2 * Zslice u z) Work.Spaces.Iz :=
    (integrableOn_phi_mul_slice hgrad).congr_fun (fun z _ => by
      simp only [Zslice_eq_integral, Work.FTS.EllipticEst.H2W.Ae.grad]) measurableSet_Ici
  have hGphi : MeasureTheory.IntegrableOn
      (fun z => (Work.Spaces.w z) ^ 2 * Gslice G z) Work.Spaces.Iz :=
    (integrableOn_phi_mul_slice hAe.memG).congr_fun (fun z _ => by
      simp only [Gslice_eq_integral]) measurableSet_Ici
  have hRid : (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 * Rslice u z)
      = Work.Spaces.HkSq α 0 u := (HkSq_zero_eq_Rslice α u).symm
  have haesmR : MeasureTheory.AEStronglyMeasurable (fun z => Rslice u z)
      (MeasureTheory.volume.restrict (Set.Ioi 0)) :=
    (aesm_slice_sq hU).congr (Filter.Eventually.of_forall (fun z => by
      simp only [Rslice_eq_integral]))
  have haesmZ : MeasureTheory.AEStronglyMeasurable (fun z => Zslice u z)
      (MeasureTheory.volume.restrict (Set.Ioi 0)) :=
    (aesm_slice_sq hgrad).congr (Filter.Eventually.of_forall (fun z => by
      simp only [Zslice_eq_integral, Work.FTS.EllipticEst.H2W.Ae.grad]))
  have haesmG : MeasureTheory.AEStronglyMeasurable (fun z => Gslice G z)
      (MeasureTheory.volume.restrict (Set.Ioi 0)) :=
    (aesm_slice_sq hAe.memG).congr (Filter.Eventually.of_forall (fun z => by
      simp only [Gslice_eq_integral]))
  have haesmS : MeasureTheory.AEStronglyMeasurable (Sslice G u)
      (MeasureTheory.volume.restrict (Set.Ioi 0)) := aesm_Sslice hAe
  have hR0 : ∀ z, 0 ≤ Rslice u z := fun z => by
    rw [Rslice]
    refine MeasureTheory.integral_nonneg_of_ae ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
    exact mul_nonneg (Work.FTS.EllipticEst.H2W.AeProof.AeSigma.sEtaR_nonneg hθ) (sq_nonneg _)
  have hG0 : ∀ z, 0 ≤ Gslice G z := fun z => by
    rw [Gslice]
    refine MeasureTheory.integral_nonneg_of_ae ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
    exact mul_nonneg (Work.FTS.EllipticEst.H2W.AeProof.AeSigma.sEtaR_nonneg hθ) (sq_nonneg _)
  have hSabs : ∀ z, 0 < z → |Sslice G u z| ≤
      (1 / 2) * (Gslice G z + Rslice u z) := by
    intro z hz
    rw [abs_le]
    constructor
    · have h1 : (∫ θ in Work.Spaces.Iθ, -(1 / 2) *
          (Work.FTS.EllipticEst.sEta θ * (G z θ) ^ 2
            + Work.FTS.EllipticEst.sEta θ * (u z θ) ^ 2)) ≤ Sslice G u z := by
        rw [Sslice]
        refine MeasureTheory.integral_mono_ae ?_ (integrableOn_Sslice hAe hz) ?_
        · exact ((integrableOn_Gslice hAe hz).add (integrableOn_Rslice hAe hz)).const_mul (-(1 / 2))
        · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
          have hσ : 0 ≤ Work.FTS.EllipticEst.sEta θ :=
            Work.FTS.EllipticEst.H2W.AeProof.AeSigma.sEtaR_nonneg hθ
          have h2 : -(1 / 2) * ((G z θ) ^ 2 + (u z θ) ^ 2) ≤ G z θ * u z θ := by
            nlinarith [sq_nonneg (G z θ + u z θ)]
          calc -(1 / 2) * (Work.FTS.EllipticEst.sEta θ * (G z θ) ^ 2
                + Work.FTS.EllipticEst.sEta θ * (u z θ) ^ 2)
              = Work.FTS.EllipticEst.sEta θ * (-(1 / 2) * ((G z θ) ^ 2 + (u z θ) ^ 2)) := by ring
            _ ≤ Work.FTS.EllipticEst.sEta θ * (G z θ * u z θ) :=
                mul_le_mul_of_nonneg_left h2 hσ
      have h2 : (∫ θ in Work.Spaces.Iθ, -(1 / 2) *
            (Work.FTS.EllipticEst.sEta θ * (G z θ) ^ 2
              + Work.FTS.EllipticEst.sEta θ * (u z θ) ^ 2))
          = -(1 / 2) * (Gslice G z + Rslice u z) := by
        rw [MeasureTheory.integral_const_mul,
          MeasureTheory.integral_add (integrableOn_Gslice hAe hz) (integrableOn_Rslice hAe hz),
          Gslice, Rslice]
      calc -(1 / 2 * (Gslice G z + Rslice u z))
          = (∫ θ in Work.Spaces.Iθ, -(1 / 2) *
              (Work.FTS.EllipticEst.sEta θ * (G z θ) ^ 2
                + Work.FTS.EllipticEst.sEta θ * (u z θ) ^ 2)) := by rw [h2]; ring
        _ ≤ Sslice G u z := h1
    · have h1 : Sslice G u z ≤ ∫ θ in Work.Spaces.Iθ, (1 / 2) *
          (Work.FTS.EllipticEst.sEta θ * (G z θ) ^ 2
            + Work.FTS.EllipticEst.sEta θ * (u z θ) ^ 2) := by
        rw [Sslice]
        refine MeasureTheory.integral_mono_ae (integrableOn_Sslice hAe hz) ?_ ?_
        · exact ((integrableOn_Gslice hAe hz).add (integrableOn_Rslice hAe hz)).const_mul (1 / 2)
        · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
          have hσ : 0 ≤ Work.FTS.EllipticEst.sEta θ :=
            Work.FTS.EllipticEst.H2W.AeProof.AeSigma.sEtaR_nonneg hθ
          have h2 : 2 * (G z θ * u z θ) ≤ (G z θ) ^ 2 + (u z θ) ^ 2 := by
            nlinarith [sq_nonneg (G z θ - u z θ)]
          calc Work.FTS.EllipticEst.sEta θ * (G z θ * u z θ)
              = (1 / 2) * (Work.FTS.EllipticEst.sEta θ * (2 * (G z θ * u z θ))) := by ring
            _ ≤ (1 / 2) * (Work.FTS.EllipticEst.sEta θ
                  * ((G z θ) ^ 2 + (u z θ) ^ 2)) :=
                mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 hσ) (by norm_num)
            _ = (1 / 2) * (Work.FTS.EllipticEst.sEta θ * (G z θ) ^ 2
                  + Work.FTS.EllipticEst.sEta θ * (u z θ) ^ 2) := by ring
      have h2 : (∫ θ in Work.Spaces.Iθ, (1 / 2) *
            (Work.FTS.EllipticEst.sEta θ * (G z θ) ^ 2
              + Work.FTS.EllipticEst.sEta θ * (u z θ) ^ 2))
          = (1 / 2) * (Gslice G z + Rslice u z) := by
        rw [MeasureTheory.integral_const_mul,
          MeasureTheory.integral_add (integrableOn_Gslice hAe hz) (integrableOn_Rslice hAe hz),
          Gslice, Rslice]
      calc Sslice G u z
          ≤ (∫ θ in Work.Spaces.Iθ, (1 / 2) *
              (Work.FTS.EllipticEst.sEta θ * (G z θ) ^ 2
                + Work.FTS.EllipticEst.sEta θ * (u z θ) ^ 2)) := h1
        _ = (1 / 2) * (Gslice G z + Rslice u z) := h2
  have hGid : (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 * Gslice G z)
      = Work.Spaces.HkSq α 0 G := by
    rw [HkSq_zero_eq_phi_mul]
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ici (fun z _ => ?_)
    simp only [Gslice_eq_integral]
  have hcut : ∀ n : ℕ, α ^ 2 * (∫ z in Set.Ioi 0,
        (Work.Spaces.w z) ^ 2 * χ n z * Zslice u z) ≤ Λ₀ * Work.Spaces.HkSq α 0 G := by
    intro n
    set ω : ℝ → ℝ := fun z => (Work.Spaces.w z) ^ 2 * χ n z with hωdef
    have hωm : Measurable ω := measurable_w_sq.mul (hχsm n 2).continuous.measurable
    have hω0 : ∀ z, 0 ≤ ω z := fun z => mul_nonneg (w_sq_nonneg z) (hχrange n z).1
    have hωle : ∀ z, ω z ≤ (Work.Spaces.w z) ^ 2 := fun z =>
      mul_le_of_le_one_right (w_sq_nonneg z) (hχrange n z).2
    have hωd : ContDiffOn ℝ 2 ω (Set.Ioi 0) :=
      contDiffOn_w_sq_two.mul (hχsm n 2).contDiffOn
    have ha : 0 < 1 / ((n : ℝ) + 1) := by positivity
    have hb : 1 / ((n : ℝ) + 1) < 2 * ((n : ℝ) + 1) := by
      have h1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      rw [div_lt_iff₀ h1]
      nlinarith [h1]
    have hsupp : ∀ z, z ∉ Set.Icc (1 / ((n : ℝ) + 1)) (2 * ((n : ℝ) + 1)) → ω z = 0 := by
      intro z hz
      rcases lt_or_ge z (1 / ((n : ℝ) + 1)) with h | h
      · have h1 : χ n z = 0 := hχleft n z (le_of_lt h)
        simp only [hωdef, h1, mul_zero]
      · have h2 : 2 * ((n : ℝ) + 1) < z := by
          rcases lt_or_ge (2 * ((n : ℝ) + 1)) z with h2 | h2
          · exact h2
          · exact absurd (Set.mem_Icc.mpr ⟨h, h2⟩) hz
        have h1 : χ n z = 0 := hχright n z (le_of_lt h2)
        simp only [hωdef, h1, mul_zero]
    have hA := truncRadialIbpSigma α u hAe.smooth hgrad hAe.memRad2 hU ω hωd ha hb hsupp hω0 hωle
    have hBz : ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
        -K * Rslice u z ≤ Lslice u z := by
      filter_upwards [hKslice α u G hAe hLeft] with z hz
      have h1 : Rslice u z = ∫ θ in Work.Spaces.Iθ,
          (u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ := by
        rw [Rslice]
        exact MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => mul_comm _ _)
      rw [h1]
      exact hz.2
    have hRint : MeasureTheory.IntegrableOn (fun z => ω z * Rslice u z) (Set.Ioi 0) :=
      integrableOn_omega_mul hRphi hωm hω0 hωle hR0 haesmR
    have hGint : MeasureTheory.IntegrableOn (fun z => ω z * Gslice G z) (Set.Ioi 0) :=
      integrableOn_omega_mul hGphi hωm hω0 hωle hG0 haesmG
    have hSint : MeasureTheory.IntegrableOn (fun z => ω z * Sslice G u z) (Set.Ioi 0) := by
      refine MeasureTheory.Integrable.mono' ((hGint.add hRint).const_mul (1 / 2))
        (hωm.aestronglyMeasurable.mul haesmS) ?_
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hω0 z)]
      calc ω z * |Sslice G u z| ≤ ω z * ((1 / 2) * (Gslice G z + Rslice u z)) :=
            mul_le_mul_of_nonneg_left (hSabs z hz) (hω0 z)
        _ = (1 / 2) * (ω z * Gslice G z + ω z * Rslice u z) := by ring
    have hLint : MeasureTheory.IntegrableOn (fun z => ω z * Lslice u z) (Set.Ioi 0) := by
      refine (hA.1.add hSint).congr ?_
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz
      show ω z * Pslice α u z + ω z * Sslice G u z = ω z * Lslice u z
      rw [Lslice_eq_Pslice_add_Sslice hAe hz]
      ring
    have hPS : (∫ z in Set.Ioi 0, ω z * Pslice α u z)
        = (∫ z in Set.Ioi 0, ω z * Lslice u z)
          - (∫ z in Set.Ioi 0, ω z * Sslice G u z) := by
      have h1 : (∫ z in Set.Ioi 0, ω z * Lslice u z)
          = (∫ z in Set.Ioi 0, ω z * Pslice α u z)
            + (∫ z in Set.Ioi 0, ω z * Sslice G u z) := by
        rw [show (∫ z in Set.Ioi 0, ω z * Lslice u z)
            = ∫ z in Set.Ioi 0, (ω z * Pslice α u z + ω z * Sslice G u z) from by
          refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun z hz => ?_)
          show ω z * Lslice u z = ω z * Pslice α u z + ω z * Sslice G u z
          rw [Lslice_eq_Pslice_add_Sslice hAe hz]
          ring]
        exact MeasureTheory.integral_add hA.1 hSint
      linarith [h1]
    have hBL : -(∫ z in Set.Ioi 0, ω z * Lslice u z)
        ≤ K * (∫ z in Set.Ioi 0, ω z * Rslice u z) := by
      have h1 : (∫ z in Set.Ioi 0, (-K) * (ω z * Rslice u z))
          ≤ ∫ z in Set.Ioi 0, ω z * Lslice u z := by
        refine MeasureTheory.integral_mono_ae (hRint.const_mul (-K)) hLint ?_
        filter_upwards [hBz, MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz _
        calc (-K) * (ω z * Rslice u z) = ω z * (-K * Rslice u z) := by ring
          _ ≤ ω z * Lslice u z := mul_le_mul_of_nonneg_left hz (hω0 z)
      rw [MeasureTheory.integral_const_mul] at h1
      linarith
    have hSle_int : (∫ z in Set.Ioi 0, ω z * Sslice G u z)
        ≤ (1 / 2) * ((∫ z in Set.Ioi 0, ω z * Gslice G z)
            + (∫ z in Set.Ioi 0, ω z * Rslice u z)) := by
      have h1 : (∫ z in Set.Ioi 0, ω z * Sslice G u z)
          ≤ ∫ z in Set.Ioi 0, (1 / 2) * (ω z * Gslice G z + ω z * Rslice u z) := by
        refine MeasureTheory.integral_mono_ae hSint ((hGint.add hRint).const_mul (1 / 2)) ?_
        filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz
        calc ω z * Sslice G u z ≤ ω z * ((1 / 2) * (Gslice G z + Rslice u z)) :=
              mul_le_mul_of_nonneg_left (abs_le.mp (hSabs z hz)).2 (hω0 z)
          _ = (1 / 2) * (ω z * Gslice G z + ω z * Rslice u z) := by ring
      rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_add hGint hRint] at h1
      linarith
    have hcc : ∀ z, 0 < z → |deriv (fun y : ℝ => y * ω y) z| ≤ D₁ * (Work.Spaces.w z) ^ 2 := by
      have h := (Work.FTS.EllipticEst.Honest.omegaW_deriv_bounds (hχsm n 2) (hχd1 n)
        (chi_second_le (hχsm n 2) (hχd1 n) (hχd2 n))
        (fun z => by rw [abs_of_nonneg (hχrange n z).1]; exact (hχrange n z).2) hC₁nn
        (by linarith)).1
      exact h
    have hcc2 : ∀ z, 0 < z →
        |deriv (deriv (fun y : ℝ => y ^ 2 * ω y)) z| ≤ D₂ * (Work.Spaces.w z) ^ 2 := by
      have h := (Work.FTS.EllipticEst.Honest.omegaW_deriv_bounds (hχsm n 2) (hχd1 n)
        (chi_second_le (hχsm n 2) (hχd1 n) (hχd2 n))
        (fun z => by rw [abs_of_nonneg (hχrange n z).1]; exact (hχrange n z).2) hC₁nn
        (by linarith)).2
      exact h
    have hsm1 : MeasureTheory.AEStronglyMeasurable (deriv (fun y : ℝ => y * ω y))
        (MeasureTheory.volume.restrict (Set.Ioi 0)) :=
      ((contDiffOn_id.mul hωd).continuousOn_deriv_of_isOpen isOpen_Ioi
        (by norm_num)).aestronglyMeasurable measurableSet_Ioi
    have hsm2 : MeasureTheory.AEStronglyMeasurable (deriv (deriv (fun y : ℝ => y ^ 2 * ω y)))
        (MeasureTheory.volume.restrict (Set.Ioi 0)) :=
      ((((contDiffOn_id.pow 2).mul hωd).deriv_of_isOpen (m := 1) isOpen_Ioi
        (by norm_num)).continuousOn_deriv_of_isOpen isOpen_Ioi
        (by norm_num)).aestronglyMeasurable measurableSet_Ioi
    have hT1bd : |∫ z in Set.Ioi 0, deriv (fun y : ℝ => y * ω y) z * Rslice u z|
        ≤ D₁ * (M ^ 2 * Work.Spaces.HkSq α 0 G) := by
      have h := (integrableOn_coef_mul_le hRphi hD₁nn hcc hR0 hsm1 haesmR).2
      rw [hRid] at h
      exact h.trans (mul_le_mul_of_nonneg_left hUle hD₁nn)
    have hT2bd : |∫ z in Set.Ioi 0, deriv (deriv (fun y : ℝ => y ^ 2 * ω y)) z * Rslice u z|
        ≤ D₂ * (M ^ 2 * Work.Spaces.HkSq α 0 G) := by
      have h := (integrableOn_coef_mul_le hRphi hD₂nn hcc2 hR0 hsm2 haesmR).2
      rw [hRid] at h
      exact h.trans (mul_le_mul_of_nonneg_left hUle hD₂nn)
    have hid : (∫ z in Set.Ioi 0, ω z * Pslice α u z)
        = -α ^ 2 * (∫ z in Set.Ioi 0, ω z * Zslice u z)
          + (α ^ 2 / 2) * (∫ z in Set.Ioi 0,
              deriv (deriv (fun y : ℝ => y ^ 2 * ω y)) z * Rslice u z)
          - (α * (5 + α) / 2) * (∫ z in Set.Ioi 0,
              deriv (fun y : ℝ => y * ω y) z * Rslice u z) := by
      have h := hA.2
      simp only [Rslice, Zslice, Pslice] at h ⊢
      exact h
    have hkey : α ^ 2 * (∫ z in Set.Ioi 0, ω z * Zslice u z)
        ≤ K * (∫ z in Set.Ioi 0, ω z * Rslice u z)
          + (1 / 2) * ((∫ z in Set.Ioi 0, ω z * Gslice G z)
              + (∫ z in Set.Ioi 0, ω z * Rslice u z))
          + (α ^ 2 / 2) * (D₂ * (M ^ 2 * Work.Spaces.HkSq α 0 G))
          + (α * (5 + α) / 2) * (D₁ * (M ^ 2 * Work.Spaces.HkSq α 0 G)) := by
      have hA1 : (α ^ 2 / 2) * (∫ z in Set.Ioi 0,
            deriv (deriv (fun y : ℝ => y ^ 2 * ω y)) z * Rslice u z)
          ≤ (α ^ 2 / 2) * (D₂ * (M ^ 2 * Work.Spaces.HkSq α 0 G)) :=
        mul_le_mul_of_nonneg_left ((le_abs_self _).trans hT2bd) (by positivity)
      have hA3 : -((α * (5 + α) / 2) * (∫ z in Set.Ioi 0,
            deriv (fun y : ℝ => y * ω y) z * Rslice u z))
          ≤ (α * (5 + α) / 2) * (D₁ * (M ^ 2 * Work.Spaces.HkSq α 0 G)) := by
        have h2 : -(∫ z in Set.Ioi 0, deriv (fun y : ℝ => y * ω y) z * Rslice u z)
            ≤ D₁ * (M ^ 2 * Work.Spaces.HkSq α 0 G) := (neg_le_abs _).trans hT1bd
        have h3 := mul_le_mul_of_nonneg_left h2 (by positivity : (0 : ℝ) ≤ α * (5 + α) / 2)
        linarith [h3]
      linarith [hid, hPS, hBL, hSle_int, hA1, hA3]
    have hRωle : (∫ z in Set.Ioi 0, ω z * Rslice u z) ≤ M ^ 2 * Work.Spaces.HkSq α 0 G :=
      calc (∫ z in Set.Ioi 0, ω z * Rslice u z)
          ≤ ∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 * Rslice u z :=
            integral_omega_mul_le hRphi hωm hω0 hωle hR0 haesmR
        _ = Work.Spaces.HkSq α 0 u := hRid
        _ ≤ M ^ 2 * Work.Spaces.HkSq α 0 G := hUle
    have hGωle : (∫ z in Set.Ioi 0, ω z * Gslice G z) ≤ Work.Spaces.HkSq α 0 G :=
      calc (∫ z in Set.Ioi 0, ω z * Gslice G z)
          ≤ ∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 * Gslice G z :=
            integral_omega_mul_le hGphi hωm hω0 hωle hG0 haesmG
        _ = Work.Spaces.HkSq α 0 G := hGid
    have hα2 : α ^ 2 / 2 ≤ 1 / 32 := by nlinarith [hα, hα4]
    have hα5 : α * (5 + α) / 2 ≤ 21 / 32 := by
      have h5 : α * (5 + α) ≤ 21 / 16 := by nlinarith [hα, hα4]
      linarith
    have h𝔤nn : 0 ≤ Work.Spaces.HkSq α 0 G := Work.Spaces.HkSq_nonneg α 0 G
    have hMnn : 0 ≤ M ^ 2 := sq_nonneg M
    have hEq : (K * M ^ 2 + (1 + M ^ 2) / 2 + ((1 / 32) * D₂ + (21 / 32) * D₁) * M ^ 2)
          * Work.Spaces.HkSq α 0 G
        = K * (M ^ 2 * Work.Spaces.HkSq α 0 G)
          + (1 / 2) * (Work.Spaces.HkSq α 0 G + M ^ 2 * Work.Spaces.HkSq α 0 G)
          + ((1 / 32) * D₂) * (M ^ 2 * Work.Spaces.HkSq α 0 G)
          + ((21 / 32) * D₁) * (M ^ 2 * Work.Spaces.HkSq α 0 G) := by ring
    have hstep : α ^ 2 * (∫ z in Set.Ioi 0, ω z * Zslice u z)
        ≤ (K * M ^ 2 + (1 + M ^ 2) / 2 + ((1 / 32) * D₂ + (21 / 32) * D₁) * M ^ 2)
            * Work.Spaces.HkSq α 0 G := by
      have h1 : K * (∫ z in Set.Ioi 0, ω z * Rslice u z)
          ≤ K * (M ^ 2 * Work.Spaces.HkSq α 0 G) :=
        mul_le_mul_of_nonneg_left hRωle (le_of_lt hKpos)
      have h2 : (1 / 2) * ((∫ z in Set.Ioi 0, ω z * Gslice G z)
            + (∫ z in Set.Ioi 0, ω z * Rslice u z))
          ≤ (1 / 2) * (Work.Spaces.HkSq α 0 G + M ^ 2 * Work.Spaces.HkSq α 0 G) := by
        have h3 := add_le_add hGωle hRωle
        linarith
      have h3 : (α ^ 2 / 2) * (D₂ * (M ^ 2 * Work.Spaces.HkSq α 0 G))
          ≤ ((1 / 32) * D₂) * (M ^ 2 * Work.Spaces.HkSq α 0 G) := by
        have h := mul_le_mul_of_nonneg_right hα2
          (by positivity : (0 : ℝ) ≤ D₂ * (M ^ 2 * Work.Spaces.HkSq α 0 G))
        linarith [h]
      have h4 : (α * (5 + α) / 2) * (D₁ * (M ^ 2 * Work.Spaces.HkSq α 0 G))
          ≤ ((21 / 32) * D₁) * (M ^ 2 * Work.Spaces.HkSq α 0 G) := by
        have h := mul_le_mul_of_nonneg_right hα5
          (by positivity : (0 : ℝ) ≤ D₁ * (M ^ 2 * Work.Spaces.HkSq α 0 G))
        linarith [h]
      linarith [hkey, h1, h2, h3, h4, hEq]
    rw [hΛ₀def, hΛdef]
    exact hstep
  have hlim : α ^ 2 * (∫ z in Work.Spaces.Iz, (Work.Spaces.w z) ^ 2 * Zslice u z)
      ≤ Λ₀ * Work.Spaces.HkSq α 0 G := by
    have hφZ : MeasureTheory.IntegrableOn
        (fun z => (Work.Spaces.w z) ^ 2 * Zslice u z) (Set.Ioi 0) :=
      hZphi.mono_set Set.Ioi_subset_Ici_self
    have hconv : Filter.Tendsto
        (fun n => ∫ z in Set.Ioi 0, (Work.Spaces.w z) ^ 2 * χ n z * Zslice u z)
        Filter.atTop (nhds (∫ z in Set.Ioi 0, (Work.Spaces.w z) ^ 2 * Zslice u z)) := by
      refine MeasureTheory.tendsto_integral_of_dominated_convergence
        (bound := fun z => |(Work.Spaces.w z) ^ 2 * Zslice u z|)
        (F := fun n z => (Work.Spaces.w z) ^ 2 * χ n z * Zslice u z) ?_ hφZ.abs ?_ ?_
      · intro n
        exact (measurable_w_sq.mul (hχsm n 2).continuous.measurable).aestronglyMeasurable.mul haesmZ
      · intro n
        filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz
        rw [Real.norm_eq_abs, abs_mul, abs_mul]
        have h1 : |(Work.Spaces.w z) ^ 2| * |χ n z| ≤ |(Work.Spaces.w z) ^ 2| := by
          rw [abs_of_nonneg (w_sq_nonneg z)]
          calc (Work.Spaces.w z) ^ 2 * |χ n z| ≤ (Work.Spaces.w z) ^ 2 * 1 :=
                mul_le_mul_of_nonneg_left
                  (by rw [abs_of_nonneg (hχrange n z).1]; exact (hχrange n z).2) (w_sq_nonneg z)
            _ = (Work.Spaces.w z) ^ 2 := mul_one _
        calc |(Work.Spaces.w z) ^ 2| * |χ n z| * |Zslice u z|
            ≤ |(Work.Spaces.w z) ^ 2| * |Zslice u z| :=
              mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
          _ = |(Work.Spaces.w z) ^ 2 * Zslice u z| := (abs_mul _ _).symm
      · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz
        have h1 : Filter.Tendsto (fun n : ℕ => χ n z) Filter.atTop (nhds 1) := hχlim z hz
        have h2 : (fun n : ℕ => (Work.Spaces.w z) ^ 2 * χ n z * Zslice u z)
            = fun n : ℕ => ((Work.Spaces.w z) ^ 2 * Zslice u z) * χ n z := by
          funext n; ring
        rw [h2]
        simpa using h1.const_mul ((Work.Spaces.w z) ^ 2 * Zslice u z)
    have h2 := le_of_tendsto' (hconv.const_mul (α ^ 2)) (fun n => hcut n)
    rwa [setIntegral_Ioi_eq_Iz] at h2
  have hmain : α ^ 2 * Work.Spaces.HkSq α 0 (fun z θ => z * Work.Spaces.pz u z θ)
      ≤ Λ₀ * Work.Spaces.HkSq α 0 G := by
    rw [HkSq_grad_eq_Zslice]
    exact hlim
  have hsqrt : α * Real.sqrt (Work.Spaces.HkSq α 0 (fun z θ => z * Work.Spaces.pz u z θ))
      ≤ Real.sqrt Λ₀ * Real.sqrt (Work.Spaces.HkSq α 0 G) := by
    have h2 : Real.sqrt (α ^ 2 * Work.Spaces.HkSq α 0 (fun z θ => z * Work.Spaces.pz u z θ))
        ≤ Real.sqrt (Λ₀ * Work.Spaces.HkSq α 0 G) := Real.sqrt_le_sqrt hmain
    rwa [Real.sqrt_mul (sq_nonneg α), Real.sqrt_sq (le_of_lt hα),
      Real.sqrt_mul (le_of_lt hΛ₀pos)] at h2
  exact hsqrt


end Work.FTS.EllipticEst.AeStepOneAux.Sig2
