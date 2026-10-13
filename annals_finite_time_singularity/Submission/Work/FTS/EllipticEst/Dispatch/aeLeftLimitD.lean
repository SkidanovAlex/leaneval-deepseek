/-
Copyright: work module for the Elgindi finite-time singularity project.

# The `θ = 0` endpoint limit of the slices in the almost-everywhere class

Target (`Work.FTS.EllipticEst.AngAWeak.aeLeftLimitD`): for every datum
`Work.FTS.EllipticEst.H2W.Ae.AeData α u G` of the weak class of the level-`0` elliptic estimate,
the `θ`-slice `θ ↦ u z θ` tends to `0` as `θ → 0⁺`, for almost every `z > 0`.

## The mechanism

The class fixes the Dirichlet data only as *values* (`u z 0 = 0`), while the weighted norms see
the open quadrant alone, so a datum could in principle carry a *jump* at `θ = 0`: the slice
could tend to `Λ(z) ≠ 0`.  The two a.e. solvability conditions `F_*(u) = F_*(G) = 0` exclude
this, through the angular-moment identity

  `Λ(z) = -(F_*(G)(z) + α²z²·F_*(∂_z²u)(z) + α(5+α)z·F_*(∂_zu)(z))`,

valid for every `z > 0`: the left endpoint limit exists for every `z > 0`
(`Work.FTS.EllipticEst.sliceLimitLeftExists`), and the identity is the classical integration by
parts of `Lzero1 (u z ·)` against `sinθcos²θ` (`Honest.sliceMoment_eq_neg_limit`, whose
hypotheses — the boundedness of the slice and of its derivative — are supplied by
`Endpt.sliceBdd_of_hmB` from `HkMem α 0 (∂_θθu)`; `Lzero1_moment_eq_neg_limitD` below) combined
with the pointwise equation (`fstar_G_eqD` below).  So it suffices to know that the two moments
`F_*(∂_zu)` and `F_*(∂_z²u)` vanish a.e.; that is `aeMomentChainD`, and it is where the real work
is:

* `F_*(∂_zu) ≡ 0` is *not* obtained from the moment relation for `u` (the box integrability of
  `∂_zu·sinθcos²θ` along `z` is exactly the missing `ℋ⁰`-honesty of `z∂_zu`); instead it comes
  from the *second-order* difference quotient of `F_*(u)`, which needs only the box
  integrability of `∂_z²u·sinθcos²θ` — and that *is* available, since `HkMem α 0 (z²∂_z²u)` is
  a field of `AeData`.  Concretely `(F_*(u)(z) - F_*(u)(z-hh))/hh → F_*(∂_zu)(z)`, and since
  `F_*(u) = 0` a.e. the quotient is zero for a.e. `hh`, which forces the limit to vanish
  (`aeZeroOfDifQuot`).
* `F_*(∂_z²u) = 0` a.e. then follows from the moment relation applied to `∂_zu` together with
  the *continuity* of `z ↦ F_*(∂_zu)(z)` (a constant plus the primitive of the locally
  integrable `z ↦ F_*(∂_z²u)(z)`).

## The pieces

The four analytic inputs are isolated in the sibling files of this directory:

* `absPzIter2SliceFacts` — box- and section-integrability of `|∂_z²u|·|sinθcos²θ|`;
* `difQuotSubDerivBound` — the second-order Taylor bound for the difference quotient of `F_*(u)`
  (slicewise `abs_difquot_sub_deriv_le`, then integrated in `θ`);
* `tendstoThetaIntervalAbsPzIter2` — the majorant of that bound tends to `0`;
* `aeZeroOfDifQuot` — an a.e.-zero function whose backward difference quotients converge at every
  point has an a.e.-zero limit function.

Everything here is `sorry`-free and rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Order.Interval.Basic
import Submission.Work.FTS.EllipticEst.H2W.Ae.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.aesm_slice_of_continuousOn_Qd
import Submission.Work.FTS.EllipticEst.sliceLimitLeftExists
import Submission.Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo
import Submission.Work.FTS.EllipticEst.Blocks.moment_relation
import Submission.Work.FTS.EllipticEst.Endpt.moment_chain_pz
import Submission.Work.FTS.EllipticEst.Endpt.boxIntegrable_pzIter2Psi
import Submission.Work.FTS.EllipticEst.Endpt.integrableOn_fstar_pzIter2
import Submission.Work.FTS.EllipticEst.Endpt.sliceBdd_of_hmB
import Submission.Work.FTS.EllipticEst.H2W.AeProof.AeSliceMomentFinite
import Submission.Work.FTS.EllipticEst.Honest.HonSliceLimitZero
import Submission.Work.FTS.EllipticEst.H2W.PsiSlices.AeBasic
import Submission.Work.FTS.EllipticEst.AngAWeak.absPzIter2SliceFacts
import Submission.Work.FTS.EllipticEst.Dispatch.difQuotSubDerivBoundD
import Submission.Work.FTS.EllipticEst.AngAWeak.tendstoThetaIntervalAbsPzIter2
import Submission.Work.FTS.EllipticEst.AngAWeak.aeZeroOfDifQuot

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology Interval
open MeasureTheory Set Filter
open Work.FTS.EllipticEst.H2W.Ae

namespace Work.FTS.EllipticEst.Dispatch

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedVariables false

local notation "Iθ" => Work.Spaces.Iθ
local notation "sg" => Work.Elliptic.sinCos2

/-! ## The angular slices of an `AeData` datum are `L¹` against `sinθcos²θ` -/

/-- `θ ↦ sinθcos²θ` is continuous. -/
private theorem continuous_sinCos2 : Continuous sg := by
  unfold Work.Elliptic.sinCos2
  fun_prop

/-- `θ ↦ |sinθcos²θ|` is integrable on `Iθ`. -/
private theorem integrableOn_abs_sinCos2 :
    MeasureTheory.IntegrableOn (fun θ : ℝ => |sg θ|) Iθ := by
  have h : MeasureTheory.IntegrableOn (fun θ : ℝ => |sg θ|) (Set.Icc 0 (Real.pi / 2)) :=
    continuous_sinCos2.abs.continuousOn.integrableOn_compact isCompact_Icc
  rwa [Work.Spaces.Iθ]

/-- **Slice integrability.**  For a datum whose `θ`-slices are bounded on the open interval
(which `HkMem α 0 (∂_θθu)` supplies through `Endpt.sliceBdd_of_hmB`) the product with the
bounded angular weight `sinθcos²θ` is integrable: at the two endpoints the *values* `u z 0` and
`u z (π/2)` vanish. -/
theorem slice_mul_sinCos2_integrableD {α : ℝ} {u : ℝ → ℝ → ℝ} {z : ℝ}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry u)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hmemB : Work.Spaces.HkMem α 0 (Work.Spaces.pthIter 2 u))
    (hz : 0 < z) (h0 : u z 0 = 0) (h1 : u z (Real.pi / 2) = 0) :
    MeasureTheory.IntegrableOn (fun θ : ℝ => u z θ * sg θ) Iθ := by
  obtain ⟨C, hCpos, hC⟩ := Work.FTS.EllipticEst.Endpt.sliceBdd_of_hmB hsm hmemB hz
  have hSm : Work.FTS.EllipticEst.SmoothOpen u :=
    Work.FTS.EllipticEst.smoothOpen_of_forall hsm
  have haesm : MeasureTheory.AEStronglyMeasurable (fun θ : ℝ => u z θ * sg θ)
      (MeasureTheory.volume.restrict Iθ) :=
    (Work.Spaces.aesm_slice_of_continuousOn_Qd (Function.uncurry u) hSm.continuousOn hz).mul
      continuous_sinCos2.aestronglyMeasurable
  refine MeasureTheory.Integrable.mono' (integrableOn_abs_sinCos2.const_mul C) haesm ?_
  refine MeasureTheory.ae_restrict_of_forall_mem
    (show MeasurableSet Iθ from measurableSet_Icc) (fun θ hθI => ?_)
  have hb : |u z θ| ≤ C := by
    rcases eq_or_lt_of_le hθI.1 with hθ0 | hθ0
    · rw [← hθ0, h0]; simp only [mul_zero, abs_zero]; exact hCpos.le
    rcases eq_or_lt_of_le hθI.2 with hθ1 | hθ1
    · rw [hθ1, h1]; simp only [mul_zero, abs_zero]; exact hCpos.le
    · exact (hC θ ⟨hθ0, hθ1⟩).1
  rw [Real.norm_eq_abs, abs_mul]
  exact mul_le_mul_of_nonneg_right hb (abs_nonneg _)

/-! ## The endpoint moment identity in the weak class -/

/-- **The angular-moment identity.**  For `z > 0` the pairing of the angular operator
`Lzero1 (u z ·)` against the kernel function `sinθcos²θ` is minus the left endpoint limit of the
slice.  This is the form of `Endpt.Lzero1_integral_eq_neg_limit` in which the boundedness of the
slice and of its derivative required by the fundamental theorem of calculus is supplied directly
by `Endpt.sliceBdd_of_hmB`. -/
theorem Lzero1_moment_eq_neg_limitD {α : ℝ} {u : ℝ → ℝ → ℝ} {z L : ℝ}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry u)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hmemB : Work.Spaces.HkMem α 0 (Work.Spaces.pthIter 2 u)) (hz : 0 < z)
    (hLz : MeasureTheory.IntegrableOn
      (fun θ : ℝ => Work.FTS.EllipticEst.Lzero1 (fun t => u z t) θ * sg θ) Iθ)
    (hlim : Filter.Tendsto (fun θ => u z θ) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds L)) :
    (∫ θ in Iθ, Work.FTS.EllipticEst.Lzero1 (fun t => u z t) θ * sg θ) = -L := by
  obtain ⟨C, hCpos, hC⟩ := Work.FTS.EllipticEst.Endpt.sliceBdd_of_hmB hsm hmemB hz
  have hcd : ContDiffOn ℝ 2 (fun θ => u z θ) (Set.Ioo 0 (Real.pi / 2)) :=
    Work.FTS.EllipticEst.Endpt.contDiffOn_slice_of_strip hsm hz 2
  exact Work.FTS.EllipticEst.Honest.sliceMoment_eq_neg_limit hCpos.le hcd
    (fun θ hθ => hC θ hθ) hLz hlim

/-! ## The moment of the equation -/

/-- **The moment of the source.**  On the open quadrant the equation reads
`G = -(α²z²)∂_z²u - (α(5+α)z)∂_zu + Lzero u` (`Work.Elliptic.bslOp_apply`); taking the
`θ`-moment against `sinθcos²θ`, and using that `Lzero u` on a slice is `Lzero1 (u z ·)`, gives
the moment identity behind `AeSliceMomentIdent`. -/
theorem fstar_G_eqD {α : ℝ} {u G : ℝ → ℝ → ℝ} (h : AeData α u G) {z : ℝ} (hz : 0 < z) :
    Work.Elliptic.Fstar G z
      = -(α ^ 2 * z ^ 2) * Work.Elliptic.Fstar (Work.Spaces.pzIter 2 u) z
        - (α * (5 + α) * z) * Work.Elliptic.Fstar (Work.Spaces.pz u) z
        + ∫ θ in Iθ, Work.FTS.EllipticEst.Lzero1 (fun t => u z t) θ * sg θ := by
  -- `Lzero` of the slice is `Lzero1` of the one-variable slice
  have hLzero : ∀ θ : ℝ, Work.Elliptic.Lzero u z θ
      = Work.FTS.EllipticEst.Lzero1 (fun t => u z t) θ := by
    intro θ
    simp only [Work.FTS.EllipticEst.Lzero1, Work.Elliptic.Lzero,
      Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero, Work.Spaces.pth]
  obtain ⟨h1, h2, h3⟩ := Work.FTS.EllipticEst.H2W.AeProof.AeSliceMomentFinite α u G h hz
  -- ## the pointwise decomposition on the open interval
  have hpt : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      Work.FTS.EllipticEst.Lzero1 (fun t => u z t) θ * sg θ
        = G z θ * sg θ + α ^ 2 * z ^ 2 * (Work.Spaces.pzIter 2 u z θ * sg θ)
          + α * (5 + α) * z * (Work.Spaces.pz u z θ * sg θ) := by
    intro θ hθ
    have heq := AeData.eq h z hz θ hθ.1 hθ.2
    rw [Work.Elliptic.bslOp_apply] at heq
    have hkey : Work.Elliptic.Lzero u z θ = G z θ + α ^ 2 * z ^ 2 * Work.Spaces.pzIter 2 u z θ
        + α * (5 + α) * z * Work.Spaces.pz u z θ := by linarith
    rw [← hLzero θ, hkey]
    ring
  have hae : (fun θ : ℝ => Work.FTS.EllipticEst.Lzero1 (fun t => u z t) θ * sg θ)
      =ᵐ[MeasureTheory.volume.restrict Iθ]
      (fun θ : ℝ => G z θ * sg θ + α ^ 2 * z ^ 2 * (Work.Spaces.pzIter 2 u z θ * sg θ)
        + α * (5 + α) * z * (Work.Spaces.pz u z θ * sg θ)) :=
    Work.FTS.EllipticEst.ae_restrict_Icc_of_forall_Ioo (fun θ hθ => hpt θ hθ)
  -- ## integrability of the source term
  have hGint : MeasureTheory.IntegrableOn (fun θ : ℝ => G z θ * sg θ) Iθ := by
    have hsub : MeasureTheory.IntegrableOn
        (fun θ : ℝ => Work.FTS.EllipticEst.Lzero1 (fun t => u z t) θ * sg θ
          - (α ^ 2 * z ^ 2 * (Work.Spaces.pzIter 2 u z θ * sg θ)
            + α * (5 + α) * z * (Work.Spaces.pz u z θ * sg θ))) Iθ :=
      h3.sub ((h2.const_mul _).add (h1.const_mul _))
    refine hsub.congr ?_
    filter_upwards [hae] with θ hθ
    linarith
  -- ## the moment identity
  have hIntegral : (∫ θ in Iθ, Work.FTS.EllipticEst.Lzero1 (fun t => u z t) θ * sg θ)
      = Work.Elliptic.Fstar G z
        + α ^ 2 * z ^ 2 * (∫ θ in Iθ, Work.Spaces.pzIter 2 u z θ * sg θ)
        + α * (5 + α) * z * (∫ θ in Iθ, Work.Spaces.pz u z θ * sg θ) := by
    have h1' : (∫ θ in Iθ, Work.FTS.EllipticEst.Lzero1 (fun t => u z t) θ * sg θ)
        = ∫ θ in Iθ, (G z θ * sg θ
            + α ^ 2 * z ^ 2 * (Work.Spaces.pzIter 2 u z θ * sg θ)
            + α * (5 + α) * z * (Work.Spaces.pz u z θ * sg θ)) :=
      MeasureTheory.integral_congr_ae hae
    have hsplit1 : (∫ θ in Iθ, (G z θ * sg θ
          + α ^ 2 * z ^ 2 * (Work.Spaces.pzIter 2 u z θ * sg θ)
          + α * (5 + α) * z * (Work.Spaces.pz u z θ * sg θ)))
        = (∫ θ in Iθ, (G z θ * sg θ
            + α ^ 2 * z ^ 2 * (Work.Spaces.pzIter 2 u z θ * sg θ)))
          + (∫ θ in Iθ, α * (5 + α) * z * (Work.Spaces.pz u z θ * sg θ)) :=
      MeasureTheory.integral_add
        (f := fun θ : ℝ => G z θ * sg θ
          + α ^ 2 * z ^ 2 * (Work.Spaces.pzIter 2 u z θ * sg θ))
        (g := fun θ : ℝ => α * (5 + α) * z * (Work.Spaces.pz u z θ * sg θ))
        (hGint.add (h2.const_mul (α ^ 2 * z ^ 2))) (h1.const_mul (α * (5 + α) * z))
    have hsplit2 : (∫ θ in Iθ, (G z θ * sg θ
          + α ^ 2 * z ^ 2 * (Work.Spaces.pzIter 2 u z θ * sg θ)))
        = (∫ θ in Iθ, G z θ * sg θ)
          + (∫ θ in Iθ, α ^ 2 * z ^ 2 * (Work.Spaces.pzIter 2 u z θ * sg θ)) :=
      MeasureTheory.integral_add
        (f := fun θ : ℝ => G z θ * sg θ)
        (g := fun θ : ℝ => α ^ 2 * z ^ 2 * (Work.Spaces.pzIter 2 u z θ * sg θ))
        hGint (h2.const_mul (α ^ 2 * z ^ 2))
    rw [h1', hsplit1, hsplit2, MeasureTheory.integral_const_mul,
      MeasureTheory.integral_const_mul]
    rfl
  have hfinal : (∫ θ in Iθ, Work.FTS.EllipticEst.Lzero1 (fun t => u z t) θ * sg θ)
      = Work.Elliptic.Fstar G z
        + α ^ 2 * z ^ 2 * Work.Elliptic.Fstar (Work.Spaces.pzIter 2 u) z
        + α * (5 + α) * z * Work.Elliptic.Fstar (Work.Spaces.pz u) z := by
    rw [hIntegral]
    rfl
  linarith [hfinal]

/-- **The angular-moment chain of the weak class `AeData`.**  For a datum `AeData α u G` the two
radial moments of the solution vanish: `F_*(∂_zu) ≡ 0` everywhere on `(0,∞)` and
`F_*(∂_z²u) = 0` almost everywhere. -/
theorem aeMomentChainD {α : ℝ} {u G : ℝ → ℝ → ℝ} (h : AeData α u G) :
    (∀ z : ℝ, 0 < z → Work.Elliptic.Fstar (Work.Spaces.pz u) z = 0) ∧
      (∀ᵐ z ∂(volume.restrict (Set.Ioi 0)),
        Work.Elliptic.Fstar (Work.Spaces.pzIter 2 u) z = 0) := by
  have hsm := AeData.smooth h
  have hS : Work.FTS.EllipticEst.SmoothOpen u :=
    Work.FTS.EllipticEst.smoothOpen_of_forall hsm
  have hmemB := AeData.memAng2 h
  have hmemZ := AeData.memRad2 h
  -- ## the two slice-integrability inputs of the moment chain
  have hψsl : ∀ z : ℝ, 0 < z → MeasureTheory.IntegrableOn (fun θ : ℝ => u z θ * sg θ) Iθ :=
    fun z hz => slice_mul_sinCos2_integrableD (α := α) hsm hmemB hz
      (AeData.dirZero h z) (AeData.dirPi h z)
  have hp1sl : ∀ z : ℝ, 0 < z →
      MeasureTheory.IntegrableOn (fun θ : ℝ => Work.Spaces.pz u z θ * sg θ) Iθ :=
    fun z hz => (Work.FTS.EllipticEst.H2W.AeProof.AeSliceMomentFinite α u G h hz).1
  -- ## the moment relation for `∂_z u` (the box integrability of `∂_z²u` is a field of `AeData`)
  have hmr1 : ∀ a b : ℝ, 0 < a → a < b →
      Work.Elliptic.Fstar (Work.Spaces.pz u) b - Work.Elliptic.Fstar (Work.Spaces.pz u) a
        = ∫ r in a..b, Work.Elliptic.Fstar (Work.Spaces.pzIter 2 u) r := by
    intro a b ha hab
    have h' := Work.FTS.EllipticEst.Blocks.moment_relation (Work.Spaces.pz u) hS.pz
      (Work.FTS.EllipticEst.Endpt.boxIntegrable_pzIter2Psi (Ψ := u) hsm hmemZ) hp1sl ha hab
    have hIcc : (∫ s in Set.Icc a b, ∫ θ in Iθ,
          Work.Spaces.pz (Work.Spaces.pz u) s θ * sg θ)
        = ∫ s in Set.Icc a b, Work.Elliptic.Fstar (Work.Spaces.pzIter 2 u) s := rfl
    have hconv : (∫ s in Set.Icc a b, Work.Elliptic.Fstar (Work.Spaces.pzIter 2 u) s)
        = ∫ r in a..b, Work.Elliptic.Fstar (Work.Spaces.pzIter 2 u) r := by
      rw [intervalIntegral.integral_of_le hab.le]
      exact (setIntegral_congr_set (MeasureTheory.Ioc_ae_eq_Icc (μ := volume))).symm
    rw [hIcc, hconv] at h'
    linarith
  -- ## integrability of the second moment along the radius
  have hT2 : ∀ a b : ℝ, 0 < a → a < b →
      MeasureTheory.IntegrableOn (Work.Elliptic.Fstar (Work.Spaces.pzIter 2 u)) (Set.Icc a b) :=
    fun a b ha hab =>
      Work.FTS.EllipticEst.Endpt.integrableOn_fstar_pzIter2 (Ψ := u) hsm hmemZ a b ha hab
  -- ## continuity of `z ↦ F_*(∂_z u)(z)`: a constant plus the primitive of `F_*(∂_z²u)`
  have hcont1 : ContinuousOn (fun z => Work.Elliptic.Fstar (Work.Spaces.pz u) z)
      (Set.Ioi 0) := by
    intro z hz
    have hz0 : 0 < z := hz
    set a : ℝ := z / 2 with ha
    have ha0 : 0 < a := by rw [ha]; linarith
    have haz : a < z := by rw [ha]; linarith
    have haz2 : z < z + 1 := by linarith
    have hIntM2 : MeasureTheory.IntegrableOn
        (fun r => Work.Elliptic.Fstar (Work.Spaces.pzIter 2 u) r) (Set.uIcc a (z + 1)) := by
      rw [Set.uIcc_of_le (by linarith : a ≤ z + 1)]
      exact hT2 a (z + 1) ha0 (by linarith)
    have hcontprim : ContinuousOn
        (fun x => ∫ r in a..x, Work.Elliptic.Fstar (Work.Spaces.pzIter 2 u) r)
        (Set.uIcc a (z + 1)) :=
      intervalIntegral.continuousOn_primitive_interval hIntM2
    have hmem : Set.uIcc a (z + 1) ∈ 𝓝 z := by
      rw [Set.uIcc_of_le (by linarith : a ≤ z + 1)]
      exact Icc_mem_nhds haz haz2
    have hcontR : ContinuousWithinAt (fun x => Work.Elliptic.Fstar (Work.Spaces.pz u) a
        + ∫ r in a..x, Work.Elliptic.Fstar (Work.Spaces.pzIter 2 u) r)
        (Set.Ioi 0) z :=
      continuousWithinAt_const.add (hcontprim.continuousAt hmem).continuousWithinAt
    have hrepr : ∀ x ∈ Set.Ioi 0, Work.Elliptic.Fstar (Work.Spaces.pz u) x
        = Work.Elliptic.Fstar (Work.Spaces.pz u) a
          + ∫ r in a..x, Work.Elliptic.Fstar (Work.Spaces.pzIter 2 u) r := by
      intro x hx
      rcases lt_trichotomy a x with hlt | heq | hgt
      · linarith [hmr1 a x ha0 hlt]
      · subst heq; simp
      · have hh := hmr1 x a hx hgt
        rw [intervalIntegral.integral_symm] at hh
        linarith
    exact hcontR.congr_of_eventuallyEq
      (Filter.eventually_of_mem self_mem_nhdsWithin fun x hx => hrepr x hx) (hrepr z hz)
  -- ## the backward difference quotient of `F_*(u)` converges to `F_*(∂_z u)`
  obtain ⟨hboxA, hsecA⟩ := Work.FTS.EllipticEst.AngAWeak.absPzIter2SliceFacts (α := α) hsm hmemZ
  have hTdif : ∀ z : ℝ, 0 < z → Filter.Tendsto
      (fun hh : ℝ => (Work.Elliptic.Fstar u z - Work.Elliptic.Fstar u (z - hh)) / hh)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds (Work.Elliptic.Fstar (Work.Spaces.pz u) z)) := by
    intro z hz
    have hev : ∀ᶠ hh : ℝ in nhdsWithin (0 : ℝ) (Set.Ioi 0), hh ∈ Set.Ioo (0 : ℝ) (z / 2) := by
      have h1 : Set.Iio (z / 2) ∈ nhdsWithin (0 : ℝ) (Set.Ioi 0) :=
        nhdsWithin_le_nhds (isOpen_Iio.mem_nhds (show (0 : ℝ) < z / 2 by linarith))
      filter_upwards [h1, self_mem_nhdsWithin] with hh hlt hgt
      exact ⟨hgt, hlt⟩
    have hlim := Work.FTS.EllipticEst.AngAWeak.tendstoThetaIntervalAbsPzIter2 hboxA hsecA hz
    have hw : Filter.Tendsto (fun hh : ℝ =>
        (Work.Elliptic.Fstar u z - Work.Elliptic.Fstar u (z - hh)) / hh
          - Work.Elliptic.Fstar (Work.Spaces.pz u) z)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
      have hlimneg : Filter.Tendsto (fun hh : ℝ =>
          -∫ θ in Iθ, (∫ x in (z - hh)..z, |Work.Spaces.pzIter 2 u x θ|) * |sg θ|)
          (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
        simpa using hlim.neg
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlimneg hlim ?_ ?_
      · filter_upwards [hev] with hh hhh
        have hb := Work.FTS.EllipticEst.Dispatch.difQuotSubDerivBoundD hsm hψsl hp1sl hz hhh.1 hhh.2
          (hboxA (z - hh) z (by linarith [hhh.1, hhh.2, hz]) (by linarith [hhh.1, hhh.2, hz]))
        exact (abs_le.mp hb).1
      · filter_upwards [hev] with hh hhh
        have hb := Work.FTS.EllipticEst.Dispatch.difQuotSubDerivBoundD hsm hψsl hp1sl hz hhh.1 hhh.2
          (hboxA (z - hh) z (by linarith [hhh.1, hhh.2, hz]) (by linarith [hhh.1, hhh.2, hz]))
        exact (abs_le.mp hb).2
    have := hw.add_const (Work.Elliptic.Fstar (Work.Spaces.pz u) z)
    simpa [sub_add_cancel] using this
  have hae1 : ∀ᵐ z ∂(volume.restrict (Set.Ioi 0)),
      Work.Elliptic.Fstar (Work.Spaces.pz u) z = 0 :=
    Work.FTS.EllipticEst.AngAWeak.aeZeroOfDifQuot (M₀ := fun z => Work.Elliptic.Fstar u z)
      (M₁ := fun z => Work.Elliptic.Fstar (Work.Spaces.pz u) z) (AeData.momU h) hTdif
  -- ## hence the first moment vanishes everywhere (continuity + a.e.-vanishing)
  have hpoint1 : ∀ z : ℝ, 0 < z → Work.Elliptic.Fstar (Work.Spaces.pz u) z = 0 := by
    intro z hz
    refine Work.FTS.EllipticEst.Endpt.eq_zero_of_forall_intervalIntegral_eq_zero_of_continuousOn
      hz ?_ hcont1
    intro s w hs hsw
    have hae : (fun r : ℝ => Work.Elliptic.Fstar (Work.Spaces.pz u) r)
        =ᵐ[volume.restrict (Set.Ioc s w)] (fun _ => (0 : ℝ)) :=
      MeasureTheory.ae_mono
        (MeasureTheory.Measure.restrict_mono (fun x hx => lt_of_lt_of_le hs (le_of_lt hx.1))
          le_rfl) hae1
    rw [intervalIntegral.integral_of_le hsw]
    rw [MeasureTheory.integral_congr_ae hae]
    simp
  -- ## hence the second moment vanishes a.e.
  have hzero2 : ∀ s t : ℝ, 0 < s → 0 < t →
      ∫ r in s..t, Work.Elliptic.Fstar (Work.Spaces.pzIter 2 u) r = 0 := by
    intro s t hs ht
    rcases le_total s t with hle | hle
    · rcases lt_or_eq_of_le hle with hlt | heq
      · have hh := hmr1 s t hs hlt
        rw [hpoint1 t (lt_trans hs hlt), hpoint1 s hs, sub_zero] at hh
        exact hh.symm
      · subst heq; simp
    · rcases lt_or_eq_of_le hle with hlt | heq
      · have hh := hmr1 t s ht hlt
        rw [hpoint1 s (lt_trans ht hlt), hpoint1 t ht, sub_zero] at hh
        rw [intervalIntegral.integral_symm, ← hh, neg_zero]
      · subst heq; simp
  have hInt2 : ∀ a b : ℝ, 0 < a → a < b →
      IntervalIntegrable (Work.Elliptic.Fstar (Work.Spaces.pzIter 2 u)) volume a b := by
    intro a b ha hab
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hab.le]
    exact hT2 a b ha hab
  have hae2 : ∀ᵐ z ∂(volume.restrict (Set.Ioi 0)),
      Work.Elliptic.Fstar (Work.Spaces.pzIter 2 u) z = 0 :=
    Work.FTS.EllipticEst.H2W.PsiSlices.ae_eq_zero_of_forall_intervalIntegral_eq_zero hzero2 hInt2
  exact ⟨hpoint1, hae2⟩

theorem aeLeftLimitD : ∀ (α : ℝ) (u G : ℝ → ℝ → ℝ),
    Work.FTS.EllipticEst.H2W.Ae.AeData α u G →
    ∀ᵐ z ∂(MeasureTheory.volume.restrict (Set.Ioi 0)),
      Filter.Tendsto (fun θ => u z θ) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
  intro α u G h
  obtain ⟨hM1, hM2⟩ := aeMomentChainD h
  have hsm := AeData.smooth h
  have hmemB := AeData.memAng2 h
  filter_upwards [hM2, AeData.momG h, MeasureTheory.self_mem_ae_restrict measurableSet_Ioi]
    with z hM2z hGz hz
  have hslice : ∀ n : ℕ, ContDiffOn ℝ n (fun θ => u z θ) (Set.Ioo 0 (Real.pi / 2)) :=
    fun n => Work.FTS.EllipticEst.Endpt.contDiffOn_slice_of_strip hsm hz n
  have h2slice : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (deriv (fun t => deriv (fun θ' => u z θ') t) θ) ^ 2
        * Work.FTS.EllipticEst.sEta θ) Iθ := by
    have h0 := Work.FTS.EllipticEst.Endpt.integrableOn_pthIter2_sEta_of_HkMem (Ψ := u) hmemB hz
    refine h0.congr (Filter.Eventually.of_forall (fun θ => ?_))
    show Work.Spaces.pthIter 2 u z θ ^ 2 * Work.FTS.EllipticEst.sEta θ
      = (deriv (fun t => deriv (fun θ' => u z θ') t) θ) ^ 2 * Work.FTS.EllipticEst.sEta θ
    rw [show Work.Spaces.pthIter 2 u z θ
      = deriv (fun t => deriv (fun θ' => u z θ') t) θ from rfl]
  obtain ⟨L, hL⟩ := Work.FTS.EllipticEst.sliceLimitLeftExists (fun θ => u z θ) hslice h2slice
  -- the endpoint moment identity and the moment of the equation
  have hLzint : MeasureTheory.IntegrableOn
      (fun θ : ℝ => Work.FTS.EllipticEst.Lzero1 (fun t => u z t) θ * sg θ) Iθ :=
    (Work.FTS.EllipticEst.H2W.AeProof.AeSliceMomentFinite α u G h hz).2.2
  have hmom := Lzero1_moment_eq_neg_limitD (α := α) hsm hmemB hz hLzint hL
  have hdecomp := fstar_G_eqD h hz
  have hL0 : L = 0 := by
    rw [hGz, hM1 z hz, hM2z, hmom] at hdecomp
    linarith
  simpa [hL0] using hL

end Work.FTS.EllipticEst.Dispatch
