import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EllipticEst.TT.WeakDefs
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.Spaces.Defs
import Submission.Work.Elliptic.Defs
import Submission.Work.Spaces.HkSq_terms
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.Cert.SmoothOpen_bslOp
import Submission.Work.FTS.EllipticEst.remov.SmoothOpen_bslOp_of_smoothOpen
import Submission.Work.FTS.EllipticEst.integrable_prod_ae
import Submission.Work.FTS.EllipticEst.aesm_uncurry_restrict_open
import Submission.Work.FTS.EllipticEst.abs_mul_sinCos2_le_weighted

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.remov.SourceBound

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## The engine: box integrability of a `∂_z`-slice of an `ℋ^k` datum

The common part of both conjuncts of `weakSliceDerivBox`: for a `C^∞` function `g` on the open
quadrant which is honestly in `ℋ^k` with `k ≥ 1`, the function
`(z,θ) ↦ ∂_z g z θ · sinθcos²θ` is integrable over the box `(a,b] × Iθ`, for every `a > 0`.

The argument is the box version of `weakSliceDeriv`.  For each `z ∈ (a,b]` (so `z > 0`) the
pointwise absorption `abs_mul_sinCos2_le_weighted` gives

`|∂_z g z θ · sinθcos²θ| ≤ (∂_z g z θ · w z/sin(2θ)^{η/2})² + 1`,

and `∂_z g · w/sin^{η/2} = z^{-1}·(D_z g · w/sin^{η/2})`, so

`|∂_z g z θ · sinθcos²θ| ≤ a^{-2}·HkIntegrand α k g z θ + 1`

by `sq_le_HkIntegrand_z` at the index `i = 1`.  The right-hand side is integrable on the box:
the angular slices of `HkIntegrand` are integrable for every `z ∈ Iz` and the `z`-integral of
the angular integral is integrable on `Iz` (the two conjuncts of `HkMem`), so Tonelli
(`integrable_prod_ae`) makes the uncurried `HkIntegrand` product-integrable.  A.e. strong
measurability comes from the smoothness of `g` on the open quadrant. -/

/-- `θ ↦ sinθcos²θ` is continuous. -/
private lemma continuous_sinCos2_snd :
    Continuous (fun p : ℝ × ℝ => Work.Elliptic.sinCos2 p.2) := by
  simp only [Work.Elliptic.sinCos2]
  exact (Real.continuous_sin.mul (Real.continuous_cos.pow 2)).comp continuous_snd

/-- **The pointwise domination on the box.**

For `0 < a < z` and `θ ∈ Iθ`,
`|∂_z g z θ · sinθcos²θ| ≤ a⁻² · HkIntegrand α k g z θ + 1`.

This is the combination of `abs_mul_sinCos2_le_weighted` (which absorbs the angular profile
into `(∂_z g · w/sin(2θ)^{η/2})² + 1`) with the identity `D_z g = z·∂_z g` and the
single-summand bound `sq_le_HkIntegrand_z` applied at `i = 1`. -/
private lemma pointwise_bound {α : ℝ} {k : ℕ} {g : ℝ → ℝ → ℝ} {a z θ : ℝ} (hk : 1 ≤ k)
    (ha : 0 < a) (hz : a < z) (hθ : θ ∈ Work.Spaces.Iθ) :
    |Work.Spaces.pz g z θ * Work.Elliptic.sinCos2 θ|
      ≤ (a ^ 2)⁻¹ * Work.Spaces.HkIntegrand α k g z θ + 1 := by
  have hzpos : 0 < z := lt_trans ha hz
  have h1 := Work.FTS.EllipticEst.abs_mul_sinCos2_le_weighted
    (f := fun θ => Work.Spaces.pz g z θ) hzpos hθ
  have hDz : Work.Spaces.DzIter 1 g z θ = z * Work.Spaces.pz g z θ := rfl
  have hz2 : z ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hzpos)
  have h2 : (Work.Spaces.pz g z θ
        * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
      = (z ^ 2)⁻¹ * ((Work.Spaces.DzIter 1 g z θ)
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
    rw [hDz, eq_inv_mul_iff_mul_eq₀ hz2]
    ring
  have h3 : Work.Spaces.HkIntegrand α k g z θ ≥
      ((Work.Spaces.DzIter 1 g z θ)
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
    have hh := Work.Spaces.sq_le_HkIntegrand_z α k g z θ 1 hk
    simpa using hh
  have hcinv : (0 : ℝ) ≤ (a ^ 2)⁻¹ := by positivity
  have hzipow : (z ^ 2)⁻¹ ≤ (a ^ 2)⁻¹ :=
    inv_anti₀ (by positivity) (pow_le_pow_left₀ ha.le hz.le 2)
  calc |Work.Spaces.pz g z θ * Work.Elliptic.sinCos2 θ|
      ≤ (Work.Spaces.pz g z θ
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 + 1 := h1
    _ = (z ^ 2)⁻¹ * ((Work.Spaces.DzIter 1 g z θ)
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 + 1 := by
        rw [h2]
    _ ≤ (a ^ 2)⁻¹ * ((Work.Spaces.DzIter 1 g z θ)
          * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 + 1 := by
        have hstep : (z ^ 2)⁻¹ * ((Work.Spaces.DzIter 1 g z θ)
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
            ≤ (a ^ 2)⁻¹ * ((Work.Spaces.DzIter 1 g z θ)
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 :=
          mul_le_mul_of_nonneg_right hzipow (sq_nonneg _)
        linarith
    _ ≤ (a ^ 2)⁻¹ * Work.Spaces.HkIntegrand α k g z θ + 1 := by
        have hstep : (a ^ 2)⁻¹ * ((Work.Spaces.DzIter 1 g z θ)
              * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2
            ≤ (a ^ 2)⁻¹ * Work.Spaces.HkIntegrand α k g z θ :=
          mul_le_mul_of_nonneg_left h3 hcinv
        linarith

/-- **The engine.**  Let `g` be `C^∞` on the open quadrant and honestly in `ℋ^k` with `k ≥ 1`.
Then for every `a > 0` and every `b`, the function `(z,θ) ↦ ∂_z g z θ · sinθcos²θ` is
integrable on the product of `(a,b]` and `Iθ`. -/
private theorem boxIntegrable_of_HkMem {α : ℝ} {k : ℕ} {g : ℝ → ℝ → ℝ}
    (hg : Work.FTS.EllipticEst.SmoothOpen g) (hmem : Work.Spaces.HkMem α k g) (hk : 1 ≤ k)
    {a b : ℝ} (ha : 0 < a) :
    MeasureTheory.Integrable
      (Function.uncurry (fun z θ => Work.Spaces.pz g z θ * Work.Elliptic.sinCos2 θ))
      ((MeasureTheory.volume.restrict (Set.Ioc a b)).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
  haveI hfinθ : IsFiniteMeasure (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
    rw [Work.Spaces.Iθ]; infer_instance
  haveI hfinz : IsFiniteMeasure (MeasureTheory.volume.restrict (Set.Ioc a b)) := inferInstance
  have hsub : Set.Ioc a b ⊆ Work.Spaces.Iz := fun x hx => le_of_lt (lt_trans ha hx.1)
  -- ## Step 1: the uncurried `HkIntegrand` is integrable on the box
  have hKint : MeasureTheory.Integrable
      (Function.uncurry (fun z θ => Work.Spaces.HkIntegrand α k g z θ))
      ((MeasureTheory.volume.restrict (Set.Ioc a b)).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
    refine Work.FTS.EllipticEst.integrable_prod_ae ?_ ?_ ?_ ?_
    · refine Filter.Eventually.of_forall (fun z => Filter.Eventually.of_forall (fun θ => ?_))
      rw [Work.Spaces.HkIntegrand]
      exact add_nonneg (Work.Spaces.hkZSum_nonneg α k g z θ)
        (Work.Spaces.hkMixedSum_nonneg α k g z θ)
    · exact Work.FTS.EllipticEst.aesm_uncurry_restrict_open _
        (hg.continuousOn_HkIntegrand α k) ha.le
    · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioc (fun z hz => ?_)
      exact hmem.1 z (hsub hz)
    · exact hmem.2.mono_set hsub
  -- ## Step 2: conclude by domination
  refine MeasureTheory.Integrable.mono'
    (g := fun p : ℝ × ℝ => (a ^ 2)⁻¹ * Work.Spaces.HkIntegrand α k g p.1 p.2 + 1)
    ?_ ?_ ?_
  · exact (hKint.const_mul ((a ^ 2)⁻¹)).add (MeasureTheory.integrable_const 1)
  · refine Work.FTS.EllipticEst.aesm_uncurry_restrict_open _
      ((hg.pz).continuousOn.mul continuous_sinCos2_snd.continuousOn) ha.le
  · rw [MeasureTheory.Measure.prod_restrict (Set.Ioc a b) Work.Spaces.Iθ]
    refine MeasureTheory.ae_restrict_of_forall_mem
      (measurableSet_Ioc.prod (by rw [Work.Spaces.Iθ]; exact measurableSet_Icc))
      (fun p hp => ?_)
    obtain ⟨hz, hθ⟩ := hp
    simp only [Real.norm_eq_abs]
    exact pointwise_bound hk ha hz.1 hθ

/-! ## The two instantiations -/

/-- `F` is `C^∞` on the open quadrant, because there it agrees with `bslOp α Ψ`. -/
theorem smoothOpen_of_EllWeakPos {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ) :
    Work.FTS.EllipticEst.SmoothOpen F :=
  Work.FTS.EllipticEst.Cert.smoothOpen_congr_bsl
    (Work.FTS.EllipticEst.remov.SmoothOpen_bslOp_of_smoothOpen
      (Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth))
    (fun z θ hz hθ0 hθ1 => h.eq z hz θ hθ0 hθ1)

/-- **Box integrability of the derivative slices.**

For a datum of the weak class `EllWeakPos α k F Ψ` (with `k ≥ 2`), every `a > 0` and every `b`,
the functions `(z,θ) ↦ pz F z θ * sinCos2 θ` and
`(z,θ) ↦ pz (fun z θ => z ^ 2 * pzIter 2 Ψ z θ) z θ * sinCos2 θ` are integrable on the product
of `(a,b]` and `Iθ`.

Proof sketch.  Identical to `weakSliceDeriv`, but using additionally the second conjunct of
`HkMem` (integrability over `z` of the `θ`-integral of the `HkIntegrand`), Tonelli, and the
Cauchy–Schwarz partner whose square is
`sin(2θ)^η * sinCos2 θ^2 * z^4 / (1+z)^4`, integrable over the box because `b` is finite and
`a > 0`. -/
theorem weakSliceDerivBox {α : ℝ} {k : ℕ} {F Ψ : ℝ → ℝ → ℝ} (hk : 2 ≤ k)
    (h : Work.FTS.EllipticEst.TT.EllWeakPos α k F Ψ) :
    ∀ a b : ℝ, 0 < a →
      (MeasureTheory.Integrable
        (Function.uncurry (fun z θ => Work.Spaces.pz F z θ * Work.Elliptic.sinCos2 θ))
        ((MeasureTheory.volume.restrict (Set.Ioc a b)).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ))) ∧
      (MeasureTheory.Integrable
        (Function.uncurry (fun z θ => Work.Spaces.pz
            (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ
          * Work.Elliptic.sinCos2 θ))
        ((MeasureTheory.volume.restrict (Set.Ioc a b)).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ))) := by
  intro a b ha
  have hSΨ : Work.FTS.EllipticEst.SmoothOpen Ψ :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  have hSF : Work.FTS.EllipticEst.SmoothOpen F := smoothOpen_of_EllWeakPos h
  have hSg : Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) :=
    (contDiff_fst.pow 2).contDiffOn.mul (hSΨ.pzIter 2)
  exact ⟨boxIntegrable_of_HkMem hSF h.memF (by omega) ha,
    boxIntegrable_of_HkMem hSg h.memA (by omega) ha⟩

end

end Work.FTS.EllipticEst.remov.SourceBound
