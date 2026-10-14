import Mathlib.Algebra.Module.LinearMap.Defs
import Mathlib.Algebra.Module.Pi
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Basic.Real.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.RingTheory.Finiteness.Prod
import Submission.Work.FTS.PhiStar.Series.Weil.integrableOn_prod_mul
import Submission.Work.FTS.StrongPersist.Clauses
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6BWork.FkAux.fkMomentJetSq
import Submission.Work.FTS.StrongPersist.N6_prod
import Submission.Work.FTS.StrongPersist.StarPkg6OfCore
import Submission.Work.FTS.VocabO2
import Submission.Work.FTS_RegExport.RXR1.mixed_abs_le_weighted
import Submission.Work.FTS_RegExport.RXR5L.Auxiliary.Tlim_aux
import Submission.Work.FTS_RegExport.RXT.Slots.v2_theta_sup_uniform
import Submission.Work.FTS_RegExport.RXT.Sys.L12FKjet.L12
import Submission.Work.FTS_RegExport.RXT.jc3_aux
import Submission.Work.FTS_StreamBdry.SB4.slice_L12_c2
import Submission.Work.R1G.DecayInZ_gA
-- ===== merged: Submission.Work.FTS.EpsEngine.zTraces_T1 =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EpsEngine

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

/-!
# `zTraces_T1` — the pointwise radial traces from `ℋ^{k+2}`-honesty

For `0 < α ≤ 1`, a datum `f` which is `C^∞` on the open quadrant and honestly in `ℋ^{k+2}`,
and a slot of order `a + b ≤ k`, the radial trace

  `z ↦ z · (D_z^b D_θ^a f (z,θ) · w z)^2`   (`w z = (1+z)²/z²`)

vanishes as `z → 0⁺` and as `z → ∞`, for every `θ ∈ (0,π/2)`.

## Route

Write `A(z) = D_z^bD_θ^a f (z,θ)·w z` and `φ(z) = z·A(z)²`.

1. **Pointwise slot bound** (`sup_theta_gen`, in the companion module
   `FTS/EpsEngine/ZTracesAux/sup_theta_gen.lean`): there is `K = K(α) ≥ 0` with
   `A(z)² ≤ K·G(z)` (and `(D_z^{b+1}D_θ^af·w)² ≤ K·G(z)`), where
   `G(z) = ∫_θ HkIntegrand α (k+2) f z θ dθ` is the angular marginal (integrable in `z` by
   `HkMem α (k+2) f`).
2. **Derivative bound**: `φ' = A² + 2A·w·(D_z^{b+1}D_θ^af − 2D_z^bD_θ^af/(1+z))`
   (`hasDerivAt_zTraces_phi`), whence `|φ'| ≤ 7K·G` pointwise.
3. **Local averaging**: `φ(z) ≤ (3K/2 + 7K)·∫_{z/2}^{3z/2} G` — the value `φ(z)` is the
   average of `φ(z)` on the window `(z/2,3z/2)`, the average of `φ` is `≤ (3K/2)∫G` by (1),
   and the oscillation `|φ(x) − φ(z)| ≤ 7K∫_{(min x z, max x z)}G ≤ 7K∫_{z/2}^{3z/2}G` by the
   fundamental theorem of calculus and (2).
4. **Squeeze**: the local integral `∫_{z/2}^{3z/2}G` tends to `0` both as `z → 0⁺`
   (absolute continuity of the Lebesgue integral) and as `z → ∞` (vanishing of tails)
   (`local_integral_tendsto_zero`), and `0 ≤ φ`.
-/

/-! ## The slot, the marginal and the trace functional -/

/-- The angular marginal of the `ℋ^m`-integrand at the radial variable `z`. -/
private def zTraceG (α : ℝ) (m : ℕ) (f : ℝ → ℝ → ℝ) : ℝ → ℝ :=
  fun z => ∫ σ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α m f z σ

/-- The `w`-weighted slot `D_z^b D_θ^a f(·,θ)·w`. -/
private def zTraceA (f : ℝ → ℝ → ℝ) (b a : ℕ) (θ : ℝ) : ℝ → ℝ :=
  fun z => Work.Spaces.mixed b a f z θ * Work.Spaces.w z

/-- The trace functional `z ↦ z·(D_z^bD_θ^af·w)²`. -/
private def zTracePhi (f : ℝ → ℝ → ℝ) (b a : ℕ) (θ : ℝ) : ℝ → ℝ :=
  fun z => z * (zTraceA f b a θ z) ^ 2

/-- The derivative of the trace functional. -/
private def zTracePhiDeriv (f : ℝ → ℝ → ℝ) (b a : ℕ) (θ : ℝ) : ℝ → ℝ :=
  fun z => (zTraceA f b a θ z) ^ 2
    + 2 * (zTraceA f b a θ z) * (Work.Spaces.w z *
        (Work.Spaces.mixed (b + 1) a f z θ - 2 * Work.Spaces.mixed b a f z θ / (1 + z)))

/-! ## Elementaries -/

private theorem zTraceG_nonneg (α : ℝ) (m : ℕ) (f : ℝ → ℝ → ℝ) (z : ℝ) :
    0 ≤ zTraceG α m f z :=
  integral_nonneg fun σ => Work.Spaces.HkIntegrand_nonneg α m f z σ

private theorem continuousOn_w : ContinuousOn Work.Spaces.w (Set.Ioi 0) := by
  have hfun : Work.Spaces.w = fun z : ℝ => (1 + z) ^ 2 / z ^ 2 := rfl
  rw [hfun]
  exact ((continuousOn_const.add continuousOn_id).pow 2).div (continuousOn_id.pow 2)
    (fun z hz => pow_ne_zero 2 (ne_of_gt hz))

private theorem continuousOn_mixed_slice {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (b a : ℕ) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    ContinuousOn (fun z => Work.Spaces.mixed b a f z θ) (Set.Ioi 0) :=
  ((hf.mixed b a).curry_z hθ).continuousOn

private theorem continuousOn_zTraceA {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (b a : ℕ) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    ContinuousOn (zTraceA f b a θ) (Set.Ioi 0) :=
  (continuousOn_mixed_slice hf b a hθ).mul continuousOn_w

private theorem continuousOn_zTracePhi {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (b a : ℕ) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    ContinuousOn (zTracePhi f b a θ) (Set.Ioi 0) :=
  continuousOn_id.mul ((continuousOn_zTraceA hf b a hθ).pow 2)

private theorem continuousOn_inv_one_add : ContinuousOn (fun z : ℝ => (1 + z)⁻¹) (Set.Ioi 0) := by
  have h : ContinuousOn (fun z : ℝ => (1 : ℝ) + z) (Set.Ioi 0) :=
    continuousOn_const.add continuousOn_id
  exact h.inv₀ (fun z hz => ne_of_gt (by have := Set.mem_Ioi.mp hz; linarith : (0 : ℝ) < 1 + z))

private theorem continuousOn_zTracePhiDeriv {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (b a : ℕ) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    ContinuousOn (zTracePhiDeriv f b a θ) (Set.Ioi 0) := by
  have hA := continuousOn_zTraceA hf b a hθ
  have hB : ContinuousOn (fun z => Work.Spaces.mixed (b + 1) a f z θ
      - 2 * Work.Spaces.mixed b a f z θ / (1 + z)) (Set.Ioi 0) :=
    (continuousOn_mixed_slice hf (b + 1) a hθ).sub
      ((continuousOn_mixed_slice hf b a hθ).const_mul 2 |>.mul continuousOn_inv_one_add)
  exact hA.pow 2 |>.add ((hA.const_mul 2).mul (continuousOn_w.mul hB))

/-! ## The pointwise derivative bound -/

private theorem zTracePhiDeriv_eq {f : ℝ → ℝ → ℝ} {b a : ℕ} {θ z : ℝ} :
    zTracePhiDeriv f b a θ z
      = (zTraceA f b a θ z) ^ 2
        + 2 * (zTraceA f b a θ z) * (Work.Spaces.mixed (b + 1) a f z θ * Work.Spaces.w z
              - 2 * (zTraceA f b a θ z) / (1 + z)) := by
  simp only [zTracePhiDeriv, zTraceA]
  ring_nf

private theorem abs_zTracePhiDeriv_le {α K : ℝ} (hK : 0 ≤ K) {f : ℝ → ℝ → ℝ} {m b a : ℕ}
    {θ z : ℝ} (hz : 0 < z)
    (hA : (zTraceA f b a θ z) ^ 2 ≤ K * zTraceG α m f z)
    (hB : (Work.Spaces.mixed (b + 1) a f z θ * Work.Spaces.w z) ^ 2 ≤ K * zTraceG α m f z) :
    |zTracePhiDeriv f b a θ z| ≤ 7 * K * zTraceG α m f z := by
  have hg0 : 0 ≤ zTraceG α m f z := zTraceG_nonneg α m f z
  have hKg : 0 ≤ K * zTraceG α m f z := mul_nonneg hK hg0
  have hc1 : 1 / (1 + z) ≤ 1 := by
    rw [div_le_one (by linarith : (0 : ℝ) < 1 + z)]
    linarith
  set A : ℝ := zTraceA f b a θ z with hAdef
  set B : ℝ := Work.Spaces.mixed (b + 1) a f z θ * Work.Spaces.w z with hBdef
  have hA2 : A ^ 2 ≤ K * zTraceG α m f z := hA
  have hB2 : B ^ 2 ≤ K * zTraceG α m f z := hB
  have hid : zTracePhiDeriv f b a θ z = A ^ 2 + 2 * A * (B - 2 * A / (1 + z)) := by
    rw [zTracePhiDeriv_eq]
  have hid2 : A ^ 2 + 2 * A * (B - 2 * A / (1 + z))
      = A ^ 2 + 2 * A * B - 4 * (A ^ 2 * (1 / (1 + z))) := by
    ring_nf
  have hUpper : A ^ 2 + 2 * A * B - 4 * (A ^ 2 * (1 / (1 + z)))
      ≤ 3 * (K * zTraceG α m f z) := by
    have h1 : 2 * A * B ≤ A ^ 2 + B ^ 2 := by nlinarith [sq_nonneg (A - B)]
    have h2 : 0 ≤ A ^ 2 * (1 / (1 + z)) := by
      have hc : (0 : ℝ) ≤ 1 / (1 + z) := by positivity
      positivity
    nlinarith [hA2, hB2, h1, h2]
  have hLower : -(7 * (K * zTraceG α m f z))
      ≤ A ^ 2 + 2 * A * B - 4 * (A ^ 2 * (1 / (1 + z))) := by
    have h1 : -(A ^ 2 + B ^ 2) ≤ 2 * A * B := by nlinarith [sq_nonneg (A + B)]
    have h3 : A ^ 2 * (1 / (1 + z)) ≤ A ^ 2 * 1 := mul_le_mul_of_nonneg_left hc1 (sq_nonneg A)
    nlinarith [hA2, hB2, h1, h3]
  rw [hid, hid2]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-! ## The fundamental-theorem-of-calculus bound -/

private theorem abs_sub_le_integral {α K : ℝ} {f : ℝ → ℝ → ℝ} {m b a : ℕ} {θ : ℝ}
    (hGint : IntegrableOn (zTraceG α m f) (Set.Ioi 0))
    (hcontφ' : ContinuousOn (zTracePhiDeriv f b a θ) (Set.Ioi 0))
    (hderiv : ∀ z, 0 < z → HasDerivAt (zTracePhi f b a θ) (zTracePhiDeriv f b a θ z) z)
    (hbnd : ∀ z, 0 < z → |zTracePhiDeriv f b a θ z| ≤ 7 * K * zTraceG α m f z)
    {u v : ℝ} (hu : 0 < u) (huv : u ≤ v) :
    |zTracePhi f b a θ v - zTracePhi f b a θ u| ≤ 7 * K * (∫ x in u..v, zTraceG α m f x) := by
  have hsub : Set.uIcc u v ⊆ Set.Ioi 0 := by
    rw [Set.uIcc_of_le huv]
    intro x hx
    exact lt_of_lt_of_le hu hx.1
  have hGii : IntervalIntegrable (zTraceG α m f) volume u v :=
    (hGint.mono_set hsub).intervalIntegrable
  have hbig : IntervalIntegrable (fun x => 7 * K * zTraceG α m f x) volume u v :=
    hGii.const_mul (7 * K)
  have hsub' : Set.uIoc u v ⊆ Set.Ioi 0 := by
    rw [Set.uIoc_of_le huv]
    exact fun x hx => lt_trans hu hx.1
  have haesm : AEStronglyMeasurable (zTracePhiDeriv f b a θ) (volume.restrict (Set.uIoc u v)) :=
    (hcontφ'.mono hsub').aestronglyMeasurable measurableSet_uIoc
  have hφ'ii : IntervalIntegrable (zTracePhiDeriv f b a θ) volume u v :=
    IntervalIntegrable.mono_fun' hbig haesm (by
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_uIoc] with x hx
      have hx0 : 0 < x := hsub' hx
      rw [Real.norm_eq_abs]
      exact hbnd x hx0)
  have hftc : (∫ x in u..v, zTracePhiDeriv f b a θ x)
      = zTracePhi f b a θ v - zTracePhi f b a θ u :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x hx => hderiv x (hsub hx)) hφ'ii
  have hmono : (∫ x in u..v, |zTracePhiDeriv f b a θ x|)
      ≤ ∫ x in u..v, 7 * K * zTraceG α m f x :=
    intervalIntegral.integral_mono_on huv hφ'ii.abs hbig (fun x hx =>
      hbnd x (lt_of_lt_of_le hu hx.1))
  have hnorm : |∫ x in u..v, zTracePhiDeriv f b a θ x|
      ≤ ∫ x in u..v, |zTracePhiDeriv f b a θ x| := by
    simpa only [Real.norm_eq_abs] using
      intervalIntegral.norm_integral_le_integral_norm (μ := volume) huv
        (f := zTracePhiDeriv f b a θ)
  calc |zTracePhi f b a θ v - zTracePhi f b a θ u|
      = |∫ x in u..v, zTracePhiDeriv f b a θ x| := by rw [hftc]
    _ ≤ ∫ x in u..v, |zTracePhiDeriv f b a θ x| := hnorm
    _ ≤ ∫ x in u..v, 7 * K * zTraceG α m f x := hmono
    _ = 7 * K * (∫ x in u..v, zTraceG α m f x) := by rw [intervalIntegral.integral_const_mul]

/-! ## The local averaging bound -/

private theorem zTrace_local {α K : ℝ} (hK : 0 ≤ K) {f : ℝ → ℝ → ℝ} {m b a : ℕ} {θ : ℝ}
    (hGint : IntegrableOn (zTraceG α m f) (Set.Ioi 0))
    (hcontφ : ContinuousOn (zTracePhi f b a θ) (Set.Ioi 0))
    (hcontφ' : ContinuousOn (zTracePhiDeriv f b a θ) (Set.Ioi 0))
    (hslot : ∀ z, 0 < z → (zTraceA f b a θ z) ^ 2 ≤ K * zTraceG α m f z)
    (hderiv : ∀ z, 0 < z → HasDerivAt (zTracePhi f b a θ) (zTracePhiDeriv f b a θ z) z)
    (hbnd : ∀ z, 0 < z → |zTracePhiDeriv f b a θ z| ≤ 7 * K * zTraceG α m f z) :
    ∀ z, 0 < z → zTracePhi f b a θ z
      ≤ (3 * K / 2 + 7 * K) * (∫ x in (z / 2)..(3 * z / 2), zTraceG α m f x) := by
  intro z hz
  have hle : z / 2 ≤ 3 * z / 2 := by linarith
  have hz2 : 0 < z / 2 := by linarith
  have hsub : Set.uIcc (z / 2) (3 * z / 2) ⊆ Set.Ioi 0 := by
    rw [Set.uIcc_of_le hle]
    intro x hx
    exact lt_of_lt_of_le hz2 hx.1
  have hGii : IntervalIntegrable (zTraceG α m f) volume (z / 2) (3 * z / 2) :=
    (hGint.mono_set hsub).intervalIntegrable
  have hφii : IntervalIntegrable (zTracePhi f b a θ) volume (z / 2) (3 * z / 2) :=
    (hcontφ.mono hsub).intervalIntegrable
  have hconst : (∫ x in (z / 2)..(3 * z / 2), zTracePhi f b a θ z)
      = z * zTracePhi f b a θ z := by
    rw [intervalIntegral.integral_const, smul_eq_mul]
    ring
  have hB1 : (∫ x in (z / 2)..(3 * z / 2), zTracePhi f b a θ x)
      ≤ ((3 * z / 2) * K) * (∫ x in (z / 2)..(3 * z / 2), zTraceG α m f x) := by
    have hstep : (∫ x in (z / 2)..(3 * z / 2), zTracePhi f b a θ x)
        ≤ ∫ x in (z / 2)..(3 * z / 2), ((3 * z / 2) * K) * zTraceG α m f x :=
      intervalIntegral.integral_mono_on hle hφii (hGii.const_mul ((3 * z / 2) * K))
        (fun x hx => by
          have hx0 : 0 < x := lt_of_lt_of_le hz2 hx.1
          have hs := hslot x hx0
          have hgx : 0 ≤ zTraceG α m f x := zTraceG_nonneg α m f x
          have hxKG : x * (K * zTraceG α m f x) ≤ (3 * z / 2) * (K * zTraceG α m f x) :=
            mul_le_mul_of_nonneg_right hx.2 (mul_nonneg hK hgx)
          have h1 : x * (zTraceA f b a θ x) ^ 2 ≤ x * (K * zTraceG α m f x) :=
            mul_le_mul_of_nonneg_left hs hx0.le
          have h2 : ((3 * z / 2) * K) * zTraceG α m f x
              = (3 * z / 2) * (K * zTraceG α m f x) := by ring
          have hfx : zTracePhi f b a θ x = x * (zTraceA f b a θ x) ^ 2 := rfl
          rw [hfx, h2]
          linarith)
    rwa [intervalIntegral.integral_const_mul] at hstep
  have hC1 : (∫ x in (z / 2)..(3 * z / 2), |zTracePhi f b a θ x - zTracePhi f b a θ z|)
      ≤ z * (7 * K * (∫ x in (z / 2)..(3 * z / 2), zTraceG α m f x)) := by
    have hpt : ∀ x ∈ Set.Icc (z / 2) (3 * z / 2),
        |zTracePhi f b a θ x - zTracePhi f b a θ z|
          ≤ 7 * K * (∫ y in (z / 2)..(3 * z / 2), zTraceG α m f y) := by
      intro x hx
      have hx0 : 0 < x := lt_of_lt_of_le hz2 hx.1
      have hfac : (0 : ℝ) ≤ 7 * K := by linarith
      rcases le_total x z with hxz | hzx
      · have h1 := abs_sub_le_integral hGint hcontφ' hderiv hbnd hx0 hxz
        rw [abs_sub_comm] at h1
        refine le_trans h1 (mul_le_mul_of_nonneg_left ?_ hfac)
        exact intervalIntegral.integral_mono_interval hx.1 hxz (by linarith) (by
          filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with y hy
          exact zTraceG_nonneg α m f y) hGii
      · have h1 := abs_sub_le_integral hGint hcontφ' hderiv hbnd hz hzx
        refine le_trans h1 (mul_le_mul_of_nonneg_left ?_ hfac)
        exact intervalIntegral.integral_mono_interval (by linarith) hzx hx.2 (by
          filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with y hy
          exact zTraceG_nonneg α m f y) hGii
    have hstep : (∫ x in (z / 2)..(3 * z / 2), |zTracePhi f b a θ x - zTracePhi f b a θ z|)
        ≤ ∫ x in (z / 2)..(3 * z / 2),
            (7 * K * (∫ y in (z / 2)..(3 * z / 2), zTraceG α m f y)) :=
      intervalIntegral.integral_mono_on hle (hφii.sub intervalIntegrable_const).abs
        intervalIntegrable_const hpt
    rw [intervalIntegral.integral_const, smul_eq_mul] at hstep
    rwa [show (3 * z / 2 - z / 2) = z by ring] at hstep
  have hmain : z * zTracePhi f b a θ z
      ≤ ((3 * z / 2) * K + 7 * K * z) * (∫ x in (z / 2)..(3 * z / 2), zTraceG α m f x) := by
    rw [← hconst]
    have h1 : (∫ x in (z / 2)..(3 * z / 2), zTracePhi f b a θ z)
        ≤ (∫ x in (z / 2)..(3 * z / 2), zTracePhi f b a θ x)
          + (∫ x in (z / 2)..(3 * z / 2), |zTracePhi f b a θ x - zTracePhi f b a θ z|) := by
      rw [← intervalIntegral.integral_add hφii (hφii.sub intervalIntegrable_const).abs]
      refine intervalIntegral.integral_mono_on hle intervalIntegrable_const
        (hφii.add (hφii.sub intervalIntegrable_const).abs) (fun x hx => ?_)
      have h := neg_le_abs (zTracePhi f b a θ x - zTracePhi f b a θ z)
      linarith
    calc (∫ x in (z / 2)..(3 * z / 2), zTracePhi f b a θ z)
        ≤ _ + _ := h1
      _ ≤ ((3 * z / 2) * K) * (∫ x in (z / 2)..(3 * z / 2), zTraceG α m f x)
            + z * (7 * K * (∫ x in (z / 2)..(3 * z / 2), zTraceG α m f x)) :=
          add_le_add hB1 hC1
      _ = ((3 * z / 2) * K + 7 * K * z) * (∫ x in (z / 2)..(3 * z / 2), zTraceG α m f x) := by
          ring
  have hdiv : zTracePhi f b a θ z
      ≤ (((3 * z / 2) * K + 7 * K * z)
          * (∫ x in (z / 2)..(3 * z / 2), zTraceG α m f x)) / z := by
    rw [le_div_iff₀ hz]
    linarith [hmain]
  calc zTracePhi f b a θ z
      ≤ (((3 * z / 2) * K + 7 * K * z)
          * (∫ x in (z / 2)..(3 * z / 2), zTraceG α m f x)) / z := hdiv
    _ = (3 * K / 2 + 7 * K) * (∫ x in (z / 2)..(3 * z / 2), zTraceG α m f x) := by
        rw [div_eq_iff (ne_of_gt hz)]
        ring

private theorem zTrace_piece_loc {G : ℝ → ℝ} (hG : MeasureTheory.IntegrableOn G (Set.Ioi 0)) :
    Filter.Tendsto (fun z : ℝ => ∫ x in Set.Ioo (z / 2) (3 * z / 2), G x)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) ∧
      Filter.Tendsto (fun z : ℝ => ∫ x in Set.Ioo (z / 2) (3 * z / 2), G x)
        Filter.atTop (nhds 0) := by
  exact ZTracesAux.local_integral_tendsto_zero hG

/-! ## The theorem -/

theorem zTraces_T1 {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) (k : ℕ) (f : Work.FTS.Galerkin.Fn)
    (hf : Work.FTS.EllipticEst.SmoothOpen f) (hk : Work.Spaces.HkMem α (k + 2) f) :
    ∀ a b : ℕ, a + b ≤ k → ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
      Filter.Tendsto (fun z => z * (Work.Spaces.mixed b a f z θ * Work.Spaces.w z) ^ 2)
        (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) ∧
      Filter.Tendsto (fun z => z * (Work.Spaces.mixed b a f z θ * Work.Spaces.w z) ^ 2)
        Filter.atTop (nhds 0) := by
  intro a b hab θ hθ
  obtain ⟨K, hK0, hKall⟩ := ZTracesAux.sup_theta_gen (α := α) hα hα1
  have hGint : IntegrableOn (zTraceG α (k + 2) f) (Set.Ioi 0) := by
    have h := hk.2
    refine h.mono_set ?_
    exact Set.Ioi_subset_Ici_self (a := (0 : ℝ))
  obtain ⟨hloc0, hlocT⟩ := zTrace_piece_loc (G := zTraceG α (k + 2) f) hGint
  have hslot : ∀ z, 0 < z → (zTraceA f b a θ z) ^ 2 ≤ K * zTraceG α (k + 2) f z := by
    intro z hz
    have h := hKall (k + 2) (by omega) f hf hk b a (by omega) z hz θ hθ.1 hθ.2
    simpa only [zTraceA, zTraceG] using h
  have hslot1 : ∀ z, 0 < z →
      (Work.Spaces.mixed (b + 1) a f z θ * Work.Spaces.w z) ^ 2
        ≤ K * zTraceG α (k + 2) f z := by
    intro z hz
    have h := hKall (k + 2) (by omega) f hf hk (b + 1) a (by omega) z hz θ hθ.1 hθ.2
    simpa only [zTraceG] using h
  have hderiv : ∀ z, 0 < z →
      HasDerivAt (zTracePhi f b a θ) (zTracePhiDeriv f b a θ z) z := by
    intro z hz
    have h := ZTracesAux.hasDerivAt_zTraces_phi (f := f) hf b a hθ z hz
    exact h
  have hbnd : ∀ z, 0 < z → |zTracePhiDeriv f b a θ z| ≤ 7 * K * zTraceG α (k + 2) f z :=
    fun z hz => abs_zTracePhiDeriv_le hK0 hz (hslot z hz) (hslot1 z hz)
  have hlocal : ∀ z, 0 < z → zTracePhi f b a θ z
      ≤ (3 * K / 2 + 7 * K) * (∫ x in (z / 2)..(3 * z / 2), zTraceG α (k + 2) f x) :=
    zTrace_local hK0 hGint (continuousOn_zTracePhi hf b a hθ)
      (continuousOn_zTracePhiDeriv hf b a hθ) hslot hderiv hbnd
  -- the two squeezing arguments
  have hzero : ∀ᶠ z : ℝ in nhdsWithin 0 (Set.Ioi 0), (0 : ℝ) ≤ zTracePhi f b a θ z := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    have hz0 : 0 < z := hz
    show (0 : ℝ) ≤ zTracePhi f b a θ z
    simp only [zTracePhi]
    positivity
  have hle0 : ∀ᶠ z : ℝ in nhdsWithin 0 (Set.Ioi 0),
      zTracePhi f b a θ z
        ≤ (3 * K / 2 + 7 * K) * (∫ x in Set.Ioo (z / 2) (3 * z / 2), zTraceG α (k + 2) f x) := by
    filter_upwards [self_mem_nhdsWithin] with z hz
    have hz0 : 0 < z := hz
    have h := hlocal z hz0
    have hconv : (∫ x in (z / 2)..(3 * z / 2), zTraceG α (k + 2) f x)
        = ∫ x in Set.Ioo (z / 2) (3 * z / 2), zTraceG α (k + 2) f x := by
      rw [intervalIntegral.integral_of_le (by linarith),
        MeasureTheory.integral_Ioc_eq_integral_Ioo]
    rwa [hconv] at h
  have hzeroT : ∀ᶠ z : ℝ in Filter.atTop, (0 : ℝ) ≤ zTracePhi f b a θ z := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with z hz
    show (0 : ℝ) ≤ zTracePhi f b a θ z
    simp only [zTracePhi]
    positivity
  have hleT : ∀ᶠ z : ℝ in Filter.atTop,
      zTracePhi f b a θ z
        ≤ (3 * K / 2 + 7 * K) * (∫ x in Set.Ioo (z / 2) (3 * z / 2), zTraceG α (k + 2) f x) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with z hz
    have h := hlocal z hz
    have hconv : (∫ x in (z / 2)..(3 * z / 2), zTraceG α (k + 2) f x)
        = ∫ x in Set.Ioo (z / 2) (3 * z / 2), zTraceG α (k + 2) f x := by
      rw [intervalIntegral.integral_of_le (by linarith),
        MeasureTheory.integral_Ioc_eq_integral_Ioo]
    rwa [hconv] at h
  have hc0 : Filter.Tendsto (fun z : ℝ => (3 * K / 2 + 7 * K) *
      (∫ x in Set.Ioo (z / 2) (3 * z / 2), zTraceG α (k + 2) f x))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
    simpa using hloc0.const_mul (3 * K / 2 + 7 * K)
  have hcT : Filter.Tendsto (fun z : ℝ => (3 * K / 2 + 7 * K) *
      (∫ x in Set.Ioo (z / 2) (3 * z / 2), zTraceG α (k + 2) f x))
      Filter.atTop (nhds 0) := by
    simpa using hlocT.const_mul (3 * K / 2 + 7 * K)
  have h1 : Filter.Tendsto (zTracePhi f b a θ) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hc0 hzero hle0
  have h2 : Filter.Tendsto (zTracePhi f b a θ) Filter.atTop (nhds 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hcT hzeroT hleT
  exact ⟨h1, h2⟩

end

end Work.FTS.EpsEngine
end
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.Apriori4Defs =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `StrongEps/E4R3/Apriori4Defs.lean` — vocabulary of the corrected a-priori chapter (v4)

curric-46 install (2026-10-12) of `cbc/fts_apriori6_ruling.md` §3 + `cbc/fts_apriori6_ruling_REVIEW.md`
(fixes F1–F3).  Replaces `AprioriChapter3` (unprovable as stated: the `ℋ⁶`-half has no ε-uniform
producer, see the ruling §Verdict) by `AprioriChapter4` = `AprioriChapter3` + `StarPkg6`, with the
`ℋ⁶`-half run on the **raw** slice energy `rawE6` and a **symmetric** kernel.

PROVED here: `kernel_exists_symm` (L0, review F2), `starPkg6_of_starCore` (L1, review F2, from
`StrongPersist.StarPkg6OfCore`), `AprioriPFourth.toB`.  Leaves: `E4R3/Apriori4Leaves/*`,
`E4R3/Sixth4.lean`, `E4R3/Fourth4.lean`; assembly: `E4R3/Apriori4.lean`.
-/

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsE4Thr.E4R4

open Work.FTS.Galerkin (Fn Fam slice)
open Work.FTS.StrongGlobal (Xn6)
open Work.FTS.StrongEps
open Work.FTS.StrongEps.EpsE4Thr

set_option autoImplicit false
set_option linter.unusedVariables false

/-- shorthand: the all-ones level-six inner product of the energy route. -/
abbrev IP6o (α : ℝ) : Fn → Fn → ℝ := Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1 α

/-- The level-six energy of the **raw** slice (not of the mollified one). -/
def rawE6 (α : ℝ) (g : Fam) (τ : ℝ) : ℝ := IP6o α (slice g τ) (slice g τ)

/-- (L0, PROVED — review F2) a SYMMETRIC smooth kernel exists: the wire's `kerBump.normed` is a
`ContDiffBump` centred at `0`, hence even (`ContDiffBump.normed_neg`). -/
theorem kernel_exists_symm :
    ∃ ρ : ℝ × ℝ → ℝ, IsSmoothKernel ρ ∧ ∀ p : ℝ × ℝ, ρ (-p) = ρ p := by
  refine ⟨Work.FTS_FinalLeaves.kerBump.normed MeasureTheory.volume,
    ⟨fun n => Work.FTS_FinalLeaves.kerBump.contDiff_normed (μ := MeasureTheory.volume),
      Work.FTS_FinalLeaves.kerBump.continuous_normed,
      fun p hp => Work.FTS_FinalLeaves.kerBump_support_pointwise p hp,
      fun p => Work.FTS_FinalLeaves.kerBump.nonneg_normed p,
      by simpa using Work.FTS_FinalLeaves.kerBump.integral_normed (μ := MeasureTheory.volume)⟩,
    fun p => Work.FTS_FinalLeaves.kerBump.normed_neg p⟩


/-! ## The two halves, ball- and bound-carrying -/




/-! ## The corrected chapter and its halves -/




/-- `EpsE4R` with two added hypotheses: kernel symmetry (carried by the theorem) and the
order-six star package.  This is the statement body of the restated `StrongEps.EpsE4R`. -/
def EpsE4R4Stmt (Ce Cs : ℝ) (ρ : ℝ × ℝ → ℝ) : Prop :=
    ∃ Cstar : ℝ, 1 ≤ Cstar ∧ ∀ C₀ : ℝ, Cstar ≤ C₀ → ∃ α₄ : ℝ, 0 < α₄ ∧
    ∀ α ∈ Set.Ioc 0 α₄, ∀ {K : ℝ} {Φs : Fn} {E : Fn → Fn} {g₀ : Fn}, 0 ≤ K →
    (∀ z, 0 ≤ z → g₀ z 0 = 0 ∧ g₀ z (π / 2) = 0) →
    (∀ u : Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u)) →
    Work.FTS.VocabO2.StarPkgo2 α Cs Φs → Work.FTS.StrongPersist.StarPkg6 α Cs Φs →
    MuLamOK α C₀ Φs E →
    (∀ ε : ℝ, 0 < ε → EpsDatum α ρ ε g₀) →
    Work.FTS.Nonlin.Xn α g₀ ≤ α ^ 2 →
    Work.FTS.StrongGlobal.Xn6 α g₀ ≤ K * α ^ 2 →
    EpsUniformMem α ρ Φs E g₀ C₀ K

end Work.FTS.StrongEps.EpsE4Thr.E4R4
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.Decay3Aux.integrableOn_majProfile =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# Integrability of the majorant profile `D * √z / (1+z)²` on `(0, ∞)`

The function `z ↦ √z / (1+z)²` is Lebesgue-integrable on `(0,∞)`: near `0` it is bounded by
`1` on the finite-measure set `(0,1]`, while on `(1,∞)` it is dominated by `z^{-3/2}`.
The factor `D` is irrelevant.  This is the "majorant profile" integrability used by the
`DecayChapter3` chain (`E4R3.Decay3`).
-/

namespace Work.FTS.StrongEps.E4R3.Decay3Aux

/-- `√z / (1+z)²` is Lebesgue-integrable on `(0, ∞)`. -/
theorem sqrt_div_sq_integrableOn :
    MeasureTheory.IntegrableOn (fun z : ℝ => Real.sqrt z / (1 + z) ^ 2) (Set.Ioi 0) := by
  -- The function is continuous on `(0,∞)`, hence a.e. strongly measurable there.
  have hcont : ContinuousOn (fun z : ℝ => Real.sqrt z / (1 + z) ^ 2) (Set.Ioi 0) := by
    apply ContinuousOn.div
    · exact Real.continuous_sqrt.continuousOn
    · fun_prop
    · intro z hz
      have hz' : (0 : ℝ) < z := hz
      positivity
  have hmeas : MeasureTheory.AEStronglyMeasurable (fun z : ℝ => Real.sqrt z / (1 + z) ^ 2)
      (MeasureTheory.volume.restrict (Set.Ioi 0)) :=
    hcont.aestronglyMeasurable measurableSet_Ioi
  -- Split `(0,∞) = (0,1] ∪ (1,∞)`.
  have hsplit : Set.Ioi (0 : ℝ) = Set.Ioc 0 1 ∪ Set.Ioi 1 := by
    ext r; simp only [Set.mem_Ioi, Set.mem_Ioc, Set.mem_union]
    constructor
    · intro h; rcases lt_or_ge (1 : ℝ) r with h1 | h1
      · exact Or.inr h1
      · exact Or.inl ⟨h, h1⟩
    · rintro (⟨h, _⟩ | h)
      · exact h
      · linarith
  rw [hsplit]
  refine MeasureTheory.IntegrableOn.union ?_ ?_
  · -- On `(0,1]` the function is bounded by `1` and the measure is finite.
    refine MeasureTheory.IntegrableOn.of_bound (measure_Ioc_lt_top) ?_ 1 ?_
    · exact hmeas.mono_set (Set.Ioc_subset_Ioi_self)
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioc] with x hx
      obtain ⟨hx0, hx1⟩ := hx
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      rw [div_le_one (by positivity)]
      have h1 : Real.sqrt x ≤ 1 := Real.sqrt_le_one.mpr hx1
      have h2 : (1 : ℝ) ≤ (1 + x) ^ 2 := by
        have := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) (by linarith : (1 : ℝ) ≤ 1 + x) 2
        simpa using this
      linarith
  · -- On `(1, ∞)` the function is dominated by `x ^ (-(3/2))`.
    have hg : MeasureTheory.IntegrableOn (fun x : ℝ => x ^ (-(3 : ℝ) / 2)) (Set.Ioi 1) :=
      integrableOn_Ioi_rpow_of_lt (by norm_num) (by norm_num)
    refine MeasureTheory.Integrable.mono' hg ?_ ?_
    · exact hmeas.mono_set (Set.Ioi_subset_Ioi (by norm_num))
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with x hx
      rw [Set.mem_Ioi] at hx
      have hx0 : (0 : ℝ) < x := by linarith
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      have hstep : Real.sqrt x / (1 + x) ^ 2 ≤ Real.sqrt x / x ^ 2 := by
        apply div_le_div_of_nonneg_left (Real.sqrt_nonneg x) (by positivity)
        exact pow_le_pow_left₀ (le_of_lt hx0) (by linarith) 2
      have hstep2 : Real.sqrt x / x ^ 2 = x ^ (-(3 : ℝ) / 2) := by
        rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast x 2, ← Real.rpow_sub hx0]
        norm_num
      rw [hstep2] at hstep
      exact hstep

theorem integrableOn_majProfile (D : ℝ) :
    MeasureTheory.IntegrableOn (fun z : ℝ => D * (Real.sqrt z / (1 + z) ^ 2)) (Set.Ioi 0) := by
  exact sqrt_div_sq_integrableOn.const_mul D

end Work.FTS.StrongEps.E4R3.Decay3Aux
end
-- ===== merged: Submission.Work.FTS_RegExport.RXR5L.Auxiliary.Tlim_bounds =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_RegExport.RXR5L.aux

theorem Tlim_bounds {α C₀ : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn}
    {g : Work.FTS.Galerkin.Fam}
    (hOK : Work.FTS.FinalV2.DynOK' (Work.FTS.Regularity.pExp α) C₀ Φs E g)
    {S : ℝ} (hS : 0 < S) :
    ∃ M : ℝ, 0 ≤ M ∧
      (∀ τ ∈ Set.Icc (0:ℝ) S,
        |Work.Construction.L12 (fun z θ => 3 * Work.Spaces.Dth
          (Work.FTS.Galerkin.slice g τ) z θ / (1 + z)) 0| ≤ M) ∧
      (∀ τ ∈ Set.Icc (0:ℝ) S, ∀ τ' ∈ Set.Icc (0:ℝ) S,
        |Work.Construction.L12 (fun z θ => 3 * Work.Spaces.Dth
            (Work.FTS.Galerkin.slice g τ) z θ / (1 + z)) 0
          - Work.Construction.L12 (fun z θ => 3 * Work.Spaces.Dth
            (Work.FTS.Galerkin.slice g τ') z θ / (1 + z)) 0|
          ≤ M * |τ - τ'|) :=
  Work.FTS_RegExport.RXR5L.Auxiliary.Tlim_bounds_from_aux (hOK := hOK)
    (hsub := Work.FTS_RegExport.RXR5L.Auxiliary.L12_sub_of_bdd_proved)
    (hbnd := Work.FTS_RegExport.RXR5L.Auxiliary.Dth_slice_bounds hα hα13 hOK.2 hS)

end Work.FTS_RegExport.RXR5L.aux
end
