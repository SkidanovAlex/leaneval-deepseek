import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.H2W.thetaPoincare_zero
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllSol.VopAux.TraceAux
import Submission.Work.FTS.EllSol.VopAux.TraceIntegrand

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllSol.VopAux

set_option autoImplicit false
set_option maxHeartbeats 1600000

open scoped Real Topology
open MeasureTheory Set Filter

/-
# The angular `θ`-Poincaré estimate with boundary traces

`Work.FTS.EllSol.VopAux.thetaPoincareOpenTrace`: for data `f` which is `C^∞` on the *open*
quadrant `(0,∞) × (0,π/2)` and whose angular slices `D_z^j f z ·` (`j ≤ k`, `z > 0`) vanish at
the two endpoints `θ = 0, π/2` in the sense of *limits*, and with `∂_θ²f ∈ ℋ^k` honestly, the
weighted `ℋ^k`-norms of `f` and `∂_θ f` are controlled by that of `∂_θ² f`, and both `f` and
`∂_θ f` are honestly in `ℋ^k`.

The proof integrates the per-`z` comparisons
`HkIntegrand_integral_le_pth2_trace` / `HkIntegrand_integral_le_pth2_pth_trace` (which rest on
the single-slice estimates `sliceF_le_sliceV` / `sliceF_deriv_le_sliceV` and the slice-group
identities) over `z ∈ Iz`, using the a.e. strong measurability of the `z`-integral of the
`ℋ^k`-integrand and the honesty of `∂_θ²f`.
-/

theorem thetaPoincareOpenTrace (k : ℕ) : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (f : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      (∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))) →
      (∀ j : ℕ, j ≤ k → ∀ z : ℝ, 0 < z →
        Filter.Tendsto (fun θ : ℝ => Work.Spaces.DzIter j f z θ)
          (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) ∧
        Filter.Tendsto (fun θ : ℝ => Work.Spaces.DzIter j f z θ)
          (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0)) →
      Work.Spaces.HkMem α k (Work.Spaces.pthIter 2 f) →
      Work.Spaces.HkMem α k f ∧ Work.Spaces.HkMem α k (Work.Spaces.pth f) ∧
        Work.Spaces.HkNorm α k f ≤ C * Work.Spaces.HkNorm α k (Work.Spaces.pthIter 2 f) ∧
        Work.Spaces.HkNorm α k (Work.Spaces.pth f)
          ≤ C * Work.Spaces.HkNorm α k (Work.Spaces.pthIter 2 f) := by
  obtain ⟨C1, hC1pos, hC1⟩ := HkIntegrand_integral_le_pth2_trace k
  obtain ⟨C2, hC2pos, hC2⟩ := HkIntegrand_integral_le_pth2_pth_trace k
  refine ⟨max 1 (max C1 C2), lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro α f hα0 hα4 hsm htrace hmem
  have hα1 : α ≤ 1 := by linarith
  have hSO : Work.FTS.EllipticEst.SmoothOpen f :=
    Work.FTS.EllipticEst.smoothOpen_of_forall hsm
  have hSOp : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.pth f) := hSO.pth
  have h1 := hC1 α f hα0 hα1 hSO htrace hmem.1
  have h2 := hC2 α f hα0 hα1 hSO htrace hmem.1
  have hC1le : C1 ≤ max 1 (max C1 C2) :=
    le_trans (le_max_left C1 C2) (le_max_right 1 (max C1 C2))
  have hC2le : C2 ≤ max 1 (max C1 C2) :=
    le_trans (le_max_right C1 C2) (le_max_right 1 (max C1 C2))
  have hmemf : Work.Spaces.HkMem α k f := by
    refine ⟨fun z hz => (h1 z hz).1, ?_⟩
    refine MeasureTheory.Integrable.mono' (hmem.2.const_mul C1)
      (aesm_integral_HkIntegrand α k hSO) ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z hz
    rw [Real.norm_of_nonneg (show (0 : ℝ) ≤ ∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α k f z θ from
      MeasureTheory.setIntegral_nonneg (s := Work.Spaces.Iθ) measurableSet_Icc
        (fun θ _ => Work.Spaces.HkIntegrand_nonneg α k f z θ))]
    exact (h1 z hz).2
  have hmem1 : Work.Spaces.HkMem α k (Work.Spaces.pth f) := by
    refine ⟨fun z hz => (h2 z hz).1, ?_⟩
    refine MeasureTheory.Integrable.mono' (hmem.2.const_mul C2)
      (aesm_integral_HkIntegrand α k hSOp) ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z hz
    rw [Real.norm_of_nonneg (show (0 : ℝ) ≤ ∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α k (Work.Spaces.pth f) z θ from
      MeasureTheory.setIntegral_nonneg (s := Work.Spaces.Iθ) measurableSet_Icc
        (fun θ _ => Work.Spaces.HkIntegrand_nonneg α k (Work.Spaces.pth f) z θ))]
    exact (h2 z hz).2
  have hSq1 : Work.Spaces.HkSq α k f ≤ C1 * Work.Spaces.HkSq α k (Work.Spaces.pthIter 2 f) := by
    have hle : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
        (fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ) z
          ≤ C1 * (fun z => ∫ θ in Work.Spaces.Iθ,
              Work.Spaces.HkIntegrand α k (Work.Spaces.pthIter 2 f) z θ) z :=
      MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici (fun z hz => (h1 z hz).2)
    have hnn : 0 ≤ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iz]
        (fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k f z θ) :=
      Filter.Eventually.of_forall fun z => MeasureTheory.setIntegral_nonneg measurableSet_Icc
        (fun θ _ => Work.Spaces.HkIntegrand_nonneg α k f z θ)
    have hInt : MeasureTheory.IntegrableOn (fun z => C1 * (∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α k (Work.Spaces.pthIter 2 f) z θ)) Work.Spaces.Iz :=
      hmem.2.const_mul C1
    have hm := MeasureTheory.integral_mono_of_nonneg hnn hInt hle
    calc Work.Spaces.HkSq α k f
        = ∫ z in Work.Spaces.Iz, (fun z => ∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α k f z θ) z := rfl
      _ ≤ ∫ z in Work.Spaces.Iz, C1 * (∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α k (Work.Spaces.pthIter 2 f) z θ) := hm
      _ = C1 * ∫ z in Work.Spaces.Iz, (∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α k (Work.Spaces.pthIter 2 f) z θ) :=
          MeasureTheory.integral_const_mul C1 _
      _ = C1 * Work.Spaces.HkSq α k (Work.Spaces.pthIter 2 f) := rfl
  have hSq2 : Work.Spaces.HkSq α k (Work.Spaces.pth f)
      ≤ C2 * Work.Spaces.HkSq α k (Work.Spaces.pthIter 2 f) := by
    have hle : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
        (fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k (Work.Spaces.pth f) z θ) z
          ≤ C2 * (fun z => ∫ θ in Work.Spaces.Iθ,
              Work.Spaces.HkIntegrand α k (Work.Spaces.pthIter 2 f) z θ) z :=
      MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici (fun z hz => (h2 z hz).2)
    have hnn : 0 ≤ᵐ[MeasureTheory.volume.restrict Work.Spaces.Iz]
        (fun z => ∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α k (Work.Spaces.pth f) z θ) :=
      Filter.Eventually.of_forall fun z => MeasureTheory.setIntegral_nonneg measurableSet_Icc
        (fun θ _ => Work.Spaces.HkIntegrand_nonneg α k (Work.Spaces.pth f) z θ)
    have hInt : MeasureTheory.IntegrableOn (fun z => C2 * (∫ θ in Work.Spaces.Iθ,
        Work.Spaces.HkIntegrand α k (Work.Spaces.pthIter 2 f) z θ)) Work.Spaces.Iz :=
      hmem.2.const_mul C2
    have hm := MeasureTheory.integral_mono_of_nonneg hnn hInt hle
    calc Work.Spaces.HkSq α k (Work.Spaces.pth f)
        = ∫ z in Work.Spaces.Iz, (fun z => ∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α k (Work.Spaces.pth f) z θ) z := rfl
      _ ≤ ∫ z in Work.Spaces.Iz, C2 * (∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α k (Work.Spaces.pthIter 2 f) z θ) := hm
      _ = C2 * ∫ z in Work.Spaces.Iz, (∫ θ in Work.Spaces.Iθ,
            Work.Spaces.HkIntegrand α k (Work.Spaces.pthIter 2 f) z θ) :=
          MeasureTheory.integral_const_mul C2 _
      _ = C2 * Work.Spaces.HkSq α k (Work.Spaces.pthIter 2 f) := rfl
  refine ⟨hmemf, hmem1, ?_, ?_⟩
  · calc Work.Spaces.HkNorm α k f = Real.sqrt (Work.Spaces.HkSq α k f) := rfl
      _ ≤ Real.sqrt (C1 * Work.Spaces.HkSq α k (Work.Spaces.pthIter 2 f)) :=
          Real.sqrt_le_sqrt hSq1
      _ = Real.sqrt C1 * Work.Spaces.HkNorm α k (Work.Spaces.pthIter 2 f) := by
          rw [Real.sqrt_mul hC1pos.le, Work.Spaces.HkNorm]
      _ ≤ max 1 (max C1 C2) * Work.Spaces.HkNorm α k (Work.Spaces.pthIter 2 f) := by
          refine mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _)
          exact le_trans (sqrt_le_max_one C1) (max_le (le_max_left _ _) hC1le)
  · calc Work.Spaces.HkNorm α k (Work.Spaces.pth f)
        = Real.sqrt (Work.Spaces.HkSq α k (Work.Spaces.pth f)) := rfl
      _ ≤ Real.sqrt (C2 * Work.Spaces.HkSq α k (Work.Spaces.pthIter 2 f)) :=
          Real.sqrt_le_sqrt hSq2
      _ = Real.sqrt C2 * Work.Spaces.HkNorm α k (Work.Spaces.pthIter 2 f) := by
          rw [Real.sqrt_mul hC2pos.le, Work.Spaces.HkNorm]
      _ ≤ max 1 (max C1 C2) * Work.Spaces.HkNorm α k (Work.Spaces.pthIter 2 f) := by
          refine mul_le_mul_of_nonneg_right ?_ (Real.sqrt_nonneg _)
          exact le_trans (sqrt_le_max_one C2) (max_le (le_max_left _ _) hC2le)

end Work.FTS.EllSol.VopAux
