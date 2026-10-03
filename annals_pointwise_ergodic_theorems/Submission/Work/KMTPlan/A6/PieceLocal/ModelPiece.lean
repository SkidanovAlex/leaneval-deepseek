/-
# The bounded-height model piece of Area A6 (`Work.KMTPlan.A6.ModelPieceBoundedH`)

This module assembles the target `Work.KMTPlan.A6.PieceBoundedH.modelPiece` from the three
bounded-height inputs stated in `Submission/Work/KMTPlan/A6/PieceBoundedH/Defs.lean`:

* `SliceFBound` / `SliceGBound` — the two packet estimates (the `(2,2,1)`-instances of the paper's
  linear lacunary variational estimates `(lin-1)`/`(lin-2)` at bounded arithmetic height);
* `KernelMassBound` — the `ℓ¹(ℤ²)`-mass of the model kernel at bounded height.

## The assembly

Write `L = lcL l₁ l₂ k₁ k₂`, `u = uScale ρ L`, `c = mdlKernel ρ P l₁ l₂ k₁ k₂` (the kernel of the
twisted bilinear multiplier `Btwist`).  For `f, g ∈ ℓ²(ℤ)`:

1. `mdlPart = mdlPartJ ⋯ 0 0` and `mdlPartJ ⋯ n x = ∫_{1/2}^1 mdlSliceJ ⋯ 0 0 t n x dt`
   (`mdlPartJ_zero_zero`, `mdlPartJ_eq_intervalIntegral`), so by the pointwise Minkowski
   inequality for the variational norm (`varNorm_mdlPartJ_le_integral`, together with the
   measurability `MdlSliceMeasurable` and the interval-integrability `MdlSliceIntervalIntegrable`
   of the slices),

     `Vʳ (mdlPart)_{n}(x) ≤ ∫⁻ t ∈ (1/2,1], Vʳ (mdlSliceJ ⋯ t)_{n}(x)`.

2. For fixed `t`, the frozen slice is the bilinear slice kernel `c` applied to the two packet
   families (`Btwist_eq_mdlKernel_apply`), so the `ℓ¹(ℤ)`-norm of its variation is at most
   `2 ‖c‖_{ℓ¹(ℤ²)} ‖Vʳ (sliceF)‖_{ℓ²} ‖Vʳ (sliceG)‖_{ℓ²}` (`sliceKernelL1_clean`), and the two
   factors are bounded by `K_F(Λ)‖f‖₂`, `K_G(Λ)‖g‖₂` uniformly in `t` (`SliceFBound`,
   `SliceGBound`).

3. `A7.eLpNorm_lintegral_le` converts the `t`-integral of the (uniformly bounded) slice norms into
   the `ℓ¹`-norm of the integral.

The degenerate cases `eLpNorm f 2 = 0` (whence `f = 0`, and `mdlPart` is bilinear, so the left-hand
side vanishes) and `eLpNorm f 2 = ⊤` (whence the right-hand side is `⊤`, the constant `K Λ` being
`≥ 1`) are handled by the same pattern as `MdlSliceCoreGain_of_memLp`.
-/
import Mathlib
import Submission.Work.KMTPlan.A6.LowModApproxNoAliasingCase
import Submission.Work.Analysis.Variational.SliceKernelL1
import Submission.Work.KMTPlan.A6.PieceBoundedH.kernelMassBound
import Submission.Work.KMTPlan.A6.PieceLocal.SliceFBound
import Submission.Work.KMTPlan.A6.PieceLocal.SliceGBound
import Submission.Work.KMTPlan.A6.MdlSliceCoreGainBig
import Submission.Port.Aesm

set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option linter.unusedVariables false

namespace Work.KMTPlan.A6.PieceLocal

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems
open Work.KMTPlan.A6.PieceBoundedH

/-! ## The slice-kernel bound (without finiteness hypotheses) -/

/-- **The `ℓ¹(ℤ)`-slice-kernel bound for the variational norm.**  This is
`Work.Analysis.Variational.SliceKernelL1` with the (unused) pointwise finiteness hypotheses of the
two families removed, in the form in which the model piece consumes it. -/
theorem sliceKernelL1_clean (r : NNReal) (hr : 1 ≤ r) (c : ℤ → ℤ → ℂ) (h k : ℕ → ℤ → ℂ) :
    MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => ∑' i : ℤ, ∑' j : ℤ, c i j * h n (x - i) * k n (x - j)))
      1 MeasureTheory.Measure.count
      ≤ 2 * (∑' p : ℤ × ℤ, ‖c p.1 p.2‖ₑ) *
          MeasureTheory.eLpNorm (fun y : ℤ => PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => h n y)) 2 MeasureTheory.Measure.count *
          MeasureTheory.eLpNorm (fun y : ℤ => PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => k n y)) 2 MeasureTheory.Measure.count := by
  set H : ℤ → ℝ≥0∞ := fun y => PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => h n y)
    with hH
  set K : ℤ → ℝ≥0∞ := fun y => PointwiseErgodicTheorems.variationalNorm r (fun n : ℕ => k n y)
    with hK
  have hpt : ∀ x : ℤ, PointwiseErgodicTheorems.variationalNorm r
      (fun n : ℕ => ∑' i : ℤ, ∑' j : ℤ, c i j * h n (x - i) * k n (x - j))
      ≤ ∑' p : ℤ × ℤ, ‖c p.1 p.2‖ₑ * (H (x - p.1) * K (x - p.2)) :=
    fun x => Work.Analysis.Variational.variationalNorm_bilinear_slice_le hr c h k x
  have h1 : MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => ∑' i : ℤ, ∑' j : ℤ, c i j * h n (x - i) * k n (x - j)))
      1 MeasureTheory.Measure.count
      ≤ MeasureTheory.eLpNorm (fun x : ℤ => ∑' p : ℤ × ℤ,
            ‖c p.1 p.2‖ₑ * (H (x - p.1) * K (x - p.2))) 1 MeasureTheory.Measure.count :=
    MeasureTheory.eLpNorm_mono_enorm (hf := by pw_aesm) fun x => by simpa only [enorm_eq_self] using hpt x
  have h2 : MeasureTheory.eLpNorm (fun x : ℤ => ∑' p : ℤ × ℤ,
          ‖c p.1 p.2‖ₑ * (H (x - p.1) * K (x - p.2))) 1 MeasureTheory.Measure.count
      ≤ (∑' p : ℤ × ℤ, ‖c p.1 p.2‖ₑ) * MeasureTheory.eLpNorm H 2 MeasureTheory.Measure.count
          * MeasureTheory.eLpNorm K 2 MeasureTheory.Measure.count :=
    Work.Analysis.Variational.eLpNorm_slice_kernel_le (fun p : ℤ × ℤ => ‖c p.1 p.2‖ₑ) H K
  have h3 : (∑' p : ℤ × ℤ, ‖c p.1 p.2‖ₑ) * MeasureTheory.eLpNorm H 2 MeasureTheory.Measure.count
          * MeasureTheory.eLpNorm K 2 MeasureTheory.Measure.count
      ≤ 2 * (∑' p : ℤ × ℤ, ‖c p.1 p.2‖ₑ)
          * MeasureTheory.eLpNorm H 2 MeasureTheory.Measure.count
          * MeasureTheory.eLpNorm K 2 MeasureTheory.Measure.count := by
    have hS : (∑' p : ℤ × ℤ, ‖c p.1 p.2‖ₑ) ≤ 2 * (∑' p : ℤ × ℤ, ‖c p.1 p.2‖ₑ) := by
      simpa only [one_mul] using mul_le_mul' (show (1 : ℝ≥0∞) ≤ 2 by norm_num)
        (le_refl (∑' p : ℤ × ℤ, ‖c p.1 p.2‖ₑ))
    exact mul_le_mul' (mul_le_mul' hS le_rfl) le_rfl
  exact (h1.trans h2).trans (by simpa only [hH, hK] using h3)

/-! ## The frozen slice as a slice kernel -/

/-- The frozen-`t` slice of the model tuple, written with the packet families `sliceF`, `sliceG`
(equal to `mdlSliceJ ρ P C₀ a f g l₁ l₂ k₁ k₂ 0 0 t`). -/
noncomputable def sliceJ (ρ : ℝ) (P : Polynomial ℤ) (C₀ : ℕ) (a : ℕ → ℝ≥0)
    (l₁ l₂ k₁ k₂ : ℕ) (t : ℝ) (f g : ℤ → ℂ) : ℕ → ℤ → ℂ :=
  fun n x =>
    if mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n then
      Work.KMTAreas.A7.Btwist ρ P l₁ l₂
        (Work.KMTAreas.A7.mStarF (Work.KMTAreas.A7.uScale ρ (lcL l₁ l₂ k₁ k₂)))
        (Work.KMTAreas.A7.mStargF P.natDegree
          (Work.KMTAreas.A7.uScale ρ (lcL l₁ l₂ k₁ k₂)))
        (sliceF ρ C₀ a l₁ l₂ k₁ k₂ t f n) (sliceG ρ P C₀ a l₁ l₂ k₁ k₂ t g n) x
    else 0

/-- `sliceJ` is the frozen slice `mdlSliceJ ⋯ 0 0 t`. -/
theorem sliceJ_eq_mdlSliceJ (ρ : ℝ) (P : Polynomial ℤ) (C₀ : ℕ) (a : ℕ → ℝ≥0)
    (l₁ l₂ k₁ k₂ : ℕ) (t : ℝ) (f g : ℤ → ℂ) :
    sliceJ ρ P C₀ a l₁ l₂ k₁ k₂ t f g
      = mdlSliceJ ρ P C₀ a f g l₁ l₂ k₁ k₂ 0 0 t := by
  funext n x
  rw [mdlSliceJ_apply]
  by_cases h : mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n
  · simp only [sliceJ, if_pos h, sliceF, sliceG, lcL,
      Work.KMTPlan.A6.varphiNtj_zero, Work.KMTPlan.A6.varphitildeNtj_zero]
  · simp only [sliceJ, if_neg h]

/-- **The frozen slice is the slice kernel `mdlKernel` applied to the two packet families.** -/
theorem sliceJ_eq_kernel (ρ : ℝ) (P : Polynomial ℤ) (C₀ : ℕ) (a : ℕ → ℝ≥0)
    (l₁ l₂ k₁ k₂ : ℕ) (t : ℝ) (f g : ℤ → ℂ) (n : ℕ) (x : ℤ) :
    sliceJ ρ P C₀ a l₁ l₂ k₁ k₂ t f g n x
      = ∑' i : ℤ, ∑' j : ℤ,
          mdlKernel ρ P l₁ l₂ k₁ k₂ i j * sliceF ρ C₀ a l₁ l₂ k₁ k₂ t f n (x - i)
            * sliceG ρ P C₀ a l₁ l₂ k₁ k₂ t g n (x - j) := by
  rw [sliceJ]
  by_cases h : mdlCore ρ C₀ a l₁ l₂ k₁ k₂ n
  · rw [if_pos h]
    exact Btwist_eq_mdlKernel_apply ρ P l₁ l₂ k₁ k₂ _ _ x
  · rw [if_neg h]
    have hf : sliceF ρ C₀ a l₁ l₂ k₁ k₂ t f n = 0 := by
      funext y; rw [sliceF, if_neg h]
    rw [hf]
    simp

/-! ## The per-`t` slice bound -/

/-- **The frozen-slice bound from the two packet estimates and the kernel mass.** -/
theorem frozenSlice_le (r : NNReal) (hr : 2 < r) (C₀ : ℕ) (ρ : ℝ) (B : ℕ) (P : Polynomial ℤ)
    (hF : SliceFBound r C₀ ρ B) (hG : SliceGBound P r C₀ ρ B) {C : ℝ}
    (hmass : ∀ (l₁ l₂ k₁ k₂ : ℕ), lcL l₁ l₂ k₁ k₂ ≤ B →
      (Summable fun p : ℤ × ℤ => ‖mdlKernel ρ P l₁ l₂ k₁ k₂ p.1 p.2‖) ∧
      (∑' p : ℤ × ℤ, ‖mdlKernel ρ P l₁ l₂ k₁ k₂ p.1 p.2‖) ≤ C) :
    ∃ K : NNReal → NNReal,
      ∀ (a : ℕ → ℝ≥0) (Λ : NNReal) (l₁ l₂ k₁ k₂ : ℕ) (t : ℝ) (f g : ℤ → ℂ),
        1 < Λ → PointwiseErgodicTheorems.Lacunary Λ a → (∀ n, 1 ≤ a n) →
        t ∈ Set.Icc (1 / 2 : ℝ) 1 → lcL l₁ l₂ k₁ k₂ ≤ B →
        MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => mdlSliceJ ρ P C₀ a f g l₁ l₂ k₁ k₂ 0 0 t n x))
          1 MeasureTheory.Measure.count
          ≤ (K Λ : ENNReal) * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count
              * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count := by
  obtain ⟨Kf, hKf⟩ := hF
  obtain ⟨Kg, hKg⟩ := hG
  have hC0 : 0 ≤ C := by
    obtain ⟨-, hC'⟩ := hmass 0 0 0 0 (by simp [lcL])
    exact le_trans (tsum_nonneg fun p => norm_nonneg _) hC'
  have hKpos : ∀ Λ : NNReal, 0 < 2 * C * (Kf Λ : ℝ) * (Kg Λ : ℝ) + 1 := by
    intro Λ
    have h1 := (Kf Λ).2
    have h2 := (Kg Λ).2
    positivity
  refine ⟨fun Λ => ENNReal.toNNReal
      (2 * ENNReal.ofReal C * (Kf Λ : ENNReal) * (Kg Λ : ENNReal)) + 1, ?_⟩
  intro a Λ l₁ l₂ k₁ k₂ t f g hΛ ha ha1 ht hLB
  have hr1 : (1 : NNReal) ≤ r := le_of_lt (lt_trans (by norm_num) hr)
  obtain ⟨hc, hC⟩ := hmass l₁ l₂ k₁ k₂ hLB
  have hslice := sliceKernelL1_clean r hr1 (fun i j => mdlKernel ρ P l₁ l₂ k₁ k₂ i j)
    (fun n => sliceF ρ C₀ a l₁ l₂ k₁ k₂ t f n)
    (fun n => sliceG ρ P C₀ a l₁ l₂ k₁ k₂ t g n)
  rw [show (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
      (fun n : ℕ => mdlSliceJ ρ P C₀ a f g l₁ l₂ k₁ k₂ 0 0 t n x))
      = (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => ∑' i : ℤ, ∑' j : ℤ,
            mdlKernel ρ P l₁ l₂ k₁ k₂ i j * sliceF ρ C₀ a l₁ l₂ k₁ k₂ t f n (x - i)
              * sliceG ρ P C₀ a l₁ l₂ k₁ k₂ t g n (x - j))) from by
    funext x
    congr 1
    funext n
    rw [← sliceJ_eq_kernel, sliceJ_eq_mdlSliceJ]]
  refine hslice.trans ?_
  have hf := hKf a Λ l₁ l₂ k₁ k₂ t f hΛ ha ha1 ht hLB
  have hg := hKg a Λ l₁ l₂ k₁ k₂ t g hΛ ha ha1 ht hLB
  -- the mass in `ℝ≥0∞`-form
  have hmassₑ : (∑' p : ℤ × ℤ, ‖mdlKernel ρ P l₁ l₂ k₁ k₂ p.1 p.2‖ₑ)
      ≤ ENNReal.ofReal C := by
    have h₁ : ∀ p : ℤ × ℤ, (0 : ℝ) ≤ ‖mdlKernel ρ P l₁ l₂ k₁ k₂ p.1 p.2‖ :=
      fun p => norm_nonneg _
    calc (∑' p : ℤ × ℤ, ‖mdlKernel ρ P l₁ l₂ k₁ k₂ p.1 p.2‖ₑ)
        = ∑' p : ℤ × ℤ, ENNReal.ofReal ‖mdlKernel ρ P l₁ l₂ k₁ k₂ p.1 p.2‖ := by
          refine tsum_congr fun p => ?_
          rw [enorm_eq_nnnorm, ← ENNReal.ofReal_coe_nnreal]
          rfl
      _ = ENNReal.ofReal (∑' p : ℤ × ℤ, ‖mdlKernel ρ P l₁ l₂ k₁ k₂ p.1 p.2‖) :=
          (ENNReal.ofReal_tsum_of_nonneg h₁ hc).symm
      _ ≤ ENNReal.ofReal C := ENNReal.ofReal_le_ofReal hC
  set A : ENNReal := 2 * ENNReal.ofReal C * (Kf Λ : ENNReal) * (Kg Λ : ENNReal) with hAdef
  have hAne : A ≠ ⊤ := by
    rw [hAdef]
    exact ENNReal.mul_ne_top (ENNReal.mul_ne_top (ENNReal.mul_ne_top
      (by norm_num) ENNReal.ofReal_ne_top) ENNReal.coe_ne_top) ENNReal.coe_ne_top
  have hcoef : A ≤ ((ENNReal.toNNReal A + 1 : NNReal) : ENNReal) := by
    rw [ENNReal.coe_add, ENNReal.coe_one, ← ENNReal.coe_toNNReal hAne]
    exact le_add_right le_rfl
  -- the coefficient bound `2 ‖c‖₁ ≤ A`
  have hcoef₂ : 2 * (∑' p : ℤ × ℤ, ‖mdlKernel ρ P l₁ l₂ k₁ k₂ p.1 p.2‖ₑ) * (Kf Λ : ENNReal)
        * (Kg Λ : ENNReal) ≤ A := by
    rw [hAdef]
    exact mul_le_mul' (mul_le_mul' (mul_le_mul' le_rfl hmassₑ) le_rfl) le_rfl
  have hmain : 2 * (∑' p : ℤ × ℤ, ‖mdlKernel ρ P l₁ l₂ k₁ k₂ p.1 p.2‖ₑ)
        * MeasureTheory.eLpNorm (fun y : ℤ => PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => sliceF ρ C₀ a l₁ l₂ k₁ k₂ t f n y)) 2 MeasureTheory.Measure.count
        * MeasureTheory.eLpNorm (fun y : ℤ => PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => sliceG ρ P C₀ a l₁ l₂ k₁ k₂ t g n y)) 2 MeasureTheory.Measure.count
      ≤ ((ENNReal.toNNReal A + 1 : NNReal) : ENNReal)
          * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count
          * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count := by
    have hstep : 2 * (∑' p : ℤ × ℤ, ‖mdlKernel ρ P l₁ l₂ k₁ k₂ p.1 p.2‖ₑ)
          * MeasureTheory.eLpNorm (fun y : ℤ => PointwiseErgodicTheorems.variationalNorm r
              (fun n : ℕ => sliceF ρ C₀ a l₁ l₂ k₁ k₂ t f n y)) 2 MeasureTheory.Measure.count
          * MeasureTheory.eLpNorm (fun y : ℤ => PointwiseErgodicTheorems.variationalNorm r
              (fun n : ℕ => sliceG ρ P C₀ a l₁ l₂ k₁ k₂ t g n y)) 2 MeasureTheory.Measure.count
        ≤ A * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count
            * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count := by
      calc 2 * (∑' p : ℤ × ℤ, ‖mdlKernel ρ P l₁ l₂ k₁ k₂ p.1 p.2‖ₑ)
            * MeasureTheory.eLpNorm (fun y : ℤ => PointwiseErgodicTheorems.variationalNorm r
                (fun n : ℕ => sliceF ρ C₀ a l₁ l₂ k₁ k₂ t f n y)) 2 MeasureTheory.Measure.count
            * MeasureTheory.eLpNorm (fun y : ℤ => PointwiseErgodicTheorems.variationalNorm r
                (fun n : ℕ => sliceG ρ P C₀ a l₁ l₂ k₁ k₂ t g n y)) 2 MeasureTheory.Measure.count
          ≤ 2 * (∑' p : ℤ × ℤ, ‖mdlKernel ρ P l₁ l₂ k₁ k₂ p.1 p.2‖ₑ)
              * ((Kf Λ : ENNReal) * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count)
              * ((Kg Λ : ENNReal) * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count) :=
            mul_le_mul' (mul_le_mul' le_rfl hf) hg
        _ = (2 * (∑' p : ℤ × ℤ, ‖mdlKernel ρ P l₁ l₂ k₁ k₂ p.1 p.2‖ₑ) * (Kf Λ : ENNReal)
              * (Kg Λ : ENNReal)) * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count
              * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count := by ring
        _ ≤ A * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count
              * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count :=
            mul_le_mul' (mul_le_mul' hcoef₂ le_rfl) le_rfl
    exact hstep.trans (mul_le_mul' (mul_le_mul' hcoef le_rfl) le_rfl)
  exact hmain

/-! ## The `t`-integration -/

/-- **The model tuple from a uniform bound on its frozen slices.**  If every frozen-`t` slice of
the model tuple has `ℓ¹`-norm at most `C` (`t ∈ [1/2,1]`), then so does the model tuple itself. -/
theorem mdlPart_le_of_slice (r : NNReal) (hr : 1 ≤ r) (P : Polynomial ℤ) (C₀ : ℕ) (ρ : ℝ)
    (a : ℕ → ℝ≥0) (l₁ l₂ k₁ k₂ : ℕ) {f g : ℤ → ℂ}
    (hf : MeasureTheory.MemLp f 2 MeasureTheory.Measure.count)
    (hg : MeasureTheory.MemLp g 2 MeasureTheory.Measure.count) {C : ENNReal}
    (hC : ∀ t ∈ Set.Icc (1 / 2 : ℝ) 1,
      MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => mdlSliceJ ρ P C₀ a f g l₁ l₂ k₁ k₂ 0 0 t n x))
        1 MeasureTheory.Measure.count ≤ C) :
    MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => mdlPart ρ P C₀ a f g l₁ l₂ k₁ k₂ n x))
      1 MeasureTheory.Measure.count ≤ C := by
  set Z : ℝ → ℤ → ℝ≥0∞ := fun t x => PointwiseErgodicTheorems.variationalNorm r
    (fun n : ℕ => mdlSliceJ ρ P C₀ a f g l₁ l₂ k₁ k₂ 0 0 t n x) with hZ
  have hle : (1 / 2 : ℝ) ≤ 1 := by norm_num
  have hpt : ∀ x : ℤ, PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => mdlPart ρ P C₀ a f g l₁ l₂ k₁ k₂ n x)
      ≤ ∫⁻ t in Set.uIoc (1 / 2 : ℝ) 1, Z t x := by
    intro x
    have hjj : (fun n : ℕ => mdlPartJ ρ P C₀ a f g l₁ l₂ k₁ k₂ 0 0 n x)
        = (fun n : ℕ => mdlPart ρ P C₀ a f g l₁ l₂ k₁ k₂ n x) := by
      funext n
      exact congrFun (congrFun (mdlPartJ_zero_zero ρ P C₀ a f g l₁ l₂ k₁ k₂) n) x
    rw [← hjj]
    refine varNorm_mdlPartJ_le_integral r hr ρ P C₀ a f g l₁ l₂ k₁ k₂ 0 0 x
      (fun n => ?_) (fun n => MdlSliceMeasurable ρ P C₀ a f g l₁ l₂ k₁ k₂ 0 0 n x)
    exact MdlSliceIntervalIntegrable ρ P C₀ a f g l₁ l₂ k₁ k₂ 0 0 n x hf hg
      (by intro h; norm_num) (by intro h; norm_num)
  have h1 : MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => mdlPart ρ P C₀ a f g l₁ l₂ k₁ k₂ n x))
      1 MeasureTheory.Measure.count
      ≤ MeasureTheory.eLpNorm (fun x : ℤ => ∫⁻ t in Set.uIoc (1 / 2 : ℝ) 1, Z t x)
          1 MeasureTheory.Measure.count :=
    MeasureTheory.eLpNorm_mono_enorm (hf := by pw_aesm) (fun x => by simpa only [enorm_eq_self] using hpt x)
  have h2 : MeasureTheory.eLpNorm (fun x : ℤ => ∫⁻ t in Set.uIoc (1 / 2 : ℝ) 1, Z t x)
        1 MeasureTheory.Measure.count ≤ C := by
    rw [Set.uIoc_of_le hle]
    exact Work.KMTAreas.A7.eLpNorm_lintegral_le 1 le_rfl Z C
      (fun t ht => hC t (Set.Ioc_subset_Icc_self ht))
  exact h1.trans h2

/-- **The model piece from the three inputs, for `ℓ²`-inputs.** -/
theorem modelPiece_memLp (P : Polynomial ℤ) (r : NNReal) (hr : 2 < r) (C₀ : ℕ) (ρ : ℝ) (B : ℕ)
    (hF : SliceFBound r C₀ ρ B) (hG : SliceGBound P r C₀ ρ B) (hM : KernelMassBound ρ P B) :
    ∃ K : NNReal → NNReal,
      ∀ (a : ℕ → ℝ≥0) (Λ : NNReal) (l₁ l₂ k₁ k₂ : ℕ) (f g : ℤ → ℂ),
        1 < Λ → PointwiseErgodicTheorems.Lacunary Λ a → (∀ n, 1 ≤ a n) →
        lcL l₁ l₂ k₁ k₂ ≤ B → (k₁ = 0 ∨ k₂ = 0) →
        MeasureTheory.MemLp f 2 MeasureTheory.Measure.count →
        MeasureTheory.MemLp g 2 MeasureTheory.Measure.count →
        MeasureTheory.eLpNorm (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => mdlPart ρ P C₀ a f g l₁ l₂ k₁ k₂ n x))
          1 MeasureTheory.Measure.count
          ≤ (K Λ : ENNReal) * MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count
              * MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count := by
  obtain ⟨C, -, hmass⟩ := hM
  obtain ⟨Kslice, hKslice⟩ := frozenSlice_le r hr C₀ ρ B P hF hG hmass
  refine ⟨Kslice, ?_⟩
  intro a Λ l₁ l₂ k₁ k₂ f g hΛ ha ha1 hLB hQ hf hg
  exact mdlPart_le_of_slice r (le_of_lt (lt_trans (by norm_num) hr)) P C₀ ρ a l₁ l₂ k₁ k₂ hf hg
    (fun t ht => hKslice a Λ l₁ l₂ k₁ k₂ t f g hΛ ha ha1 ht hLB)

/-- **The model piece from the three inputs.** -/
theorem modelPiece_of_inputs (P : Polynomial ℤ) (r : NNReal) (hr : 2 < r) (C₀ : ℕ) (ρ : ℝ)
    (B : ℕ) (hF : SliceFBound r C₀ ρ B) (hG : SliceGBound P r C₀ ρ B)
    (hM : KernelMassBound ρ P B) :
    Work.KMTPlan.A6.ModelPieceBoundedH P r C₀ ρ B := by
  obtain ⟨K, hK⟩ := modelPiece_memLp P r hr C₀ ρ B hF hG hM
  refine ⟨fun Λ => max (K Λ) 1, ?_⟩
  intro a Λ l₁ l₂ k₁ k₂ f g hΛ ha ha1 hLB hQ
  have hr1 : (1 : NNReal) ≤ r := le_of_lt (lt_trans (by norm_num) hr)
  have hKne : (((max (K Λ) 1 : NNReal)) : ENNReal) ≠ 0 :=
    ENNReal.coe_ne_zero.mpr (by positivity)
  by_cases hf0 : MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count = 0
  · rw [eq_zero_of_eLpNorm_two_eq_zero hf0]
    have hzero : (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
        (fun n : ℕ => mdlPart ρ P C₀ a 0 g l₁ l₂ k₁ k₂ n x))
        = (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
            (fun n : ℕ => mdlPartJ ρ P C₀ a 0 g l₁ l₂ k₁ k₂ 0 0 n x)) := by
      funext x
      congr 1
      funext n
      exact (congrFun (congrFun (mdlPartJ_zero_zero ρ P C₀ a 0 g l₁ l₂ k₁ k₂) n) x).symm
    rw [hzero, eLpNorm_variationalNorm_mdlPartJ_left_zero hr1]
    exact bot_le
  · by_cases hg0 : MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count = 0
    · rw [eq_zero_of_eLpNorm_two_eq_zero hg0]
      have hzero : (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
          (fun n : ℕ => mdlPart ρ P C₀ a f 0 l₁ l₂ k₁ k₂ n x))
          = (fun x : ℤ => PointwiseErgodicTheorems.variationalNorm r
              (fun n : ℕ => mdlPartJ ρ P C₀ a f 0 l₁ l₂ k₁ k₂ 0 0 n x)) := by
        funext x
        congr 1
        funext n
        exact (congrFun (congrFun (mdlPartJ_zero_zero ρ P C₀ a f 0 l₁ l₂ k₁ k₂) n) x).symm
      rw [hzero, eLpNorm_variationalNorm_mdlPartJ_right_zero hr1]
      exact bot_le
    · by_cases hfT : MeasureTheory.eLpNorm f 2 MeasureTheory.Measure.count = ⊤
      · rw [hfT, ENNReal.mul_top hKne, ENNReal.top_mul hg0]
        exact le_top
      · by_cases hgT : MeasureTheory.eLpNorm g 2 MeasureTheory.Measure.count = ⊤
        · rw [hgT, ENNReal.mul_top (mul_ne_zero hKne hf0)]
          exact le_top
        · refine (hK a Λ l₁ l₂ k₁ k₂ f g hΛ ha ha1 hLB hQ
              (memLp_two_count_of_ne_top hfT) (memLp_two_count_of_ne_top hgT)).trans ?_
          exact mul_le_mul' (mul_le_mul' (ENNReal.coe_le_coe.mpr (le_max_left _ _)) le_rfl) le_rfl

theorem modelPiece (P : Polynomial ℤ) (hd : 2 ≤ P.natDegree) (r : NNReal) (hr : 2 < r)
    (C₀ : ℕ) (hC₀ : 1 ≤ C₀) (hA1 : Work.KMTContract.AreaA1) (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1)
    (B : ℕ) : Work.KMTPlan.A6.ModelPieceBoundedH P r C₀ ρ B :=
  modelPiece_of_inputs P r hr C₀ ρ B
    (sliceFBound r hr C₀ hC₀ ρ hρ hρ1 B)
    (sliceGBound P hd r hr C₀ hC₀ ρ hρ hρ1 B)
    (kernelMassBound ρ hρ hρ1 P B)

end

end Work.KMTPlan.A6.PieceLocal
