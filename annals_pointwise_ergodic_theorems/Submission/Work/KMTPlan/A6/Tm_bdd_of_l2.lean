import Mathlib
import Submission.Work.KMTAreas.A7.Tle_varphiNt_bounded
import Submission.Work.KMTPlan.A6.memlpOfMemLpCount

open MeasureTheory
open scoped ENNReal NNReal BigOperators

namespace Work.KMTPlan.A6

open Work.Analysis.IonescuWainger Work.Analysis.IWMultiplier

/-- **The `ℓ²`-to-`ℓ^∞` bound for the exact-height Ionescu--Wainger multiplier `Tm ρ l φ`.**
For a `C²` compactly supported symbol `φ` whose `L¹` norms of `φ` and of `φ''` are bounded by
`S`, the kernel `tmKer ρ l φ` of the multiplier decays like `j^{-2}` (`iwKernel_decay_of_bump`),
hence is in `ℓ¹` with a bound `C` depending only on `ρ, l, S`.  Convolution with an `ℓ¹` kernel
maps `ℓ²` to `ℓ^∞`, with bound `‖Tm ρ l φ f‖_∞ ≤ C ‖f‖_{ℓ²}`. -/
theorem Tm_bdd_of_l2 (ρ : ℝ) (l : ℕ) (S : ℝ) (hSnn : 0 ≤ S) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (φ : ℝ → ℂ), ContDiff ℝ 2 φ → HasCompactSupport φ →
      (∫ y : ℝ, ‖φ y‖) ≤ S → (∫ y : ℝ, ‖iteratedDeriv 2 φ y‖) ≤ S →
      ∀ (f : ℤ → ℂ), MeasureTheory.MemLp f 2 MeasureTheory.Measure.count →
      ∀ y : ℤ, ‖Work.KMTAreas.A7.Tm ρ l φ f y‖
        ≤ C * Real.sqrt (∑' j : ℤ, ‖f j‖ ^ 2) := by
  classical
  -- The arithmetic frequency set of the exact-height projection and the kernel-decay constant.
  set A : Finset Analysis.IonescuWainger.Circle := Work.KMTAreas.A7.diffFreqs ρ l with hA
  set W : ℝ := 4 * ((A.card : ℝ) * S) + 1 with hW
  have hWnn : 0 ≤ W := by rw [hW]; positivity
  -- The comparison sequence `j ↦ W / (1+|j|)²` is summable.
  have hKw : Summable (fun j : ℤ => W * ‖Work.KMTAreas.A7.kmtKernWeight j‖) :=
    Work.KMTAreas.A7.summable_kmtKernWeight.mul_left W
  refine ⟨∑' j : ℤ, W * ‖Work.KMTAreas.A7.kmtKernWeight j‖,
    tsum_nonneg (fun j => mul_nonneg hWnn (norm_nonneg _)), ?_⟩
  intro φ hφcd hφcs h1 h2 f hf y
  -- Kernel decay for this particular symbol `φ`.
  have hker : ∀ j : ℤ, ‖iwKernel (iwSymbolSet A (periodize φ)) j‖
      ≤ W * ‖Work.KMTAreas.A7.kmtKernWeight j‖ := by
    intro j
    have h := Work.KMTAreas.A7.iwKernel_decay_of_bump A hφcd hφcs hSnn h1 h2 j
    simpa [hW] using h
  have hkerSum : Summable (fun j : ℤ => ‖iwKernel (iwSymbolSet A (periodize φ)) j‖) :=
    Summable.of_nonneg_of_le (fun j => norm_nonneg _) hker hKw
  -- The membership `f ∈ ℓ²` gives summability of `∑ ‖f j‖²`.
  have hmem : Memℓp f (2 : ℝ≥0∞) := memlpOfMemLpCount (by norm_num) (by norm_num) hf
  have hfsum : Summable (fun j : ℤ => ‖f j‖ ^ 2) := by
    have h := (memℓp_gen_iff (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal)).mp hmem
    simpa using h
  -- Every term of an `ℓ²` sequence is bounded by its `ℓ²` norm.
  have hR : ∀ z : ℤ, ‖f z‖ ≤ Real.sqrt (∑' j : ℤ, ‖f j‖ ^ 2) := by
    intro z
    refine (Real.le_sqrt (norm_nonneg _) (tsum_nonneg (fun j => by positivity))).mpr ?_
    exact hfsum.le_tsum z (fun j _ => by positivity)
  have hprodSum : Summable
      (fun j : ℤ => ‖iwKernel (iwSymbolSet A (periodize φ)) j‖ * ‖f (y - j)‖) :=
    Summable.of_nonneg_of_le (fun j => mul_nonneg (norm_nonneg _) (norm_nonneg _))
      (fun j => mul_le_mul_of_nonneg_left (hR (y - j)) (norm_nonneg _))
      (hkerSum.mul_right (Real.sqrt (∑' j : ℤ, ‖f j‖ ^ 2)))
  have hsumC : Summable (fun j : ℤ => iwKernel (iwSymbolSet A (periodize φ)) j * f (y - j)) :=
    Summable.of_norm_bounded
      (g := fun j : ℤ =>
        ‖iwKernel (iwSymbolSet A (periodize φ)) j‖ * Real.sqrt (∑' j : ℤ, ‖f j‖ ^ 2))
      (hkerSum.mul_right (Real.sqrt (∑' j : ℤ, ‖f j‖ ^ 2)))
      (fun j => by rw [norm_mul]; exact mul_le_mul_of_nonneg_left (hR (y - j)) (norm_nonneg _))
  calc ‖Work.KMTAreas.A7.Tm ρ l φ f y‖
      = ‖∑' j : ℤ, iwKernel (iwSymbolSet A (periodize φ)) j * f (y - j)‖ := by
        rw [hA]; rfl
    _ ≤ ∑' j : ℤ, ‖iwKernel (iwSymbolSet A (periodize φ)) j * f (y - j)‖ :=
        norm_tsum_le_tsum_norm hsumC.norm
    _ = ∑' j : ℤ, ‖iwKernel (iwSymbolSet A (periodize φ)) j‖ * ‖f (y - j)‖ :=
        tsum_congr (fun j => norm_mul _ _)
    _ ≤ ∑' j : ℤ,
          ‖iwKernel (iwSymbolSet A (periodize φ)) j‖ * Real.sqrt (∑' j : ℤ, ‖f j‖ ^ 2) :=
        Summable.tsum_le_tsum (fun j => mul_le_mul_of_nonneg_left (hR (y - j)) (norm_nonneg _))
          hprodSum (hkerSum.mul_right (Real.sqrt (∑' j : ℤ, ‖f j‖ ^ 2)))
    _ = (∑' j : ℤ, ‖iwKernel (iwSymbolSet A (periodize φ)) j‖)
          * Real.sqrt (∑' j : ℤ, ‖f j‖ ^ 2) :=
        tsum_mul_right
    _ ≤ (∑' j : ℤ, W * ‖Work.KMTAreas.A7.kmtKernWeight j‖)
          * Real.sqrt (∑' j : ℤ, ‖f j‖ ^ 2) :=
        mul_le_mul_of_nonneg_right (Summable.tsum_le_tsum hker hkerSum hKw) (Real.sqrt_nonneg _)

end Work.KMTPlan.A6
