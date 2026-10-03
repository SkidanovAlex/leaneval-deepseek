/-
# `‖T^{≤l}_{φ_{N,t}} f‖_{ℓ^∞}` is bounded uniformly in `t ∈ [1/2,1]` (KMT §6)

For the modulated Ionescu--Wainger bump `φ_{N,t}(ξ) = φ_N(ξ) · e(Ntξ)` (`varphiNt N k t`) at the
*fixed* scales `N, k`, the operator `T^{≤l}_{φ_{N,t}}` is bounded on `ℓ^∞(ℤ)`, with a bound that is
uniform over `t ∈ [1/2,1]`: `∃ C, ∀ t ∈ [1/2,1], ∀ y, ‖Tle ρ l (varphiNt N k t) f y‖ ≤ C`
whenever `‖f‖_∞ ≤ Cf`.

The proof has three parts, all of them "kernel `ℓ¹`" estimates:

* `iwKernel_decay_of_bump`: for a `C²` compactly supported `F : ℝ → ℂ` and any finite set `A` of
  circle frequencies, the kernel `j ↦ iwKernel (iwSymbolSet A (periodize F)) j` decays like
  `j^{-2}`, with the explicit constant `4 · (card A · S) + 1` where `S` bounds `‖F‖₁` and
  `‖F´´‖₁`.  This combines the Poisson-summation identity
  `Work.KMTPlan.A6.iwKernel_periodize_fourier` (the kernel is `𝓕 G` at `j`, for
  `G = ∑_{α∈A} F(· - a_α)`), the explicit quadratic Fourier decay
  `Work.KMTAreas.A7.FourierDecayExplicit`, and the two (already proved, general) `L¹` bounds
  `Work.KMTAreas.A7.integral_norm_sum_kmtTransl_le` and
  `…integral_norm_iteratedDeriv_sum_kmtTransl_le`.
* `Work.KMTAreas.A7.varphiNt_bounds` (a companion module): `φ_{N,t}` is `C²` with compact support
  and `‖φ_{N,t}‖₁`, `‖φ_{N,t}´´‖₁` are bounded uniformly on `t ∈ [1/2,1]`.
* the assembly below: the kernel dominates the operator by `(∑_j ‖κ_j‖) · ‖f‖_∞`, and the
  majorant `∑_j (4 (card A) S + 1)/(1+|j|)²` converges.
-/
import Mathlib
import Submission.Work.KMTAreas.A7.KmtKernelL1Uniform
import Submission.Work.KMTPlan.A6.iwKernel_periodize_fourier
import Submission.Work.KMTAreas.A7.varphiNt_bounds

set_option maxHeartbeats 1000000

namespace Work.KMTAreas.A7

noncomputable section

open MeasureTheory Finset Filter Topology
open scoped ENNReal NNReal BigOperators FourierTransform
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems
open Work.Analysis.IonescuWainger Work.Analysis.IWMultiplier

/-! ## Helpers -/

/-- A function with compact support on `ℝ` vanishes beyond some radius. -/
theorem exists_abs_le_of_hasCompactSupport {ψ : ℝ → ℂ} (hs : HasCompactSupport ψ) :
    ∃ R : ℝ, ∀ y : ℝ, R ≤ |y| → ψ y = 0 := by
  obtain ⟨K, hK, hK0⟩ := (exists_compact_iff_hasCompactSupport (f := ψ)).mpr hs
  obtain ⟨r, hr⟩ := (Metric.isBounded_iff_subset_closedBall (0 : ℝ)).mp hK.isBounded
  refine ⟨r + 1, fun y hy => hK0 y fun hyK => ?_⟩
  have hyr : |y| ≤ r := by
    have h := hr hyK
    rwa [Metric.mem_closedBall, Real.dist_eq, sub_zero] at h
  linarith

/-- A bounded sequence times an `ℓ¹` kernel is summable. -/
private theorem summable_mul_of_bounded {κ z : ℤ → ℂ} {B : ℝ}
    (hκ : Summable fun j : ℤ => ‖κ j‖) (hz : ∀ j : ℤ, ‖z j‖ ≤ B) :
    Summable fun j : ℤ => κ j * z j := by
  refine Summable.of_norm_bounded (f := fun j : ℤ => κ j * z j)
    (g := fun j : ℤ => max B 0 * ‖κ j‖) (hκ.mul_left (max B 0)) (fun j => ?_)
  rw [norm_mul]
  calc ‖κ j‖ * ‖z j‖ ≤ ‖κ j‖ * max B 0 :=
        mul_le_mul_of_nonneg_left ((hz j).trans (le_max_left _ _)) (norm_nonneg _)
    _ = max B 0 * ‖κ j‖ := by ring

/-! ## Quadratic decay of the IW kernel of a compactly supported `C²` bump -/

/-- **Quadratic decay of the kernel of the Ionescu--Wainger symbol of a bump.**  For a `C²`
function `F : ℝ → ℂ` with compact support and any finite set `A` of circle frequencies, the
kernel `iwKernel (iwSymbolSet A (periodize F)) ·` is bounded by `4 · (card A · S) + 1` times the
comparison weight `kmtKernWeight`, where `S` bounds both `∫‖F‖` and `∫‖F´´‖`. -/
theorem iwKernel_decay_of_bump (A : Finset Work.Analysis.IonescuWainger.Circle) {F : ℝ → ℂ}
    (hFcd : ContDiff ℝ 2 F) (hFcs : HasCompactSupport F) {S : ℝ} (hSnn : 0 ≤ S)
    (h1 : (∫ y, ‖F y‖) ≤ S) (h2 : (∫ y, ‖iteratedDeriv 2 F y‖) ≤ S) :
    ∀ j : ℤ, ‖iwKernel (iwSymbolSet A (periodize F)) j‖
      ≤ (4 * ((A.card : ℝ) * S) + 1) * ‖kmtKernWeight j‖ := by
  -- The function `G` whose Fourier transform is the kernel.
  set G : ℝ → ℂ :=
    fun y => ∑ α ∈ A, F (y - (AddCircle.equivIco (1 : ℝ) 0 α).val) with hGdef
  have hGcd : ContDiff ℝ 2 G := by
    rw [hGdef]
    exact ContDiff.sum (fun α _ => hFcd.comp (contDiff_id.sub contDiff_const))
  -- A radius outside which `F` vanishes, and the corresponding bound for `G`.
  obtain ⟨R, hR⟩ := exists_abs_le_of_hasCompactSupport hFcs
  have hGzero : ∀ y : ℝ, R + 1 ≤ |y| → G y = 0 := by
    rw [hGdef]; intro y hy
    refine Finset.sum_eq_zero (fun α _ => hR _ ?_)
    have h1 : |(AddCircle.equivIco (1 : ℝ) 0 α).val| ≤ 1 := abs_kmtFreqRep_le_one α
    have h2 : |y| - |(AddCircle.equivIco (1 : ℝ) 0 α).val| ≤
        |y - (AddCircle.equivIco (1 : ℝ) 0 α).val| := abs_sub_abs_le_abs_sub y _
    linarith
  have hGcs : HasCompactSupport G := by
    refine HasCompactSupport.of_support_subset_isCompact
      (K := Set.Icc (-(R + 1)) (R + 1)) isCompact_Icc ?_
    intro y hy
    have h : ¬ (R + 1 ≤ |y|) := fun hh => hy (hGzero y hh)
    rw [not_le, abs_lt] at h
    exact ⟨le_of_lt h.1, le_of_lt h.2⟩
  -- The two `L¹` bounds and the explicit decay of `𝓕 G`.
  have hInt1 : (∫ y, ‖G y‖) ≤ (A.card : ℝ) * ∫ y, ‖F y‖ :=
    integral_norm_sum_kmtTransl_le A F hFcd.continuous hFcs
  have hInt2 : (∫ y, ‖iteratedDeriv 2 G y‖) ≤ (A.card : ℝ) * ∫ y, ‖iteratedDeriv 2 F y‖ :=
    integral_norm_iteratedDeriv_sum_kmtTransl_le A F hFcd hFcs
  have hmax : max (∫ y, ‖G y‖) (∫ y, ‖iteratedDeriv 2 G y‖) ≤ (A.card : ℝ) * S := by
    refine max_le ?_ ?_
    · exact le_trans hInt1 (mul_le_mul_of_nonneg_left h1 (Nat.cast_nonneg _))
    · exact le_trans hInt2 (mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg _))
  have hdec := FourierDecayExplicit hGcd hGcs
  intro j
  have hstep : ‖FourierTransform.fourier G (j : ℝ)‖
      ≤ (4 * ((A.card : ℝ) * S) + 1) * ‖kmtKernWeight j‖ := by
    have hpos : (0 : ℝ) < (1 + |(j : ℝ)|) ^ 2 := by positivity
    have h1 : ‖FourierTransform.fourier G (j : ℝ)‖ * (1 + |(j : ℝ)|) ^ 2
        ≤ 4 * ((A.card : ℝ) * S) + 1 := by
      have h := hdec (j : ℝ)
      rw [le_div_iff₀ hpos] at h
      exact h.trans (by nlinarith [hmax])
    rw [norm_kmtKernWeight j, mul_one_div]
    exact (le_div_iff₀ hpos).mpr h1
  rwa [Work.KMTPlan.A6.iwKernel_periodize_fourier A hFcd.continuous hFcs j]

/-! ## The `ℓ^∞` bound for the IW projection of the modulated bump -/

/-- The assembly step: the uniform-in-`t` hypotheses supplied by `Work.KMTAreas.A7.varphiNt_bounds`
give the `ℓ^∞` bound for `Tle ρ l (varphiNt N k t)`. -/
theorem Tle_varphiNt_bounded_of_bounds (ρ : ℝ) (l : ℕ) (N k : ℕ) (f : ℤ → ℂ) (Cf : ℝ)
    (hf : ∀ y : ℤ, ‖f y‖ ≤ Cf) {S : ℝ} (hSnn : 0 ≤ S)
    (hB : ∀ t ∈ Set.Icc (1/2 : ℝ) 1,
      ContDiff ℝ 2 (fun ξ => varphiNt N k t ξ) ∧
      HasCompactSupport (fun ξ => varphiNt N k t ξ) ∧
      (∫ y, ‖varphiNt N k t y‖) ≤ S ∧
      (∫ y, ‖iteratedDeriv 2 (fun ξ => varphiNt N k t ξ) y‖) ≤ S) :
    ∃ C : ℝ, ∀ t ∈ Set.Icc (1/2 : ℝ) 1, ∀ y : ℤ,
      ‖Tle ρ l (varphiNt N k t) f y‖ ≤ C := by
  classical
  have hCfnn : 0 ≤ Cf := le_trans (norm_nonneg (f 0)) (hf 0)
  set A : Finset Work.Analysis.IonescuWainger.Circle := iwArithFreqs ρ l with hA
  set C₀ : ℝ := 4 * ((A.card : ℝ) * S) + 1 with hC₀
  have hC₀nn : 0 ≤ C₀ := by rw [hC₀]; positivity
  -- The kernel decay, uniformly in `t`.
  have hdec : ∀ t ∈ Set.Icc (1/2 : ℝ) 1, ∀ j : ℤ,
      ‖iwKernel (iwSymbolSet A (periodize (varphiNt N k t))) j‖
        ≤ C₀ * ‖kmtKernWeight j‖ := by
    intro t ht j
    obtain ⟨hcd, hcs, h1, h2⟩ := hB t ht
    exact iwKernel_decay_of_bump A hcd hcs hSnn h1 h2 j
  refine ⟨(∑' j : ℤ, C₀ * ‖kmtKernWeight j‖ * Cf) + 1, ?_⟩
  intro t ht y
  have hκ : Summable (fun j : ℤ =>
      ‖iwKernel (iwSymbolSet A (periodize (varphiNt N k t))) j‖) :=
    Summable.of_nonneg_of_le (fun j => norm_nonneg _) (fun j => hdec t ht j)
      (summable_kmtKernWeight.mul_left C₀)
  have hsum : Summable (fun j : ℤ =>
      iwKernel (iwSymbolSet A (periodize (varphiNt N k t))) j * f (y - j)) :=
    summable_mul_of_bounded hκ (fun j => hf _)
  have hsum2 : Summable (fun j : ℤ =>
      ‖iwKernel (iwSymbolSet A (periodize (varphiNt N k t))) j‖ * ‖f (y - j)‖) :=
    Summable.of_nonneg_of_le (fun j => mul_nonneg (norm_nonneg _) (norm_nonneg _))
      (fun j => mul_le_mul_of_nonneg_left ((hf (y - j)).trans (le_max_left _ _)) (norm_nonneg _))
      (hκ.mul_right (max Cf 0))
  rw [Tle_apply]
  calc ‖∑' j : ℤ, iwKernel (iwSymbolSet A (periodize (varphiNt N k t))) j * f (y - j)‖
      ≤ ∑' j : ℤ, ‖iwKernel (iwSymbolSet A (periodize (varphiNt N k t))) j * f (y - j)‖ :=
        norm_tsum_le_tsum_norm hsum.norm
    _ = ∑' j : ℤ,
          ‖iwKernel (iwSymbolSet A (periodize (varphiNt N k t))) j‖ * ‖f (y - j)‖ :=
        tsum_congr (fun j => norm_mul _ _)
    _ ≤ ∑' j : ℤ, C₀ * ‖kmtKernWeight j‖ * Cf := by
        refine Summable.tsum_le_tsum (fun j => ?_) hsum2
          ((summable_kmtKernWeight.mul_left C₀).mul_right Cf)
        exact mul_le_mul (hdec t ht j) (hf (y - j)) (norm_nonneg _)
          (mul_nonneg hC₀nn (norm_nonneg _))
    _ ≤ (∑' j : ℤ, C₀ * ‖kmtKernWeight j‖ * Cf) + 1 := le_add_of_nonneg_right zero_le_one

/-! ## The target -/

theorem Tle_varphiNt_bounded (ρ : ℝ) (l : ℕ) (N k : ℕ) (f : ℤ → ℂ) (Cf : ℝ)
    (hf : ∀ y : ℤ, ‖f y‖ ≤ Cf) :
    ∃ C : ℝ, ∀ t ∈ Set.Icc (1/2 : ℝ) 1, ∀ y : ℤ,
      ‖Work.KMTAreas.A7.Tle ρ l (Work.KMTAreas.A7.varphiNt N k t) f y‖ ≤ C := by
  obtain ⟨R, S, hSnn, hB⟩ := varphiNt_bounds N k
  exact Tle_varphiNt_bounded_of_bounds ρ l N k f Cf hf hSnn
    (fun t ht => ⟨(hB t ht).2.1, (hB t ht).2.2.1, (hB t ht).2.2.2.1, (hB t ht).2.2.2.2⟩)

end

end Work.KMTAreas.A7
