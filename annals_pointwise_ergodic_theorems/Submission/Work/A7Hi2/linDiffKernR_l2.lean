import Mathlib
import Submission.Work.A7Hi2.linDiffKernR_summable
import Submission.Work.A7Hi2.linDiffKernR_symbol
import Submission.Work.KMTPlan.A6.tsum_eLpNorm_sq_iwConv_le
import Submission.Port.Aesm

/-!
# The `ℓ²` bound for the linearised difference kernel of the real-scale dilation family

This module proves `Work.A7Hi2.linDiffKernR_l2`.

The mathematical content is a **Fourier multiplier bound on `ℤ`**: if `k : ℤ → ℂ` is an `ℓ¹`
sequence whose symbol `θ ↦ ∑'_j k_j e^{2πijθ}` is bounded by `C`, then the convolution operator
`T_k f = k ⋆ f` is bounded on `ℓ²(ℤ)` with norm at most `C`.  The proof is Plancherel:

* `k ∈ ℓ¹` makes the symbol series converge uniformly, defining the continuous symbol
  `kSymC : C(ℝ/ℤ, ℂ)`, whose Fourier coefficients are the `k_j` (`fourierCoeff_eq_of_eq_tsum`);
* the `ℓ²` multiplier with symbol `kSymC` (`IonescuWainger.multiplierOf`) has operator norm at
  most `‖kSymC‖_∞ ≤ C`, and acts on `ℤ` by convolution with `k`
  (`Work.KMTPlan.A6.multiplierOf_apply_eq_tsum`);
* `eLpNorm · 2 (count : Measure ℤ)` is the `ℓ²` norm of the corresponding element of `lp _ 2`.

The kernel `k = linDiffKernR K σ ρ U ω` is a finite signed sum of the difference kernels
`diffKernR K (σ n) (ρ n)`, each of which is `ℓ¹` because it is the difference of two sampled
dilations `bumpKernR K s` of a Schwartz function at real scales `s ≥ 1`
(`Work.A7Hi2.linDiffKernR_summable`).  Its symbol is the signed sum of the symbols `symDiffR`
(`Work.A7Hi2.linDiffKernR_symbol`), so the hypothesis `hsym` of `linDiffKernR_l2` — the "overlap"
bound for the symbols of the lacunary family — is exactly the hypothesis needed, and the constant
`A = max 1 Csym` works.
-/

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.A7Hi2

open MeasureTheory
open scoped ENNReal BigOperators

noncomputable section

open Work.Analysis.IonescuWainger

/-- **The `ℓ²` convolution bound from a bound on the symbol.**  Let `k : ℤ → ℂ` be an `ℓ¹`
sequence whose symbol `θ ↦ ∑'_j k j * e^{2πijθ}` is bounded by `C`.  Then convolution with `k` is
bounded on `ℓ²(ℤ)` with constant `C`. -/
theorem l2_conv_le_of_symbol_bound (k : ℤ → ℂ) (C : ℝ) (hC : 0 < C)
    (hk : Summable (fun j : ℤ => ‖k j‖))
    (hsym : ∀ θ : ℝ, ‖∑' j : ℤ, k j * Work.KMTAreas.ADev.chr j θ‖ ≤ C) :
    ∀ f : ℤ → ℂ, Summable f →
      MeasureTheory.eLpNorm (fun x : ℤ => ∑' y : ℤ, k (x - y) * f y) 2
          (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ)
        ≤ ENNReal.ofReal C * MeasureTheory.eLpNorm f 2
            (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ) := by
  intro f hf
  -- the symbol series converges uniformly
  have hsumC : Summable (fun j : ℤ =>
      k j • (fourier (T := 1) j : C(AddCircle (1 : ℝ), ℂ))) := by
    refine Summable.of_norm ?_
    have h : (fun j : ℤ => ‖k j • (fourier (T := 1) j : C(AddCircle (1 : ℝ), ℂ))‖)
        = fun j => ‖k j‖ := by
      funext j
      rw [norm_smul, fourier_norm, mul_one]
    rw [h]
    exact hk
  set kSymC : C(AddCircle (1 : ℝ), ℂ) := ∑' j : ℤ, k j • fourier (T := 1) j with hkSymC
  have hkSymC_apply : ∀ ξ : AddCircle (1 : ℝ),
      kSymC ξ = ∑' j : ℤ, k j * fourier (T := 1) j ξ := by
    intro ξ
    have h := (ContinuousLinearMap.hasSum (ContinuousMap.evalCLM ℂ ξ) hsumC.hasSum).tsum_eq
    simp only [ContinuousMap.evalCLM_apply] at h
    rw [hkSymC]
    exact h.symm
  -- the symbol is pointwise bounded by `C` and continuous
  have hbound : ∀ ξ : AddCircle (1 : ℝ), ‖kSymC ξ‖ ≤ C := by
    intro ξ
    rw [hkSymC_apply ξ]
    exact Work.KMTAreas.A7.norm_tsum_fourier_le k C hsym ξ
  have hcont : Continuous kSymC := map_continuous kSymC
  have hmm : MemLp kSymC ⊤ circleMeasure :=
    MemLp.of_bound hcont.aestronglyMeasurable C (ae_of_all _ hbound)
  have heLp : eLpNorm kSymC ⊤ circleMeasure ≤ ENNReal.ofReal C := by
    rw [eLpNorm_exponent_top (hf := by pw_aesm), eLpNormEssSup_eq_essSup_enorm]
    refine essSup_le_of_ae_le (ENNReal.ofReal C) (ae_of_all _ fun ξ => ?_)
    rw [ENNReal.ofReal, enorm_le_coe, ← NNReal.coe_le_coe, coe_nnnorm,
      Real.coe_toNNReal C hC.le]
    exact hbound ξ
  have hop : ‖multiplierOf kSymC hmm‖ ≤ C := norm_multiplierOf_le hmm hC.le heLp
  -- the multiplier acts by convolution with `k`
  have hg2 : Memℓp f 2 := Work.KMTAreas.A7.summable_memℓp_two hf
  have hconv : ⇑(multiplierOf kSymC hmm (⟨f, hg2⟩ : L2Z))
      = fun n : ℤ => ∑' j : ℤ, k j * f (n - j) := by
    funext n
    rw [Work.KMTPlan.A6.multiplierOf_apply_eq_tsum kSymC hmm (⟨f, hg2⟩ : L2Z) n]
    refine tsum_congr fun j => ?_
    rw [Work.KMTAreas.A7.fourierCoeff_eq_of_eq_tsum k hk kSymC (fun ξ => hkSymC_apply ξ) j]
  have hmem : Memℓp (fun n : ℤ => ∑' j : ℤ, k j * f (n - j)) 2 :=
    hconv ▸ (multiplierOf kSymC hmm (⟨f, hg2⟩ : L2Z)).property
  have hflip : (fun x : ℤ => ∑' y : ℤ, k (x - y) * f y)
      = fun n : ℤ => ∑' j : ℤ, k j * f (n - j) := by
    funext x
    exact Work.KMTAreas.A7.tsum_conv_flip_lattice k f x
  have e2 : (⟨fun n : ℤ => ∑' j : ℤ, k j * f (n - j), hmem⟩
        : lp (fun _ : ℤ => ℂ) 2)
      = multiplierOf kSymC hmm (⟨f, hg2⟩ : L2Z) := Subtype.ext hconv.symm
  rw [hflip, Work.Analysis.IWMultiplier.eLpNorm_two_count_eq_ofReal_lpNorm _ hmem, e2,
    Work.Analysis.IWMultiplier.eLpNorm_two_count_eq_ofReal_lpNorm f hg2]
  calc ENNReal.ofReal ‖multiplierOf kSymC hmm (⟨f, hg2⟩ : L2Z)‖
      ≤ ENNReal.ofReal (C * ‖(⟨f, hg2⟩ : L2Z)‖) := by
        refine ENNReal.ofReal_le_ofReal ?_
        calc ‖multiplierOf kSymC hmm (⟨f, hg2⟩ : L2Z)‖
            ≤ ‖multiplierOf kSymC hmm‖ * ‖(⟨f, hg2⟩ : L2Z)‖ :=
              ContinuousLinearMap.le_opNorm _ _
          _ ≤ C * ‖(⟨f, hg2⟩ : L2Z)‖ := by gcongr
    _ = ENNReal.ofReal C * ENNReal.ofReal ‖(⟨f, hg2⟩ : L2Z)‖ := ENNReal.ofReal_mul hC.le

theorem linDiffKernR_l2 (K : SchwartzMap ℝ ℂ) (Csym : ℝ) (hCsym : 0 < Csym)
    (hsym : ∀ (σ ρ : ℕ → ℝ), (∀ n, 1 ≤ σ n) → (∀ n, 2 * σ n ≤ σ (n + 1)) →
      (∀ n, 1 ≤ ρ n) → (∀ n, 2 * ρ n ≤ ρ (n + 1)) →
      (∀ n, ρ n ≤ σ n ∧ σ n ≤ 2 * ρ n) → ∀ (U : Finset ℕ) (θ : ℝ),
      ∑ n ∈ U, ‖symDiffR K (σ n) (ρ n) θ‖ ≤ Csym) :
    ∃ A : ℝ, 0 < A ∧ ∀ (σ ρ : ℕ → ℝ), (∀ n, 1 ≤ σ n) → (∀ n, 2 * σ n ≤ σ (n + 1)) →
      (∀ n, 1 ≤ ρ n) → (∀ n, 2 * ρ n ≤ ρ (n + 1)) →
      (∀ n, ρ n ≤ σ n ∧ σ n ≤ 2 * ρ n) → ∀ (U : Finset ℕ) (ω : ℕ → Bool) (f : ℤ → ℂ),
      Summable f →
      MeasureTheory.eLpNorm (fun x : ℤ => ∑' y : ℤ, linDiffKernR K σ ρ U ω (x - y) * f y)
          2 (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ)
        ≤ ENNReal.ofReal A * MeasureTheory.eLpNorm f 2
            (MeasureTheory.Measure.count : MeasureTheory.Measure ℤ) := by
  refine ⟨max 1 Csym, lt_max_iff.mpr (Or.inl zero_lt_one), ?_⟩
  intro σ ρ hσ1 hσ2 hρ1 hρ2 hcomp U ω f hf
  have hk : Summable (fun j : ℤ => ‖linDiffKernR K σ ρ U ω j‖) :=
    linDiffKernR_summable K σ ρ hσ1 hρ1 U ω
  have hsym' : ∀ θ : ℝ,
      ‖∑' j : ℤ, linDiffKernR K σ ρ U ω j * Work.KMTAreas.ADev.chr j θ‖ ≤ Csym := by
    intro θ
    rw [linDiffKernR_symbol K σ ρ hσ1 hρ1 U ω θ]
    calc ‖∑ n ∈ U, Work.KMTAreas.ADev.bSign ω n * symDiffR K (σ n) (ρ n) θ‖
        ≤ ∑ n ∈ U, ‖Work.KMTAreas.ADev.bSign ω n * symDiffR K (σ n) (ρ n) θ‖ :=
          norm_sum_le _ _
      _ = ∑ n ∈ U, ‖symDiffR K (σ n) (ρ n) θ‖ := by
          refine Finset.sum_congr rfl fun n _ => ?_
          rw [norm_mul, Work.KMTAreas.ADev.norm_bSign, one_mul]
      _ ≤ Csym := hsym σ ρ hσ1 hσ2 hρ1 hρ2 hcomp U θ
  have hCsym' : 0 < max 1 Csym := lt_max_iff.mpr (Or.inl zero_lt_one)
  refine (l2_conv_le_of_symbol_bound (linDiffKernR K σ ρ U ω) Csym hCsym hk hsym' f hf).trans ?_
  exact mul_le_mul_of_nonneg_right (ENNReal.ofReal_le_ofReal (le_max_right 1 Csym))
    (by positivity)

end

end Work.A7Hi2
