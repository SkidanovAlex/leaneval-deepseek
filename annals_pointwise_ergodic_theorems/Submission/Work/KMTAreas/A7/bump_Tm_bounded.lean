/-
# Pointwise boundedness of the exact-height IW multipliers `Tm` on the small-scale bumps

The small-scale §7 assembly of area `A7` uses the two *concrete* bump families of the model tuple,

  `smallSymbF ρ C₀ a l₁ l₂ k₁ k₂ t`  (`f`-side: the modulated bump `φ_{N,t} = varphiNt N k₁ t`),
  `smallSymbG ρ P C₀ a l₁ l₂ k₁ k₂ t` (`g`-side: the modulated bump `φ̃_{N,t} = varphitildeNt P d N k₂ t`),

both of which are *either* `0` (at index `0` and off the small-scale condition `smallCond`)
*or* one of the bumps.  This module proves that the exact-height Ionescu--Wainger multiplier

  `Tm ρ l φ f = iwConv (A_l \ A_{l-1}) (periodize φ) f`

applied to such a bump and to a merely *bounded* sequence `f : ℤ → ℂ` is again bounded
(`Work.KMTAreas.A7.bump_Tm_bounded`).  Boundedness on `ℓ^∞` is exactly what the Rademacher--Menshov
step needs from the two columns of the tuple: the variational norm of a family is estimated from
the pointwise (hence `ℓ^∞`) control of the individual pieces.

## Proof

`Tm ρ l φ` is the convolution with the kernel `j ↦ iwKernel (iwSymbolSet (diffFreqs ρ l) (periodize φ)) j`,
so it suffices to bound that kernel in `ℓ¹(ℤ)`:

* **`g`-side** (`Tm_varphitildeNt_bounded`): the arithmetic-character factorisation of
  `Work.KMTPlan.A6.IwKernelArithChar` writes the kernel as
  `(∑_{α ∈ diffFreqs ρ l} e(-jα)) · cw φ j`, with `‖∑_{α∈A} e(-jα)‖ ≤ A.card`; the modulation rule
  `fourier_varphitildeNt_eq` shifts `cw φ j = 𝓕 φ j` to `𝓕 (varphitildeN d N k₂) (j - PevalR P (N t))`,
  `fourierDecay_varphitildeN` gives quadratic decay at the shifted frequency, `abs_PevalR_mul_le`
  bounds the shift uniformly for `t ∈ [1/2,1]`, and `one_div_sq_le_of_abs_sub_le` moves the decay
  back to `j`.
* **`f`-side** (`Tm_varphiNt_bounded`): the `C²`-with-compact-support bump bounds
  `varphiNt_bounds` (`∫‖φ_{N,t}‖`, `∫‖φ_{N,t}''‖ ≤ S`, `S` independent of `t`) feed
  `iwKernel_decay_of_bump`, which gives `‖κ_j‖ ≤ (4 · card A · S + 1) / (1 + |j|)²`.

In both cases `norm_tsum_kernel_mul_le` (the `ℓ¹`-implies-`ℓ^∞` step, stated for an arbitrary
finite set of frequencies) finishes: `‖Tm ρ l φ f‖_∞ ≤ C_κ · ∑_j (1 + |j|)^{-2} · ‖f‖_∞`.

The case analysis over `smallSymbF = 0` / `= varphiNt …` and `smallSymbG = 0` / `= varphitildeNt …`
is the assembly; `smallSymbF_zero`, `smallSymbG_zero` and `Tm_zero` (the zero symbol gives the zero
sequence) handle the vanishing cases.
-/
import Mathlib
import Submission.Work.KMTAreas.A7.SmallModelDefs
import Submission.Work.KMTAreas.A7.FpieceEqTm
import Submission.Work.KMTAreas.A7.Tle_varphiNt_bounded
import Submission.Work.KMTAreas.A7.Tle_varphitildeNt_bounded

set_option maxHeartbeats 1000000

namespace Work.KMTAreas.A7

noncomputable section

open MeasureTheory Polynomial Finset Filter Topology
open scoped ENNReal NNReal BigOperators FourierTransform
open PointwiseErgodicTheorems Submission.PointwiseErgodicTheorems
open Work.Analysis.IonescuWainger Work.Analysis.IWMultiplier

/-! ## §1.  Two elementary facts -/

/-- The modulus of a sum of characters is bounded by the number of frequencies. -/
lemma norm_sum_fourier_le_card (A : Finset Work.Analysis.IonescuWainger.Circle) (y : ℤ) :
    ‖∑ α ∈ A, fourier (T := 1) y α‖ ≤ (A.card : ℝ) := by
  calc ‖∑ α ∈ A, fourier (T := 1) y α‖ ≤ ∑ α ∈ A, ‖fourier (T := 1) y α‖ := norm_sum_le _ _
    _ = ∑ _α ∈ A, (1 : ℝ) := by
        refine Finset.sum_congr rfl (fun α _ => ?_)
        rw [fourier_apply]
        exact _root_.Circle.norm_coe _
    _ = (A.card : ℝ) := by simp

/-- The exact-height multiplier of the zero symbol is the zero operator. -/
lemma Tm_zero (ρ : ℝ) (l : ℕ) (f : ℤ → ℂ) : Tm ρ l (0 : ℝ → ℂ) f = 0 := by
  funext y
  simp only [Tm, iwConv_apply, Pi.zero_apply]
  simp [iwKernel, fourierCoeff, periodize]

/-! ## §2.  The `ℓ^∞` bounds for the two bump families -/

/-- **The `f`-side bump**: for a bounded sequence `f`, the exact-height IW multiplier with the
modulated bump `φ_{N,t}` as symbol is bounded, uniformly in `t ∈ [1/2,1]`. -/
theorem Tm_varphiNt_bounded (ρ : ℝ) (l N k₁ : ℕ) (f : ℤ → ℂ) (Cf : ℝ)
    (hf : ∀ y : ℤ, ‖f y‖ ≤ Cf) :
    ∃ C : ℝ, ∀ t ∈ Set.Icc (1/2 : ℝ) 1, ∀ y : ℤ,
      ‖Tm ρ l (varphiNt N k₁ t) f y‖ ≤ C := by
  classical
  obtain ⟨R, S, hSnn, hB⟩ := varphiNt_bounds N k₁
  set Cκ : ℝ := 4 * (((diffFreqs ρ l).card : ℝ) * S) + 1 with hCκdef
  refine ⟨(Cκ * (∑' j : ℤ, 1 / (1 + |(j : ℝ)|) ^ 2)) * max Cf 0, fun t ht y => ?_⟩
  have hdec : ∀ j : ℤ,
      ‖iwKernel (iwSymbolSet (diffFreqs ρ l) (periodize (varphiNt N k₁ t))) j‖
        ≤ Cκ / (1 + |(j : ℝ)|) ^ 2 := by
    intro j
    have h := iwKernel_decay_of_bump (diffFreqs ρ l) (hB t ht).2.1 (hB t ht).2.2.1 hSnn
      (hB t ht).2.2.2.1 (hB t ht).2.2.2.2 j
    rw [norm_kmtKernWeight j] at h
    rw [hCκdef, div_eq_mul_one_div]
    exact h
  have hmain := norm_tsum_kernel_mul_le hdec hf y
  rw [Tm, iwConv_apply]
  simp only [smul_eq_mul]
  exact hmain

/-- **The `g`-side bump**: for a bounded sequence `g`, the exact-height IW multiplier with the
modulated bump `φ̃_{N,t}` as symbol is bounded, uniformly in `t ∈ [1/2,1]`. -/
theorem Tm_varphitildeNt_bounded (P : Polynomial ℤ) (ρ : ℝ) (l d N k₂ : ℕ) (g : ℤ → ℂ) (Cg : ℝ)
    (hg : ∀ y : ℤ, ‖g y‖ ≤ Cg) :
    ∃ C : ℝ, ∀ t ∈ Set.Icc (1/2 : ℝ) 1, ∀ y : ℤ,
      ‖Tm ρ l (varphitildeNt P d N k₂ t) g y‖ ≤ C := by
  classical
  obtain ⟨Cf, hCfpos, hCfdec⟩ := fourierDecay_varphitildeN d N k₂
  set Mv : ℝ := max 1 ((∑ i ∈ Finset.range (P.natDegree + 1), |(P.coeff i : ℝ)|) *
    (1 + (N : ℝ)) ^ P.natDegree) with hMv
  set K : ℝ := (2 * Mv + 1) ^ 2 with hK
  have hMnonneg : 0 ≤ Mv := le_trans zero_le_one (le_max_left 1 _)
  refine ⟨(((diffFreqs ρ l).card : ℝ) * Cf * K) *
      (∑' j : ℤ, 1 / (1 + |(j : ℝ)|) ^ 2) * max Cg 0, fun t ht y => ?_⟩
  have ht1 : |t| ≤ 1 := by
    obtain ⟨h1, h2⟩ := ht
    rw [abs_le]
    exact ⟨by linarith, h2⟩
  have hc : |PevalR P ((N : ℝ) * t)| ≤ Mv :=
    le_trans (abs_PevalR_mul_le P N ht1) (le_max_right 1 _)
  have hdec : ∀ j : ℤ,
      ‖iwKernel (iwSymbolSet (diffFreqs ρ l) (periodize (varphitildeNt P d N k₂ t))) j‖
        ≤ (((diffFreqs ρ l).card : ℝ) * Cf * K) / (1 + |(j : ℝ)|) ^ 2 := by
    intro j
    rw [Work.KMTPlan.A6.IwKernelArithChar (diffFreqs ρ l)
      (integrable_varphitildeNt_aux P d N k₂ t) j, cw_eq_fourierTransform]
    rw [fourier_varphitildeNt_eq P d N k₂ t (j : ℝ)]
    have h1 : ‖∑ α ∈ diffFreqs ρ l, fourier (T := 1) (-j) α‖ ≤ ((diffFreqs ρ l).card : ℝ) :=
      norm_sum_fourier_le_card _ (-j)
    have h2 : ‖FourierTransform.fourier (varphitildeN d N k₂)
          ((j : ℝ) - PevalR P ((N : ℝ) * t))‖ ≤ Cf * K / (1 + |(j : ℝ)|) ^ 2 := by
      refine le_trans (hCfdec _) ?_
      have hmaj := one_div_sq_le_of_abs_sub_le hMnonneg hc j
      calc Cf / (1 + |(j : ℝ) - PevalR P ((N : ℝ) * t)|) ^ 2
          = Cf * (1 / (1 + |(j : ℝ) - PevalR P ((N : ℝ) * t)|) ^ 2) := div_eq_mul_one_div _ _
        _ ≤ Cf * (K / (1 + |(j : ℝ)|) ^ 2) := by
            refine mul_le_mul_of_nonneg_left ?_ hCfpos.le
            rw [hK]
            exact hmaj
        _ = Cf * K / (1 + |(j : ℝ)|) ^ 2 := (mul_div_assoc _ _ _).symm
    calc ‖(∑ α ∈ diffFreqs ρ l, fourier (T := 1) (-j) α) *
            FourierTransform.fourier (varphitildeN d N k₂)
              ((j : ℝ) - PevalR P ((N : ℝ) * t))‖
        = ‖∑ α ∈ diffFreqs ρ l, fourier (T := 1) (-j) α‖ *
            ‖FourierTransform.fourier (varphitildeN d N k₂)
              ((j : ℝ) - PevalR P ((N : ℝ) * t))‖ := norm_mul _ _
      _ ≤ ((diffFreqs ρ l).card : ℝ) * (Cf * K / (1 + |(j : ℝ)|) ^ 2) :=
          mul_le_mul h1 h2 (norm_nonneg _) (Nat.cast_nonneg _)
      _ = (((diffFreqs ρ l).card : ℝ) * Cf * K) / (1 + |(j : ℝ)|) ^ 2 := by ring
  have hmain := norm_tsum_kernel_mul_le hdec hg y
  rw [Tm, iwConv_apply]
  simp only [smul_eq_mul]
  exact hmain

/-! ## §3.  The target -/

theorem bump_Tm_bounded (P : Polynomial ℤ) (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ ≤ 1) (C₀ : ℕ)
    (a : ℕ → NNReal) (l₁ l₂ k₁ k₂ : ℕ) (t : ℝ) (ht : t ∈ Set.Icc ((1:ℝ)/2) 1) :
    (∀ (k l : ℕ) (f : ℤ → ℂ), (∃ Cf : ℝ, ∀ y : ℤ, ‖f y‖ ≤ Cf) →
        ∃ Cf' : ℝ, ∀ y : ℤ, ‖Work.KMTAreas.A7.Tm ρ l
          (Work.KMTAreas.A7.smallSymbF ρ C₀ a l₁ l₂ k₁ k₂ t k) f y‖ ≤ Cf') ∧
    (∀ (k l : ℕ) (g : ℤ → ℂ), (∃ Cg : ℝ, ∀ y : ℤ, ‖g y‖ ≤ Cg) →
        ∃ Cg' : ℝ, ∀ y : ℤ, ‖Work.KMTAreas.A7.Tm ρ l
          (Work.KMTAreas.A7.smallSymbG ρ P C₀ a l₁ l₂ k₁ k₂ t k) g y‖ ≤ Cg') := by
  classical
  refine ⟨?_, ?_⟩
  · intro k l f hf
    obtain ⟨Cf, hCf⟩ := hf
    by_cases hk : k = 0
    · have hsym : smallSymbF ρ C₀ a l₁ l₂ k₁ k₂ t k = 0 := by
        rw [hk]
        exact smallSymbF_zero ρ C₀ a l₁ l₂ k₁ k₂ t
      refine ⟨1, fun y => ?_⟩
      rw [hsym, Tm_zero]
      simp
    · by_cases hc : smallCond ρ C₀ a l₁ l₂ k₁ k₂ k
      · have hsym : smallSymbF ρ C₀ a l₁ l₂ k₁ k₂ t k = varphiNt (Nat.floor (a k)) k₁ t := by
          funext ξ
          show (if k = 0 then 0 else if smallCond ρ C₀ a l₁ l₂ k₁ k₂ k then
              varphiNt (Nat.floor (a k)) k₁ t ξ else 0) = varphiNt (Nat.floor (a k)) k₁ t ξ
          rw [if_neg hk, if_pos hc]
        rw [hsym]
        obtain ⟨C, hC⟩ := Tm_varphiNt_bounded ρ l (Nat.floor (a k)) k₁ f Cf hCf
        exact ⟨C, fun y => hC t ht y⟩
      · have hsym : smallSymbF ρ C₀ a l₁ l₂ k₁ k₂ t k = 0 := by
          funext ξ
          show (if k = 0 then 0 else if smallCond ρ C₀ a l₁ l₂ k₁ k₂ k then
              varphiNt (Nat.floor (a k)) k₁ t ξ else 0) = 0
          rw [if_neg hk, if_neg hc]
        refine ⟨1, fun y => ?_⟩
        rw [hsym, Tm_zero]
        simp
  · intro k l g hg
    obtain ⟨Cg, hCg⟩ := hg
    by_cases hk : k = 0
    · have hsym : smallSymbG ρ P C₀ a l₁ l₂ k₁ k₂ t k = 0 := by
        rw [hk]
        exact smallSymbG_zero ρ P C₀ a l₁ l₂ k₁ k₂ t
      refine ⟨1, fun y => ?_⟩
      rw [hsym, Tm_zero]
      simp
    · by_cases hc : smallCond ρ C₀ a l₁ l₂ k₁ k₂ k
      · have hsym : smallSymbG ρ P C₀ a l₁ l₂ k₁ k₂ t k =
            varphitildeNt P P.natDegree (Nat.floor (a k)) k₂ t := by
          funext ξ
          show (if k = 0 then 0 else if smallCond ρ C₀ a l₁ l₂ k₁ k₂ k then
              varphitildeNt P P.natDegree (Nat.floor (a k)) k₂ t ξ else 0) =
            varphitildeNt P P.natDegree (Nat.floor (a k)) k₂ t ξ
          rw [if_neg hk, if_pos hc]
        rw [hsym]
        obtain ⟨C, hC⟩ := Tm_varphitildeNt_bounded P ρ l P.natDegree (Nat.floor (a k)) k₂ g Cg hCg
        exact ⟨C, fun y => hC t ht y⟩
      · have hsym : smallSymbG ρ P C₀ a l₁ l₂ k₁ k₂ t k = 0 := by
          funext ξ
          show (if k = 0 then 0 else if smallCond ρ C₀ a l₁ l₂ k₁ k₂ k then
              varphitildeNt P P.natDegree (Nat.floor (a k)) k₂ t ξ else 0) = 0
          rw [if_neg hk, if_neg hc]
        refine ⟨1, fun y => ?_⟩
        rw [hsym, Tm_zero]
        simp

end

end Work.KMTAreas.A7
