import Mathlib
import Submission.Work.FIArea6Road.TauHeartDefs
import Submission.Work.FIArea6.S16FcoefSum
import Submission.Work.FIArea6Road.TauHeartFserEqQ
import Submission.Work.FIArea6Road.TauHeartArith
import Submission.Work.FIArea6.TauPieces.TsumHeartDefs
import Submission.Work.FIArea6Hecke.S16CoreDefs
import Submission.Work.FITop4.Bridge.area5_6_defs
import Submission.Work.FIArea6Hecke.S16CleanDefs
import Submission.Work.FIArea6Road.TailFreqLBound
import Submission.Work.FIArea6Road.TailLogNStep
import Submission.Work.FIArea6Road.TauHeartFcoefMass
import Submission.Work.FIArea6Road.TauHeartFcoefTailSub

set_option autoImplicit false
set_option maxHeartbeats 1600000

namespace Work.FIArea6Road

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section


/-! ## 1. Geometry of the §16 sector

Two elementary facts about the principal argument are used: the imaginary part of a Gaussian
integer is `√|z|²·sin(arg z)`, and the sector `[φ, φ+2πθ]` cut at `π` (or the sector hanging below
`−π`) has angular distance at most `2πθ` from the real axis. -/

/-- `|Im z| = √|z|²·|sin(arg z)|` for a Gaussian integer. -/
lemma abs_im_toComplex_eq (z : GaussianInt) :
    |((z.im : ℝ))| = Real.sqrt (Work.FIPlan.gnorm z : ℝ) *
      |Real.sin (Complex.arg z.toComplex)| := by
  have him : ‖z.toComplex‖ * Real.sin (Complex.arg z.toComplex) = (z.im : ℝ) := by
    have h := congrArg Complex.im (Complex.norm_mul_exp_arg_mul_I z.toComplex)
    rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
      Complex.exp_ofReal_mul_I_im] at h
    rw [Work.FIArea5.S16Hecke.norm_toComplex z] at h
    simpa using h
  rw [← him, abs_mul, abs_of_nonneg (norm_nonneg _), Work.FIArea5.S16Hecke.norm_toComplex z]

/-- A primary Gaussian integer is nonzero. -/
lemma isPrimary_ne_zero {z : GaussianInt} (hz : Work.FIPlan.IsPrimary z) : z ≠ 0 := by
  rintro rfl
  exact absurd hz.1 (by norm_num)

/-- **The sector `[φ, π]` is within `2πθ` of the positive real axis.** -/
lemma abs_sin_le_of_near_pi {α φ θ : ℝ} (h1 : φ ≤ α) (h2 : α ≤ Real.pi)
    (h3 : Real.pi - φ ≤ 2 * Real.pi * θ) :
    |Real.sin α| ≤ 2 * Real.pi * θ := by
  have h := Real.abs_sin_le_abs (x := Real.pi - α)
  have hπ : (0:ℝ) ≤ Real.pi - α := by linarith
  rw [abs_of_nonneg hπ] at h
  rw [(Real.sin_pi_sub α).symm]
  linarith

/-- **The sector `(−π, −π + 2πθ]` is within `2πθ` of the negative real axis.** -/
lemma abs_sin_le_of_near_neg_pi {α θ : ℝ} (h1 : -Real.pi < α)
    (h2 : α ≤ -Real.pi + 2 * Real.pi * θ) :
    |Real.sin α| ≤ 2 * Real.pi * θ := by
  have h := Real.abs_sin_le_abs (x := α + Real.pi)
  have hπ : (0:ℝ) ≤ α + Real.pi := by linarith
  rw [abs_of_nonneg hπ] at h
  have hsin : |Real.sin α| = |Real.sin (α + Real.pi)| := by
    rw [Real.sin_add_pi, abs_neg]
  rw [hsin]
  linarith

/-- **The `ℓ`-th Fourier mode of `(z/|z|)^j`** — the power identity behind (16.27). -/
lemma zpow_div_eq_exp (z : GaussianInt) (hne : z ≠ 0) (n : ℤ) :
    (z.toComplex / ((Real.sqrt (Work.FIPlan.gnorm z : ℝ)) : ℂ)) ^ n
      = Complex.exp ((n : ℂ) * Complex.I * ((Complex.arg z.toComplex : ℝ) : ℂ)) := by
  have hnc : z.toComplex ≠ 0 :=
    fun h => hne (GaussianInt.toComplex_injective (h.trans GaussianInt.toComplex_zero.symm))
  have hc : ((Real.sqrt (Work.FIPlan.gnorm z : ℝ)) : ℂ) ≠ 0 := by
    have h1 : (0 : ℝ) < Real.sqrt (Work.FIPlan.gnorm z : ℝ) := by
      rw [← Work.FIArea5.S16Hecke.norm_toComplex z]
      exact norm_pos_iff.mpr hnc
    exact_mod_cast ne_of_gt h1
  have hw : z.toComplex / ((Real.sqrt (Work.FIPlan.gnorm z : ℝ)) : ℂ)
      = Complex.exp (((Complex.arg z.toComplex : ℝ) : ℂ) * Complex.I) := by
    have h := Complex.norm_mul_exp_arg_mul_I z.toComplex
    rw [Work.FIArea5.S16Hecke.norm_toComplex z] at h
    rw [div_eq_iff hc]
    exact h.symm.trans (mul_comm _ _)
  rw [hw, ← Complex.exp_int_mul]
  congr 1
  ring

/-- **The `ℓ`-th Fourier mode of the §16 summand**: multiplying the `j`-th summand by
`e^{iℓ·arg z}` produces the `(j+ℓ)`-th summand. -/
lemma s16Core_mul_exp_eq (Pa : Work.FITop.Params) (j ℓ : ℤ) (chi : GaussianInt → ℂ)
    (p : ℝ → ℝ) {z : GaussianInt} (hz : Work.FIPlan.IsPrimary z) :
    Complex.exp ((ℓ : ℂ) * Complex.I * ((Complex.arg z.toComplex : ℝ) : ℂ))
        * s16Core Pa j chi p z
      = (p (Work.FIPlan.gnorm z) : ℂ) * (ArithmeticFunction.moebius (Work.FIPlan.gnorm z) : ℂ)
          * (Work.FIPlan.gammaTrunc Pa.C (Work.FIPlan.gnorm z) : ℂ)
          * Work.FIArea5.S16Hecke.psi chi (j + ℓ) z := by
  have hne : z ≠ 0 := isPrimary_ne_zero hz
  have h1 : (z.toComplex / ((Real.sqrt (Work.FIPlan.gnorm z : ℝ)) : ℂ)) ^ (j + ℓ)
      = Complex.exp ((ℓ : ℂ) * Complex.I * ((Complex.arg z.toComplex : ℝ) : ℂ))
        * (z.toComplex / ((Real.sqrt (Work.FIPlan.gnorm z : ℝ)) : ℂ)) ^ j := by
    rw [zpow_div_eq_exp z hne (j + ℓ), zpow_div_eq_exp z hne j, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  unfold Work.FIArea5.S16Hecke.psi s16Core
  rw [h1]
  ring

/-- **Interchange of a finite sum with an infinite series.** -/
lemma hasSum_finset_sum {ι : Type*} {M : Type*} [AddCommMonoid M] [TopologicalSpace M]
    [ContinuousAdd M] (s : Finset ι) (a : ι → M) (f : ι → ℤ → M)
    (h : ∀ i ∈ s, HasSum (f i) (a i)) :
    HasSum (fun ℓ : ℤ => ∑ i ∈ s, f i ℓ) (∑ i ∈ s, a i) := by
  classical
  induction s using Finset.induction with
  | empty => simpa using hasSum_zero (f := fun _ : ℤ => (0 : M))
  | insert i s hi ih =>
      have h1 : HasSum (f i) (a i) := h i (Finset.mem_insert_self i s)
      have h2 : HasSum (fun ℓ => ∑ x ∈ s, f x ℓ) (∑ x ∈ s, a x) :=
        ih (fun j hj => h j (Finset.mem_insert_of_mem hj))
      have h3 := h1.add h2
      simpa [Finset.sum_insert hi] using h3

lemma tsum_finset_sum {ι : Type*} {M : Type*} [AddCommMonoid M] [TopologicalSpace M]
    [ContinuousAdd M] [T2Space M] (s : Finset ι) (a : ι → M) (f : ι → ℤ → M)
    (h : ∀ i ∈ s, HasSum (f i) (a i)) :
    (∑' ℓ : ℤ, ∑ i ∈ s, f i ℓ) = ∑ i ∈ s, a i :=
  (hasSum_finset_sum s a f h).tsum_eq

/-! ## 2. The trivial (no-cancellation) bound for the τ-restricted Hecke sum

The τ-restriction is a `0/1` weight, and `p`'s support confines the sum to the window
`⌊N⌋ < n ≤ ⌊(1+θ)N⌋`, so the whole sum is bounded by the window length times `4(Pa.τ)²`. -/

/-- `‖q̂(ℓ)‖` is summable over `ℤ` (the pointwise decay of `fcoef_bound`). -/
lemma summable_norm_fcoef (q : ℝ → ℝ) {θ : ℝ} (hθ : 0 < θ) (hθ1 : θ ≤ 1)
    (hqC : ContDiff ℝ 2 q) (hq0 : ∀ α, 0 ≤ q α) (hq1 : ∀ α, q α ≤ 1)
    (hqsupp : ∀ α, q α ≠ 0 → 0 ≤ α ∧ α ≤ 2 * Real.pi * θ)
    (hd2 : ∀ α, |iteratedDeriv 2 q α| ≤ 1048576 / θ ^ 2) :
    Summable (fun ℓ : ℤ => ‖Work.FIArea5.S16.fcoef q ℓ‖) :=
  Summable.of_nonneg_of_le
    (f := fun ℓ : ℤ => (1 / (2 * Real.pi)) * (10000000 * θ * (1 + (θ * (ℓ : ℝ)) ^ 2)⁻¹))
    (g := fun ℓ : ℤ => ‖Work.FIArea5.S16.fcoef q ℓ‖)
    (fun ℓ => norm_nonneg _)
    (fun ℓ => Work.FIArea5.S16.fcoef_bound q θ hθ hθ1 hqC hq0 hq1 hqsupp hd2 ℓ)
    (((Work.FIArea5.S16.int_summ θ hθ).mul_left (10000000 * θ)).mul_left (1 / (2 * Real.pi)))

/-! ## 3. The bad sectors contribute nothing (the axis pin)

In the cut case `φ > π − 2πθ` (and in the non-cut case with `φ < −π`) every point of the sector
lies within `2πθ` of a real axis, hence (for the τ- and `p`-supported `z`) inside the axis band
excluded by `IsAxisFree`; the axis pin then forces every summand to vanish. -/

/-! ## 4. The good case: the sector sum is the Fourier–Hecke series

When `−π ≤ φ ≤ π − 2πθ` the whole sector `[φ, φ + 2πθ]` sits inside the principal range, so the
argument `β_z = arg z − φ` of every summand lies in `(−2π + 2πθ, 2π]`, where the periodisation of
`q` agrees with `q` (`TauHeartFserEqQ`).  The axis clause is then redundant (axis pin), and the
finite box sum is exchanged with the Fourier series and regrouped by the norm. -/

/-- `‖e^{i nc}‖ = 1` for real `c`. -/
lemma norm_exp_int_mul_I (n : ℤ) (c : ℝ) : ‖Complex.exp ((n : ℂ) * Complex.I * (c : ℂ))‖ = 1 := by
  rw [show (n : ℂ) * Complex.I * (c : ℂ) = (((n : ℝ) * c : ℝ) : ℂ) * Complex.I by
    push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

/-! ## 5. The support window

`p`'s support confines every contributing norm to the window `⌊N⌋ < n ≤ ⌊(1+θ)N⌋`, whose length is
at most `3θN` (for `θN ≥ 1`) resp. `1` (for `θN < 1`). -/

lemma card_window_le_three (Pa : Work.FITop.Params) (h : 1 ≤ Pa.θ * Pa.N) :
    ((Finset.Icc (⌊Pa.N⌋₊ + 1) ⌊(1 + Pa.θ) * Pa.N⌋₊).card : ℝ) ≤ 3 * (Pa.θ * Pa.N) := by
  have hN0 : (0 : ℝ) ≤ Pa.N := by linarith [Pa.hN1]
  have hθN0 : (0 : ℝ) ≤ Pa.θ * Pa.N := mul_nonneg (le_of_lt Pa.hθ0) hN0
  have hpos : (0 : ℝ) ≤ (1 + Pa.θ) * Pa.N := by
    have h1 : (1 : ℝ) ≤ 1 + Pa.θ := by linarith [Pa.hθ0]
    exact mul_nonneg (by linarith) hN0
  have h2 : (1 + Pa.θ) * Pa.N < ((⌊Pa.N⌋₊ + ⌊Pa.θ * Pa.N⌋₊ + 2 : ℕ) : ℝ) := by
    have h3 : Pa.N < (⌊Pa.N⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one Pa.N
    have h4 : Pa.θ * Pa.N < (⌊Pa.θ * Pa.N⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
    rw [add_mul, one_mul]
    push_cast
    linarith
  have h2' : ⌊(1 + Pa.θ) * Pa.N⌋₊ < ⌊Pa.N⌋₊ + ⌊Pa.θ * Pa.N⌋₊ + 2 :=
    (Nat.floor_lt hpos (n := ⌊Pa.N⌋₊ + ⌊Pa.θ * Pa.N⌋₊ + 2)).mpr h2
  have hA : ⌊(1 + Pa.θ) * Pa.N⌋₊ ≤ ⌊Pa.θ * Pa.N⌋₊ + 1 + ⌊Pa.N⌋₊ := by omega
  have hsub : ⌊(1 + Pa.θ) * Pa.N⌋₊ - ⌊Pa.N⌋₊ ≤ ⌊Pa.θ * Pa.N⌋₊ + 1 := by
    calc ⌊(1 + Pa.θ) * Pa.N⌋₊ - ⌊Pa.N⌋₊
        ≤ (⌊Pa.θ * Pa.N⌋₊ + 1 + ⌊Pa.N⌋₊) - ⌊Pa.N⌋₊ := Nat.sub_le_sub_right hA _
      _ = ⌊Pa.θ * Pa.N⌋₊ + 1 := by omega
  have hcard : (Finset.Icc (⌊Pa.N⌋₊ + 1) ⌊(1 + Pa.θ) * Pa.N⌋₊).card
      = ⌊(1 + Pa.θ) * Pa.N⌋₊ - ⌊Pa.N⌋₊ := by
    rw [Nat.card_Icc]
    omega
  have h6 : ((⌊Pa.θ * Pa.N⌋₊ : ℕ) : ℝ) + 1 ≤ Pa.θ * Pa.N + 1 := by
    have := Nat.floor_le hθN0
    linarith
  have h7 : ((⌊(1 + Pa.θ) * Pa.N⌋₊ - ⌊Pa.N⌋₊ : ℕ) : ℝ)
      ≤ ((⌊Pa.θ * Pa.N⌋₊ + 1 : ℕ) : ℝ) := by
    exact_mod_cast hsub
  rw [hcard]
  push_cast at h7 ⊢
  linarith

lemma card_window_le_one (Pa : Work.FITop.Params) (h : Pa.θ * Pa.N < 1) :
    ((Finset.Icc (⌊Pa.N⌋₊ + 1) ⌊(1 + Pa.θ) * Pa.N⌋₊).card : ℝ) ≤ 1 := by
  have hN0 : (0 : ℝ) ≤ Pa.N := by linarith [Pa.hN1]
  have hpos : (0 : ℝ) ≤ (1 + Pa.θ) * Pa.N := by
    have h1 : (1 : ℝ) ≤ 1 + Pa.θ := by linarith [Pa.hθ0]
    exact mul_nonneg (by linarith) hN0
  have h2 : (1 + Pa.θ) * Pa.N < ((⌊Pa.N⌋₊ + 2 : ℕ) : ℝ) := by
    have h3 : Pa.N < (⌊Pa.N⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one Pa.N
    rw [add_mul, one_mul]
    push_cast
    linarith
  have h2' : ⌊(1 + Pa.θ) * Pa.N⌋₊ < ⌊Pa.N⌋₊ + 2 :=
    (Nat.floor_lt hpos (n := ⌊Pa.N⌋₊ + 2)).mpr h2
  rw [Nat.card_Icc]
  have : ⌊(1 + Pa.θ) * Pa.N⌋₊ + 1 - (⌊Pa.N⌋₊ + 1) ≤ 1 := by omega
  exact_mod_cast this

/-- `‖e^{i nc}‖ = 1` for real `c` (negative exponent form). -/
lemma norm_exp_neg_int_mul_I (n : ℤ) (c : ℝ) :
    ‖Complex.exp (-((n : ℂ) * Complex.I * (c : ℂ)))‖ = 1 := by
  rw [show -((n : ℂ) * Complex.I * (c : ℂ)) = ((-((n : ℝ) * c) : ℝ) : ℂ) * Complex.I by
    push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

end

end Work.FIArea6Road
