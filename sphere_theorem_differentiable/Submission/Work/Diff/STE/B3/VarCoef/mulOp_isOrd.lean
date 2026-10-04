import Mathlib
import Submission.Work.Diff.STE.B3.VarCoef.OpOrder
import Submission.Work.Diff.STE.B3.SymCalcStep8.lapPow_mul_comm_CSqZ_le
import Submission.Work.Diff.STE.summable_weighted_fourierCoeff_of_contDiff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Multiplication by a smooth `1`-periodic function is an operator of order `0`

This is the `M_m` entry of the order calculus of `Work.Diff.STE.B3.VarCoef.OpOrder`:
for a smooth `1`-periodic `m : (ι → ℝ) → ℝ`, the multiplier `mulOp m` is of order `0`, i.e.

  `CSqZ (t - 0) (fourierCoeff (m • f)) ≤ C t · CSqZ t (fourierCoeff f)`   for every `t : ℤ`,

together with the preservation of smooth `1`-periodic functions and `ℂ`-linearity on them.

## Route

The Fourier coefficients of the product are the convolution of the coefficient families,
`fourierCoeff (m • f) = conv (fourierCoeff m) (fourierCoeff f)`, and `m` smooth and periodic means
that `fourierCoeff m` has finite weighted `ℓ¹` moments of every order
(`Work.Diff.STE.B3.summable_wt_pow_mul_norm_fourierCoeff`).  The **kernel bound**
`Work.Diff.STE.B3.SymCalcStep8.kernel_abs_CSqZ_le` then applies *at every integer exponent*
(the two-sided Peetre inequality `⟨m⟩^t ≤ (2⟨l⟩)^{|t|}⟨m-l⟩^t` is what makes the negative
exponents work): convolution with a rapidly decaying nonnegative kernel
`k l = ‖fourierCoeff m l‖` is bounded on `CSqZ t`, and the honest convolution is dominated by the
absolute-value one via `Work.Diff.STE.norm_conv_le`.  No case distinction on the sign of `t` is
needed.
-/

noncomputable section

open scoped BigOperators

namespace Work.Diff.STE.B3.VarCoef

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## 1. The complexification of a real-valued function -/

/-- The complexification of a smooth function is smooth. -/
theorem contDiff_complex_ofReal {m : (ι → ℝ) → ℝ} (hm : ContDiff ℝ (⊤ : ℕ∞) m) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x => ((m x : ℝ) : ℂ)) :=
  Complex.ofRealCLM.contDiff.comp hm

/-- The complexification of a `1`-periodic function is `1`-periodic. -/
theorem periodic1_complex_ofReal {m : (ι → ℝ) → ℝ} (hmp : Work.Diff.STE.Periodic1 m) :
    Work.Diff.STE.Periodic1 (fun x => ((m x : ℝ) : ℂ)) := fun i x => by simp only [hmp i x]

/-! ## 2. `mulOp` preserves smooth periodic functions and is `ℂ`-linear -/

theorem pres_mulOp (m : (ι → ℝ) → ℝ) (hm : ContDiff ℝ (⊤ : ℕ∞) m)
    (hmp : Work.Diff.STE.Periodic1 m) : Preserves (mulOp m) := by
  intro f hf
  exact ⟨(Complex.ofRealCLM.contDiff.comp hm).mul hf.1, fun i x => by
    simp only [mulOp, hf.2 i x, hmp i x]⟩

theorem linSP_mulOp (m : (ι → ℝ) → ℝ) : LinSP (mulOp m) where
  add f g _ _ := by funext x; simp only [mulOp, Pi.add_apply, mul_add]
  smul c f _ := by funext x; simp only [mulOp, Pi.smul_apply, smul_eq_mul]; ring

/-! ## 3. The order-`0` bound on the weighted coefficient scale, at every integer exponent -/

/-- **Multiplication by a smooth `1`-periodic function is bounded on `CSqZ τ`, for every
integer exponent `τ`.** -/
theorem mulOp_CSqZ_le (m : (ι → ℝ) → ℝ) (hm : ContDiff ℝ (⊤ : ℕ∞) m)
    (hmp : Work.Diff.STE.Periodic1 m) (τ : ℤ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : (ι → ℝ) → ℂ, SmoothPer f →
      Work.Diff.STE.B3.SymCalcStep8.CSqZ τ (Work.Diff.STE.fourierCoeff (mulOp m f))
        ≤ C * Work.Diff.STE.B3.SymCalcStep8.CSqZ τ (Work.Diff.STE.fourierCoeff f) := by
  classical
  set mc : (ι → ℝ) → ℂ := fun x => ((m x : ℝ) : ℂ) with hmc_def
  have hmc_sm : ContDiff ℝ (⊤ : ℕ∞) mc := contDiff_complex_ofReal hm
  have hmc_per : Work.Diff.STE.Periodic1 mc := periodic1_complex_ofReal hmp
  -- the weighted `ℓ¹` moments of the Fourier coefficients of the multiplier
  have hmom : ∀ N : ℕ, Summable (fun l : ι → ℤ => Work.Diff.STE.wt l ^ N
      * ‖Work.Diff.STE.fourierCoeff mc l‖) := fun N =>
    Work.Diff.STE.B3.summable_wt_pow_mul_norm_fourierCoeff N mc hmc_sm hmc_per
  -- the kernel bound at the exponent `τ`
  obtain ⟨C, hC0, hC⟩ := Work.Diff.STE.B3.SymCalcStep8.kernel_abs_CSqZ_le
    (fun l : ι → ℤ => ‖Work.Diff.STE.fourierCoeff mc l‖) (fun l => norm_nonneg _) hmom τ
  refine ⟨C, hC0, fun f hf => ?_⟩
  have hfr : Work.Diff.STE.B3.SymCalcStep8.Rapid (Work.Diff.STE.fourierCoeff f) := fun N =>
    Work.Diff.STE.summable_weighted_fourierCoeff_of_contDiff f hf.1 hf.2 N
  obtain ⟨hmaj_summ, hmaj_bound⟩ := hC (Work.Diff.STE.fourierCoeff f) hfr
  -- the absolute-value convolution family dominating `conv (fourierCoeff mc) (fourierCoeff f)`
  set G : (ι → ℤ) → ℂ := fun k => ((∑' l : ι → ℤ, ‖Work.Diff.STE.fourierCoeff mc l‖
      * ‖Work.Diff.STE.fourierCoeff f (k - l)‖ : ℝ) : ℂ) with hG_def
  -- the Fourier coefficients of the product are the convolution
  have hcoef : ∀ k : ι → ℤ, Work.Diff.STE.fourierCoeff (mulOp m f) k
      = Work.Diff.STE.conv (Work.Diff.STE.fourierCoeff mc) (Work.Diff.STE.fourierCoeff f) k := by
    intro k
    have h := Work.Diff.STE.B3.fourierCoeff_mul f mc hf.1 hmc_sm hmc_per k
    rw [← h]
    congr 1
    funext x
    simp only [mulOp, hmc_def, mul_comm]
  have hfl1 : Summable (fun k : ι → ℤ => ‖Work.Diff.STE.fourierCoeff mc k‖) := by
    simpa using hmom 0
  have hfl2 : Summable (fun k : ι → ℤ => ‖Work.Diff.STE.fourierCoeff f k‖ ^ 2) := by
    simpa using hfr 0
  have hGnorm : ∀ k : ι → ℤ, ‖G k‖
      = ∑' l : ι → ℤ, ‖Work.Diff.STE.fourierCoeff mc l‖
          * ‖Work.Diff.STE.fourierCoeff f (k - l)‖ := by
    intro k
    rw [hG_def, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (tsum_nonneg fun l => mul_nonneg (norm_nonneg _) (norm_nonneg _))]
  have hG_summ : Summable (fun k : ι → ℤ => Work.Diff.STE.wt k ^ τ * ‖G k‖ ^ 2) :=
    hmaj_summ.congr (fun k => by rw [hGnorm k])
  have hmain : Work.Diff.STE.B3.SymCalcStep8.CSqZ τ (Work.Diff.STE.fourierCoeff (mulOp m f))
      ≤ Work.Diff.STE.B3.SymCalcStep8.CSqZ τ G := by
    refine Work.Diff.STE.B3.SymCalcStep8.CSqZ_le_of_norm_le
      (F := Work.Diff.STE.fourierCoeff (mulOp m f)) ?_ τ hG_summ
    intro k
    rw [hGnorm k, hcoef k]
    exact Work.Diff.STE.norm_conv_le _ _ hfl1 hfl2 k
  refine le_trans hmain ?_
  rw [hG_def]
  exact hmaj_bound

/-! ## 4. The target -/

/-- The `M_m` entry of the order calculus: multiplication by a smooth `1`-periodic real
function is an operator of order `0`. -/
theorem mulOp_isOrd_aux (m : (ι → ℝ) → ℝ) (hm : ContDiff ℝ (⊤ : ℕ∞) m)
    (hmp : Work.Diff.STE.Periodic1 m) :
    ∃ C : ℤ → ℝ, IsOrd 0 C (mulOp m) := by
  refine isOrd_of_pointwise (pres_mulOp m hm hmp) (linSP_mulOp m) ?_
  intro t
  obtain ⟨C, hC0, hC⟩ := mulOp_CSqZ_le m hm hmp t
  exact ⟨C, hC0, fun f hf => by rw [sub_zero]; exact hC f hf⟩

theorem mulOp_isOrd {ι : Type*} [Fintype ι] [DecidableEq ι] (m : (ι → ℝ) → ℝ)
    (hm : ContDiff ℝ (⊤ : ℕ∞) m) (hmp : Work.Diff.STE.Periodic1 m) :
    ∃ C : ℤ → ℝ, Work.Diff.STE.B3.VarCoef.IsOrd 0 C (Work.Diff.STE.B3.VarCoef.mulOp m) :=
  mulOp_isOrd_aux m hm hmp

end Work.Diff.STE.B3.VarCoef
