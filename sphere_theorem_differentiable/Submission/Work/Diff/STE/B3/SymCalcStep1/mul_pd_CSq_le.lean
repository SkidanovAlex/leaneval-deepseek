import Mathlib
import Submission.Work.Diff.STE.Torus
import Submission.Work.Diff.STE.B3.SymCalc
import Submission.Work.Diff.STE.B3.SymCalcStep1.conv_CSq_le
import Submission.Work.Diff.STE.B3.ENormSq_le_CSq
import Submission.Work.Diff.STE.fourierCoeff_mul_seriesFun
import Submission.Work.Diff.STE.summable_weighted_fourierCoeff_of_contDiff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The weighted `ℓ²` bound for `M · ∂ₚ u` on the torus

This is the "multiplication by a smooth function followed by one derivative" estimate of the
symbol-calculus layer:

  `CSq s (fourierCoeff (fun x => M x * pd p u x)) ≤ C · CSq (s + 1) (fourierCoeff u)`

for a smooth `1`-periodic `M` and *every* smooth `1`-periodic `u` (the constant `C` depends only
on `M`, `p` and `s`, not on `u`).

## Proof

Everything is done on the Fourier side.

* **The product rule.**  `M` is smooth and periodic, so Fourier inversion
  (`Work.Diff.STE.flat.seriesFun_fourierCoeff`) writes it as the series of its own coefficients,
  and `Work.Diff.STE.fourierCoeff_mul_seriesFun` gives the convolution formula
  `fourierCoeff (u · seriesFun a) = conv a (fourierCoeff u)` with `a = fourierCoeff M`.

* **The derivative.**  `fourierCoeff_pd` is the multiplier identity
  `fourierCoeff (pd p u) = dmul p (fourierCoeff u)`, i.e. `∂ₚ` is `2πi k_p` on the coefficient
  family.

* **Convolution with a rapidly decaying kernel** is bounded on the weighted `ℓ²` space
  (`Work.Diff.STE.B3.SymCalcStep1.conv_CSq_le`), the moment hypothesis
  `∀ N, Σ_l ⟨l⟩^N ‖a l‖ < ∞` being the rapid decay of the Fourier coefficients of the smooth
  function `M` (`summable_wt_pow_norm_fourierCoeff_of_contDiff`).

* **The derivative costs exactly one weight**: `‖dmul p c k‖² = (2π)² (k_p)² ‖c k‖²` and
  `(k_p)² ≤ wt k`, hence `CSq s (dmul p c) ≤ (2π)² CSq (s + 1) c`.
-/

noncomputable section

namespace Work.Diff.STE.B3.SymCalcStep1

open scoped BigOperators

/-- The square of the `p`-th lattice coordinate is dominated by the weight: `(k p)² ≤ ⟨k⟩`. -/
private lemma sym_sq_coord_le_wt {ι : Type*} [Fintype ι] (k : ι → ℤ) (p : ι) :
    ((((k p : ℤ)) : ℝ) ^ 2) ≤ Work.Diff.STE.wt k := by
  have h1 : ((((k p : ℤ)) : ℝ) ^ 2) ≤ ∑ j, ((((k j : ℤ)) : ℝ) ^ 2) :=
    Finset.single_le_sum (f := fun j => ((((k j : ℤ)) : ℝ) ^ 2)) (fun j _ => sq_nonneg _)
      (Finset.mem_univ p)
  have h2 : (0 : ℝ) ≤ 1 := by norm_num
  simp only [Work.Diff.STE.wt]
  linarith

/-- The squared norm of the derivative multiplier: `‖2πi k_p · c k‖² = (2π)² (k_p)² ‖c k‖²`. -/
private lemma sym_norm_dmul_sq {ι : Type*} [Fintype ι] (p : ι) (c : (ι → ℤ) → ℂ)
    (k : ι → ℤ) :
    ‖Work.Diff.STE.dmul p c k‖ ^ 2
      = (2 * Real.pi) ^ 2 * ((((k p : ℤ)) : ℝ) ^ 2) * ‖c k‖ ^ 2 := by
  have hnorm : ‖(2 * Real.pi * Complex.I * (((k p : ℤ)) : ℂ))‖
      = 2 * Real.pi * |(((k p : ℤ)) : ℝ)| := by
    rw [show (2 * Real.pi * Complex.I * (((k p : ℤ)) : ℂ))
        = (((2 * Real.pi * ((k p : ℤ) : ℝ)) : ℝ) : ℂ) * Complex.I by push_cast; ring]
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_mul,
      abs_of_pos (by positivity)]
  rw [Work.Diff.STE.dmul, norm_mul, hnorm, mul_pow, mul_pow, sq_abs]

theorem mul_pd_CSq_le
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (M : (ι → ℝ) → ℂ) (hMsm : ContDiff ℝ (⊤ : ℕ∞) M) (hMper : Work.Diff.STE.Periodic1 M)
    (p : ι) (s : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : (ι → ℝ) → ℂ,
      ContDiff ℝ (⊤ : ℕ∞) u → Work.Diff.STE.Periodic1 u →
      Work.Diff.STE.CSq s (Work.Diff.STE.fourierCoeff (fun x => M x * Work.Diff.STE.pd p u x))
        ≤ C * Work.Diff.STE.CSq (s + 1) (Work.Diff.STE.fourierCoeff u) := by
  classical
  -- rapid decay of the Fourier coefficients of `M`
  have ha : ∀ N : ℕ, Summable (fun l : ι → ℤ =>
      (Work.Diff.STE.wt l) ^ N * ‖Work.Diff.STE.fourierCoeff M l‖) := fun N =>
    Work.Diff.STE.summable_wt_pow_norm_fourierCoeff_of_contDiff M hMsm hMper N
  obtain ⟨C1, hC1nn, hC1⟩ := conv_CSq_le (ι := ι) s (Work.Diff.STE.fourierCoeff M) ha
  refine ⟨C1 * (2 * Real.pi) ^ 2, mul_nonneg hC1nn (sq_nonneg _), ?_⟩
  intro u hu huper
  have hperu : Work.Diff.STE.PeriodicIn p u := fun x => huper p x
  have hu1 : ContDiff ℝ 1 u := hu.of_le (WithTop.coe_le_coe.mpr le_top)
  -- ## Step 1: the Fourier coefficients of `∂ₚ u`
  have hpd : Work.Diff.STE.fourierCoeff (Work.Diff.STE.pd p u)
      = Work.Diff.STE.dmul p (Work.Diff.STE.fourierCoeff u) := by
    funext k
    rw [Work.Diff.STE.fourierCoeff_pd p u k hu1 hperu]
    rfl
  -- ## Step 2: the product rule (Fourier inversion for `M`)
  have hinv : ∀ x : ι → ℝ,
      Work.Diff.STE.seriesFun (Work.Diff.STE.fourierCoeff M) x = M x :=
    Work.Diff.STE.flat.seriesFun_fourierCoeff M hMsm hMper
  have hfun : (fun x : ι → ℝ => M x * Work.Diff.STE.pd p u x)
      = fun x : ι → ℝ =>
          Work.Diff.STE.pd p u x * Work.Diff.STE.seriesFun (Work.Diff.STE.fourierCoeff M) x := by
    funext x
    rw [hinv x, mul_comm]
  have ha1 : Summable (fun l : ι → ℤ => ‖Work.Diff.STE.fourierCoeff M l‖) := by
    simpa using ha 0
  have hcoe : Work.Diff.STE.fourierCoeff (fun x : ι → ℝ => M x * Work.Diff.STE.pd p u x)
      = Work.Diff.STE.conv (Work.Diff.STE.fourierCoeff M)
          (Work.Diff.STE.dmul p (Work.Diff.STE.fourierCoeff u)) := by
    funext k
    rw [hfun, Work.Diff.STE.fourierCoeff_mul_seriesFun (Work.Diff.STE.pd p u)
      (Work.Diff.STE.fourierCoeff M) k
      (Work.Diff.STE.integrableOn_unitCube_of_continuous (Work.Diff.STE.continuous_pd hu1 p)) ha1,
      hpd]
  -- ## Step 3: the weighted summability of `dmul p c` at level `s`, with the pointwise bound
  have hcsum : Summable (fun k : ι → ℤ => (Work.Diff.STE.wt k) ^ (s + 1)
      * ‖Work.Diff.STE.fourierCoeff u k‖ ^ 2) :=
    Work.Diff.STE.summable_weighted_fourierCoeff_of_contDiff u hu huper (s + 1)
  have hpt : ∀ k : ι → ℤ, (Work.Diff.STE.wt k) ^ s
      * ‖Work.Diff.STE.dmul p (Work.Diff.STE.fourierCoeff u) k‖ ^ 2
      ≤ (2 * Real.pi) ^ 2 * ((Work.Diff.STE.wt k) ^ (s + 1)
          * ‖Work.Diff.STE.fourierCoeff u k‖ ^ 2) := by
    intro k
    have hsq := sym_sq_coord_le_wt k p
    have hws : 0 ≤ (Work.Diff.STE.wt k) ^ s :=
      pow_nonneg (le_of_lt (Work.Diff.STE.wt_pos k)) s
    have hA : 0 ≤ (2 * Real.pi) ^ 2 := sq_nonneg _
    have hn : 0 ≤ ‖Work.Diff.STE.fourierCoeff u k‖ ^ 2 := sq_nonneg _
    rw [sym_norm_dmul_sq p (Work.Diff.STE.fourierCoeff u) k, pow_succ]
    calc (Work.Diff.STE.wt k) ^ s
          * ((2 * Real.pi) ^ 2 * ((((k p : ℤ)) : ℝ) ^ 2)
              * ‖Work.Diff.STE.fourierCoeff u k‖ ^ 2)
        = ((2 * Real.pi) ^ 2 * ‖Work.Diff.STE.fourierCoeff u k‖ ^ 2)
            * ((Work.Diff.STE.wt k) ^ s * ((((k p : ℤ)) : ℝ) ^ 2)) := by ring
      _ ≤ ((2 * Real.pi) ^ 2 * ‖Work.Diff.STE.fourierCoeff u k‖ ^ 2)
            * ((Work.Diff.STE.wt k) ^ s * Work.Diff.STE.wt k) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hsq hws)
            (mul_nonneg hA hn)
      _ = (2 * Real.pi) ^ 2
            * ((Work.Diff.STE.wt k) ^ s * Work.Diff.STE.wt k
                * ‖Work.Diff.STE.fourierCoeff u k‖ ^ 2) := by ring
  have hdcsum : Summable (fun k : ι → ℤ => (Work.Diff.STE.wt k) ^ s
      * ‖Work.Diff.STE.dmul p (Work.Diff.STE.fourierCoeff u) k‖ ^ 2) :=
    Summable.of_nonneg_of_le
      (fun k => mul_nonneg (pow_nonneg (le_of_lt (Work.Diff.STE.wt_pos k)) s) (sq_nonneg _))
      hpt (hcsum.mul_left ((2 * Real.pi) ^ 2))
  -- ## Step 4: the two estimates
  have h1 : Work.Diff.STE.CSq s (Work.Diff.STE.conv (Work.Diff.STE.fourierCoeff M)
      (Work.Diff.STE.dmul p (Work.Diff.STE.fourierCoeff u)))
      ≤ C1 * Work.Diff.STE.CSq s (Work.Diff.STE.dmul p (Work.Diff.STE.fourierCoeff u)) :=
    hC1 _ hdcsum
  have h2 : Work.Diff.STE.CSq s (Work.Diff.STE.dmul p (Work.Diff.STE.fourierCoeff u))
      ≤ (2 * Real.pi) ^ 2 * Work.Diff.STE.CSq (s + 1) (Work.Diff.STE.fourierCoeff u) := by
    calc Work.Diff.STE.CSq s (Work.Diff.STE.dmul p (Work.Diff.STE.fourierCoeff u))
        = ∑' k : ι → ℤ, (Work.Diff.STE.wt k) ^ s
            * ‖Work.Diff.STE.dmul p (Work.Diff.STE.fourierCoeff u) k‖ ^ 2 := rfl
      _ ≤ ∑' k : ι → ℤ, (2 * Real.pi) ^ 2 * ((Work.Diff.STE.wt k) ^ (s + 1)
            * ‖Work.Diff.STE.fourierCoeff u k‖ ^ 2) :=
          Summable.tsum_le_tsum hpt hdcsum (hcsum.mul_left _)
      _ = (2 * Real.pi) ^ 2 * ∑' k : ι → ℤ, (Work.Diff.STE.wt k) ^ (s + 1)
            * ‖Work.Diff.STE.fourierCoeff u k‖ ^ 2 := Summable.tsum_mul_left _ hcsum
      _ = (2 * Real.pi) ^ 2 * Work.Diff.STE.CSq (s + 1) (Work.Diff.STE.fourierCoeff u) := rfl
  calc Work.Diff.STE.CSq s (Work.Diff.STE.fourierCoeff (fun x : ι → ℝ => M x * Work.Diff.STE.pd p u x))
      = Work.Diff.STE.CSq s (Work.Diff.STE.conv (Work.Diff.STE.fourierCoeff M)
          (Work.Diff.STE.dmul p (Work.Diff.STE.fourierCoeff u))) := by rw [hcoe]
    _ ≤ C1 * Work.Diff.STE.CSq s (Work.Diff.STE.dmul p (Work.Diff.STE.fourierCoeff u)) := h1
    _ ≤ C1 * ((2 * Real.pi) ^ 2
          * Work.Diff.STE.CSq (s + 1) (Work.Diff.STE.fourierCoeff u)) :=
        mul_le_mul_of_nonneg_left h2 hC1nn
    _ = (C1 * (2 * Real.pi) ^ 2) * Work.Diff.STE.CSq (s + 1)
          (Work.Diff.STE.fourierCoeff u) := by ring

end Work.Diff.STE.B3.SymCalcStep1
