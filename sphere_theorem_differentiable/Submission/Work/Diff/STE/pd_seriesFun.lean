import Mathlib
import Submission.Work.Diff.STE.Torus
import Submission.Work.Diff.STE.pd_fourierExp

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `pd_seriesFun`: differentiation of the Fourier series term by term

For a coefficient family `c : (ι → ℤ) → ℂ` whose weighted `ℓ¹` norms
`Σ_k ⟨k⟩^N ‖c k‖` are finite for every `N`, the series
`seriesFun c = fun x => Σ_k c k · exp (2πi k·x)` may be differentiated term by term:
the `i`-th partial derivative is the series with coefficient family `dmul i c`
(the Fourier multiplier of `∂ᵢ`, `k ↦ 2πi kᵢ`).

The proof is the Weierstrass-type theorem `hasFDerivAt_tsum` on the countable index
type `ι → ℤ`, with uniform bound `‖fderiv (c k · char k)‖ ≤ 2π · card ι · ⟨k⟩² ‖c k‖`.
-/

noncomputable section

namespace Work.Diff.STE

open BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-! ## Elementary norm computations -/

/-- The Fourier characters have unit modulus. -/
lemma norm_fourierExp (k : ι → ℤ) (x : ι → ℝ) : ‖fourierExp k x‖ = 1 := by
  rw [fourierExp]
  have h : (2 * (Real.pi : ℂ) * Complex.I * ∑ i, (k i : ℂ) * (x i : ℂ))
      = (((2 * Real.pi * ∑ i, ((k i : ℤ) : ℝ) * (x i)) : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [h, Complex.norm_exp_ofReal_mul_I]

/-- `exp (fourierLin k y)` is `fourierExp k y`, in particular of modulus `1`. -/
lemma norm_exp_fourierLin (k : ι → ℤ) (y : ι → ℝ) :
    ‖Complex.exp (fourierLin k y)‖ = 1 := by
  have h := norm_fourierExp k y
  simpa only [fourierExp_eq_exp_lin] using h

/-- Each coordinate of `k` is dominated by the weight `⟨k⟩² = 1 + Σ kᵢ²`. -/
lemma abs_intCast_le_wt (k : ι → ℤ) (j : ι) : |((k j : ℤ) : ℝ)| ≤ wt k := by
  have h1 : |((k j : ℤ) : ℝ)| ≤ 1 + ((k j : ℤ) : ℝ) ^ 2 := by
    by_cases h : |((k j : ℤ) : ℝ)| ≤ 1
    · nlinarith [sq_nonneg (((k j : ℤ) : ℝ))]
    · rw [not_le] at h
      have h2 : |((k j : ℤ) : ℝ)| ≤ |((k j : ℤ) : ℝ)| ^ 2 := by
        nlinarith [abs_nonneg (((k j : ℤ) : ℝ))]
      rw [sq_abs] at h2
      linarith [sq_nonneg (((k j : ℤ) : ℝ))]
  have h2 : ((k j : ℤ) : ℝ) ^ 2 ≤ ∑ i, ((k i : ℤ) : ℝ) ^ 2 :=
    Finset.single_le_sum (f := fun i => ((k i : ℤ) : ℝ) ^ 2) (fun i _ => sq_nonneg _)
      (Finset.mem_univ j)
  simp only [wt]
  linarith

/-- The norm of the linear form `fourierLin k` is bounded by `2π · card ι · ⟨k⟩²`. -/
lemma norm_fourierLin_le (k : ι → ℤ) :
    ‖fourierLin k‖ ≤ 2 * Real.pi * (Fintype.card ι : ℝ) * wt k := by
  have hconst : ‖(2 : ℂ) * (Real.pi : ℂ) * Complex.I‖ = 2 * Real.pi := by
    have h2 : ‖(2 : ℂ)‖ = 2 := by norm_num
    have hp : ‖(Real.pi : ℂ)‖ = Real.pi := by simp
    calc ‖(2 : ℂ) * (Real.pi : ℂ) * Complex.I‖
        = ‖(2 : ℂ)‖ * ‖(Real.pi : ℂ)‖ * ‖Complex.I‖ := by rw [norm_mul, norm_mul]
      _ = 2 * Real.pi := by
            rw [h2, Complex.norm_I, mul_one]
            exact congrArg (2 * ·) hp
  refine ContinuousLinearMap.opNorm_le_bound _ ?_ (fun v => ?_)
  · exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) Real.pi_nonneg)
      (Nat.cast_nonneg _)) (le_of_lt (wt_pos k))
  · rw [fourierLin_apply, norm_mul, hconst]
    have hsum : ‖∑ j, (k j : ℂ) * (v j : ℂ)‖ ≤ (∑ j, |((k j : ℤ) : ℝ)|) * ‖v‖ := by
      calc ‖∑ j, (k j : ℂ) * (v j : ℂ)‖ ≤ ∑ j, ‖(k j : ℂ) * (v j : ℂ)‖ := norm_sum_le _ _
        _ = ∑ j, |((k j : ℤ) : ℝ)| * |v j| := by
              refine Finset.sum_congr rfl (fun j _ => ?_)
              rw [norm_mul, Complex.norm_intCast]
              exact congrArg (fun z => |((k j : ℤ) : ℝ)| * z) (RCLike.norm_ofReal (v j))
        _ ≤ ∑ j, |((k j : ℤ) : ℝ)| * ‖v‖ := by
              refine Finset.sum_le_sum (fun j _ => ?_)
              exact mul_le_mul_of_nonneg_left (norm_le_pi_norm v j) (abs_nonneg _)
        _ = (∑ j, |((k j : ℤ) : ℝ)|) * ‖v‖ := by rw [Finset.sum_mul]
    have hwt : (∑ j, |((k j : ℤ) : ℝ)|) ≤ (Fintype.card ι : ℝ) * wt k := by
      calc (∑ j, |((k j : ℤ) : ℝ)|) ≤ ∑ _j : ι, wt k :=
            Finset.sum_le_sum (fun j _ => abs_intCast_le_wt k j)
        _ = (Fintype.card ι : ℝ) * wt k := by
              rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    calc 2 * Real.pi * ‖∑ j, (k j : ℂ) * (v j : ℂ)‖
        ≤ 2 * Real.pi * ((∑ j, |((k j : ℤ) : ℝ)|) * ‖v‖) :=
          mul_le_mul_of_nonneg_left hsum (by positivity)
      _ ≤ 2 * Real.pi * (((Fintype.card ι : ℝ) * wt k) * ‖v‖) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hwt (norm_nonneg v))
            (by positivity)
      _ = (2 * Real.pi * (Fintype.card ι : ℝ) * wt k) * ‖v‖ := by ring

/-- The uniform bound on the derivative of the `k`-th summand. -/
lemma norm_smul_fourierLin_le (c : ℂ) (k : ι → ℤ) (y : ι → ℝ) :
    ‖(c * Complex.exp (fourierLin k y)) • (fourierLin k)‖
      ≤ (2 * Real.pi * (Fintype.card ι : ℝ) * wt k) * ‖c‖ := by
  rw [norm_smul, norm_mul, norm_exp_fourierLin, mul_one]
  calc ‖c‖ * ‖fourierLin k‖ ≤ ‖c‖ * (2 * Real.pi * (Fintype.card ι : ℝ) * wt k) :=
        mul_le_mul_of_nonneg_left (norm_fourierLin_le k) (norm_nonneg c)
    _ = (2 * Real.pi * (Fintype.card ι : ℝ) * wt k) * ‖c‖ := by ring

/-! ## The derivative of one summand -/

/-- The Fréchet derivative of `x ↦ c · exp (2πi k·x)` at `y`. -/
lemma hasFDerivAt_smul_fourierExp (c : ℂ) (k : ι → ℤ) (y : ι → ℝ) :
    HasFDerivAt (fun x : ι → ℝ => c * fourierExp k x)
      ((c * Complex.exp (fourierLin k y)) • (fourierLin k)) y := by
  have hcomp : HasFDerivAt (fourierExp k)
      ((Complex.exp (fourierLin k y) • (1 : ℂ →L[ℝ] ℂ)).comp (fourierLin k)) y := by
    rw [fourierExp_eq_exp_lin]
    exact ((Complex.hasStrictFDerivAt_exp_real (fourierLin k y)).hasFDerivAt.comp y
      (fourierLin k).hasFDerivAt)
  have h2 := hcomp.const_mul c
  have h3 : c • ((Complex.exp (fourierLin k y) • (1 : ℂ →L[ℝ] ℂ)).comp (fourierLin k))
      = (c * Complex.exp (fourierLin k y)) • (fourierLin k) := by
    ext v
    simp only [smul_apply, ContinuousLinearMap.comp_apply, one_apply_eq_self, smul_eq_mul]
    ring
  rwa [h3] at h2

/-! ## The main theorem -/

theorem pd_seriesFun {ι : Type*} [Fintype ι] [DecidableEq ι] (i : ι) (c : (ι → ℤ) → ℂ)
    (h : ∀ N : ℕ, Summable (fun k : ι → ℤ => (Work.Diff.STE.wt k) ^ N * ‖c k‖)) :
    ∀ x : ι → ℝ,
      Work.Diff.STE.pd i (Work.Diff.STE.seriesFun c) x
        = Work.Diff.STE.seriesFun (Work.Diff.STE.dmul i c) x := by
  intro x
  have h1 : Summable (fun k : ι → ℤ => wt k * ‖c k‖) := by simpa using h 1
  have h0 : Summable (fun k : ι → ℤ => ‖c k‖) := by simpa using h 0
  have hu : Summable
      (fun k : ι → ℤ => (2 * Real.pi * (Fintype.card ι : ℝ) * wt k) * ‖c k‖) := by
    have h2 : Summable
        (fun k : ι → ℤ => (2 * Real.pi * (Fintype.card ι : ℝ)) * (wt k * ‖c k‖)) :=
      h1.mul_left _
    refine h2.congr (fun k => ?_)
    ring
  have hf0 : Summable (fun k : ι → ℤ => c k * fourierExp k x) := by
    refine Summable.of_norm_bounded h0 (fun k => ?_)
    rw [norm_mul, norm_fourierExp, mul_one]
  have hderiv : fderiv ℝ (seriesFun c) x
      = (∑' k : ι → ℤ, (c k * Complex.exp (fourierLin k x)) • (fourierLin k)) :=
    (hasFDerivAt_tsum hu (fun k y => hasFDerivAt_smul_fourierExp (c k) k y)
      (fun k y => norm_smul_fourierLin_le (c k) k y) hf0 x).fderiv
  have hS : Summable
      (fun k : ι → ℤ => (c k * Complex.exp (fourierLin k x)) • (fourierLin k)) :=
    Summable.of_norm_bounded hu (fun k => norm_smul_fourierLin_le (c k) k x)
  have key : (∑' k : ι → ℤ, (c k * Complex.exp (fourierLin k x)) • (fourierLin k))
        (Pi.single i (1 : ℝ))
      = ∑' k : ι → ℤ,
          ((c k * Complex.exp (fourierLin k x)) • (fourierLin k)) (Pi.single i (1 : ℝ)) := by
    have hmap := ContinuousLinearMap.map_tsum
      (ContinuousLinearMap.apply ℝ ℂ (Pi.single i (1 : ℝ))) hS
    simpa only [ContinuousLinearMap.apply_apply] using hmap
  simp only [pd]
  rw [hderiv, key]
  refine (tsum_congr (fun k => ?_)).trans rfl
  rw [smul_apply, smul_eq_mul, fourierLin_single, fourierExp_eq_exp_lin]
  simp only [dmul]
  ring

end Work.Diff.STE
