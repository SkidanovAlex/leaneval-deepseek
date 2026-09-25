import Mathlib
import Submission.Commons.Analysis.Sum.lacunary_finset_sum_inv_le
import Submission.Commons.Analysis.Sum.lacunary_finset_card_le
import Submission.Commons.Analysis.Sum.lacunary_finset_sum_le

/-!
# A uniform bound for the lacunary Calderón–Zygmund symbol sum

`Commons.Analysis.CalderonZygmund.czSymb_bound` bounds the symbol sum
`∑_{N ∈ D} ε_N ψ(A N^d ξ) e(λ_N A N^d ξ)` by a constant *depending on the finite lacunary set
`D`* (namely `C · #D`).  This file strengthens the estimate to a bound that is *uniform in `D`*,
using the fact that `ψ(0) = 0` together with the derivative bound `‖ψ'‖ ≤ C` forces
`‖ψ(t)‖ ≤ C |t|`: the terms with `A N^d |ξ| > C` vanish (by the support hypothesis on `ψ`) and
the surviving terms are bounded by a multiple of `A N^d`, whose lacunary sum is controlled by
`A N^d ≤ C / |ξ|` (a form of `Commons.Analysis.Sum.lacunary_finset_sum_le`).
-/

namespace Commons.Analysis.CalderonZygmund

open Finset

/-- For real `t`, the complex exponential `exp (2 * π * I * t)` has norm `1`. -/
private lemma norm_exp_two_pi_I (t : ℝ) :
    ‖Complex.exp (2 * Real.pi * Complex.I * (t : ℂ))‖ = 1 := by
  have hEq : 2 * Real.pi * Complex.I * (t : ℂ)
      = ((2 * Real.pi * t : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [hEq, Complex.norm_exp_ofReal_mul_I]

/-- Variant: if the complex factor `u` equals the coercion of a real number `a`,
then `exp (2 * π * I * u)` has norm `1`. -/
private lemma norm_exp_two_pi_I_eq {a : ℝ} {u : ℂ} (hu : u = (a : ℂ)) :
    ‖Complex.exp (2 * Real.pi * Complex.I * u)‖ = 1 := by
  rw [hu]; exact norm_exp_two_pi_I a

/-- If a Schwartz function `ψ` vanishes at `0` and its first derivative is bounded by `C`,
then `‖ψ t‖ ≤ C |t|` for every `t`.  This is the mean value inequality applied on the whole
line, using `norm_iteratedFDeriv_one` to identify the first iterated derivative with `fderiv`. -/
private lemma schwartz_norm_le_mul_abs (ψ : SchwartzMap ℝ ℂ) (C : ℝ) (hψ0 : ψ 0 = 0)
    (hψ1 : ∀ ξ, ‖iteratedFDeriv ℝ 1 (ψ : ℝ → ℂ) ξ‖ ≤ C) (t : ℝ) :
    ‖ψ t‖ ≤ C * |t| := by
  have hdiff : ∀ x : ℝ, DifferentiableAt ℝ (ψ : ℝ → ℂ) x := fun x => ψ.differentiableAt
  have hbound : ∀ x : ℝ, ‖fderiv ℝ (ψ : ℝ → ℂ) x‖ ≤ C := by
    intro x
    rw [← norm_iteratedFDeriv_one]
    exact hψ1 x
  have h := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℝ) (f := (ψ : ℝ → ℂ))
      (s := Set.univ) (C := C) (fun x _ => hdiff x) (fun x _ => hbound x)
      convex_univ (Set.mem_univ 0) (Set.mem_univ t)
  rw [hψ0, sub_zero, sub_zero, Real.norm_eq_abs] at h
  exact h

/-- For every admissible `ψ` (Schwartz, `ψ 0 = 0`, supported in `[-C, C]`, with derivatives up
to order `2` bounded by `C`), every `Λ`-lacunary finite set `D` of positive reals, every
`|ε_N| ≤ 1`, every phase `lam` and every `ξ`, the symbol sum
`∑_{N ∈ D} ε_N ψ(A N^d ξ) e(λ_N A N^d ξ)` is bounded by a constant `B > 0` depending only on
`C, Λ, d` — in particular uniformly in the finite lacunary set `D`. -/
theorem czSymb_bound_uniform (C Λ A : ℝ) (hC : 0 < C) (hΛ : 1 < Λ) (d : ℕ) (hd : 1 ≤ d) (hA : 0 < A) : ∃ B : ℝ, 0 < B ∧ ∀ (D : Finset ℝ) (hDpos : ∀ N ∈ D, 0 < N) (hlac : ∀ M ∈ D, ∀ N ∈ D, M < N → Λ * M ≤ N) (ψ : SchwartzMap ℝ ℂ) (hψ0 : ψ 0 = 0) (hψsupp : ∀ ξ, ξ ∉ Set.Icc (-C) C → ψ ξ = 0) (hψj : ∀ j : ℕ, j ≤ 2 → ∀ ξ, ‖iteratedFDeriv ℝ j (ψ : ℝ → ℂ) ξ‖ ≤ C) (lam : ℝ → ℝ) (eps : ℝ → ℂ) (heps : ∀ N ∈ D, ‖eps N‖ ≤ 1) (ξ : ℝ), ‖∑ N ∈ D, eps N * (ψ (A * N ^ d * ξ) * Complex.exp (2 * Real.pi * Complex.I * (lam N * A * N ^ d * ξ)))‖ ≤ B := by
  have hd0 : d ≠ 0 := by omega
  have hpd : 1 < Λ ^ d := one_lt_pow₀ hΛ hd0
  have hrpos : 0 < (1 - (Λ ^ d)⁻¹)⁻¹ :=
    inv_pos.mpr (by have h := inv_lt_one_of_one_lt₀ hpd; linarith)
  refine ⟨max 1 (C ^ 2 * (1 - (Λ ^ d)⁻¹)⁻¹),
    lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro D hDpos hlac ψ hψ0 hψsupp hψj lam eps heps ξ
  rcases eq_or_ne ξ 0 with rfl | hξ
  · simp [hψ0]
  · have habsξpos : 0 < |ξ| := abs_pos.mpr hξ
    set f : ℝ → ℂ := fun N => eps N * (ψ (A * N ^ d * ξ) * Complex.exp (2 * Real.pi * Complex.I * (lam N * A * N ^ d * ξ))) with hf
    set T : Finset ℝ := D.filter (fun N => A * N ^ d ≤ C / |ξ|) with hT
    -- The terms outside `T` vanish, because there `A N^d |ξ| > C` and `ψ` is supported in `[-C, C]`.
    have hsum_eq : ∑ N ∈ D, f N = ∑ N ∈ T, f N := by
      rw [hT]
      refine (Finset.sum_filter_of_ne ?_).symm
      intro N hND hne
      by_contra hcon
      have hcon' : C / |ξ| < A * N ^ d := lt_of_not_ge hcon
      have hNpos : 0 < N := hDpos N hND
      have hNdpos : 0 < N ^ d := pow_pos hNpos d
      have hCabs : C < A * N ^ d * |ξ| := (div_lt_iff₀ habsξpos).mp hcon'
      have hnorm : |A * N ^ d * ξ| = A * N ^ d * |ξ| := by
        rw [abs_mul, abs_mul, abs_of_pos hA, abs_of_pos hNdpos]
      have hnotmem : A * N ^ d * ξ ∉ Set.Icc (-C) C := by
        intro hmem
        rw [Set.mem_Icc] at hmem
        rcases lt_abs.mp (by rw [hnorm]; exact hCabs) with h | h
        · exact absurd hmem.2 (not_le.mpr h)
        · exact absurd hmem.1 (not_le.mpr (by linarith))
      have hψz : ψ (A * N ^ d * ξ) = 0 := hψsupp _ hnotmem
      exact hne (by simp [hf, hψz])
    -- Termwise bound on `T`, using `‖ψ(t)‖ ≤ C|t|`.
    have hterm : ∀ N ∈ T, ‖f N‖ ≤ C * (A * N ^ d) * |ξ| := by
      intro N hN
      rw [hT] at hN
      have hND : N ∈ D := (Finset.mem_filter.mp hN).1
      have hNpos : 0 < N := hDpos N hND
      have hNdpos : 0 < N ^ d := pow_pos hNpos d
      have hepsN : ‖eps N‖ ≤ 1 := heps N hND
      have hψb : ‖ψ (A * N ^ d * ξ)‖ ≤ C * |A * N ^ d * ξ| :=
        schwartz_norm_le_mul_abs ψ C hψ0 (fun x => hψj 1 (by norm_num) x) _
      have hexp : ‖Complex.exp (2 * Real.pi * Complex.I * (lam N * A * N ^ d * ξ))‖ = 1 := by
        refine norm_exp_two_pi_I_eq (a := lam N * A * N ^ d * ξ) ?_
        push_cast; ring
      have hnorm : |A * N ^ d * ξ| = A * N ^ d * |ξ| := by
        rw [abs_mul, abs_mul, abs_of_pos hA, abs_of_pos hNdpos]
      simp only [hf]
      rw [norm_mul, norm_mul, hexp, mul_one]
      calc ‖eps N‖ * ‖ψ (A * N ^ d * ξ)‖
          ≤ 1 * (C * |A * N ^ d * ξ|) := mul_le_mul hepsN hψb (norm_nonneg _) (by norm_num)
        _ = C * (A * N ^ d) * |ξ| := by rw [hnorm]; ring
    have hsum_bound : ‖∑ N ∈ T, f N‖ ≤ C * |ξ| * ∑ N ∈ T, A * N ^ d := by
      calc ‖∑ N ∈ T, f N‖ ≤ ∑ N ∈ T, ‖f N‖ := norm_sum_le T f
        _ ≤ ∑ N ∈ T, C * (A * N ^ d) * |ξ| := Finset.sum_le_sum hterm
        _ = C * |ξ| * ∑ N ∈ T, A * N ^ d := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro N hN; ring
    -- The lacunary forward sum estimate controls `∑_{N ∈ T} A N^d`.
    have hle := Commons.Analysis.Sum.lacunary_finset_sum_le hΛ d hd A hA D hDpos hlac
      (C / |ξ|) (div_pos hC habsξpos)
    rw [← hT] at hle
    calc ‖∑ N ∈ D, f N‖ = ‖∑ N ∈ T, f N‖ := by rw [hsum_eq]
      _ ≤ C * |ξ| * ∑ N ∈ T, A * N ^ d := hsum_bound
      _ ≤ C * |ξ| * ((1 - (Λ ^ d)⁻¹)⁻¹ * (C / |ξ|)) := by
            apply mul_le_mul_of_nonneg_left hle; positivity
      _ = C * C * (1 - (Λ ^ d)⁻¹)⁻¹ := by
            field_simp
      _ = C ^ 2 * (1 - (Λ ^ d)⁻¹)⁻¹ := by ring
      _ ≤ max 1 (C ^ 2 * (1 - (Λ ^ d)⁻¹)⁻¹) := le_max_right _ _

end Commons.Analysis.CalderonZygmund
