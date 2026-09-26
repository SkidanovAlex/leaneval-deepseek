import Mathlib
import Submission.Work.FunctionalEquations.Basic
import Submission.Work.FunctionalEquations.SeminormGrowthOfRadialGrowth

namespace Work.FunctionalEquations

open LeanEval.Analysis.CKMRVInterpolation Work.Core Work.FE Filter Topology
open scoped FourierTransform SchwartzMap

/-!
# Summability of the terms of the Fourier expansions of `F` and `F̃`

In the CKMRV construction each of the four series in the expansions
`expansion_F` and `expansion_Ftilde` (paper (3.1), (3.2)) has to converge
pointwise for every `x` and every `τ` in the upper half plane.  The two
ingredients are:

* `‖dirichletTerm m τ‖ = exp (-(2 π m Im τ))`, so the Dirichlet terms decay
  geometrically since `Im τ > 0`; and
* the values `basis (m, j) x` grow at most polynomially in `m`, by the Schwartz
  seminorm growth hypothesis `growth_seminorm` of `InterpolationSolution`
  (via `SchwartzMap.norm_le_seminorm`), while `rate m = √(2 m)` also grows at
  most like `m + 1`.

Exponential decay beats polynomial growth, so all four series are summable.
-/

/-- The Dirichlet term `e^{2 π i m τ}` has norm `e^{-2 π m Im τ}`. -/
lemma normDirichletTermAux (m : ℕ) (τ : ℂ) :
    ‖dirichletTerm m τ‖ = Real.exp (-(2 * Real.pi * (m : ℝ) * τ.im)) := by
  rw [dirichletTerm, Complex.norm_exp]
  congr 1
  have h : 2 * (Real.pi : ℂ) * Complex.I * (m : ℂ) * τ
      = ((2 * Real.pi * (m : ℝ) : ℝ) : ℂ) * Complex.I * τ := by
    push_cast; ring
  rw [h]
  simp [Complex.mul_re, Complex.mul_im]

/-- The norm of a real number seen as a complex number. -/
private lemma norm_ofReal_complex (r : ℝ) : ‖(r : ℂ)‖ = |r| := by
  have h : ‖(r : ℂ)‖ ^ 2 = |r| ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_ofReal, sq_abs]; ring
  nlinarith [norm_nonneg (r : ℂ), abs_nonneg r]

/-- The rate `√(2 m)` is at most `m + 1`. -/
lemma rate_le_add_one (m : ℕ) : rate m ≤ (m : ℝ) + 1 := by
  rw [rate, Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  nlinarith [sq_nonneg (m : ℝ)]

/-- A polynomial weight times a geometric sequence with ratio `t ∈ [0,1)` is summable. -/
private lemma summable_add_one_pow_mul_geometric {N : ℕ} {t : ℝ} (ht0 : 0 ≤ t) (ht1 : t < 1) :
    Summable fun n : ℕ => ((n : ℝ) + 1) ^ N * t ^ n := by
  have htabs : ‖t‖ < 1 := by rw [Real.norm_eq_abs, abs_of_nonneg ht0]; exact ht1
  have hgeom : Summable fun n : ℕ => (n : ℝ) ^ N * t ^ n :=
    summable_pow_mul_geometric_of_norm_lt_one N htabs
  have hgeom1 : Summable fun n : ℕ => t ^ n := summable_geometric_of_norm_lt_one htabs
  have hmain : Summable fun n : ℕ => (2 : ℝ) ^ N * (((n : ℝ) ^ N * t ^ n) + t ^ n) :=
    (hgeom.add hgeom1).mul_left _
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hmain
  have hb : ((n : ℝ) + 1) ^ N ≤ (2 : ℝ) ^ N * ((n : ℝ) ^ N + 1) := by
    have hmax : ((n : ℝ) + 1) ≤ 2 * max (n : ℝ) 1 := by
      rcases le_or_gt 1 (n : ℝ) with hh | hh
      · rw [max_eq_left hh]; linarith
      · rw [max_eq_right hh.le]; linarith
    have hstep : ((n : ℝ) + 1) ^ N ≤ (2 * max (n : ℝ) 1) ^ N :=
      pow_le_pow_left₀ (by positivity) hmax N
    have hmaxN : (max (n : ℝ) 1) ^ N ≤ (n : ℝ) ^ N + 1 := by
      rcases le_or_gt 1 (n : ℝ) with hh | hh
      · rw [max_eq_left hh]
        have : (0 : ℝ) ≤ (n : ℝ) ^ N := by positivity
        linarith
      · rw [max_eq_right hh.le]; simp
    calc ((n : ℝ) + 1) ^ N ≤ (2 * max (n : ℝ) 1) ^ N := hstep
      _ = (2 : ℝ) ^ N * (max (n : ℝ) 1) ^ N := by rw [mul_pow]
      _ ≤ (2 : ℝ) ^ N * ((n : ℝ) ^ N + 1) :=
          mul_le_mul_of_nonneg_left hmaxN (by positivity)
  calc ((n : ℝ) + 1) ^ N * t ^ n ≤ ((2 : ℝ) ^ N * ((n : ℝ) ^ N + 1)) * t ^ n :=
        mul_le_mul_of_nonneg_right hb (by positivity)
    _ = (2 : ℝ) ^ N * (((n : ℝ) ^ N * t ^ n) + t ^ n) := by ring

/-- **Exponential decay beats polynomial growth, with the Dirichlet kernel.**
If `‖c m‖ ≤ C (m+1)^N` for all `m ∈ Set.Ici 1` then `m ↦ c m e^{2 π i m τ}`
is summable for every `τ` in the upper half plane. -/
theorem summable_mul_dirichletTerm {c : Set.Ici (1 : ℕ) → ℂ} {N : ℕ} {C : ℝ}
    (_hC : 0 ≤ C) (h : ∀ m : Set.Ici (1 : ℕ), ‖c m‖ ≤ C * ((m.1 : ℝ) + 1) ^ N)
    (τ : ℂ) (hτ : 0 < τ.im) :
    Summable fun m : Set.Ici (1 : ℕ) => c m * dirichletTerm m.1 τ := by
  set t : ℝ := Real.exp (-(2 * Real.pi * τ.im)) with ht
  have ht0 : 0 < t := Real.exp_pos _
  have ht1 : t < 1 := by rw [ht, Real.exp_lt_one_iff]; nlinarith [Real.pi_pos, hτ]
  have hw : Summable fun m : Set.Ici (1 : ℕ) => ((m.1 : ℝ) + 1) ^ N * t ^ (m.1) :=
    (summable_add_one_pow_mul_geometric ht0.le ht1).subtype _
  refine Summable.of_norm_bounded (hw.mul_left C) fun m => ?_
  have hdir : ‖dirichletTerm m.1 τ‖ = t ^ (m.1) := by
    rw [normDirichletTermAux]
    have harg : -(2 * Real.pi * ((m.1 : ℕ) : ℝ) * τ.im)
        = (m.1 : ℝ) * (-(2 * Real.pi * τ.im)) := by ring
    rw [harg, Real.exp_nat_mul, ← ht]
  rw [norm_mul, hdir]
  calc ‖c m‖ * t ^ (m.1) ≤ (C * ((m.1 : ℝ) + 1) ^ N) * t ^ (m.1) :=
        mul_le_mul_of_nonneg_right (h m) (pow_nonneg ht0.le _)
    _ = C * (((m.1 : ℝ) + 1) ^ N * t ^ (m.1)) := by ring

/-- Same as `summable_mul_dirichletTerm`, with an extra factor `rate m = √(2 m)`;
the polynomial growth hypothesis absorbs it because `rate m ≤ m + 1`. -/
theorem summable_rate_mul_dirichletTerm {c : Set.Ici (1 : ℕ) → ℂ} {N : ℕ} {C : ℝ}
    (hC : 0 ≤ C) (h : ∀ m : Set.Ici (1 : ℕ), ‖c m‖ ≤ C * ((m.1 : ℝ) + 1) ^ N)
    (τ : ℂ) (hτ : 0 < τ.im) :
    Summable fun m : Set.Ici (1 : ℕ) => (rate m.1 : ℂ) * c m * dirichletTerm m.1 τ := by
  refine summable_mul_dirichletTerm (c := fun m => (rate m.1 : ℂ) * c m)
    (N := N + 1) (C := C) hC (fun m => ?_) τ hτ
  have hr0 : 0 ≤ rate m.1 := Real.sqrt_nonneg _
  have hm0 : (0 : ℝ) ≤ (m.1 : ℝ) + 1 := by positivity
  rw [norm_mul, norm_ofReal_complex, abs_of_nonneg hr0]
  calc rate m.1 * ‖c m‖ ≤ ((m.1 : ℝ) + 1) * (C * ((m.1 : ℝ) + 1) ^ N) := by
        refine mul_le_mul (rate_le_add_one m.1) (h m) (norm_nonneg _) hm0
    _ = C * ((m.1 : ℝ) + 1) ^ (N + 1) := by rw [pow_succ]; ring

theorem SummableExpansionTerms {n : ℕ} [NeZero n] (S : InterpolationSolution n) (τ : ℂ)
    (hτ : 0 < τ.im) (x : E n) :
    Summable (fun m : Set.Ici (1 : ℕ) => (S.basis (m, 0)).1 x * dirichletTerm m.1 τ) ∧
    Summable (fun m : Set.Ici (1 : ℕ) => (S.basis (m, 1)).1 x * dirichletTerm m.1 τ) ∧
    Summable (fun m : Set.Ici (1 : ℕ) =>
      (rate m.1 : ℂ) * (S.basis (m, 2)).1 x * dirichletTerm m.1 τ) ∧
    Summable (fun m : Set.Ici (1 : ℕ) =>
      (rate m.1 : ℂ) * (S.basis (m, 3)).1 x * dirichletTerm m.1 τ) := by
  obtain ⟨C, N, hC, hbound⟩ := SeminormGrowthOfRadialGrowth S.basis S.growth_radial 0 0
  have hb : ∀ (j : Fin 4) (m : Set.Ici (1 : ℕ)),
      ‖(S.basis (m, j)).1 x‖ ≤ C * ((m.1 : ℝ) + 1) ^ N := fun j m =>
    le_trans (SchwartzMap.norm_le_seminorm ℂ _ x) (hbound m j)
  exact ⟨summable_mul_dirichletTerm hC (fun m => hb 0 m) τ hτ,
    summable_mul_dirichletTerm hC (fun m => hb 1 m) τ hτ,
    summable_rate_mul_dirichletTerm hC (fun m => hb 2 m) τ hτ,
    summable_rate_mul_dirichletTerm hC (fun m => hb 3 m) τ hτ⟩

end Work.FunctionalEquations
