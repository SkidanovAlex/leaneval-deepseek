/-
# The abstract `E_ρ = ρ ∂` machinery of `Work.FTS.GalBasis.cc.PsiCutAux`, at *all* orders

`PsiCutAux` bounds the iterates of the one-variable operator `E_ρ f = ρ · f'` applied to the
profile `Real.smoothTransition` only up to order `4` (`Eiter_deriv_bound`, `k + j ≤ 4`), because
that is all `psiCut_spec` needs.  The cutoff bounds of `CptApp.cutBounds` ask for the `D`-iterates
*of every order*, so this file generalises the two statements:

* `Eiter_deriv_bound_all` — the abstract induction, for all `k, j`, with the hypothesis that `M`
  bounds *all* the derivatives of `ρ` (and `B` those of `f`) on `[0,1]`;
* `exists_iteratedDeriv_smoothTransition_bound` — the all-order derivative bounds of
  `Real.smoothTransition` on `[0,1]` (compactness of `[0,1]` + continuity of the iterated
  derivatives);
* `exists_Eiter_smoothTransition_bound` — **the engine**: given all-order bounds `M` for `ρ`
  and `B` for `σ = Real.smoothTransition` on `[0,1]`, there is `K : ℕ → ℝ` with
  `|Eiter k ρ σ v| ≤ K k` for *every* `k` and *every* `v : ℝ`.  Off `[0,1]` the profile is
  locally constant (`𝕋 ≡ 0` on `(-∞,0)`, `𝕋 ≡ 1` on `(1,∞)`), so all the positive iterates
  vanish there (`Eiter_eq_zero_of_open_const`).

The two consumer instances are the affine coefficient `ρ (u) = u - c` (radial steps) and the
rescaled angular coefficient `ρ (u) = λ sin (2 (u+1)/λ)` (`rhoM λ`).
-/
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Submission.Work.FTS.GalBasis.cc.PsiCutAux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Honesty.CptApp

set_option linter.unusedVariables false

open Work.FTS.GalBasis.cc (Eiter Eop Cbnd contDiff_Eiter Eiter_zero Eiter_succ
  Eiter_eq_zero_of_open_const)

/-- **The abstract bound at all orders.**  If `M` bounds every derivative of `ρ` and `B` every
derivative of `f` on `[0,1]`, then the recursive constant `Cbnd M B k j` bounds the `j`-th
derivative of the `k`-th iterate of `E_ρ f = ρ f'` on `[0,1]`. -/
theorem Eiter_deriv_bound_all {ρ f : ℝ → ℝ} {M B : ℕ → ℝ}
    (hMnn : ∀ m, 0 ≤ M m) (hBnn : ∀ m, 0 ≤ B m)
    (hρ : ∀ n : ℕ, ContDiff ℝ n ρ) (hf : ∀ n : ℕ, ContDiff ℝ n f)
    (hM : ∀ m : ℕ, ∀ u ∈ Set.Icc (0 : ℝ) 1, |iteratedDeriv m ρ u| ≤ M m)
    (hB : ∀ m : ℕ, ∀ u ∈ Set.Icc (0 : ℝ) 1, |iteratedDeriv m f u| ≤ B m) :
    ∀ k j : ℕ, ∀ u ∈ Set.Icc (0 : ℝ) 1,
      |iteratedDeriv j (Eiter k ρ f) u| ≤ Cbnd M B k j := by
  intro k
  induction k with
  | zero =>
    intro j u hu
    have e : iteratedDeriv j (Eiter 0 ρ f) u = iteratedDeriv j f u := by rw [Eiter_zero]
    rw [e]
    exact hB j u hu
  | succ k ih =>
    intro j u hu
    rw [Eiter_succ, Eop]
    have hρj : ContDiffAt ℝ (↑j) ρ u := (hρ j).contDiffAt
    have hgard : ContDiffAt ℝ (↑j) (deriv (Eiter k ρ f)) u :=
      ((contDiff_Eiter hρ hf k (j + 1)).deriv').contDiffAt
    rw [iteratedDeriv_mul hρj hgard]
    simp only [Cbnd]
    refine le_trans (Finset.abs_sum_le_sum_abs _ _) (Finset.sum_le_sum ?_)
    intro i hi
    simp only [Finset.mem_range] at hi
    have hij : i ≤ j := Nat.lt_succ_iff.mp hi
    rw [abs_mul, abs_mul]
    have hci : (0 : ℝ) ≤ (j.choose i : ℝ) := by positivity
    rw [abs_of_nonneg hci]
    have h1 : |iteratedDeriv i ρ u| ≤ M i := hM i u hu
    have he : iteratedDeriv (j - i + 1) (Eiter k ρ f) u
        = iteratedDeriv (j - i) (deriv (Eiter k ρ f)) u := by
      rw [iteratedDeriv_succ']
    rw [← he]
    have h2 : |iteratedDeriv (j - i + 1) (Eiter k ρ f) u| ≤ Cbnd M B k (j - i + 1) :=
      ih (j - i + 1) u hu
    exact mul_le_mul (mul_le_mul le_rfl h1 (abs_nonneg _) (by positivity)) h2 (abs_nonneg _)
      (mul_nonneg (by positivity) (hMnn i))

/-- All the iterated derivatives of the smooth step are bounded on `[0,1]`, by a constant
depending on the order. -/
theorem exists_iteratedDeriv_smoothTransition_bound :
    ∃ B : ℕ → ℝ, (∀ m : ℕ, 0 ≤ B m) ∧ ∀ m : ℕ, ∀ u ∈ Set.Icc (0 : ℝ) 1,
      |iteratedDeriv m Real.smoothTransition u| ≤ B m := by
  have hb : ∀ m : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ u ∈ Set.Icc (0 : ℝ) 1,
      |iteratedDeriv m Real.smoothTransition u| ≤ C := by
    intro m
    have hcont : Continuous (iteratedDeriv m Real.smoothTransition) := by
      apply ContDiff.continuous_iteratedDeriv' m
      exact Real.smoothTransition.contDiff
    obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hcont.continuousOn
    exact ⟨max C 0, le_max_right _ _, fun u hu => by
      have h := hC u hu
      rw [Real.norm_eq_abs] at h
      exact le_trans h (le_max_left _ _)⟩
  choose B hB0 hB using hb
  exact ⟨B, hB0, hB⟩

/-- **The engine.**  If `M` bounds every derivative of `ρ` and `B` every derivative of the smooth
step on `[0,1]`, then there is `K : ℕ → ℝ` with `|Eiter k ρ 𝕋 v| ≤ K k` for all `k` and all
`v : ℝ`. -/
theorem exists_Eiter_smoothTransition_bound {ρ : ℝ → ℝ} {M B : ℕ → ℝ}
    (hMnn : ∀ m, 0 ≤ M m) (hBnn : ∀ m, 0 ≤ B m)
    (hρ : ∀ n : ℕ, ContDiff ℝ n ρ)
    (hM : ∀ m : ℕ, ∀ u ∈ Set.Icc (0 : ℝ) 1, |iteratedDeriv m ρ u| ≤ M m)
    (hB : ∀ m : ℕ, ∀ u ∈ Set.Icc (0 : ℝ) 1,
      |iteratedDeriv m Real.smoothTransition u| ≤ B m) :
    ∃ K : ℕ → ℝ, (∀ k : ℕ, 0 ≤ K k) ∧ ∀ (k : ℕ) (v : ℝ),
      |Eiter k ρ Real.smoothTransition v| ≤ K k := by
  refine ⟨fun k => max (Cbnd M B k 0) 1, fun k => le_trans zero_le_one (le_max_right _ _), ?_⟩
  intro k v
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  · subst hk0
    simp only [Eiter_zero]
    have hσ : |Real.smoothTransition v| ≤ 1 := by
      rcases le_or_gt v 0 with hv | hv
      · rw [Real.smoothTransition.zero_of_nonpos hv, abs_zero]
        norm_num
      rcases le_or_gt 1 v with hv1 | hv1
      · rw [Real.smoothTransition.one_of_one_le hv1, abs_one]
      · rw [abs_of_nonneg (Real.smoothTransition.nonneg v)]
        exact Real.smoothTransition.le_one v
    exact le_trans hσ (le_max_right _ _)
  · by_cases hv : v ∈ Set.Icc (0 : ℝ) 1
    · have h := Eiter_deriv_bound_all hMnn hBnn hρ
        Work.FTS.GalBasis.cc.contDiff_smoothTransition hM hB k 0 v hv
      simp only [iteratedDeriv_zero] at h
      exact le_trans h (le_max_left _ _)
    · rw [Set.mem_Icc, not_and_or] at hv
      have hzero : Eiter k ρ Real.smoothTransition v = 0 := by
        rcases hv with hv | hv
        · have hv' : v < 0 := lt_of_not_ge hv
          exact Eiter_eq_zero_of_open_const isOpen_Iio (Set.mem_Iio.mpr hv') (fun w hw => by
            rw [Real.smoothTransition.zero_of_nonpos (le_of_lt hw),
              Real.smoothTransition.zero_of_nonpos (le_of_lt hv')]) k hkpos v
            (Set.mem_Iio.mpr hv')
        · have hv' : 1 < v := lt_of_not_ge hv
          exact Eiter_eq_zero_of_open_const isOpen_Ioi (Set.mem_Ioi.mpr hv') (fun w hw => by
            rw [Real.smoothTransition.one_of_one_le (le_of_lt hw),
              Real.smoothTransition.one_of_one_le (le_of_lt hv')]) k hkpos v
            (Set.mem_Ioi.mpr hv')
      rw [hzero, abs_zero]
      exact le_trans zero_le_one (le_max_right _ _)

end Work.FTS.PhiStar.Honesty.CptApp
