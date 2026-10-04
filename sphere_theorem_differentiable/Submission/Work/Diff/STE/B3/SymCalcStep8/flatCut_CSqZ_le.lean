import Mathlib
import Submission.Work.Diff.STE.B3.SymCalcStep8.CSqZ
import Submission.Work.Diff.STE.B3.SymCalcStep1.conj_cut_aux

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.B3.SymCalcStep8

/-!
# `flatCut_CSqZ_le`: the Friedrichs cutoff `S_ε` is a *contraction* on every weighted `ℓ²` mass

The function-level cutoff `S_ε = flatCut ρ ε` acts on Fourier coefficients by
`û ↦ (fun k => (ρ (ε • k) : ℂ) · û k)` (`Work.Diff.STE.B3.SymCalcStep1.fourierCoeff_flatCut`), and
`‖ρ‖ ≤ 1` makes this multiplier a *contraction*:

  `CSqZ t (fourierCoeff (flatCut ρ ε W)) ≤ CSqZ t (fourierCoeff W)`

for every `t : ℤ` and every smooth `1`-periodic `W`.  The comparison of the two `tsum`s is
legitimate because the weighted mass of the Fourier coefficients of a smooth `1`-periodic function
converges at *every* integer exponent (`flatCut_summable_zpow` below): for `t ≥ 0` this is the
rapid decay of the Fourier coefficients and for `t < 0` it follows from `wt k ≥ 1`.

Note that no gain in `ε` is claimed here (unlike `flat_multiplier_gain_CSqZ`); the point of this
lemma is that `S_ε` never loses derivatives, uniformly in `ε`.
-/

open scoped BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The weighted mass `∑_k ⟨k⟩^t ‖û(k)‖²` converges at **every** integer exponent `t`, for every
smooth `1`-periodic `g`.  For `t ≥ 0` this is the rapid decay of the Fourier coefficients
(`summable_weighted_fourierCoeff_of_contDiff`); for `t < 0` it follows from `⟨k⟩^t ≤ 1`. -/
lemma flatCut_summable_zpow (g : (ι → ℝ) → ℂ) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hper : Work.Diff.STE.Periodic1 g) (m : ℤ) :
    Summable (fun k : ι → ℤ =>
      (Work.Diff.STE.wt k) ^ m * ‖Work.Diff.STE.fourierCoeff g k‖ ^ 2) := by
  by_cases hm : 0 ≤ m
  · have hcast : ((m.toNat : ℕ) : ℤ) = m := Int.toNat_of_nonneg hm
    have h1 := Work.Diff.STE.summable_weighted_fourierCoeff_of_contDiff g hg hper m.toNat
    have hkey : ∀ k : ι → ℤ, (Work.Diff.STE.wt k) ^ m = (Work.Diff.STE.wt k) ^ m.toNat := by
      intro k
      conv_lhs => rw [hcast.symm]
      exact zpow_natCast (Work.Diff.STE.wt k) m.toNat
    refine h1.congr (fun k => ?_)
    rw [hkey k]
  · refine Summable.of_nonneg_of_le
      (f := fun k : ι → ℤ => ‖Work.Diff.STE.fourierCoeff g k‖ ^ 2)
      (fun k => mul_nonneg (zpow_nonneg (le_of_lt (Work.Diff.STE.wt_pos k)) m) (sq_nonneg _))
      (fun k => ?_)
      (by simpa using
        (Work.Diff.STE.summable_weighted_fourierCoeff_of_contDiff g hg hper 0 :
          Summable (fun k : ι → ℤ =>
            (Work.Diff.STE.wt k) ^ 0 * ‖Work.Diff.STE.fourierCoeff g k‖ ^ 2)))
    have hle : (Work.Diff.STE.wt k) ^ m ≤ 1 :=
      zpow_le_one_of_nonpos₀ (Work.Diff.STE.wt_one_le k) (le_of_lt (lt_of_not_ge hm))
    calc (Work.Diff.STE.wt k) ^ m * ‖Work.Diff.STE.fourierCoeff g k‖ ^ 2
        ≤ 1 * ‖Work.Diff.STE.fourierCoeff g k‖ ^ 2 :=
          mul_le_mul_of_nonneg_right hle (sq_nonneg _)
      _ = ‖Work.Diff.STE.fourierCoeff g k‖ ^ 2 := one_mul _

/-- The pointwise multiplier comparison: since `‖ρ‖ ≤ 1`, the `m`-th term of
`CSqZ t (fourierCoeff (flatCut ρ ε g))` is at most the `m`-th term of `CSqZ t (fourierCoeff g)`. -/
lemma flatCut_term_le (ρ : (ι → ℝ) → ℝ) (hρ : ∀ y : ι → ℝ, ‖ρ y‖ ≤ 1) (ε : ℝ) (t : ℤ)
    (g : (ι → ℝ) → ℂ) (m : ι → ℤ) :
    (Work.Diff.STE.wt m) ^ t
        * ‖(ρ (ε • (fun i => (m i : ℝ))) : ℂ) * Work.Diff.STE.fourierCoeff g m‖ ^ 2
      ≤ (Work.Diff.STE.wt m) ^ t * ‖Work.Diff.STE.fourierCoeff g m‖ ^ 2 := by
  refine mul_le_mul_of_nonneg_left ?_ (zpow_nonneg (le_of_lt (Work.Diff.STE.wt_pos m)) t)
  have hmul : ‖(ρ (ε • (fun i => (m i : ℝ))) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs]
    exact hρ _
  have hsq : ‖(ρ (ε • (fun i => (m i : ℝ))) : ℂ)‖ ^ 2 ≤ 1 :=
    pow_le_one₀ (norm_nonneg _) hmul
  rw [norm_mul, mul_pow]
  calc ‖(ρ (ε • (fun i => (m i : ℝ))) : ℂ)‖ ^ 2 * ‖Work.Diff.STE.fourierCoeff g m‖ ^ 2
      ≤ 1 * ‖Work.Diff.STE.fourierCoeff g m‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hsq (sq_nonneg _)
    _ = ‖Work.Diff.STE.fourierCoeff g m‖ ^ 2 := one_mul _

theorem flatCut_CSqZ_le {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ρ : (ι → ℝ) → ℝ) (hρ : ∀ y : ι → ℝ, ‖ρ y‖ ≤ 1) (ε : ℝ) (t : ℤ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ W : (ι → ℝ) → ℂ, ContDiff ℝ (⊤ : ℕ∞) W → Work.Diff.STE.Periodic1 W →
      Work.Diff.STE.B3.SymCalcStep8.CSqZ t
          (Work.Diff.STE.fourierCoeff (Work.Diff.STE.B3.SymCalc.flatCut ρ ε W))
        ≤ C * Work.Diff.STE.B3.SymCalcStep8.CSqZ t (Work.Diff.STE.fourierCoeff W) := by
  classical
  refine ⟨1, zero_le_one, ?_⟩
  intro W hW hper
  rw [one_mul]
  have hcoeff : Work.Diff.STE.fourierCoeff (Work.Diff.STE.B3.SymCalc.flatCut ρ ε W)
      = fun k : ι → ℤ => (ρ (ε • (fun i => (k i : ℝ))) : ℂ)
          * Work.Diff.STE.fourierCoeff W k :=
    funext fun k => Work.Diff.STE.B3.SymCalcStep1.fourierCoeff_flatCut ρ hρ ε hW hper k
  rw [hcoeff]
  simp only [CSqZ]
  have hterm := fun m : ι → ℤ => flatCut_term_le ρ hρ ε t W m
  have hsumR : Summable (fun m : ι → ℤ =>
      (Work.Diff.STE.wt m) ^ t * ‖Work.Diff.STE.fourierCoeff W m‖ ^ 2) :=
    flatCut_summable_zpow W hW hper t
  have hsumL : Summable (fun m : ι → ℤ => (Work.Diff.STE.wt m) ^ t
      * ‖(ρ (ε • (fun i => (m i : ℝ))) : ℂ) * Work.Diff.STE.fourierCoeff W m‖ ^ 2) :=
    Summable.of_nonneg_of_le
      (fun m => mul_nonneg (zpow_nonneg (le_of_lt (Work.Diff.STE.wt_pos m)) t) (sq_nonneg _))
      hterm hsumR
  exact Summable.tsum_le_tsum hterm hsumL hsumR

end Work.Diff.STE.B3.SymCalcStep8
