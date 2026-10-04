import Mathlib
import Submission.Work.Diff.STE.B3.SymCalcStep8.CSqZ
import Submission.Work.Diff.STE.B3.SymCalcStep5.conjCut_lapPow
import Submission.Work.Diff.STE.B3.SymCalcStep6.lapPow_toolbox

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `lapPow_CSqZ_le`: the flat Laplacian power `Λ^a` gains exactly `2a` weighted derivatives

`Λ^a = Work.Diff.STE.B3.SymCalcStep5.lapPow a` is the Fourier multiplier with symbol
`flatLam m = Σᵢ (2π mᵢ)²`, and `flatLam m ≤ 4π² ⟨m⟩` for the weight `⟨m⟩ = wt m`.  Hence, on the
weighted `ℓ²` mass `CSqZ t` at an *integer* exponent `t`,

  `CSqZ t (fourierCoeff (Λ^a g)) ≤ (4π²)^{2a} · CSqZ (t + 2a) (fourierCoeff g)`

for every smooth `1`-periodic `g`.  The pointwise bound on the terms is the obvious one,

  `⟨m⟩^t · ‖(flatLam m)^a û(m)‖² ≤ (4π²)^{2a} · ⟨m⟩^{t+2a} ‖û(m)‖²`,

and the summability that makes the comparison of the two `tsum`s legitimate comes from the rapid
decay of the Fourier coefficients of a smooth `1`-periodic function (for a nonnegative exponent),
resp. from `⟨m⟩^t ≤ 1` (for a negative one).
-/

noncomputable section

open scoped BigOperators

namespace Work.Diff.STE.B3.SymCalcStep8

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The weight `⟨m⟩ = wt m`: `⟨m⟩^t · ⟨m⟩^{2a} = ⟨m⟩^{t + 2a}` for `t : ℤ`, `a : ℕ`. -/
lemma wt_zpow_mul_nat (m : ι → ℤ) (t : ℤ) (a : ℕ) :
    (Work.Diff.STE.wt m) ^ t * (Work.Diff.STE.wt m) ^ (2 * a)
      = (Work.Diff.STE.wt m) ^ (t + 2 * (a : ℤ)) := by
  rw [← zpow_natCast (Work.Diff.STE.wt m) (2 * a),
      ← zpow_add₀ (ne_of_gt (Work.Diff.STE.wt_pos m))]
  have h2 : ((2 * a : ℕ) : ℤ) = 2 * (a : ℤ) := by push_cast; ring
  rw [h2]

/-- The weighted mass `∑ ⟨m⟩^t ‖û(m)‖²` converges at *every* integer exponent `t`, for a smooth
`1`-periodic `g`.  For `t ≥ 0` this is the rapid decay of the Fourier coefficients; for `t < 0`
it follows from `⟨m⟩^t ≤ 1`. -/
lemma summable_zpow_wt_fourierCoeff (g : (ι → ℝ) → ℂ) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hper : Work.Diff.STE.Periodic1 g) (m : ℤ) :
    Summable (fun k : ι → ℤ =>
      (Work.Diff.STE.wt k) ^ m * ‖Work.Diff.STE.fourierCoeff g k‖ ^ 2) := by
  by_cases hm : 0 ≤ m
  · have hcast : ((m.toNat : ℕ) : ℤ) = m := Int.toNat_of_nonneg hm
    have h1 := Work.Diff.STE.summable_weighted_fourierCoeff_of_contDiff g hg hper m.toNat
    have hkey (k : ι → ℤ) :
        (Work.Diff.STE.wt k) ^ m = (Work.Diff.STE.wt k) ^ m.toNat := by
      conv_lhs => rw [← hcast]
      rw [zpow_natCast]
    refine h1.congr (fun k => ?_)
    rw [hkey k]
  · have hm' : m < 0 := lt_of_not_ge hm
    refine Summable.of_nonneg_of_le
      (f := fun k : ι → ℤ => ‖Work.Diff.STE.fourierCoeff g k‖ ^ 2)
      (fun k => ?_) (fun k => ?_) ?_
    · exact mul_nonneg (zpow_nonneg (le_of_lt (Work.Diff.STE.wt_pos k)) m) (sq_nonneg _)
    · have h := zpow_le_one_of_nonpos₀ (Work.Diff.STE.wt_one_le k) (le_of_lt hm')
      calc (Work.Diff.STE.wt k) ^ m * ‖Work.Diff.STE.fourierCoeff g k‖ ^ 2
          ≤ 1 * ‖Work.Diff.STE.fourierCoeff g k‖ ^ 2 :=
            mul_le_mul_of_nonneg_right h (sq_nonneg _)
        _ = ‖Work.Diff.STE.fourierCoeff g k‖ ^ 2 := one_mul _
    · have h1 := Work.Diff.STE.summable_weighted_fourierCoeff_of_contDiff g hg hper 0
      simpa using h1

/-- The pointwise multiplier comparison, in the shape used by the `tsum` comparison. -/
lemma lapPow_term_le (a : ℕ) (t : ℤ) (g : (ι → ℝ) → ℂ) (m : ι → ℤ) :
    (Work.Diff.STE.wt m) ^ t
        * ‖(((Work.Diff.STE.B3.SymCalc.flatLam m) ^ a : ℝ) : ℂ)
            * Work.Diff.STE.fourierCoeff g m‖ ^ 2
      ≤ (4 * Real.pi ^ 2) ^ (2 * a)
          * ((Work.Diff.STE.wt m) ^ (t + 2 * (a : ℤ))
              * ‖Work.Diff.STE.fourierCoeff g m‖ ^ 2) := by
  have hnorm : ‖(((Work.Diff.STE.B3.SymCalc.flatLam m) ^ a : ℝ) : ℂ)
        * Work.Diff.STE.fourierCoeff g m‖ ^ 2
      = (Work.Diff.STE.B3.SymCalc.flatLam m) ^ (2 * a)
        * ‖Work.Diff.STE.fourierCoeff g m‖ ^ 2 := by
    rw [norm_mul, mul_pow, Work.Diff.STE.B3.SymCalcStep6.norm_flatLam_pow_cast,
      ← pow_mul, Nat.mul_comm]
  have hflat : (Work.Diff.STE.B3.SymCalc.flatLam m) ^ (2 * a)
      ≤ (4 * Real.pi ^ 2) ^ (2 * a) * (Work.Diff.STE.wt m) ^ (2 * a) := by
    calc (Work.Diff.STE.B3.SymCalc.flatLam m) ^ (2 * a)
        ≤ ((4 * Real.pi ^ 2) * Work.Diff.STE.wt m) ^ (2 * a) :=
          pow_le_pow_left₀ (Work.Diff.STE.B3.SymCalcStep6.flatLam_nonneg m)
            (Work.Diff.STE.B3.SymCalcStep6.flatLam_le_wt m) (2 * a)
      _ = (4 * Real.pi ^ 2) ^ (2 * a) * (Work.Diff.STE.wt m) ^ (2 * a) := by
          rw [mul_pow]
  rw [hnorm]
  calc (Work.Diff.STE.wt m) ^ t
        * ((Work.Diff.STE.B3.SymCalc.flatLam m) ^ (2 * a)
            * ‖Work.Diff.STE.fourierCoeff g m‖ ^ 2)
      ≤ (Work.Diff.STE.wt m) ^ t
          * (((4 * Real.pi ^ 2) ^ (2 * a) * (Work.Diff.STE.wt m) ^ (2 * a))
              * ‖Work.Diff.STE.fourierCoeff g m‖ ^ 2) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hflat (sq_nonneg _))
          (zpow_nonneg (le_of_lt (Work.Diff.STE.wt_pos m)) t)
    _ = (4 * Real.pi ^ 2) ^ (2 * a)
          * ((Work.Diff.STE.wt m) ^ (t + 2 * (a : ℤ))
              * ‖Work.Diff.STE.fourierCoeff g m‖ ^ 2) := by
        rw [show (Work.Diff.STE.wt m) ^ t
              * (((4 * Real.pi ^ 2) ^ (2 * a) * (Work.Diff.STE.wt m) ^ (2 * a))
                  * ‖Work.Diff.STE.fourierCoeff g m‖ ^ 2)
            = (4 * Real.pi ^ 2) ^ (2 * a)
              * ((Work.Diff.STE.wt m) ^ t * (Work.Diff.STE.wt m) ^ (2 * a))
              * ‖Work.Diff.STE.fourierCoeff g m‖ ^ 2 by ring]
        rw [wt_zpow_mul_nat, mul_assoc]

theorem lapPow_CSqZ_le {ι : Type*} [Fintype ι] [DecidableEq ι] (a : ℕ) (t : ℤ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ g : (ι → ℝ) → ℂ, ContDiff ℝ (⊤ : ℕ∞) g → Work.Diff.STE.Periodic1 g →
      Work.Diff.STE.B3.SymCalcStep8.CSqZ t
          (Work.Diff.STE.fourierCoeff (Work.Diff.STE.B3.SymCalcStep5.lapPow a g))
        ≤ C * Work.Diff.STE.B3.SymCalcStep8.CSqZ (t + 2 * (a : ℤ))
            (Work.Diff.STE.fourierCoeff g) := by
  classical
  refine ⟨(4 * Real.pi ^ 2) ^ (2 * a), by positivity, ?_⟩
  intro g hg hper
  have hId := (Work.Diff.STE.B3.SymCalcStep6.lapPow_toolbox a 0).1 g hg hper
  rw [hId]
  simp only [CSqZ]
  have hsumR : Summable (fun m : ι → ℤ => (4 * Real.pi ^ 2) ^ (2 * a)
      * ((Work.Diff.STE.wt m) ^ (t + 2 * (a : ℤ))
          * ‖Work.Diff.STE.fourierCoeff g m‖ ^ 2)) :=
    (summable_zpow_wt_fourierCoeff g hg hper (t + 2 * (a : ℤ))).mul_left _
  have hsumL : Summable (fun m : ι → ℤ => (Work.Diff.STE.wt m) ^ t
      * ‖(((Work.Diff.STE.B3.SymCalc.flatLam m) ^ a : ℝ) : ℂ)
          * Work.Diff.STE.fourierCoeff g m‖ ^ 2) :=
    Summable.of_nonneg_of_le
      (fun m => mul_nonneg (zpow_nonneg (le_of_lt (Work.Diff.STE.wt_pos m)) t) (sq_nonneg _))
      (fun m => lapPow_term_le a t g m) hsumR
  have hle := Summable.tsum_le_tsum (fun m => lapPow_term_le a t g m) hsumL hsumR
  rw [tsum_mul_left] at hle
  exact hle

end Work.Diff.STE.B3.SymCalcStep8
