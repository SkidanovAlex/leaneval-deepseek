import Mathlib
import Submission.Work.Diff.STE.B3.SymCalcStep8.CSqZ
import Submission.Work.Diff.STE.fourierCoeff_pd
import Submission.Work.Diff.STE.summable_weighted_fourierCoeff_of_contDiff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# One partial derivative costs one power of the weight

For a smooth `1`-periodic `W : (ι → ℝ) → ℂ` and an integer exponent `t`, the partial derivative
`∂ᵢ W = pd i W` is the Fourier multiplier `m ↦ 2πi mᵢ` (`Work.Diff.STE.fourierCoeff_pd`), so on the
integer-exponent weighted `ℓ²` mass `CSqZ` one has

  `CSqZ t (fourierCoeff (∂ᵢ W)) ≤ 4π² · CSqZ (t + 1) (fourierCoeff W)`.

The constant is the sharp one: the pointwise comparison is
`⟨m⟩^t ‖2πi mᵢ ŵ(m)‖² ≤ 4π² ⟨m⟩^{t+1} ‖ŵ(m)‖²`, which is the single inequality
`mᵢ² ≤ ⟨m⟩ = 1 + Σ_j m_j²` multiplied by `4π² ⟨m⟩^t ‖ŵ(m)‖² ≥ 0`.
-/

noncomputable section

open scoped BigOperators

namespace Work.Diff.STE.B3.SymCalcStep8

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The Fourier multiplier of `∂ᵢ`, `m ↦ 2πi mᵢ` (written so as to be syntactically the multiplier
produced by `Work.Diff.STE.fourierCoeff_pd`). -/
def pdCSqZ_mult (i : ι) (m : ι → ℤ) : ℂ := 2 * Real.pi * Complex.I * ((m i : ℤ) : ℂ)

/-- The squared modulus of the multiplier of `∂ᵢ` is `(2π mᵢ)²`. -/
lemma pdCSqZ_norm_sq_factor (i : ι) (m : ι → ℤ) :
    ‖pdCSqZ_mult i m‖ ^ 2 = (2 * Real.pi * (((m i : ℤ)) : ℝ)) ^ 2 := by
  have h : pdCSqZ_mult i m
      = (((2 * Real.pi * (((m i : ℤ)) : ℝ)) : ℝ) : ℂ) * Complex.I := by
    simp only [pdCSqZ_mult]
    push_cast
    ring
  rw [h, ← Complex.normSq_eq_norm_sq, Complex.normSq_mul, Complex.normSq_I, mul_one,
    Complex.normSq_ofReal]
  ring

/-- One coordinate square is dominated by the weight `⟨m⟩ = 1 + Σ_j m_j²`. -/
lemma pdCSqZ_wt_coord_sq_le (i : ι) (m : ι → ℤ) :
    (((m i : ℤ)) : ℝ) ^ 2 ≤ Work.Diff.STE.wt m := by
  have h := Finset.single_le_sum (s := Finset.univ)
    (f := fun j : ι => (((m j : ℤ)) : ℝ) ^ 2) (fun j _ => sq_nonneg _) (Finset.mem_univ i)
  have h' : (((m i : ℤ)) : ℝ) ^ 2 ≤ ∑ j : ι, (((m j : ℤ)) : ℝ) ^ 2 := by simpa using h
  simp only [Work.Diff.STE.wt]
  linarith

/-- **The pointwise comparison**: one `∂ᵢ` costs one power of the weight. -/
lemma pdCSqZ_term_le (i : ι) (t : ℤ) (g : (ι → ℝ) → ℂ) (m : ι → ℤ) :
    (Work.Diff.STE.wt m) ^ t * ‖pdCSqZ_mult i m * Work.Diff.STE.fourierCoeff g m‖ ^ 2
      ≤ (4 * Real.pi ^ 2)
          * ((Work.Diff.STE.wt m) ^ (t + 1) * ‖Work.Diff.STE.fourierCoeff g m‖ ^ 2) := by
  have hw : 0 < Work.Diff.STE.wt m := Work.Diff.STE.wt_pos m
  have hsq : (((m i : ℤ)) : ℝ) ^ 2 ≤ Work.Diff.STE.wt m := pdCSqZ_wt_coord_sq_le i m
  have hcoef : (2 * Real.pi * (((m i : ℤ)) : ℝ)) ^ 2 ≤ 4 * Real.pi ^ 2 * Work.Diff.STE.wt m := by
    have h2 : (2 * Real.pi * (((m i : ℤ)) : ℝ)) ^ 2
        = 4 * Real.pi ^ 2 * ((((m i : ℤ)) : ℝ) ^ 2) := by ring
    rw [h2]
    exact mul_le_mul_of_nonneg_left hsq (by positivity)
  have hnorm : ‖pdCSqZ_mult i m * Work.Diff.STE.fourierCoeff g m‖ ^ 2
      = (2 * Real.pi * (((m i : ℤ)) : ℝ)) ^ 2 * ‖Work.Diff.STE.fourierCoeff g m‖ ^ 2 := by
    rw [norm_mul, mul_pow, pdCSqZ_norm_sq_factor]
  have hwt : (Work.Diff.STE.wt m) ^ (t + 1)
      = (Work.Diff.STE.wt m) ^ t * Work.Diff.STE.wt m := by
    rw [zpow_add₀ (ne_of_gt hw), zpow_one]
  rw [hnorm, hwt]
  calc (Work.Diff.STE.wt m) ^ t
        * ((2 * Real.pi * (((m i : ℤ)) : ℝ)) ^ 2 * ‖Work.Diff.STE.fourierCoeff g m‖ ^ 2)
      ≤ (Work.Diff.STE.wt m) ^ t
          * ((4 * Real.pi ^ 2 * Work.Diff.STE.wt m) * ‖Work.Diff.STE.fourierCoeff g m‖ ^ 2) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hcoef (sq_nonneg _))
          (zpow_nonneg (le_of_lt hw) t)
    _ = (4 * Real.pi ^ 2)
          * ((Work.Diff.STE.wt m) ^ t * Work.Diff.STE.wt m
              * ‖Work.Diff.STE.fourierCoeff g m‖ ^ 2) := by ring

/-- **Summability of the weighted Fourier mass at every integer exponent**, for a smooth
`1`-periodic `g`.  For `e ≥ 0` this is the rapid decay of the Fourier coefficients of a smooth
periodic function; for `e < 0` it follows from `⟨m⟩^e ≤ 1`. -/
lemma pdCSqZ_summable_zpow (g : (ι → ℝ) → ℂ) (hg : ContDiff ℝ (⊤ : ℕ∞) g)
    (hper : Work.Diff.STE.Periodic1 g) (e : ℤ) :
    Summable (fun m : ι → ℤ =>
      (Work.Diff.STE.wt m) ^ e * ‖Work.Diff.STE.fourierCoeff g m‖ ^ 2) := by
  by_cases he : 0 ≤ e
  · have hcast : ((e.toNat : ℕ) : ℤ) = e := Int.toNat_of_nonneg he
    have h1 := Work.Diff.STE.summable_weighted_fourierCoeff_of_contDiff g hg hper e.toNat
    refine h1.congr (fun m => ?_)
    have hkey : (Work.Diff.STE.wt m) ^ e = (Work.Diff.STE.wt m) ^ e.toNat := by
      conv_lhs => rw [← hcast]
      rw [zpow_natCast]
    rw [hkey]
  · have he' : e < 0 := lt_of_not_ge he
    refine Summable.of_nonneg_of_le (f := fun m : ι → ℤ => ‖Work.Diff.STE.fourierCoeff g m‖ ^ 2)
      (fun m => mul_nonneg (zpow_nonneg (le_of_lt (Work.Diff.STE.wt_pos m)) e) (sq_nonneg _))
      (fun m => ?_) ?_
    · have h := zpow_le_one_of_nonpos₀ (Work.Diff.STE.wt_one_le m) (le_of_lt he')
      calc (Work.Diff.STE.wt m) ^ e * ‖Work.Diff.STE.fourierCoeff g m‖ ^ 2
          ≤ 1 * ‖Work.Diff.STE.fourierCoeff g m‖ ^ 2 :=
            mul_le_mul_of_nonneg_right h (sq_nonneg _)
        _ = ‖Work.Diff.STE.fourierCoeff g m‖ ^ 2 := one_mul _
    · simpa using Work.Diff.STE.summable_weighted_fourierCoeff_of_contDiff g hg hper 0

theorem pd_CSqZ_le {ι : Type*} [Fintype ι] [DecidableEq ι] (i : ι) (t : ℤ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ W : (ι → ℝ) → ℂ, ContDiff ℝ (⊤ : ℕ∞) W → Work.Diff.STE.Periodic1 W →
      Work.Diff.STE.B3.SymCalcStep8.CSqZ t
          (Work.Diff.STE.fourierCoeff (Work.Diff.STE.pd i W))
        ≤ C * Work.Diff.STE.B3.SymCalcStep8.CSqZ (t + 1) (Work.Diff.STE.fourierCoeff W) := by
  classical
  refine ⟨4 * Real.pi ^ 2, by positivity, ?_⟩
  intro W hW hper
  have h1 : ContDiff ℝ 1 W := hW.of_le (WithTop.coe_le_coe.mpr le_top)
  have hp : Work.Diff.STE.PeriodicIn i W := fun x => hper i x
  have hcoeff : Work.Diff.STE.fourierCoeff (Work.Diff.STE.pd i W)
      = fun m : ι → ℤ => pdCSqZ_mult i m * Work.Diff.STE.fourierCoeff W m := by
    funext m
    have h := Work.Diff.STE.fourierCoeff_pd i W m h1 hp
    simpa only [pdCSqZ_mult] using h
  rw [hcoeff]
  simp only [CSqZ]
  have hsumR : Summable (fun m : ι → ℤ => (4 * Real.pi ^ 2)
      * ((Work.Diff.STE.wt m) ^ (t + 1) * ‖Work.Diff.STE.fourierCoeff W m‖ ^ 2)) :=
    (pdCSqZ_summable_zpow W hW hper (t + 1)).mul_left _
  have hsumL : Summable (fun m : ι → ℤ => (Work.Diff.STE.wt m) ^ t
      * ‖pdCSqZ_mult i m * Work.Diff.STE.fourierCoeff W m‖ ^ 2) :=
    Summable.of_nonneg_of_le
      (fun m => mul_nonneg (zpow_nonneg (le_of_lt (Work.Diff.STE.wt_pos m)) t) (sq_nonneg _))
      (fun m => pdCSqZ_term_le i t W m) hsumR
  have hle := Summable.tsum_le_tsum (fun m => pdCSqZ_term_le i t W m) hsumL hsumR
  rw [tsum_mul_left] at hle
  exact hle

end Work.Diff.STE.B3.SymCalcStep8
