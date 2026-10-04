import Mathlib
import Submission.Work.Diff.STE.B3.SymCalcStep5.conjCut_lapPow
import Submission.Work.Diff.STE.summable_weighted_fourierCoeff_of_contDiff
import Submission.Work.Diff.STE.contDiff_seriesFun
import Submission.Work.Diff.STE.flat.fourierCoeff_seriesFun
import Submission.Work.Diff.STE.flat.seriesFun_fourierCoeff
import Submission.Work.Diff.STE.B3.ENormSq_le_CSq

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The flat Laplacian power `Λ^j` as a Fourier multiplier: the toolbox

`Work.Diff.STE.B3.SymCalcStep5.lapPow j` is the flat Laplacian power `Λ^j` on the torus, *defined*
as the Fourier multiplier with symbol `flatLam m ^ j`.  This file records the four elementary
facts that the symbol-calculus layer of B3 needs about it, all of them consequences of
`flatLam m = Σᵢ (2π mᵢ)²` being comparable to the weight `⟨m⟩² = wt m`:

1. `fourierCoeff (Λ^j w) k = (flatLam k)^j · û(k)` — Fourier inversion for the absolutely
   convergent series `seriesFun (fun k => (flatLam k)^j û(k))` (`flat.fourierCoeff_seriesFun`),
   the absolute summability coming from the rapid decay of `û` for a smooth `1`-periodic `w`;
2. `CSq s (fourierCoeff (Λ^j w)) ≤ C · CSq (s + 2j) (fourierCoeff w)` — the multiplier is a
   polynomial of degree `j` in `flatLam`, and `flatLam m ≤ 4π² wt m`, so the weight shifts by
   exactly `2j`, with the explicit constant `C = (4π²)^{2j}`;
3. `Λ^j w` is smooth for smooth `w` — `contDiff_seriesFun`, whose hypothesis (summability of
   `⟨k⟩^N ‖c k‖` for every `N`) is again the rapid decay of `û`;
4. `Λ^j w` is `1`-periodic for *every* `w` — a `seriesFun` is a sum of characters.
-/

noncomputable section

namespace Work.Diff.STE.B3.SymCalcStep6

open MeasureTheory BigOperators

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- `lapPow j w` is *by definition* the Fourier series with coefficients
`(flatLam k)^j · û(k)`. -/
lemma lapPow_eq_seriesFun (j : ℕ) (w : (ι → ℝ) → ℂ) :
    Work.Diff.STE.B3.SymCalcStep5.lapPow j w
      = Work.Diff.STE.seriesFun
          (fun k : ι → ℤ => (((Work.Diff.STE.B3.SymCalc.flatLam k) ^ j : ℝ) : ℂ)
            * Work.Diff.STE.fourierCoeff w k) := rfl

/-- The flat symbol `flatLam m = Σᵢ (2π mᵢ)²` is nonnegative. -/
lemma flatLam_nonneg (k : ι → ℤ) : 0 ≤ Work.Diff.STE.B3.SymCalc.flatLam k := by
  simp only [Work.Diff.STE.B3.SymCalc.flatLam]
  exact Finset.sum_nonneg fun i _ => sq_nonneg _

/-- The flat symbol is dominated by the weight: `flatLam m ≤ 4π² ⟨m⟩`. -/
lemma flatLam_le_wt (k : ι → ℤ) :
    Work.Diff.STE.B3.SymCalc.flatLam k ≤ (4 * Real.pi ^ 2) * Work.Diff.STE.wt k := by
  have hsum : ∑ i, ((k i : ℝ)) ^ 2 ≤ Work.Diff.STE.wt k := by
    have h1 : (0 : ℝ) ≤ ∑ i, (((k i : ℤ)) : ℝ) ^ 2 :=
      Finset.sum_nonneg fun i _ => sq_nonneg _
    simp only [Work.Diff.STE.wt]
    linarith
  calc Work.Diff.STE.B3.SymCalc.flatLam k
      = ∑ i, (2 * Real.pi * (k i : ℝ)) ^ 2 := rfl
    _ = (4 * Real.pi ^ 2) * ∑ i, ((k i : ℝ)) ^ 2 := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun i _ => by ring
    _ ≤ (4 * Real.pi ^ 2) * Work.Diff.STE.wt k :=
        mul_le_mul_of_nonneg_left hsum (by positivity)

/-- The modulus of the multiplier `(flatLam k)^j` (viewed as a complex number) is
`(flatLam k)^j`. -/
lemma norm_flatLam_pow_cast (j : ℕ) (k : ι → ℤ) :
    ‖((((Work.Diff.STE.B3.SymCalc.flatLam k) ^ j : ℝ)) : ℂ)‖
      = (Work.Diff.STE.B3.SymCalc.flatLam k) ^ j := by
  rw [Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (pow_nonneg (flatLam_nonneg k) j)]

/-- The pointwise multiplier bound: `‖(flatLam k)^j‖ ≤ (4π²)^j ⟨k⟩^j`. -/
lemma norm_flatLam_pow_cast_le (j : ℕ) (k : ι → ℤ) :
    ‖((((Work.Diff.STE.B3.SymCalc.flatLam k) ^ j : ℝ)) : ℂ)‖
      ≤ (4 * Real.pi ^ 2) ^ j * (Work.Diff.STE.wt k) ^ j := by
  rw [norm_flatLam_pow_cast]
  calc (Work.Diff.STE.B3.SymCalc.flatLam k) ^ j
      ≤ ((4 * Real.pi ^ 2) * Work.Diff.STE.wt k) ^ j :=
        pow_le_pow_left₀ (flatLam_nonneg k) (flatLam_le_wt k) j
    _ = (4 * Real.pi ^ 2) ^ j * (Work.Diff.STE.wt k) ^ j := by rw [mul_pow]

/-- **Weighted `ℓ¹` decay of the multiplier family.**  For a smooth `1`-periodic `w`, every weight
`⟨k⟩^N` times the modulus of the `k`-th coefficient `(flatLam k)^j û(k)` of `Λ^j w` is summable.
This is the rapid decay input of both Fourier inversion and the smoothness of the series. -/
lemma summable_wt_pow_lapCoeff (j N : ℕ) (w : (ι → ℝ) → ℂ)
    (hw : ContDiff ℝ (⊤ : ℕ∞) w) (hper : Work.Diff.STE.Periodic1 w) :
    Summable (fun k : ι → ℤ => (Work.Diff.STE.wt k) ^ N *
      ‖((((Work.Diff.STE.B3.SymCalc.flatLam k) ^ j : ℝ)) : ℂ)
        * Work.Diff.STE.fourierCoeff w k‖) := by
  have hbase :=
    Work.Diff.STE.summable_wt_pow_norm_fourierCoeff_of_contDiff w hw hper (N + j)
  refine Summable.of_nonneg_of_le
    (fun k => mul_nonneg (pow_nonneg (Work.Diff.STE.wt_pos k).le N) (norm_nonneg _))
    (fun k => ?_) (hbase.mul_left ((4 * Real.pi ^ 2) ^ j))
  rw [norm_mul]
  calc (Work.Diff.STE.wt k) ^ N *
        (‖((((Work.Diff.STE.B3.SymCalc.flatLam k) ^ j : ℝ)) : ℂ)‖
          * ‖Work.Diff.STE.fourierCoeff w k‖)
      ≤ (Work.Diff.STE.wt k) ^ N *
          (((4 * Real.pi ^ 2) ^ j * (Work.Diff.STE.wt k) ^ j)
            * ‖Work.Diff.STE.fourierCoeff w k‖) := by
        refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg (Work.Diff.STE.wt_pos k).le N)
        exact mul_le_mul_of_nonneg_right (norm_flatLam_pow_cast_le j k) (norm_nonneg _)
    _ = (4 * Real.pi ^ 2) ^ j *
          ((Work.Diff.STE.wt k) ^ (N + j) * ‖Work.Diff.STE.fourierCoeff w k‖) := by
        rw [show (Work.Diff.STE.wt k) ^ N *
              (((4 * Real.pi ^ 2) ^ j * (Work.Diff.STE.wt k) ^ j)
                * ‖Work.Diff.STE.fourierCoeff w k‖)
            = (4 * Real.pi ^ 2) ^ j
              * ((Work.Diff.STE.wt k) ^ N * (Work.Diff.STE.wt k) ^ j)
              * ‖Work.Diff.STE.fourierCoeff w k‖ by ring]
        rw [← pow_add]
        ring

theorem lapPow_toolbox
    {ι : Type*} [Fintype ι] [DecidableEq ι] (j : ℕ) (s : ℕ) :
    (∀ w : (ι → ℝ) → ℂ, ContDiff ℝ (⊤ : ℕ∞) w → Work.Diff.STE.Periodic1 w →
      Work.Diff.STE.fourierCoeff (Work.Diff.STE.B3.SymCalcStep5.lapPow j w)
        = fun k : ι → ℤ => (((Work.Diff.STE.B3.SymCalc.flatLam k) ^ j : ℝ) : ℂ)
            * Work.Diff.STE.fourierCoeff w k)
    ∧ (∃ C : ℝ, 0 ≤ C ∧ ∀ w : (ι → ℝ) → ℂ, ContDiff ℝ (⊤ : ℕ∞) w →
        Work.Diff.STE.Periodic1 w →
        Work.Diff.STE.CSq s (Work.Diff.STE.fourierCoeff (Work.Diff.STE.B3.SymCalcStep5.lapPow j w))
          ≤ C * Work.Diff.STE.CSq (s + 2 * j) (Work.Diff.STE.fourierCoeff w))
    ∧ (∀ w : (ι → ℝ) → ℂ, ContDiff ℝ (⊤ : ℕ∞) w → Work.Diff.STE.Periodic1 w →
        ContDiff ℝ (⊤ : ℕ∞) (Work.Diff.STE.B3.SymCalcStep5.lapPow j w))
    ∧ (∀ w : (ι → ℝ) → ℂ, Work.Diff.STE.Periodic1 (Work.Diff.STE.B3.SymCalcStep5.lapPow j w)) := by
  classical
  have hId : ∀ w : (ι → ℝ) → ℂ, ContDiff ℝ (⊤ : ℕ∞) w → Work.Diff.STE.Periodic1 w →
      Work.Diff.STE.fourierCoeff (Work.Diff.STE.B3.SymCalcStep5.lapPow j w)
        = fun k : ι → ℤ => (((Work.Diff.STE.B3.SymCalc.flatLam k) ^ j : ℝ) : ℂ)
            * Work.Diff.STE.fourierCoeff w k := by
    intro w hw hper
    rw [lapPow_eq_seriesFun]
    funext k
    refine Work.Diff.STE.flat.fourierCoeff_seriesFun _ ?_ k
    have h := summable_wt_pow_lapCoeff (ι := ι) j 0 w hw hper
    simpa using h
  refine ⟨hId, ?_, ?_, ?_⟩
  · refine ⟨(4 * Real.pi ^ 2) ^ (2 * j), pow_nonneg (by positivity) _, ?_⟩
    intro w hw hper
    rw [hId w hw hper]
    have hsum := Work.Diff.STE.summable_weighted_fourierCoeff_of_contDiff w hw hper (s + 2 * j)
    have hpt : ∀ k : ι → ℤ,
        (Work.Diff.STE.wt k) ^ s
            * ‖((((Work.Diff.STE.B3.SymCalc.flatLam k) ^ j : ℝ)) : ℂ)
                * Work.Diff.STE.fourierCoeff w k‖ ^ 2
          ≤ (4 * Real.pi ^ 2) ^ (2 * j)
            * ((Work.Diff.STE.wt k) ^ (s + 2 * j)
                * ‖Work.Diff.STE.fourierCoeff w k‖ ^ 2) := by
      intro k
      have hnorm : ‖((((Work.Diff.STE.B3.SymCalc.flatLam k) ^ j : ℝ)) : ℂ)
            * Work.Diff.STE.fourierCoeff w k‖ ^ 2
          = (Work.Diff.STE.B3.SymCalc.flatLam k) ^ (2 * j)
            * ‖Work.Diff.STE.fourierCoeff w k‖ ^ 2 := by
        rw [norm_mul, mul_pow, norm_flatLam_pow_cast, ← pow_mul, Nat.mul_comm]
      have hflat : (Work.Diff.STE.B3.SymCalc.flatLam k) ^ (2 * j)
          ≤ (4 * Real.pi ^ 2) ^ (2 * j) * (Work.Diff.STE.wt k) ^ (2 * j) := by
        calc (Work.Diff.STE.B3.SymCalc.flatLam k) ^ (2 * j)
            ≤ ((4 * Real.pi ^ 2) * Work.Diff.STE.wt k) ^ (2 * j) :=
              pow_le_pow_left₀ (flatLam_nonneg k) (flatLam_le_wt k) (2 * j)
          _ = (4 * Real.pi ^ 2) ^ (2 * j) * (Work.Diff.STE.wt k) ^ (2 * j) := by
              rw [mul_pow]
      rw [hnorm]
      calc (Work.Diff.STE.wt k) ^ s
            * ((Work.Diff.STE.B3.SymCalc.flatLam k) ^ (2 * j)
                * ‖Work.Diff.STE.fourierCoeff w k‖ ^ 2)
          ≤ (Work.Diff.STE.wt k) ^ s
              * (((4 * Real.pi ^ 2) ^ (2 * j) * (Work.Diff.STE.wt k) ^ (2 * j))
                * ‖Work.Diff.STE.fourierCoeff w k‖ ^ 2) := by
            refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg (Work.Diff.STE.wt_pos k).le s)
            exact mul_le_mul_of_nonneg_right hflat (sq_nonneg _)
        _ = (4 * Real.pi ^ 2) ^ (2 * j)
              * ((Work.Diff.STE.wt k) ^ (s + 2 * j)
                * ‖Work.Diff.STE.fourierCoeff w k‖ ^ 2) := by
            rw [pow_add]
            ring
    have hsumL : Summable (fun k : ι → ℤ =>
        (Work.Diff.STE.wt k) ^ s
          * ‖((((Work.Diff.STE.B3.SymCalc.flatLam k) ^ j : ℝ)) : ℂ)
              * Work.Diff.STE.fourierCoeff w k‖ ^ 2) :=
      Summable.of_nonneg_of_le
        (fun k => mul_nonneg (pow_nonneg (Work.Diff.STE.wt_pos k).le s) (sq_nonneg _))
        hpt (hsum.mul_left ((4 * Real.pi ^ 2) ^ (2 * j)))
    have hle := Summable.tsum_le_tsum hpt hsumL (hsum.mul_left ((4 * Real.pi ^ 2) ^ (2 * j)))
    simp only [Work.Diff.STE.CSq]
    refine hle.trans (le_of_eq ?_)
    exact tsum_mul_left
  · intro w hw hper
    rw [lapPow_eq_seriesFun]
    exact Work.Diff.STE.contDiff_seriesFun _
      (fun N => summable_wt_pow_lapCoeff (ι := ι) j N w hw hper)
  · intro w
    rw [lapPow_eq_seriesFun]
    exact Work.Diff.STE.flat.periodic1_seriesFun _

end Work.Diff.STE.B3.SymCalcStep6
