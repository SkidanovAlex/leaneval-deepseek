/-
# Pointwise bound on the modulated height-`0` deviation

For `P : ℤ[X]` and `d = P.natDegree`, the deviation of the modulated bump from the unmodulated one
is `ballDev P N t ξ = φ̃_N(ξ) · (e(P(Nt) ξ) - 1)`.  Its modulus is bounded by
`C · min 1 (ballScale P N · |ξ|)`: the cutoff `η` is bounded by `1`, `‖e^{2πiy} - 1‖ ≤ 2π|y|`, and
the polynomial value at `N t`, `t ∈ [1/2,1]`, is dominated by `(Σ|cᵢ|)·(1+N)^d ≲ ballScale P N`
(`Work.KMTAreas.A7.abs_PevalR_div_gScale_le`, with `gScale d N 0 = ballScale P N`).
-/
import Mathlib
import Submission.Work.KMTPlan.A6.BallDevDefs
import Submission.Work.KMTAreas.A7.abs_PevalR_div_gScale_le
import Submission.Commons.Analysis.Fourier.lintegral_translate_sub_sq_le_of_fourier_support

set_option autoImplicit false

namespace Work.KMTPlan.A6

open MeasureTheory Polynomial
open scoped ENNReal NNReal BigOperators

/-- The `g`-side frequency scale at the bottom height `k₂ = 0` is the reciprocal width
`ballScale` of the bump. -/
theorem ballScale_eq_gScale (P : Polynomial ℤ) (N : ℕ) :
    ballScale P N = Work.KMTAreas.A7.gScale P.natDegree N 0 := by
  rw [ballScale, Work.KMTAreas.A7.gScale]
  have he : (P.natDegree : ℝ) * ((Work.Analysis.EndVar.logN N : ℤ) : ℝ)
      = (((P.natDegree : ℤ) * Work.Analysis.EndVar.logN N : ℤ) : ℝ) := by push_cast; ring
  rw [he, Real.rpow_intCast]
  congr 2

/-- `‖e^{2πiy} - 1‖ ≤ 2π|y|` for the KMT character `ee`. -/
theorem ee_sub_one_norm_le (y : ℝ) :
    ‖Work.KMTAreas.A7.ee y - 1‖ ≤ 2 * Real.pi * |y| := by
  have h : Work.KMTAreas.A7.ee y = (Real.fourierChar y : ℂ) := by
    rw [Work.KMTAreas.A7.ee, Real.fourierChar_apply]
    push_cast
    ring_nf
  rw [h]
  exact Commons.Analysis.Fourier.fourierChar_sub_one_norm_le y

theorem ballDevBound (P : Polynomial ℤ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) (t : ℝ), t ∈ Set.Icc (1 / 2 : ℝ) 1 → ∀ ξ : ℝ,
      ‖ballDev P N t ξ‖
        ≤ C * min 1 (ballScale P N * |ξ|) := by
  classical
  set S : ℝ := ∑ i ∈ Finset.range (P.natDegree + 1), |(P.coeff i : ℝ)| with hS
  have hSnn : 0 ≤ S := by rw [hS]; exact Finset.sum_nonneg (fun i _ => abs_nonneg _)
  -- the modulation phase is dominated by the frequency scale
  have hpoly : ∀ (N : ℕ) (t : ℝ), |t| ≤ 1 →
      |Work.KMTAreas.A7.PevalR P ((N : ℝ) * t)|
        ≤ (2 * (S + 1) * 3 ^ P.natDegree) * ballScale P N := by
    intro N t ht
    have hdiv := Work.KMTAreas.A7.abs_PevalR_div_gScale_le P P.natDegree N 0 le_rfl ht
    rw [ballScale_eq_gScale]
    have hpos : 0 < Work.KMTAreas.A7.gScale P.natDegree N 0 := by
      rw [Work.KMTAreas.A7.gScale]; positivity
    have h2 : |Work.KMTAreas.A7.PevalR P ((N : ℝ) * t)|
        ≤ (S + 1) * 3 ^ P.natDegree * (1 + (2 : ℝ) ^ (P.natDegree * 0))
            * Work.KMTAreas.A7.gScale P.natDegree N 0 :=
      (div_le_iff₀ hpos).mp (by simpa [hS] using hdiv)
    have h3 : (1 + (2 : ℝ) ^ (P.natDegree * 0)) = 2 := by norm_num
    calc |Work.KMTAreas.A7.PevalR P ((N : ℝ) * t)|
        ≤ (S + 1) * 3 ^ P.natDegree * (1 + (2 : ℝ) ^ (P.natDegree * 0))
            * Work.KMTAreas.A7.gScale P.natDegree N 0 := h2
      _ = (2 * (S + 1) * 3 ^ P.natDegree) * Work.KMTAreas.A7.gScale P.natDegree N 0 := by
          rw [h3]; ring
  refine ⟨2 * Real.pi * (2 * (S + 1) * 3 ^ P.natDegree), by positivity, ?_⟩
  intro N t ht ξ
  have ht1 : |t| ≤ 1 := by
    rw [abs_le]
    exact ⟨by linarith [ht.1], ht.2⟩
  rcases lt_or_ge (ballScale P N * |ξ|) 1 with hlt | hge
  · rw [min_eq_right hlt.le]
    have hfac : ‖ballDev P N t ξ‖
        ≤ 2 * Real.pi * |Work.KMTAreas.A7.PevalR P ((N : ℝ) * t)| * |ξ| := by
      rw [ballDev_apply]
      calc ‖Work.KMTAreas.A7.varphitildeN P.natDegree N 0 ξ
            * (Work.KMTAreas.A7.ee (Work.KMTAreas.A7.PevalR P ((N : ℝ) * t) * ξ) - 1)‖
          = ‖Work.KMTAreas.A7.varphitildeN P.natDegree N 0 ξ‖
            * ‖Work.KMTAreas.A7.ee (Work.KMTAreas.A7.PevalR P ((N : ℝ) * t) * ξ) - 1‖ :=
            norm_mul _ _
        _ ≤ 1 * (2 * Real.pi * |Work.KMTAreas.A7.PevalR P ((N : ℝ) * t) * ξ|) := by
            refine mul_le_mul ?_ (ee_sub_one_norm_le _) (norm_nonneg _) (by norm_num)
            rw [varphitildeN_zero_eq_ballScale]
            exact Work.KMTContract.norm_kmtEta_le _
        _ = 2 * Real.pi * |Work.KMTAreas.A7.PevalR P ((N : ℝ) * t)| * |ξ| := by
            rw [abs_mul]; ring
    calc ‖ballDev P N t ξ‖
        ≤ 2 * Real.pi * |Work.KMTAreas.A7.PevalR P ((N : ℝ) * t)| * |ξ| := hfac
      _ ≤ 2 * Real.pi * ((2 * (S + 1) * 3 ^ P.natDegree) * ballScale P N) * |ξ| := by
          have hπ : (0 : ℝ) ≤ 2 * Real.pi := by positivity
          have hξ : (0 : ℝ) ≤ |ξ| := abs_nonneg _
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left (hpoly N t ht1) hπ) hξ
      _ = (2 * Real.pi * (2 * (S + 1) * 3 ^ P.natDegree)) * (ballScale P N * |ξ|) := by ring
  · rw [min_eq_left hge]
    rw [ballDev_vanish P N t hge, norm_zero]
    exact mul_nonneg (by positivity) (by norm_num)

end Work.KMTPlan.A6
