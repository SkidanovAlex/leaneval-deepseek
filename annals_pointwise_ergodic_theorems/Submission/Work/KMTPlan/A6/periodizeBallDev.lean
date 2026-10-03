/-
# The periodisation of the modulated height-`0` deviation

`periodize ψ θ = ∑' k : ℤ, ψ (circRep θ + k)` where `circRep θ ∈ [0,1)` is the canonical
representative of `θ` in the frequency circle `ℝ/ℤ`.  For `ψ = ballDev P N t` only the translates
`k = 0` and `k = -1` can contribute: the deviation vanishes wherever `ballScale P N * |ξ| ≥ 1`
(`Work.KMTPlan.A6.ballDev_vanish`), `ballScale P N ≥ 1` (`Work.KMTPlan.A6.ballScale_one_le`), while
`|circRep θ + k| ≥ 1` for every integer `k ∉ {0, -1}`.
-/
import Mathlib
import Submission.Work.KMTPlan.A6.BallDevDefs

set_option autoImplicit false

namespace Work.KMTPlan.A6

open MeasureTheory Polynomial
open scoped ENNReal NNReal BigOperators

theorem periodizeBallDev (P : Polynomial ℤ) (N : ℕ) (t : ℝ)
    (θ : Work.Analysis.IonescuWainger.Circle) :
    Work.Analysis.IonescuWainger.periodize (ballDev P N t) θ
      = ballDev P N t (circRep θ) + ballDev P N t (circRep θ - 1) := by
  have hσ1 : (1 : ℝ) ≤ ballScale P N := ballScale_one_le P N
  have hx0 : 0 ≤ circRep θ := circRep_nonneg θ
  have hx1 : circRep θ < 1 := circRep_lt_one θ
  have hzero : ∀ k : ℤ, k ∉ ({0, -1} : Finset ℤ) →
      ballDev P N t (circRep θ + (k : ℝ)) = 0 := by
    intro k hk
    have hk0 : k ≠ 0 := by intro h; exact hk (by rw [h]; simp)
    have hkm1 : k ≠ -1 := by intro h; exact hk (by rw [h]; simp)
    refine ballDev_vanish P N t ?_
    have hk1 : (1 : ℝ) ≤ |circRep θ + (k : ℝ)| := by
      rcases lt_or_ge k (-1) with hlt | hge
      · have hk2 : k ≤ -2 := by omega
        have hkR : (k : ℝ) ≤ -2 := by exact_mod_cast hk2
        have h2 : circRep θ + (k : ℝ) ≤ -1 := by linarith
        rw [abs_of_nonpos (by linarith)]
        linarith
      · have hkg1 : (1 : ℤ) ≤ k := by
          have h1 : (-1 : ℤ) < k := lt_of_le_of_ne hge (Ne.symm hkm1)
          have h2 : (0 : ℤ) < k := by omega
          omega
        have hkR : (1 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hkg1
        have h2 : (1 : ℝ) ≤ circRep θ + (k : ℝ) := by linarith
        rw [abs_of_nonneg (by linarith)]
        linarith
    calc (1 : ℝ) ≤ |circRep θ + (k : ℝ)| := hk1
      _ = 1 * |circRep θ + (k : ℝ)| := (one_mul _).symm
      _ ≤ ballScale P N * |circRep θ + (k : ℝ)| :=
          mul_le_mul_of_nonneg_right hσ1 (abs_nonneg _)
  simp only [circRep]
  rw [Work.Analysis.IonescuWainger.periodize]
  have hzero' : ∀ k : ℤ, k ∉ ({0, -1} : Finset ℤ) →
      ballDev P N t ((AddCircle.equivIco (1 : ℝ) 0 θ).val + (k : ℝ)) = 0 :=
    fun k hk => hzero k hk
  rw [tsum_eq_sum (s := ({0, -1} : Finset ℤ)) hzero']
  rw [Finset.sum_insert (by simp), Finset.sum_singleton]
  norm_num
  rw [sub_eq_add_neg]

end Work.KMTPlan.A6
