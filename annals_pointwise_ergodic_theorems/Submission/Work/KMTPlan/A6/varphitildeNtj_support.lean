import Mathlib
import Submission.Work.KMTPlan.A6.varphitildeNtj_bounds
import Submission.Work.KMTPlan.A6.tmRandSymbG_l2

namespace Work.KMTPlan.A6

/-- **Support of the modified `g`-side bump `φ̃_{N,k,j}(t) = (2^{-dk}N^dξ)^j φ̃_{N,k}(t)`.**

The modified bump is the product of a power of the frequency variable with the (modulated) bump
`φ̃_{N,k}`, so a nonzero value forces the unmodulated bump `φ̃_N` to be nonzero at `x`.  The
support bounds are then those of `φ̃_N`: the upper bound `|x| ≤ 2^{d(k - Log N)}` for every `k`
(`Work.KMTAreas.A7.varphitildeNt_support_all`), and the lower bound of the annulus for `k ≥ 1`
(`Work.KMTPlan.A6.varphitildeN_annulus`). -/
theorem varphitildeNtj_support (P : Polynomial ℤ) (hd : 1 ≤ P.natDegree) (N k : ℕ) (j : ℤ)
    (t x : ℝ) (h : Work.KMTPlan.A6.varphitildeNtj P N k j t x ≠ 0) :
    (2 : ℝ) ^ ((P.natDegree : ℝ) * ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ))) * |x| ≤ 1 ∧
      (1 ≤ k → (2 : ℝ) ^ (-((P.natDegree : ℝ) + 1))
        < (2 : ℝ) ^ ((P.natDegree : ℝ)
            * ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ))) * |x|) := by
  -- the modified bump is `(2^{-dk}N^d x)^j` times the unmodulated modulated bump
  have hfac : Work.KMTPlan.A6.varphitildeNtj P N k j t x =
      ((((2 : ℝ) ^ (-((P.natDegree : ℝ) * (k : ℝ))) * ((N : ℝ)) ^ P.natDegree * x : ℝ)) : ℂ) ^ j
        * Work.KMTAreas.A7.varphitildeNt P P.natDegree N k t x := rfl
  have hNt : Work.KMTAreas.A7.varphitildeNt P P.natDegree N k t x ≠ 0 :=
    fun hz => h (by rw [hfac, hz, mul_zero])
  -- the upper bound: the support bound for the unmodulated bump `φ̃_N`
  have hup : |x| ≤ (2 : ℝ) ^ ((P.natDegree : ℝ) * ((k : ℝ) - (Work.Analysis.EndVar.logN N : ℝ))) :=
    Work.KMTAreas.A7.varphitildeNt_support_all P P.natDegree N k t x hNt
  have hApos : 0 < (2 : ℝ) ^ ((P.natDegree : ℝ) * ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ))) :=
    Real.rpow_pos_of_pos (by norm_num) _
  have hmul := mul_le_mul_of_nonneg_left hup hApos.le
  have hexp : (2 : ℝ) ^ ((P.natDegree : ℝ) * ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ))) *
      (2 : ℝ) ^ ((P.natDegree : ℝ) * ((k : ℝ) - (Work.Analysis.EndVar.logN N : ℝ))) = 1 := by
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    have h0 : (P.natDegree : ℝ) * ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ)) +
        (P.natDegree : ℝ) * ((k : ℝ) - (Work.Analysis.EndVar.logN N : ℝ)) = 0 := by ring
    rw [h0, Real.rpow_zero]
  constructor
  · calc (2 : ℝ) ^ ((P.natDegree : ℝ) * ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ))) * |x|
        ≤ (2 : ℝ) ^ ((P.natDegree : ℝ) * ((Work.Analysis.EndVar.logN N : ℝ) - (k : ℝ))) *
            (2 : ℝ) ^ ((P.natDegree : ℝ) * ((k : ℝ) - (Work.Analysis.EndVar.logN N : ℝ))) := hmul
      _ = 1 := hexp
  · intro hk
    -- for `k ≥ 1` the unmodulated bump vanishes near the origin, giving the lower bound
    have hN : Work.KMTAreas.A7.varphitildeN P.natDegree N k x ≠ 0 :=
      (mul_ne_zero_iff.mp hNt).1
    exact (varphitildeN_annulus hd hk hN).1

end Work.KMTPlan.A6
