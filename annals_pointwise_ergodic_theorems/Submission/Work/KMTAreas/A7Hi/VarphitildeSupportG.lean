import Mathlib
import Submission.Work.KMTAreas.A7.varphitildeNt_support_all
import Submission.Work.KMTAreas.A7.fiberVarSamplingLargeLossAuxBdd

namespace Work.KMTAreas.A7Hi

open MeasureTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

/-- The `g`-side strict support bound.  The strict main-regime inequality `k₂ + 2u + 1 ≤ Log N`
puts the `d`-fold bump `φ̃_{N,t}` inside the *half*-ball of radius `2^{-2du}` — which is the
plateau radius of the gate `mStargF d u = η_{≤-2du}`.

(`varphitildeNt_support_all` gives the true support ball of radius `2^{d(k₂−Log N)}`; the strict
regime gives `d(k₂−Log N) ≤ -d(2u+1) ≤ -2du-1` since `d ≥ 1`.) -/
theorem varphitildeNt_support_strict_g (P : Polynomial ℤ) (hd : 1 ≤ P.natDegree) (N k₂ u : ℕ)
    (t : ℝ) (hstrict : k₂ + 2 * u + 1 ≤ (Work.Analysis.EndVar.logN N).toNat) :
    ∀ ξ : ℝ, Work.KMTAreas.A7.varphitildeNt P P.natDegree N k₂ t ξ ≠ 0 →
      |ξ| ≤ (2 : ℝ) ^ (-(2 * (((P.natDegree * u : ℕ) : ℤ))) - 1) := by
  intro ξ hξ
  have hall := Work.KMTAreas.A7.varphitildeNt_support_all P P.natDegree N k₂ t ξ hξ
  have hlog : (Work.Analysis.EndVar.logN N : ℝ) = ((Work.Analysis.EndVar.logN N).toNat : ℝ) := by
    rw [Work.Analysis.EndVar.logN]
    simp only [Int.toNat_natCast]
    push_cast
    ring
  have hku : (k₂ : ℝ) + 2 * (u : ℝ) + 1 ≤ (Work.Analysis.EndVar.logN N : ℝ) := by
    have h1 : ((k₂ : ℝ) + 2 * (u : ℝ) + 1)
        ≤ (((Work.Analysis.EndVar.logN N).toNat : ℕ) : ℝ) := by
      exact_mod_cast hstrict
    rw [hlog]
    exact h1
  have hsub : (k₂ : ℝ) - (Work.Analysis.EndVar.logN N : ℝ) ≤ -(2 * (u : ℝ) + 1) := by linarith
  have hd0 : (0 : ℝ) ≤ (P.natDegree : ℝ) := Nat.cast_nonneg _
  have hd1 : (1 : ℝ) ≤ (P.natDegree : ℝ) := by exact_mod_cast hd
  have hmul : (P.natDegree : ℝ) * ((k₂ : ℝ) - (Work.Analysis.EndVar.logN N : ℝ))
      ≤ -(2 * ((P.natDegree * u : ℕ) : ℝ)) - 1 := by
    have hcu : ((P.natDegree * u : ℕ) : ℝ) = (P.natDegree : ℝ) * (u : ℝ) := by push_cast; ring
    rw [hcu]
    nlinarith [mul_le_mul_of_nonneg_left hsub hd0, hd1,
      (show (0 : ℝ) ≤ (u : ℝ) from Nat.cast_nonneg u)]
  have hcast : ((-(2 * (((P.natDegree * u : ℕ) : ℤ))) - 1 : ℤ) : ℝ)
      = -(2 * ((P.natDegree * u : ℕ) : ℝ)) - 1 := by push_cast; ring
  calc |ξ| ≤ (2 : ℝ) ^ ((P.natDegree : ℝ) * ((k₂ : ℝ) - (Work.Analysis.EndVar.logN N : ℝ))) := hall
    _ ≤ (2 : ℝ) ^ (-(2 * ((P.natDegree * u : ℕ) : ℝ)) - 1) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) hmul
    _ = (2 : ℝ) ^ ((-(2 * (((P.natDegree * u : ℕ) : ℤ))) - 1 : ℤ) : ℝ) := by rw [hcast]
    _ = (2 : ℝ) ^ (-(2 * (((P.natDegree * u : ℕ) : ℤ))) - 1) := by rw [Real.rpow_intCast]

/-- The `g`-side quarter-ball support bound.  Farey (`8·2^{k₂}·q ≤ N`) puts `φ̃_{N,t}` inside the
ball of radius `1/(4q)`, which is the band hypothesis of the coset comparison
(`Work.KMTAreas.A7.convSublatticeCosetCompareBdd`). -/
theorem varphitildeNt_support_le_quarter_g (P : Polynomial ℤ) (hd : 1 ≤ P.natDegree)
    (q : ℕ) (hq : 1 ≤ q) (N k₂ : ℕ) (t : ℝ)
    (hfarey : 8 * (2 : ℝ) ^ k₂ * (q : ℝ) ≤ (N : ℝ)) :
    ∀ ξ : ℝ, Work.KMTAreas.A7.varphitildeNt P P.natDegree N k₂ t ξ ≠ 0 →
      |ξ| ≤ 1 / (4 * (q : ℝ)) := by
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hloggt := Work.KMTAreas.A7.two_pow_logN_gt N
  have hNpos : (0 : ℝ) < (N : ℝ) := by
    have : (0 : ℝ) < 8 * (2 : ℝ) ^ k₂ * (q : ℝ) := by positivity
    linarith
  have hlogpos : (0 : ℝ) < (2 : ℝ) ^ (Work.Analysis.EndVar.logN N : ℝ) := by positivity
  have hsplit : (2 : ℝ) ^ ((k₂ : ℝ) - (Work.Analysis.EndVar.logN N : ℝ))
      = (2 : ℝ) ^ k₂ / (2 : ℝ) ^ (Work.Analysis.EndVar.logN N : ℝ) := by
    rw [Real.rpow_sub (by norm_num : (0 : ℝ) < 2), Real.rpow_natCast]
  -- Step A: `2^{k₂ - Log N} < 1/(4q)`
  have hA : (2 : ℝ) ^ ((k₂ : ℝ) - (Work.Analysis.EndVar.logN N : ℝ)) < 1 / (4 * (q : ℝ)) := by
    rw [hsplit, div_lt_div_iff₀ hlogpos (by positivity)]
    have h3 : (2 : ℝ) ^ k₂ * (4 * (q : ℝ)) ≤ (N : ℝ) / 2 := by nlinarith [hfarey]
    nlinarith [hloggt, h3]
  -- Step B: the exponent is `≤ 0`
  have hB : (k₂ : ℝ) - (Work.Analysis.EndVar.logN N : ℝ) ≤ 0 := by
    have h1 : (2 : ℝ) ^ ((k₂ : ℝ) - (Work.Analysis.EndVar.logN N : ℝ)) < (2 : ℝ) ^ (0 : ℝ) := by
      have hle1 : 1 / (4 * (q : ℝ)) ≤ 1 := by
        rw [div_le_iff₀ (by positivity : (0 : ℝ) < 4 * (q : ℝ))]
        have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
        linarith
      simpa using lt_of_lt_of_le hA hle1
    exact le_of_lt ((Real.rpow_lt_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).mp h1)
  -- Step C: `d·x ≤ x`
  have hd1 : (1 : ℝ) ≤ (P.natDegree : ℝ) := by exact_mod_cast hd
  have hC : (P.natDegree : ℝ) * ((k₂ : ℝ) - (Work.Analysis.EndVar.logN N : ℝ))
      ≤ (k₂ : ℝ) - (Work.Analysis.EndVar.logN N : ℝ) := by
    nlinarith [hB, hd1]
  intro ξ hξ
  have hall := Work.KMTAreas.A7.varphitildeNt_support_all P P.natDegree N k₂ t ξ hξ
  calc |ξ| ≤ (2 : ℝ) ^ ((P.natDegree : ℝ) * ((k₂ : ℝ) - (Work.Analysis.EndVar.logN N : ℝ))) :=
        hall
    _ ≤ (2 : ℝ) ^ ((k₂ : ℝ) - (Work.Analysis.EndVar.logN N : ℝ)) :=
        (Real.rpow_le_rpow_left_iff (by norm_num : (1 : ℝ) < 2)).mpr hC
    _ ≤ 1 / (4 * (q : ℝ)) := le_of_lt hA

end

end Work.KMTAreas.A7Hi
