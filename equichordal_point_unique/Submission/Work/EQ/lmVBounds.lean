import Mathlib
import Submission.Work.EQ.LocModelDefs
import Submission.Work.EQ.lmKeyNum
import Submission.Work.EQ.lmSigAux

/-!
# Bounds for `lmV`, `lmTau` and `lmG2` on the local-model box

Setting: `lmS a a₀ = a/2 - a₀`, `lmT a a₀ = a₀ + 1 + a/2`, `lmH a a₀ = min (lmS a a₀) (lmT a a₀)/16`
(see `Submission/Work/EQ/LocModelDefs.lean`), with `0 < a < 1` and `a/2 - 1 < a₀ < -a/2`.

On the box `|ξ|, |η| ≤ lmH a a₀` the real part `v` (relative to `O₁ = -a/2`) of the first image
`chordMap O₂ P` stays comparable to `lmT a a₀`, the modulus `τ = lmTau` is bounded above by `3`
and away from `0` by `lmT a a₀/2`, and the second vertical factor `lmG2 = 1 - 1/τ` is at most
`1 + 2/lmT a a₀`.

The σ-estimates `lmSigAux` (`Submission/Work/EQ/lmSigAux.lean`) and the numerical
estimate `lmKeyNum` (`Submission/Work/EQ/lmKeyNum.lean`) are proved separately; the proof below is a
chain of elementary estimates.  Writing `S = lmS a a₀ ∈ (a,1)`,
`T = lmT a a₀ ∈ (a,1)` (so `S + T = 1 + a`) and `u = lmU a a₀ ξ = ξ - S ∈ [-17S/16, -15S/16]`,
one has `σ = lmSig a a₀ ξ η = √(u²+η²) ∈ [15S/16, |u|+|η|]`, hence
`-u/σ ∈ [1 - |η|/|u|, 1]` and `|η|/|u| ≤ 16 H/(15 S)`, `|1 - 1/σ| ≤ 1 + 16/(15S)`.  With the
numerical estimate `H + 16H/(15S) ≤ T/2` (`lmKeyNum`) this gives
`T - H - |η|/|u| ≤ v ≤ T + H`, i.e. `T/2 ≤ v ≤ 2T`, and `|lmY1| ≤ T/2`; the bounds on `τ` follow
from `τ = √(v²+Y₁²)` and `|G2| = |1 - 1/τ| ≤ 1 + 1/τ`.
-/

namespace Work.EQ

open Real

theorem lmVBounds {a a₀ ξ η : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    (h1 : a/2 - 1 < a₀) (h2 : a₀ < -(a/2))
    (hξ : |ξ| ≤ Work.EQ.lmH a a₀) (hη : |η| ≤ Work.EQ.lmH a a₀) :
    Work.EQ.lmT a a₀ / 2 ≤ Work.EQ.lmV a a₀ ξ η ∧ Work.EQ.lmV a a₀ ξ η ≤ 2 * Work.EQ.lmT a a₀ ∧
    Work.EQ.lmT a a₀ / 2 ≤ Work.EQ.lmTau a a₀ ξ η ∧ Work.EQ.lmTau a a₀ ξ η ≤ 3 ∧
    |Work.EQ.lmG2 a a₀ ξ η| ≤ 1 + 2/Work.EQ.lmT a a₀ := by
  have hSig := lmSigAux (a := a) (a₀ := a₀) (ξ := ξ) (η := η) ha0 ha1 h1 h2 hξ hη
  have hKey := lmKeyNum ha0 ha1 h1 h2
  have hSpos : 0 < lmS a a₀ := by simp only [lmS]; linarith
  have hTpos : 0 < lmT a a₀ := by simp only [lmT]; linarith
  have hTlt : lmT a a₀ < 1 := by simp only [lmT]; linarith
  have hHpos : 0 < lmH a a₀ := by
    simp only [lmH]; exact div_pos (lt_min hSpos (by linarith)) (by norm_num)
  have hσ_lb : 15 * lmS a a₀ / 16 ≤ lmSig a a₀ ξ η := hSig.2.1
  have hσ_pos : 0 < lmSig a a₀ ξ η := by linarith
  have hinv : (lmSig a a₀ ξ η)⁻¹ ≤ 16 / (15 * lmS a a₀) := by
    have h := one_div_le_one_div_of_le (a := 15 * lmS a a₀ / 16) (b := lmSig a a₀ ξ η)
      (by linarith) hσ_lb
    have heq : 1 / (15 * lmS a a₀ / 16) = 16 / (15 * lmS a a₀) := by field_simp
    have h' : (lmSig a a₀ ξ η)⁻¹ ≤ 1 / (15 * lmS a a₀ / 16) := by simpa using h
    rwa [heq] at h'
  have hξlb : -lmH a a₀ ≤ ξ := (abs_le.mp hξ).1
  have hξub : ξ ≤ lmH a a₀ := (abs_le.mp hξ).2
  have hb : lmH a a₀ + |η| / |lmU a a₀ ξ| ≤ lmT a a₀ / 2 := by
    have hr := hSig.2.2.2.1
    linarith
  have hVeq : lmV a a₀ ξ η = (lmT a a₀ - 1) + ξ + (-(lmU a a₀ ξ)) / lmSig a a₀ ξ η := by
    simp only [lmV, lmX1, lmT, lmU]; ring
  have hV_lb : lmT a a₀ / 2 ≤ lmV a a₀ ξ η := by
    have hw := hSig.2.2.2.2.1
    rw [hVeq]; linarith
  have hV_ub : lmV a a₀ ξ η ≤ 2 * lmT a a₀ := by
    have hw := hSig.2.2.2.2.2
    have hHleT : lmH a a₀ ≤ lmT a a₀ / 16 := by
      simp only [lmH]; exact div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
    rw [hVeq]; linarith
  have hVnn : 0 ≤ lmV a a₀ ξ η := by linarith
  have hY1 : |lmY1 a a₀ ξ η| ≤ lmT a a₀ / 2 := by
    have heq : lmY1 a a₀ ξ η = η * (1 - (lmSig a a₀ ξ η)⁻¹) := by simp only [lmY1]; ring
    rw [heq, abs_mul]
    have h2 : |1 - (lmSig a a₀ ξ η)⁻¹| ≤ 1 + (lmSig a a₀ ξ η)⁻¹ := by
      rw [abs_le]
      constructor <;> linarith [inv_nonneg.mpr (le_of_lt hσ_pos)]
    calc |η| * |1 - (lmSig a a₀ ξ η)⁻¹| ≤ lmH a a₀ * (1 + (lmSig a a₀ ξ η)⁻¹) :=
          mul_le_mul hη h2 (abs_nonneg _) (le_of_lt hHpos)
      _ ≤ lmH a a₀ * (1 + 16 / (15 * lmS a a₀)) := by
          apply mul_le_mul_of_nonneg_left _ (le_of_lt hHpos)
          linarith
      _ = lmH a a₀ + 16 * lmH a a₀ / (15 * lmS a a₀) := by ring
      _ ≤ lmT a a₀ / 2 := hKey
  have hτeq : lmTau a a₀ ξ η = Real.sqrt ((lmV a a₀ ξ η)^2 + (lmY1 a a₀ ξ η)^2) := rfl
  have hτ_lb : lmT a a₀ / 2 ≤ lmTau a a₀ ξ η := by
    rw [hτeq]
    have hsq : (lmV a a₀ ξ η)^2 ≤ (lmV a a₀ ξ η)^2 + (lmY1 a a₀ ξ η)^2 := by
      nlinarith [sq_nonneg (lmY1 a a₀ ξ η)]
    have hnn : (0:ℝ) ≤ (lmV a a₀ ξ η)^2 + (lmY1 a a₀ ξ η)^2 :=
      by nlinarith [sq_nonneg (lmV a a₀ ξ η), sq_nonneg (lmY1 a a₀ ξ η)]
    have h := (Real.le_sqrt hVnn hnn).mpr hsq
    linarith
  have hτ_ub : lmTau a a₀ ξ η ≤ 3 := by
    rw [hτeq]
    have hsq : (lmV a a₀ ξ η)^2 + (lmY1 a a₀ ξ η)^2 ≤
        (|lmV a a₀ ξ η| + |lmY1 a a₀ ξ η|)^2 := by
      nlinarith [abs_nonneg (lmV a a₀ ξ η), abs_nonneg (lmY1 a a₀ ξ η),
        sq_abs (lmV a a₀ ξ η), sq_abs (lmY1 a a₀ ξ η)]
    have h : Real.sqrt ((lmV a a₀ ξ η)^2 + (lmY1 a a₀ ξ η)^2) ≤
        |lmV a a₀ ξ η| + |lmY1 a a₀ ξ η| := by
      calc Real.sqrt ((lmV a a₀ ξ η)^2 + (lmY1 a a₀ ξ η)^2)
          ≤ Real.sqrt ((|lmV a a₀ ξ η| + |lmY1 a a₀ ξ η|)^2) := Real.sqrt_le_sqrt hsq
        _ = |lmV a a₀ ξ η| + |lmY1 a a₀ ξ η| := Real.sqrt_sq (by positivity)
    have habs : |lmV a a₀ ξ η| = lmV a a₀ ξ η := abs_of_nonneg hVnn
    rw [habs] at h
    linarith
  have hG2 : |lmG2 a a₀ ξ η| ≤ 1 + 2/lmT a a₀ := by
    have hτpos : 0 < lmTau a a₀ ξ η := by linarith
    have h2 : (lmTau a a₀ ξ η)⁻¹ ≤ 2 / lmT a a₀ := by
      have h := one_div_le_one_div_of_le (a := lmT a a₀ / 2) (b := lmTau a a₀ ξ η)
        (by linarith) hτ_lb
      have heq : 1 / (lmT a a₀ / 2) = 2 / lmT a a₀ := by field_simp
      have h' : (lmTau a a₀ ξ η)⁻¹ ≤ 1 / (lmT a a₀ / 2) := by simpa using h
      rwa [heq] at h'
    have h1 : |1 - (lmTau a a₀ ξ η)⁻¹| ≤ 1 + (lmTau a a₀ ξ η)⁻¹ := by
      rw [abs_le]
      constructor <;> linarith [inv_nonneg.mpr (le_of_lt hτpos)]
    have heq : lmG2 a a₀ ξ η = 1 - (lmTau a a₀ ξ η)⁻¹ := by simp only [lmG2]
    rw [heq]; linarith
  exact ⟨hV_lb, hV_ub, hτ_lb, hτ_ub, hG2⟩

end Work.EQ
