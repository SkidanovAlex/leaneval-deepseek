import Mathlib
import Submission.Work.KMTAreas.A7.randSymbG_aux

namespace Work.KMTAreas.A7

open Work.Analysis.EndVar

noncomputable section

/-! ## The profile identity `φ̃_{N,t} = gProfile ∘ (gScale ·)`

`varphitildeN d N k₂` is written in `Large/Defs.lean` in the *expanded* form, with the frequency
scale `2^{d (Log N - k₂)}` appearing through real powers (`rpow`), whereas the fixed profile
`gProfile d k₂` is rescaled by `gScale d N k₂ = 2^{d(Log N - k₂)}`, an integer power (`zpow`).
This file proves that the two agree, so that every statement about the `g`-side bump can be
phrased in terms of the single fixed profile `gProfile` and the numerical scale `gScale`. -/

/-- The real-power frequency scale `2^{d (Log N - k₂)}` equals the integer-power scale
`2^{d · (Log N - k₂)}`. -/
private lemma two_rpow_sub (d : ℕ) (L : ℤ) (k : ℕ) :
    (2 : ℝ) ^ ((d : ℝ) * ((L : ℝ) - (k : ℝ))) = (2 : ℝ) ^ ((d : ℤ) * (L - (k : ℤ))) := by
  rw [show ((d : ℝ) * ((L : ℝ) - (k : ℝ))) = (((d : ℤ) * (L - (k : ℤ)) : ℤ) : ℝ) by
    push_cast; ring]
  exact Real.rpow_intCast 2 _

/-- The next dyadic value of the real-power frequency scale: shifting `k` by one multiplies the
scale by `2^d` (the factor by which `gProfile` rescales its argument). -/
private lemma two_rpow_sub_add_one (d : ℕ) (L : ℤ) (k : ℕ) :
    (2 : ℝ) ^ ((d : ℝ) * ((L : ℝ) - (k : ℝ) + 1))
      = (2 : ℝ) ^ d * (2 : ℝ) ^ ((d : ℤ) * (L - (k : ℤ))) := by
  rw [show ((d : ℝ) * ((L : ℝ) - (k : ℝ) + 1))
        = (((d : ℤ) * (L - (k : ℤ) + 1) : ℤ) : ℝ) by push_cast; ring]
  rw [Real.rpow_intCast]
  rw [show (d : ℤ) * (L - (k : ℤ) + 1) = (d : ℤ) + (d : ℤ) * (L - (k : ℤ)) by ring]
  rw [zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
  rw [zpow_natCast]

/-- `gScale` is the integer-power frequency scale `2^{d (Log N - k₂)}`. -/
private lemma gScale_eq_rpow (d N k₂ : ℕ) :
    gScale d N k₂ = (2 : ℝ) ^ ((d : ℝ) * ((logN N : ℝ) - (k₂ : ℝ))) :=
  (two_rpow_sub d (logN N) k₂).symm

/-- Rescaling the profile argument by `2^d` corresponds to the next dyadic frequency scale. -/
private lemma mul_gScale_eq_rpow (d N k₂ : ℕ) :
    (2 : ℝ) ^ d * gScale d N k₂
      = (2 : ℝ) ^ ((d : ℝ) * ((logN N : ℝ) - (k₂ : ℝ) + 1)) := by
  rw [gScale, ← two_rpow_sub_add_one d (logN N) k₂]

theorem varphitildeNt_eq_profile (P : Polynomial ℤ) (d : ℕ) (N k₂ : ℕ) (t : ℝ) :
    varphitildeNt P d N k₂ t
      = fun ξ : ℝ => gProfile d k₂ (gScale d N k₂ * ξ) * ee (PevalR P ((N : ℝ) * t) * ξ) := by
  funext ξ
  simp only [varphitildeNt]
  congr 1
  unfold varphitildeN gProfile
  by_cases h : k₂ = 0
  · subst h
    rw [if_pos rfl, if_pos rfl]
    congr 1
    rw [gScale_eq_rpow]
    simp
  · rw [if_neg h, if_neg h]
    congr 1
    · congr 1
      rw [gScale_eq_rpow]
    · congr 1
      rw [← mul_assoc, mul_gScale_eq_rpow]

end

end Work.KMTAreas.A7
