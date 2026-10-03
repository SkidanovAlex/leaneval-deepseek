/-
# The plateau of the KMT cutoff `m_* = η_{≤ -2u}`

The symbol `mStarF u` of §6 of Krause--Mirek--Tao is the Littlewood--Paley cutoff
`η_{≤ -2u} = etaCut kmtEta (-(2 * u))`, i.e. `x ↦ kmtEta (x / 2^{-2u})`.  Since the paper's bump
`η` satisfies `η = 1` on `[-1/2,1/2]` and `η = 0` off `[-1,1]` (`Work.KMTContract.kmtEta_one`,
`Work.KMTContract.kmtEta_zero`), the rescaled cutoff is

* identically `1` on the closed arc `[-2^{-2u}/2, 2^{-2u}/2] = [-2^{-2u-1}, 2^{-2u-1}]`, and
* identically `0` off the open arc `(-2^{-2u}, 2^{-2u})`.

This is the elementary plateau property of `m_*` used whenever a symbol supported in
`ℝ_{≤ -2u - 1}` (in particular the modulated bump `φ_{N,t}` in the main regime) is to be
multiplied by `m_*`, cf. `Work.KMTPlan.A6.Tle_mdlF_eq_Tm`.
-/
import Mathlib
import Submission.Work.KMTAreas.A7.LargeInterface
import Submission.Work.BourgainPlan.IonescuWainger.ArcDefs

set_option autoImplicit false

namespace Work.KMTAreas.A7

open Work.Analysis.IonescuWainger

theorem mStarF_plateau (U : ℕ) :
    (∀ x : ℝ, |x| ≤ (2 : ℝ) ^ (-(2 * (U : ℤ)) - 1) → Work.KMTAreas.A7.mStarF U x = 1) ∧
    (∀ x : ℝ, (2 : ℝ) ^ (-(2 * (U : ℤ))) ≤ |x| → Work.KMTAreas.A7.mStarF U x = 0) := by
  constructor
  · intro x hx
    rw [mStarF, etaCut]
    refine Work.KMTContract.kmtEta_one ?_
    have hb : (0 : ℝ) < (2 : ℝ) ^ (-(2 * (U : ℤ))) := zpow_pos (by norm_num) _
    rw [abs_div, abs_of_pos hb, div_le_iff₀ hb]
    calc |x| ≤ (2 : ℝ) ^ (-(2 * (U : ℤ)) - 1) := hx
      _ = (1 / 2) * (2 : ℝ) ^ (-(2 * (U : ℤ))) := by
          rw [zpow_sub₀ (by norm_num : (2 : ℝ) ≠ 0), zpow_one]
          ring
  · intro x hx
    rw [mStarF, etaCut]
    refine Work.KMTContract.kmtEta_zero ?_
    have hb : (0 : ℝ) < (2 : ℝ) ^ (-(2 * (U : ℤ))) := zpow_pos (by norm_num) _
    rw [abs_div, abs_of_pos hb, le_div_iff₀ hb]
    simpa using hx

end Work.KMTAreas.A7
