/-
# `APSwitchUpper.riPhiEnvDefs` — the explicit majorant of `riPhi` for the window sum

The switched-window excess is bounded by the *numerical window sum* of the Rosser–Iwaniec
upper profile `riPhi = F − 1` (`Submission/Work/NumberTheory/Chen/APSwitchUpper/prof.lean`).
The analytic content of that sum is isolated here as an **explicit elementary majorant**
`riPhiEnv` of `riPhi` on `s ≥ 11/5`, with which the (purely numerical) window sum is finite
and computable.

## The shape of `riPhiEnv`

Write `C := ∫_2^∞ riPsi` and `T := ∫_3^∞ riPhi`.  The delay identities of the `profC` family
(the *summed* form of the recursions, proved in the companion module) give

* `B(u) := riPsi u = ((3+C)·log(3/(u−1)) − 4 + u + T)/u`  for `2 ≤ u ≤ 4`,
* `riPhi s = C/s` for `s ≤ 1`,  `riPhi s = ((3−s)+C)/s` for `1 ≤ s ≤ 3`,
* `riPhi s = (C − (3+C)·A'(s−1) − (T−4)·log((s−1)/2) − (s−3))/s`  for `3 ≤ s ≤ 5`,
* `riPhi s ≤ (C − ∫_2^4 B)/s` for `s ≥ 5`,

where `A'(x) := ∫_2^x log(3/(u−1))/u du` is the primitive of `B`'s `C`-part.

## The constants

The two numbers needed are bounds `C ≤ envC` and `T ≥ envT`, obtained from the delay
identities plus the crude a-priori bounds `C ≤ 0.641`, `T ≤ 0.498`:

* `T ≥ 0.078988…` — from the mass identity `T = ∫_2^∞ B(u)·log((u+1)/3) du`, restricted to
  `[2,4]` and combined with `C ≥ (3+C)·A'(4) + (T−4)·log 2 + 2` (which is `C ≥ ∫_2^4 B`);
  the envelope uses the (weaker) `envT = 0.0785`;
* `C ≤ (4 − 3·log 3 − T)/log 3 ≤ (4 − 3·log 3 − 0.0789)/log 3 = 0.569137 ≤ envC = 0.5692`
  — from the summed moment identity `log 3·C + T ≤ 4 − 3·log 3`.  (The margin is
  `6.3·10⁻⁵`, so the arithmetic must use explicit rational bounds on `log 3`.)

`envNum`/`riPhiEnv` are monotone in the pair `(C,T)` in the required directions
(increasing in `C`, decreasing in `T`), which is why the single pair `(envC, envT)` gives a
majorant.
-/
import Mathlib
import Submission.Work.NumberTheory.Chen.APSwitchUpper.prof
import Submission.Work.NumberTheory.Chen.APSwitchUpper.Defs

open Finset
open scoped BigOperators

namespace Work.NumberTheory.Chen.APSwitchUpper

noncomputable section

open MeasureTheory

/-- `A'(x) = ∫_2^x log(3/(u−1))/u du`: the primitive of the `C`-part of the `riPsi` profile. -/
def Aprime (x : ℝ) : ℝ := ∫ u in (2 : ℝ)..x, Real.log (3 / (u - 1)) / u

/-- `A'(2) = 0`. -/
theorem Aprime_two : Aprime 2 = 0 := by
  rw [Aprime, intervalIntegral.integral_same]


/-- The upper bound for `C = ∫_2^∞ riPsi` used by the envelope. -/
def envC : ℝ := 5692 / 10000

/-- The lower bound for `T = ∫_3^∞ riPhi` used by the envelope. -/
def envT : ℝ := 785 / 10000

/-- The numerator of the envelope in the range `s ≥ 3`. -/
def envNum (s : ℝ) : ℝ :=
  envC - ((3 + envC) * Aprime (min (s - 1) 4) + (envT - 4) * Real.log (min (s - 1) 4 / 2)
    + (min (s - 1) 4 - 2))

/-- **The explicit majorant of `riPhi`.**  Piecewise: `((3−s)+C)/s` on `[11/5,3]`, the
delay-identity numerator for `3 ≤ s ≤ 5`, and `(C − ∫_2^4 B)/s` for `s ≥ 5`. -/
def riPhiEnv (s : ℝ) : ℝ := if s ≤ 3 then ((3 - s) + envC) / s else envNum s / s

/-- `riPhiEnv` agrees with `((3-s)+envC)/s` on `[11/5,3]`. -/
theorem riPhiEnv_of_le_three {s : ℝ} (hs : s ≤ 3) : riPhiEnv s = ((3 - s) + envC) / s := by
  rw [riPhiEnv, if_pos hs]

/-- `riPhiEnv` is the delay numerator divided by `s` for `s ≥ 3`. -/
theorem riPhiEnv_of_three_le {s : ℝ} (hs : 3 ≤ s) : riPhiEnv s = envNum s / s := by
  by_cases h : s ≤ 3
  · have h3 : s = 3 := le_antisymm h hs
    subst h3
    rw [riPhiEnv_of_le_three le_rfl]
    unfold envNum
    norm_num [Aprime_two, min_eq_left (show (2:ℝ) ≤ (3:ℝ) - 1 by norm_num)]
  · rw [riPhiEnv, if_neg h]

/-- For `s ≥ 5` the envelope is the constant `envNum 5` divided by `s`. -/
theorem riPhiEnv_of_five_le {s : ℝ} (hs : 5 ≤ s) : riPhiEnv s = envNum 5 / s := by
  rw [riPhiEnv_of_three_le (by linarith)]
  have h1 : min (s - 1) 4 = 4 := by
    rw [min_eq_right_iff]; linarith
  have h2 : min ((5:ℝ) - 1) 4 = 4 := by norm_num
  unfold envNum
  rw [h1, h2]

end

end Work.NumberTheory.Chen.APSwitchUpper
