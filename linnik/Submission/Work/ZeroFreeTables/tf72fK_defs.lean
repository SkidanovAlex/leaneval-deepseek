/-
# ZeroFreeTables — the signed kernel and gap functional for HB Lemma 7.2 at λ = 6/7

For the test function `f = tf72f (6/7)` of Heath-Brown (1992), Lemma 7.2 (supported on
`[0, 7/3]`), the `F`-method gap

  `lam ↦ F (-lam) - 2 F (6/7 - lam)`,  `F z = ∫_0^{7/3} e^{-z t} f t dt`,

can be written as a single integral against the *signed kernel*

  `tf72fK t = (1 - 2 exp (-(6/7) t)) * f t`,

namely `tf72fPhi lam = ∫_0^{7/3} exp (lam t) * tf72fK t dt`.  The kernel changes sign
exactly once, at `t = (7/6) log 2` (where `exp ((6/7) t) = 2`), which is what makes the
gap monotone on `[0, 792/1000]`.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.testFn72_defs

open scoped Interval
open MeasureTheory

noncomputable section
namespace Work.ZeroFreeTables

/-- The signed kernel `t ↦ (1 - 2 exp (-(6/7) t)) * tf72f (6/7) t`.  It is `≤ 0` for
`t ≤ (7/6) log 2` and `≥ 0` afterwards. -/
def tf72fK (t : ℝ) : ℝ := (1 - 2 * Real.exp (-(6/7) * t)) * tf72f (6/7) t

/-- The gap functional `F (-lam) - 2 F (6/7 - lam)` written as a single integral. -/
def tf72fPhi (lam : ℝ) : ℝ := ∫ t in (0:ℝ)..(7/3), Real.exp (lam * t) * tf72fK t

end Work.ZeroFreeTables
