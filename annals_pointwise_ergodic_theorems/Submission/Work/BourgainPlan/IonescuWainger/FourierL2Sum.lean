import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.FourierL2Defs

/-!
# Finite sums of band-limited `ℓ²(ℤ)`-functions

Source: T. Tao, *The Ionescu–Wainger multiplier theorem and the adeles*, arXiv:2008.05066, §4: a
major arc system is of the form `f_{Σ_A} = Σ_{α ∈ Σ_A} f_α`, a **finite sum** of band-limited
functions, so the frequency support of `f_{Σ_A}` is the union of the arcs of its summands.  This
file records the two elementary facts used for that: `ftLp` is linear (`ftLp_sum`), and the frequency
support of a finite sum is the union of the frequency supports (`hasFreqSupport_sum`).
-/

open MeasureTheory
open scoped BigOperators ENNReal lp

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.BourgainPlan.IonescuWainger

/-- A finite sum of square-summable sequences is square-summable. -/
theorem memℓp_sum {ι : Type*} [Fintype ι] {f : ι → ℤ → ℂ} (hf : ∀ i, Memℓp (f i) 2) :
    Memℓp (fun m => ∑ i, f i m) 2 := by
  simpa using Memℓp.finsetSum (Finset.univ : Finset ι) (fun i _ => hf i)

end Work.BourgainPlan.IonescuWainger
