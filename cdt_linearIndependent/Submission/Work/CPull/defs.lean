import Mathlib
import Submission.CDTPlan.InterfacesC

/-!
# Area CPull — shared definitions for the meromorphic-pullback development

`evp f z` is the evaluation of a rational power series at a complex number, as the sum of its
series: `∑' n, (coeff n f : ℂ) * z ^ n`.  It is the bridge between the formal power series
`seventeen` of `InterfacesC` and the analytic functions on the disc.

`Lf` is the formal `log (1 - X)` and `Li2f` the formal dilogarithm `Σ X^n/n²`.
-/

namespace Work.CPull

open PowerSeries

/-- Evaluation of a rational power series at a complex number. -/
noncomputable def evp (f : PowerSeries ℚ) (z : ℂ) : ℂ :=
  ∑' n : ℕ, ((PowerSeries.coeff n f : ℚ) : ℂ) * z ^ n

/-- The formal series `log (1 - X)`. -/
noncomputable def Lf : PowerSeries ℚ := PowerSeries.mk fun n => if n = 0 then 0 else -(1 / (n : ℚ))

/-- The formal dilogarithm `Σ X^n / n²`. -/
noncomputable def Li2f : PowerSeries ℚ :=
  PowerSeries.mk fun n => if n = 0 then 0 else 1 / ((n : ℚ) ^ 2)

@[simp] lemma evp_zero (z : ℂ) : evp (0 : PowerSeries ℚ) z = 0 := by
  simp [evp]

@[simp] lemma evp_one (z : ℂ) : evp (1 : PowerSeries ℚ) z = 1 := by
  have h : (fun n : ℕ => ((PowerSeries.coeff n (1 : PowerSeries ℚ) : ℚ) : ℂ) * z ^ n)
      = fun n : ℕ => if n = 0 then (1 : ℂ) else 0 := by
    funext n
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · simp [PowerSeries.coeff_one, hn]
  rw [evp, h]
  simp

@[simp] lemma evp_C (c : ℚ) (z : ℂ) : evp (PowerSeries.C c) z = (c : ℂ) := by
  have h : (fun n : ℕ => ((PowerSeries.coeff n (PowerSeries.C c) : ℚ) : ℂ) * z ^ n)
      = fun n : ℕ => if n = 0 then (c : ℂ) else 0 := by
    funext n
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    · simp [PowerSeries.coeff_C, hn]
  rw [evp, h]
  simp

lemma evp_X (z : ℂ) : evp (PowerSeries.X : PowerSeries ℚ) z = z := by
  have h : (fun n : ℕ => ((PowerSeries.coeff n (PowerSeries.X : PowerSeries ℚ) : ℚ) : ℂ) * z ^ n)
      = fun n : ℕ => if n = 1 then z else 0 := by
    funext n
    rcases eq_or_ne n 1 with rfl | hn
    · simp
    · simp [PowerSeries.coeff_X, hn]
  rw [evp, h]
  simp

end Work.CPull
