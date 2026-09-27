import Mathlib
import Submission.Work.KT.FP.PencilDefs
import Submission.Work.KT.Fund.SpectralAux

namespace Work.KT.FP

open Matrix MeasureTheory intervalIntegral
open scoped Topology Interval

noncomputable section

/-- **Continuity of `pResA A B` on a circle inside the invertibility locus.**

If the pencil `z ↦ z • A + B` is a unit at every point of the circle `‖z‖ = ρ`, then
`z ↦ pResA A B z = (zA + B)⁻¹ A` is continuous on that circle. -/
theorem pResA_continuousOn_sphere {R : Type*} [NormedRing R] [NormedAlgebra ℂ R] [CompleteSpace R]
    (A B : R) {ρ : ℝ} (hunit : ∀ z : ℂ, ‖z‖ = ρ → IsUnit (z • A + B)) :
    ContinuousOn (fun z : ℂ => pResA A B z) (Metric.sphere (0:ℂ) ρ) := by
  have hunits : ContinuousOn Ring.inverse {x : R | IsUnit x} := by
    intro x hx
    simpa only [IsUnit.unit_spec hx] using
      (NormedRing.inverse_continuousAt hx.unit).continuousWithinAt
  have hlin : Continuous fun z : ℂ => z • A + B :=
    (continuous_id.smul continuous_const).add continuous_const
  have hmaps : Set.MapsTo (fun z : ℂ => z • A + B) (Metric.sphere (0:ℂ) ρ) {x : R | IsUnit x} :=
    fun z hz => hunit z (by
      have h := Metric.mem_sphere.mp hz
      rwa [dist_eq_norm, sub_zero] at h)
  have h := hunits.comp hlin.continuousOn hmaps
  have hconst : ContinuousOn (fun _ : ℂ => A) (Metric.sphere (0:ℂ) ρ) := continuousOn_const
  exact (h.mul hconst).congr (fun z _ => by simp [pResA, pRes])

/-- **The product of the two pencil circle integrals as an iterated integral.**

If the pencil `z ↦ z • A + B` is invertible on the closed annulus `r ≤ ‖z‖ ≤ s`
(`0 < r < s`) then
`(∮_{|z|=r} pResA A B z) * (∮_{|w|=s} pResA A B w) = ∮_{|z|=r} ∮_{|w|=s} pResA A B z * pResA A B w`.

Proof: `circleIntegral_mul_const` pulls the constant `pCirc A B s` inside the outer integral, then
`circleIntegral_const_mul` and `circleIntegral.integral_congr` identify `pResA A B z * pCirc A B s`
with `∮_{|w|=s} pResA A B z * pResA A B w`; integrability of `pResA A B` on both circles comes from
continuity there (`hunit`) and `ContinuousOn.circleIntegrable`. -/
theorem pCirc_mul_pCirc_iterated {R : Type*} [NormedRing R] [NormedAlgebra ℂ R] [CompleteSpace R]
    (A B : R) {r s : ℝ} (hr : 0 < r) (hrs : r < s)
    (hunit : ∀ z : ℂ, r ≤ ‖z‖ → ‖z‖ ≤ s → IsUnit (z • A + B)) :
    pCirc A B r * pCirc A B s =
      ∮ z in C(0, r), ∮ w in C(0, s), pResA A B z * pResA A B w := by
  have hrs' : r ≤ s := le_of_lt hrs
  have hs0 : 0 ≤ s := le_trans (le_of_lt hr) hrs'
  -- Continuity of `pResA A B` on the two circles.
  have hcontr : ContinuousOn (fun z : ℂ => pResA A B z) (Metric.sphere (0:ℂ) r) :=
    pResA_continuousOn_sphere A B
      (fun z hz => hunit z (le_of_eq hz.symm) (by rw [hz]; exact hrs'))
  have hconts : ContinuousOn (fun z : ℂ => pResA A B z) (Metric.sphere (0:ℂ) s) :=
    pResA_continuousOn_sphere A B
      (fun z hz => hunit z (by rw [hz]; exact hrs') (le_of_eq hz))
  -- Hence circle-integrability on both circles.
  have hintr : CircleIntegrable (fun z : ℂ => pResA A B z) 0 r :=
    hcontr.circleIntegrable (le_of_lt hr)
  have hints : CircleIntegrable (fun z : ℂ => pResA A B z) 0 s :=
    hconts.circleIntegrable hs0
  -- Pull the constant `pCirc A B s` inside the outer integral ...
  simp only [pCirc]
  rw [← Work.KT.Fund.circleIntegral_mul_const (∮ w in C(0, s), pResA A B w)
        (fun z => pResA A B z) 0 r hintr]
  -- ... and identify the integrands pointwise with the inner circle integral.
  refine circleIntegral.integral_congr (le_of_lt hr) (fun z _ => ?_)
  exact (Work.KT.Fund.circleIntegral_const_mul (pResA A B z) (fun z => pResA A B z) 0 s
    hints).symm

end

end Work.KT.FP
