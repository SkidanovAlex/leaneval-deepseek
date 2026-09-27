import Mathlib
import Submission.Work.KT.FP.PencilDefs
import Submission.Work.KT.Fund.SpectralAux

namespace Work.KT.FP

open MeasureTheory intervalIntegral
open scoped Topology Interval

noncomputable section

/-- **Fubini for the iterated circle integral of `(w - z)⁻¹ • pResA A B w`.**

If the pencil `z ↦ z • A + B` is invertible on the closed annulus `r ≤ ‖z‖ ≤ s`
(`0 < r < s`), then the iterated circle integrals over `|z| = r` and `|w| = s` may be exchanged.

The kernel `(z, w) ↦ (w - z)⁻¹ • pResA A B w` is continuous on
`Metric.sphere 0 r ×ˢ Metric.sphere 0 s` because `r < s` forces `w ≠ z` there and `pResA A B`
is continuous on the circle `|w| = s` (from `hunit` and
`ContinuousOn Ring.inverse {x | IsUnit x}`); then apply
`Work.KT.Fund.circleIntegral_swap`. -/
theorem swap_inv_sub_pResA {R : Type*} [NormedRing R] [NormedAlgebra ℂ R] [CompleteSpace R]
    (A B : R) {r s : ℝ} (hr : 0 < r) (hrs : r < s)
    (hunit : ∀ z : ℂ, r ≤ ‖z‖ → ‖z‖ ≤ s → IsUnit (z • A + B)) :
    (∮ z in C(0, r), ∮ w in C(0, s), (w - z)⁻¹ • pResA A B w) =
      ∮ w in C(0, s), ∮ z in C(0, r), (w - z)⁻¹ • pResA A B w := by
  have hr0 : 0 ≤ r := le_of_lt hr
  have hrs' : r ≤ s := le_of_lt hrs
  have hs0 : 0 ≤ s := le_trans hr0 hrs'
  -- Continuity of `Ring.inverse` on the units.
  have hunits : ContinuousOn Ring.inverse {x : R | IsUnit x} := by
    intro x hx
    simpa only [IsUnit.unit_spec hx] using
      (NormedRing.inverse_continuousAt hx.unit).continuousWithinAt
  have hlin : Continuous fun z : ℂ => z • A + B :=
    (continuous_id.smul continuous_const).add continuous_const
  -- The resolvent `Ring.inverse (w • A + B)` is continuous on the circle `|w| = s`.
  have hres : ContinuousOn (fun w : ℂ => Ring.inverse (w • A + B)) (Metric.sphere (0:ℂ) s) := by
    have hcomp := hunits.comp (s := Metric.sphere (0:ℂ) s) hlin.continuousOn (fun w hw => ?_)
    · simpa [Function.comp_def] using hcomp
    · have hw_s : ‖w‖ = s := by simpa [dist_eq_norm] using Metric.mem_sphere.mp hw
      exact hunit w (by rw [hw_s]; exact hrs') (by rw [hw_s])
  -- Hence `pResA A B` is continuous on that circle.
  have hpResA : ContinuousOn (fun w : ℂ => pResA A B w) (Metric.sphere (0:ℂ) s) := by
    have hconst : ContinuousOn (fun _ : ℂ => A) (Metric.sphere (0:ℂ) s) := continuousOn_const
    exact (hres.mul hconst).congr (fun w _ => by simp [pResA, pRes])
  -- Continuity of the kernel on the product of the two circles.
  have hF : ContinuousOn (Function.uncurry (fun z w : ℂ => (w - z)⁻¹ • pResA A B w))
      (Metric.sphere (0:ℂ) r ×ˢ Metric.sphere (0:ℂ) s) := by
    have hdiff : ContinuousOn (fun p : ℂ × ℂ => p.2 - p.1)
        (Metric.sphere (0:ℂ) r ×ˢ Metric.sphere (0:ℂ) s) :=
      (continuous_snd.sub continuous_fst).continuousOn
    have hne : ∀ p ∈ (Metric.sphere (0:ℂ) r ×ˢ Metric.sphere (0:ℂ) s), p.2 - p.1 ≠ 0 := by
      intro p hp
      obtain ⟨hp1, hp2⟩ := Set.mem_prod.mp hp
      have h1 : ‖p.1‖ = r := by simpa [dist_eq_norm] using Metric.mem_sphere.mp hp1
      have h2 : ‖p.2‖ = s := by simpa [dist_eq_norm] using Metric.mem_sphere.mp hp2
      intro hcon
      have hthis : ‖p.2‖ = ‖p.1‖ := by rw [sub_eq_zero.mp hcon]
      rw [h1, h2] at hthis
      linarith
    have hinv : ContinuousOn (fun p : ℂ × ℂ => (p.2 - p.1)⁻¹)
        (Metric.sphere (0:ℂ) r ×ˢ Metric.sphere (0:ℂ) s) :=
      hdiff.inv₀ hne
    have hres2 : ContinuousOn (fun p : ℂ × ℂ => pResA A B p.2)
        (Metric.sphere (0:ℂ) r ×ˢ Metric.sphere (0:ℂ) s) := by
      have hc := hpResA.comp (s := Metric.sphere (0:ℂ) r ×ˢ Metric.sphere (0:ℂ) s)
        (continuous_snd (Y := ℂ)).continuousOn (fun p hp => (Set.mem_prod.mp hp).2)
      simpa [Function.comp_def] using hc
    have hsm := hinv.smul hres2
    rw [show Function.uncurry (fun z w : ℂ => (w - z)⁻¹ • pResA A B w)
        = (fun p : ℂ × ℂ => (p.2 - p.1)⁻¹ • pResA A B p.2) from rfl]
    exact hsm
  exact Work.KT.Fund.circleIntegral_swap (fun z w : ℂ => (w - z)⁻¹ • pResA A B w) hr0 hs0 hF

end

end Work.KT.FP
