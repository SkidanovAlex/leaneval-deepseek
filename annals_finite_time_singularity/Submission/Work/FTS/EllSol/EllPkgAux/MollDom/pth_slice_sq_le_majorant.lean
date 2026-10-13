/-
# The pointwise majorant of the angular derivative of a trace-class slice

For a trace-class datum `G` (`Work.FTS.EllSol.EllPkgAux.TraceClass G`) and a fixed radius
`z > 0`, the angular derivative of the slice `s ↦ G z s` is bounded for `s ∈ (0, π/2)` by

  `|∂_θG(z,s)| ≤ |∂_θG(z,π/4)| + √(∫_{Iθ} (∂_θ²G(z,θ))² σ_η θ) · √(π/4)`,

where `π/4` is the landmark angle.  This is the fundamental theorem of calculus from `π/4` to
`s`, together with the interval Cauchy–Schwarz bound; squaring gives
`(∂_θG(z,s))² ≤ thSliceMajorant G z`.

The two ingredients are separated out:

* `Work.FTS.EllSol.EllPkgAux.MollDom.abs_interval_integral_le_sqrt_thEta` — the sub-interval
  Cauchy–Schwarz bound with constant `√(π/4)`;
* `Work.FTS.EllSol.EllPkgAux.MollDom.pth2_slice_integrable` — the honesty of the `∂_θ²`-slice
  (`SliceHonestOpen G`, the last conjunct of `TraceClass`), which makes the `σ_η`-weighted
  slice integrable and hence the Cauchy–Schwarz factor honest.

The regularity of the slice (`C²` on the open interval) comes from the `SmoothOpen` conjunct of
`TraceClass` via `SmoothOpen.curry_θ`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Submission.Work.FTS.EllSol.EllPkgAux.MollDom.zSchurWindowDefs
import Submission.Work.FTS.EllSol.EllPkgAux.MollDom.slice_deriv_bdd
import Submission.Work.FTS.EllSol.EllPkgAux.MollDom.pth2_slice_integrable
import Submission.Work.FTS.EllSol.EllPkgAux.MollDom.abs_interval_integral_le_sqrt_thEta

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllSol.EllPkgAux.MollDom

set_option maxHeartbeats 800000

theorem pth_slice_sq_le_majorant (G : ℝ → ℝ → ℝ) (hT : Work.FTS.EllSol.EllPkgAux.TraceClass G) :
    ∀ z : ℝ, 0 < z → ∀ s ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      (Work.Spaces.pth G z s) ^ 2
        ≤ Work.FTS.EllSol.EllPkgAux.MollDom.thSliceMajorant G z := by
  intro z hz s hs
  obtain ⟨hsm, h0, hpi, htr0, htrpi, hdz0, hdzpi, hhon⟩ := hT
  -- ## The `C²`-regularity of the slice
  have hsmo : (2 : WithTop ℕ∞) ≤ Work.Stability.smoothOrder := by
    simp [Work.Stability.smoothOrder]
  have hf2 : ContDiffOn ℝ 2 (fun θ : ℝ => G z θ) (Set.Ioo (0 : ℝ) (Real.pi / 2)) :=
    (hsm.curry_θ hz).of_le hsmo
  -- ## Honesty of the `σ_η`-weighted `∂_θ²`-slice
  have hInt : MeasureTheory.IntegrableOn (fun θ : ℝ =>
      (Work.Spaces.pth (Work.Spaces.pth G) z θ) ^ 2 * Work.FTS.EllipticEst.thEta θ)
      Work.Spaces.Iθ := pth2_slice_integrable G hhon.1 z hz
  have hq0 : (0 : ℝ) < Real.pi / 4 := by positivity
  have hq1 : Real.pi / 4 < Real.pi / 2 := by linarith [Real.pi_pos]
  -- ## The interval Cauchy–Schwarz bound on a subinterval of length `≤ π/4`
  have hkey : ∀ a b : ℝ, 0 < a → a ≤ b → b < Real.pi / 2 → b - a ≤ Real.pi / 4 →
      |∫ t in a..b, Work.Spaces.pth (Work.Spaces.pth G) z t|
        ≤ Real.sqrt (∫ θ in Work.Spaces.Iθ,
              (Work.Spaces.pth (Work.Spaces.pth G) z θ) ^ 2
                * Work.FTS.EllipticEst.thEta θ)
          * Real.sqrt (Real.pi / 4) := by
    intro a b ha hab hb hlen
    have hsub : Set.uIcc a b ⊆ Set.Ioo (0 : ℝ) (Real.pi / 2) := by
      intro t ht
      rw [Set.uIcc_of_le hab] at ht
      exact ⟨lt_of_lt_of_le ha ht.1, lt_of_le_of_lt ht.2 hb⟩
    exact abs_interval_integral_le_sqrt_thEta
      ((Work.FTS.EllSol.c2_continuousOn_deriv_deriv hf2).mono hsub) hInt ha hab hb hlen
  -- ## The pointwise bound, by the fundamental theorem of calculus from the landmark `π/4`
  have hpt : |Work.Spaces.pth G z s|
      ≤ |Work.Spaces.pth G z (Real.pi / 4)|
        + Real.sqrt (∫ θ in Work.Spaces.Iθ,
            (Work.Spaces.pth (Work.Spaces.pth G) z θ) ^ 2
              * Work.FTS.EllipticEst.thEta θ) * Real.sqrt (Real.pi / 4) := by
    rcases le_total s (Real.pi / 4) with hle | hge
    · -- ## `s ≤ π/4`: run the fundamental theorem from `s` up to the landmark
      have hFTC : ∫ t in s..(Real.pi / 4), Work.Spaces.pth (Work.Spaces.pth G) z t
          = Work.Spaces.pth G z (Real.pi / 4) - Work.Spaces.pth G z s := by
        refine intervalIntegral.integral_eq_sub_of_hasDerivAt
          (f := Work.Spaces.pth G z) (f' := Work.Spaces.pth (Work.Spaces.pth G) z) ?_ ?_
        · intro t ht
          rw [Set.uIcc_of_le hle] at ht
          exact Work.FTS.EllSol.c2_hasDerivAt_deriv hf2
            ⟨lt_of_lt_of_le hs.1 ht.1, lt_of_le_of_lt ht.2 hq1⟩
        · exact Work.FTS.EllSol.c2_intervalIntegrable_deriv_deriv hf2 hs.1 hle hq1
      have hsq := hkey s (Real.pi / 4) hs.1 hle hq1 (by linarith [hs.1])
      have heq : Work.Spaces.pth G z s
          = Work.Spaces.pth G z (Real.pi / 4)
            + (- ∫ t in s..(Real.pi / 4), Work.Spaces.pth (Work.Spaces.pth G) z t) := by
        rw [hFTC]; ring
      rw [heq]
      calc |Work.Spaces.pth G z (Real.pi / 4)
              + (- ∫ t in s..(Real.pi / 4), Work.Spaces.pth (Work.Spaces.pth G) z t)|
          ≤ |Work.Spaces.pth G z (Real.pi / 4)|
            + |∫ t in s..(Real.pi / 4), Work.Spaces.pth (Work.Spaces.pth G) z t| := by
            simpa only [abs_neg] using abs_add_le (Work.Spaces.pth G z (Real.pi / 4))
              (- ∫ t in s..(Real.pi / 4), Work.Spaces.pth (Work.Spaces.pth G) z t)
        _ ≤ |Work.Spaces.pth G z (Real.pi / 4)|
            + Real.sqrt (∫ θ in Work.Spaces.Iθ,
                (Work.Spaces.pth (Work.Spaces.pth G) z θ) ^ 2
                  * Work.FTS.EllipticEst.thEta θ) * Real.sqrt (Real.pi / 4) := by
            linarith [hsq]
    · -- ## `π/4 ≤ s`: run the fundamental theorem from the landmark up to `s`
      have hFTC : ∫ t in (Real.pi / 4)..s, Work.Spaces.pth (Work.Spaces.pth G) z t
          = Work.Spaces.pth G z s - Work.Spaces.pth G z (Real.pi / 4) := by
        refine intervalIntegral.integral_eq_sub_of_hasDerivAt
          (f := Work.Spaces.pth G z) (f' := Work.Spaces.pth (Work.Spaces.pth G) z) ?_ ?_
        · intro t ht
          rw [Set.uIcc_of_le hge] at ht
          exact Work.FTS.EllSol.c2_hasDerivAt_deriv hf2
            ⟨lt_of_lt_of_le hq0 ht.1, lt_of_le_of_lt ht.2 hs.2⟩
        · exact Work.FTS.EllSol.c2_intervalIntegrable_deriv_deriv hf2 hq0 hge hs.2
      have hsq := hkey (Real.pi / 4) s hq0 hge hs.2 (by linarith [hs.2])
      have heq : Work.Spaces.pth G z s
          = Work.Spaces.pth G z (Real.pi / 4)
            + ∫ t in (Real.pi / 4)..s, Work.Spaces.pth (Work.Spaces.pth G) z t := by
        rw [hFTC]; ring
      rw [heq]
      calc |Work.Spaces.pth G z (Real.pi / 4)
              + ∫ t in (Real.pi / 4)..s, Work.Spaces.pth (Work.Spaces.pth G) z t|
          ≤ |Work.Spaces.pth G z (Real.pi / 4)|
            + |∫ t in (Real.pi / 4)..s, Work.Spaces.pth (Work.Spaces.pth G) z t| :=
            abs_add_le _ _
        _ ≤ |Work.Spaces.pth G z (Real.pi / 4)|
            + Real.sqrt (∫ θ in Work.Spaces.Iθ,
                (Work.Spaces.pth (Work.Spaces.pth G) z θ) ^ 2
                  * Work.FTS.EllipticEst.thEta θ) * Real.sqrt (Real.pi / 4) := by
            linarith [hsq]
  -- ## Square both sides
  calc (Work.Spaces.pth G z s) ^ 2 = |Work.Spaces.pth G z s| ^ 2 := by rw [← sq_abs]
    _ ≤ (|Work.Spaces.pth G z (Real.pi / 4)|
          + Real.sqrt (∫ θ in Work.Spaces.Iθ,
              (Work.Spaces.pth (Work.Spaces.pth G) z θ) ^ 2
                * Work.FTS.EllipticEst.thEta θ) * Real.sqrt (Real.pi / 4)) ^ 2 :=
        pow_le_pow_left₀ (abs_nonneg _) hpt 2
    _ = Work.FTS.EllSol.EllPkgAux.MollDom.thSliceMajorant G z := rfl

end Work.FTS.EllSol.EllPkgAux.MollDom
