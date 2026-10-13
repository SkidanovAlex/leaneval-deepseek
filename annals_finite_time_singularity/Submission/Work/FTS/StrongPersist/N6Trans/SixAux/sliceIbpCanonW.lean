import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Submission.Work.FTS.TransportS.SlotT2.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.RPFresh.hasDerivAt_w2z_mul

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# The slice-by-slice radial integration by parts against the canonical weight

For a fixed `θ ∈ (0, π/2)` the canonical weight `canonW q · θ` is (a constant times) the
radial weight `w(z)² = (1+z)⁴/z⁴`, which satisfies the exact identity

  `z · (w²)'(z) = -4 · w(z)²/(1+z)`,  hence  `(z w²)'(z) = ((z-3)/(1+z)) · w(z)²`.

Consequently, if `|h| ≤ M` and `|z h'| ≤ M`, then

  `(d/dz) (z · canonW q z θ · h z) = canonW q z θ · (z h' + ((z-3)/(1+z)) h)`,

so the absolute value of this derivative is dominated by `4 M canonW q · θ`.  Integrating by
parts against `Y²` on `(0,∞)` — the boundary terms vanish by the two limit hypotheses —
turns `∫ canonW q · θ · h · (z Y') · Y` into `-(1/2) ∫ (z canonW h)' Y²`, which is exactly
the loss of a factor `2M` in the estimate.

## Main statement

`Work.FTS.StrongPersist.N6Trans.SixAux.sliceIbpCanonW`.
-/

noncomputable section
open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.N6Trans.SixAux

open Work.FTS.TransportS.SlotT2 (canonW canonW_nonneg)

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! ## The derivative of `z ↦ z · canonW q z θ · h z` -/

/-- For `θ` fixed, the function `z ↦ z · canonW q z θ · h z` has the derivative
`canonW q z θ · (z h' + ((z-3)/(1+z)) h)` on `(0,∞)`.  The point is the identity
`(z w²)' = ((z-3)/(1+z)) w²` for the radial weight `w(z) = (1+z)²/z²`, which combines with the
product rule and the extra factor `z`. -/
theorem hasDerivAt_zCanonW_mul {q : ℝ} {h : ℝ → ℝ} {θ : ℝ}
    (hh : ∀ z ∈ Set.Ioi (0 : ℝ), HasDerivAt h (deriv h z) z) :
    ∀ x ∈ Set.Ioi (0 : ℝ), HasDerivAt (fun z => z * canonW q z θ * h z)
      (canonW q x θ * (x * deriv h x + ((x - 3) / (1 + x)) * h x)) x := by
  intro x hx
  have h0 := (Work.RPFresh.hasDerivAt_w2z_mul (f := h) hx (hh x hx)).mul_const
    ((Real.sin (2 * θ)) ^ (-q))
  have hfun : (fun z => z * canonW q z θ * h z)
      = (fun z => (Work.Spaces.w z) ^ 2 * z * h z * (Real.sin (2 * θ)) ^ (-q)) := by
    funext z
    simp only [canonW]
    ring
  have hder : canonW q x θ * (x * deriv h x + ((x - 3) / (1 + x)) * h x)
      = (Work.Spaces.w x) ^ 2 * (x * deriv h x + (x - 3) / (1 + x) * h x)
        * (Real.sin (2 * θ)) ^ (-q) := by
    simp only [canonW]
    ring
  rw [hfun, hder]
  exact h0

/-- The `deriv` form of `hasDerivAt_zCanonW_mul`. -/
theorem deriv_zCanonW_mul {q : ℝ} {h : ℝ → ℝ} {θ : ℝ}
    (hh : ∀ z ∈ Set.Ioi (0 : ℝ), HasDerivAt h (deriv h z) z) :
    ∀ x ∈ Set.Ioi (0 : ℝ), deriv (fun z => z * canonW q z θ * h z) x
      = canonW q x θ * (x * deriv h x + ((x - 3) / (1 + x)) * h x) :=
  fun x hx => (hasDerivAt_zCanonW_mul (q := q) hh x hx).deriv

/-- The pointwise domination of the derivative: `|(z canonW h)'| ≤ 4 M canonW` on `(0,∞)`,
using `|h| ≤ M`, `|z h'| ≤ M` and `|(z-3)/(1+z)| ≤ 3`. -/
theorem abs_deriv_zCanonW_mul_le {q M : ℝ} {h : ℝ → ℝ} {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2))
    (hh : ∀ z ∈ Set.Ioi (0 : ℝ), HasDerivAt h (deriv h z) z)
    (hhn : ∀ z ∈ Set.Ioi (0 : ℝ), |h z| ≤ M)
    (hDhn : ∀ z ∈ Set.Ioi (0 : ℝ), |z * deriv h z| ≤ M) :
    ∀ x ∈ Set.Ioi (0 : ℝ),
      |deriv (fun z => z * canonW q z θ * h z) x| ≤ 4 * M * canonW q x θ := by
  intro x hx
  have hx0 : 0 < x := hx
  have hθ' : θ ∈ Work.Spaces.Iθ := ⟨le_of_lt hθ.1, le_of_lt hθ.2⟩
  have hCnn : 0 ≤ canonW q x θ := canonW_nonneg hθ'
  rw [deriv_zCanonW_mul (q := q) hh x hx]
  have h1 : |x * deriv h x + ((x - 3) / (1 + x)) * h x| ≤ M + 3 * M := by
    have hA : |x * deriv h x| ≤ M := hDhn x hx
    have hB : |((x - 3) / (1 + x)) * h x| ≤ 3 * M := by
      rw [abs_mul]
      have h1x : (0 : ℝ) < 1 + x := by linarith
      have h2 : |(x - 3) / (1 + x)| ≤ 3 := by
        rw [abs_div, abs_of_pos h1x, div_le_iff₀ h1x]
        have h3 : |x - 3| ≤ x + 3 := by
          rw [abs_le]
          constructor <;> linarith
        linarith
      exact mul_le_mul h2 (hhn x hx) (abs_nonneg _) (by linarith)
    calc |x * deriv h x + ((x - 3) / (1 + x)) * h x|
        ≤ |x * deriv h x| + |((x - 3) / (1 + x)) * h x| := abs_add_le _ _
      _ ≤ M + 3 * M := add_le_add hA hB
  calc |canonW q x θ * (x * deriv h x + ((x - 3) / (1 + x)) * h x)|
      = canonW q x θ * |x * deriv h x + ((x - 3) / (1 + x)) * h x| := by
        rw [abs_mul, abs_of_nonneg hCnn]
    _ ≤ canonW q x θ * (M + 3 * M) := mul_le_mul_of_nonneg_left h1 hCnn
    _ = 4 * M * canonW q x θ := by ring

/-! ## The integration by parts -/

theorem sliceIbpCanonW {q M : ℝ} (hM : 0 ≤ M) {h Y : ℝ → ℝ} {θ : ℝ}
    (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2))
    (hh : ∀ z ∈ Set.Ioi (0 : ℝ), HasDerivAt h (deriv h z) z)
    (hY : ∀ z ∈ Set.Ioi (0 : ℝ), HasDerivAt Y (deriv Y z) z)
    (hhn : ∀ z ∈ Set.Ioi (0 : ℝ), |h z| ≤ M)
    (hDhn : ∀ z ∈ Set.Ioi (0 : ℝ), |z * deriv h z| ≤ M)
    (hint1 : MeasureTheory.IntegrableOn
      (fun z => Work.FTS.TransportS.SlotT2.canonW q z θ * (Y z) ^ 2) (Set.Ioi (0 : ℝ)))
    (hint2 : MeasureTheory.IntegrableOn
      (fun z => Work.FTS.TransportS.SlotT2.canonW q z θ * h z * (z * deriv Y z) * Y z)
      (Set.Ioi (0 : ℝ)))
    (hlim0 : Filter.Tendsto
      (fun z => z * Work.FTS.TransportS.SlotT2.canonW q z θ * h z * (Y z) ^ 2)
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0))
    (hlimT : Filter.Tendsto
      (fun z => z * Work.FTS.TransportS.SlotT2.canonW q z θ * h z * (Y z) ^ 2)
      Filter.atTop (nhds 0)) :
    |∫ z in Set.Ioi (0 : ℝ),
        Work.FTS.TransportS.SlotT2.canonW q z θ * h z * (z * deriv Y z) * Y z|
      ≤ 2 * M * ∫ z in Set.Ioi (0 : ℝ),
          Work.FTS.TransportS.SlotT2.canonW q z θ * (Y z) ^ 2 := by
  -- ### the majorant `4 M · canonW q · θ · Y²`
  have hmaj : MeasureTheory.Integrable
      (fun z : ℝ => 4 * M * (canonW q z θ * (Y z) ^ 2))
      (volume.restrict (Set.Ioi (0 : ℝ))) :=
    hint1.const_mul (4 * M)
  -- ### integrability of `(z canonW h) · (Y²)'`
  have huv' : MeasureTheory.IntegrableOn
      (fun z : ℝ => (z * canonW q z θ * h z) * (2 * Y z * deriv Y z)) (Set.Ioi (0 : ℝ)) := by
    refine IntegrableOn.congr_fun (hint2.const_mul (2 : ℝ)) (fun z _ => ?_) measurableSet_Ioi
    ring
  -- ### the two `HasDerivAt` inputs of the integration by parts
  have hu : ∀ x ∈ Set.Ioi (0 : ℝ), HasDerivAt (fun z => z * canonW q z θ * h z)
      (deriv (fun z => z * canonW q z θ * h z) x) x :=
    fun x hx => (hasDerivAt_zCanonW_mul (q := q) hh x hx).differentiableAt.hasDerivAt
  have hv : ∀ x ∈ Set.Ioi (0 : ℝ), HasDerivAt (fun z => (Y z) ^ 2) (2 * Y x * deriv Y x) x := by
    intro x hx
    have h0 := (hY x hx).mul (hY x hx)
    have h : HasDerivAt (fun z : ℝ => Y z * Y z) (2 * Y x * deriv Y x) x :=
      h0.congr_deriv (by ring)
    have heq : (fun z : ℝ => Y z ^ 2) = (fun z : ℝ => Y z * Y z) := by
      funext z
      ring
    rw [heq]
    exact h
  -- ### the pointwise bound for the derivative
  have hpt : ∀ z ∈ Set.Ioi (0 : ℝ),
      |deriv (fun z => z * canonW q z θ * h z) z * (Y z) ^ 2|
        ≤ 4 * M * (canonW q z θ * (Y z) ^ 2) := by
    intro z hz
    have hle := abs_deriv_zCanonW_mul_le (q := q) (M := M) hθ hh hhn hDhn z hz
    calc |deriv (fun z => z * canonW q z θ * h z) z * (Y z) ^ 2|
        = |deriv (fun z => z * canonW q z θ * h z) z| * (Y z) ^ 2 := by
          rw [abs_mul, abs_of_nonneg (sq_nonneg (Y z))]
      _ ≤ (4 * M * canonW q z θ) * (Y z) ^ 2 := mul_le_mul_of_nonneg_right hle (sq_nonneg _)
      _ = 4 * M * (canonW q z θ * (Y z) ^ 2) := by ring
  -- ### integrability of `(z canonW h)' · Y²`
  have hu'v : MeasureTheory.IntegrableOn
      (fun z : ℝ => deriv (fun z => z * canonW q z θ * h z) z * (Y z) ^ 2) (Set.Ioi (0 : ℝ)) := by
    have hY2 : AEStronglyMeasurable (fun z : ℝ => (Y z) ^ 2)
        (volume.restrict (Set.Ioi (0 : ℝ))) := by
      have hcont : ContinuousOn Y (Set.Ioi (0 : ℝ)) :=
        fun z hz => (hY z hz).continuousAt.continuousWithinAt
      have h1 : AEStronglyMeasurable Y (volume.restrict (Set.Ioi (0 : ℝ))) :=
        ContinuousOn.aestronglyMeasurable (μ := volume) hcont measurableSet_Ioi
      have h2 : AEStronglyMeasurable (fun z : ℝ => Y z * Y z)
          (volume.restrict (Set.Ioi (0 : ℝ))) := h1.mul h1
      simpa only [sq] using h2
    have hd : AEStronglyMeasurable
        (fun z : ℝ => deriv (fun z => z * canonW q z θ * h z) z)
        (volume.restrict (Set.Ioi (0 : ℝ))) :=
      (aestronglyMeasurable_deriv (fun z => z * canonW q z θ * h z) volume).mono_measure
        Measure.restrict_le_self
    refine hmaj.mono' (hd.mul hY2) ?_
    refine ae_restrict_of_forall_mem measurableSet_Ioi (fun z hz => ?_)
    rw [Real.norm_eq_abs]
    exact hpt z hz
  have hu'abs : MeasureTheory.Integrable
      (fun z : ℝ => |deriv (fun z => z * canonW q z θ * h z) z * (Y z) ^ 2|)
      (volume.restrict (Set.Ioi (0 : ℝ))) := by
    have h := MeasureTheory.Integrable.abs hu'v
    simpa only [Real.norm_eq_abs] using h
  -- ### the integration by parts
  have hIBP := MeasureTheory.integral_Ioi_mul_deriv_eq_deriv_mul (a := (0 : ℝ))
    (u := fun z => z * canonW q z θ * h z)
    (u' := fun z => deriv (fun z => z * canonW q z θ * h z) z)
    (v := fun z => (Y z) ^ 2)
    (v' := fun z => 2 * Y z * deriv Y z)
    (a' := (0 : ℝ)) (b' := (0 : ℝ)) hu hv huv' hu'v hlim0 hlimT
  have hL : (∫ z in Set.Ioi (0 : ℝ), (z * canonW q z θ * h z) * (2 * Y z * deriv Y z))
      = 2 * (∫ z in Set.Ioi (0 : ℝ), canonW q z θ * h z * (z * deriv Y z) * Y z) := by
    rw [← MeasureTheory.integral_const_mul]
    exact MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun z _ => by ring)
  have h2A : 2 * (∫ z in Set.Ioi (0 : ℝ), canonW q z θ * h z * (z * deriv Y z) * Y z)
      = -(∫ z in Set.Ioi (0 : ℝ),
          deriv (fun z => z * canonW q z θ * h z) z * (Y z) ^ 2) := by
    rw [← hL]
    simpa using hIBP
  have hAeq : (∫ z in Set.Ioi (0 : ℝ), canonW q z θ * h z * (z * deriv Y z) * Y z)
      = -(1 / 2) * (∫ z in Set.Ioi (0 : ℝ),
          deriv (fun z => z * canonW q z θ * h z) z * (Y z) ^ 2) := by
    linarith [h2A]
  -- ### the bound on the derivative term
  have hBnd : |∫ z in Set.Ioi (0 : ℝ),
        deriv (fun z => z * canonW q z θ * h z) z * (Y z) ^ 2|
      ≤ 4 * M * ∫ z in Set.Ioi (0 : ℝ), canonW q z θ * (Y z) ^ 2 := by
    have hconst : (∫ z in Set.Ioi (0 : ℝ), 4 * M * (canonW q z θ * (Y z) ^ 2))
        = 4 * M * ∫ z in Set.Ioi (0 : ℝ), canonW q z θ * (Y z) ^ 2 :=
      MeasureTheory.integral_const_mul (4 * M) _
    calc |∫ z in Set.Ioi (0 : ℝ), deriv (fun z => z * canonW q z θ * h z) z * (Y z) ^ 2|
        ≤ ∫ z in Set.Ioi (0 : ℝ),
            |deriv (fun z => z * canonW q z θ * h z) z * (Y z) ^ 2| :=
          MeasureTheory.abs_integral_le_integral_abs
      _ ≤ ∫ z in Set.Ioi (0 : ℝ), 4 * M * (canonW q z θ * (Y z) ^ 2) :=
          MeasureTheory.integral_mono_ae hu'abs hmaj
            (ae_restrict_of_forall_mem measurableSet_Ioi (fun z hz => hpt z hz))
      _ = 4 * M * ∫ z in Set.Ioi (0 : ℝ), canonW q z θ * (Y z) ^ 2 := hconst
  -- ### conclusion
  rw [hAeq, abs_mul]
  have habs : |-(1 / 2 : ℝ)| = 1 / 2 := by norm_num
  rw [habs]
  calc (1 / 2) * |∫ z in Set.Ioi (0 : ℝ),
          deriv (fun z => z * canonW q z θ * h z) z * (Y z) ^ 2|
      ≤ (1 / 2) * (4 * M * ∫ z in Set.Ioi (0 : ℝ), canonW q z θ * (Y z) ^ 2) :=
        mul_le_mul_of_nonneg_left hBnd (by norm_num)
    _ = 2 * M * ∫ z in Set.Ioi (0 : ℝ), canonW q z θ * (Y z) ^ 2 := by ring

end Work.FTS.StrongPersist.N6Trans.SixAux
