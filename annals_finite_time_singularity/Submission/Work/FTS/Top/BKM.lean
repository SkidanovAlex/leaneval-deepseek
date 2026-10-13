/-
# `Work.FTS.Top.BKM` — the Beale–Kato–Majda divergence of a `BlowupAt`

The last clause of the challenge statement is the divergence of the BKM integral
`t ↦ ∫₀ᵗ (⨆ₓ ‖ω(x,s)‖) ds` at the blow-up time.  For a `BlowupAt` this is exactly the
stability chapter's `St5` (`Work.StabilityFar.bkm_divergence_of_vortLinfLower`), whose inputs are

* the pointwise lower bound `c/(T-t) ≤ ‖ω(·,t)‖_∞` — the `lower` field of `BlowupAt`;
* the interval-integrability of the integrand — `Work.FTS.Top.intervalIntegrable_vortLInf`.

Nothing else is needed, and in particular no regularity at or past the blow-up time.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.FTS.Top.Defs
import Submission.Work.FTS.Top.Integrable.intervalIntegrable_vortLInf
import Submission.Work.StabilityFar.St5

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open FiniteTimeSingularity Set Gradient Matrix Filter Topology MeasureTheory
open scoped Topology Matrix NNReal ENNReal

set_option autoImplicit false

namespace Work.FTS.Top

/-- **The interval-integrability of the BKM integrand** for a `BlowupAt`: the top-namespace form
of `Work.FTS.Top.Integrable.intervalIntegrable_vortLInf`.  What makes it true is that the strip
regularity is only assumed on the *closed* sub-strips `[0,t]`, `t < T` — so a uniform bound on the
vorticity is available there, and the worst case (`t → T⁻`) is exactly the blow-up. -/
theorem intervalIntegrable_vortLInf {α : ℝ≥0} {T : ℝ} (B : BlowupAt α T) :
    ∀ t ∈ Set.Ico 0 T, IntervalIntegrable (Work.LWP.vortLInf B.u) volume 0 t :=
  Work.FTS.Top.Integrable.intervalIntegrable_vortLInf B

namespace BlowupAt

/-- **The `lower` clause of `BlowupAt` is the `VortLinfLower` predicate** of the stability chapter
(the two are definitionally the same statement). -/
theorem vortLinfLower {α : ℝ≥0} {T : ℝ} (B : BlowupAt α T) :
    ∃ c : ℝ, 0 < c ∧ Work.StabilityFar.VortLinfLower B.u T c := B.lower

/-- **The BKM integral of a `BlowupAt` diverges at the blow-up time.**  This is the whole content
of the last clause of the main statement, reduced to the `lower` field. -/
theorem bkm_divergence {α : ℝ≥0} {T : ℝ} (B : BlowupAt α T) :
    Filter.Tendsto (Work.LWP.bkm B.u) (𝓝[<] T) Filter.atTop := by
  obtain ⟨c, hc, hlow⟩ := B.lower
  exact Work.StabilityFar.bkm_divergence_of_vortLinfLower B.hT hc hlow
    (Work.FTS.Top.intervalIntegrable_vortLInf B)

/-- **A `BlowupAt` really does blow up.**  The vorticity sup-norm is unbounded above on `[0,T)`:
for every `K` there is `t ∈ Ico 0 T` with `K < ‖ω(·,t)‖_∞`.

This is the quantitative content of the `lower` field, and it is the complement of the uniform
bound on the *closed* sub-strips `[0,t]`, `t < T` (proved in
`Submission/Work/FTS/Top/Integrable/intervalIntegrable_vortLInf.lean`): together they say exactly
that the growth of the vorticity is confined to the approach to `T`, which is what a non-vacuous
blow-up interface should say. -/
theorem unbounded_vortLInf {α : ℝ≥0} {T : ℝ} (B : BlowupAt α T) (K : ℝ) :
    ∃ t ∈ Set.Ico 0 T, K < Work.LWP.vortLInf B.u t := by
  obtain ⟨c, hc, hlow⟩ := B.lower
  set δ : ℝ := min (T / 2) (c / (|K| + 1)) with hδ
  have hδpos : 0 < δ := lt_min (by linarith [B.hT]) (div_pos hc (by positivity))
  have hδT : δ < T := lt_of_le_of_lt (min_le_left _ _) (by linarith [B.hT])
  have hlow' : c / (T - (T - δ)) ≤ Work.LWP.vortLInf B.u (T - δ) :=
    hlow (T - δ) ⟨by linarith, by linarith⟩
  have hval : c / (T - (T - δ)) = c / δ := by ring_nf
  rw [hval] at hlow'
  refine ⟨T - δ, ⟨by linarith, by linarith⟩, lt_of_lt_of_le ?_ hlow'⟩
  rw [lt_div_iff₀ hδpos]
  by_cases hK : K ≤ 0
  · nlinarith [hδpos, hc]
  · push_neg at hK
    have h1 : δ ≤ c / (|K| + 1) := min_le_right _ _
    have h3 : K * δ ≤ K * (c / (|K| + 1)) := mul_le_mul_of_nonneg_left h1 hK.le
    have h4 : K * (c / (|K| + 1)) < c := by
      rw [← mul_div_assoc, div_lt_iff₀ (by positivity : (0 : ℝ) < |K| + 1)]
      nlinarith [le_abs_self K, hc]
    linarith

/-- **The same divergence in the literal form of the challenge statement**: the BKM integral is
written out as `t ↦ ∫₀ᵗ ⨆ₓ ‖ω(x,s)‖ ds`.  The two forms are the same by
`Work.LWP.bkm_eq_challenge_integral`. -/
theorem bkm_divergence_integral {α : ℝ≥0} {T : ℝ} (B : BlowupAt α T) :
    Filter.Tendsto (fun t => ∫ s in 0..t, ⨆ x, ‖vorticity (fun y => B.u y s) x‖)
      (𝓝[<] T) Filter.atTop := by
  have h := B.bkm_divergence
  have h2 : Work.LWP.bkm B.u
      = fun t => ∫ s in 0..t, ⨆ x, ‖vorticity (fun y => B.u y s) x‖ :=
    funext (Work.LWP.bkm_eq_challenge_integral B.u)
  rwa [h2] at h

/-- **The `T = 1` instance, routed literally through `Work.StabilityFar.bkm_divergence_at_one`.**
This is the last clause of the challenge statement at the physical blow-up time, in the exact
shape in which `Work.FTS.Top.theorem_1_of_blowupAt` consumes it: the only inputs are the `lower`
field of the interface and `Work.FTS.Top.intervalIntegrable_vortLInf`. -/
theorem bkm_divergence_one {α : ℝ≥0} (B : BlowupAt α 1) :
    Filter.Tendsto (fun t => ∫ s in 0..t, ⨆ x, ‖vorticity (fun y => B.u y s) x‖)
      (𝓝[<] 1) Filter.atTop := by
  obtain ⟨c, hc, hlow⟩ := B.lower
  exact Work.StabilityFar.bkm_divergence_at_one hc hlow
    (Work.FTS.Top.intervalIntegrable_vortLInf B)

end BlowupAt

end Work.FTS.Top
