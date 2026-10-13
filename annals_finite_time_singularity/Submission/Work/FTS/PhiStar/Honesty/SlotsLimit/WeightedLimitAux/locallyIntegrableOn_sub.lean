/-
Work module for the Elgindi finite-time singularity project.

# Local integrability on the open quadrant of an `L²`-weighted function minus a continuous one

The open quadrant `Q0 = (0,∞) × (0,π/2)` (`Work.FTS.EllipticEst.Q0`) carries a positive
continuous weight `ρ` (in the applications `ρ` is a power of `sin(2θ)` or a radial weight,
which *vanishes* on the boundary `∂Q0`).  The point of this file is the elementary observation
that no boundary information is needed to compare two `L²`-type objects *locally*:

* `u` is only assumed a.e. strongly measurable on `Q0` with `u²ρ²` integrable on `Q0`;
* `v` is only assumed continuous on `Q0` (it need not be bounded near `∂Q0`).

Then `u - v` is locally integrable on `Q0`.

The reason is that local integrability on an *open* set is a strictly local property: around an
interior point `x ∈ Q0` one may choose a closed ball `K ⊆ Q0`, on which `ρ` has a positive
minimum `m` by compactness.  There `u² ≤ u²ρ²/m²`, so `u² ∈ L¹(K)`, and since `K` has finite
measure this gives `u ∈ L¹(K)` because `|u| ≤ 1 + u²`.  Finally `v ∈ L¹(K)` by continuity and
compactness.  This is the `ρ`-positivity input consumed by
`Work.FTS.PhiStar.Honesty.SlotsLimit.WeightedLimitAux.locallyIntegrableOn_sub`, which is the
statement requested by the `SlotsLimit` layer (the limit of weighted slots is compared with a
continuous candidate).
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EllipticEst.OpenQDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty.SlotsLimit.WeightedLimitAux

open scoped MeasureTheory ENNReal Topology
open MeasureTheory Set Filter

/-- The elementary pointwise bound `|a| ≤ 1 + a²`, used to upgrade an `L²`-function on a set of
finite measure to an `L¹`-function. -/
lemma abs_le_one_add_sq (a : ℝ) : |a| ≤ 1 + a ^ 2 := by
  nlinarith [sq_nonneg (|a| - 1), sq_abs a, abs_nonneg a]

/-- **Local integrability from a weighted square bound.**  If `ρ` is continuous and positive on
the open quadrant `Q0`, `u` is a.e. strongly measurable on `Q0` and `u²ρ²` is integrable on
`Q0`, then `u` is locally integrable on `Q0` with respect to Lebesgue measure.

Note that no lower bound on `ρ` near the boundary of `Q0` is assumed: the argument is purely
local and works on a compact piece of `Q0`. -/
theorem locallyIntegrableOn_of_integrableOn_sq_mul_sq {ρ : ℝ → ℝ → ℝ} {u : ℝ × ℝ → ℝ}
    (hρpos : ∀ p ∈ Work.FTS.EllipticEst.Q0, 0 < ρ p.1 p.2)
    (hρcont : ContinuousOn (Function.uncurry ρ) Work.FTS.EllipticEst.Q0)
    (hum : AEStronglyMeasurable u (volume.restrict Work.FTS.EllipticEst.Q0))
    (hu : IntegrableOn (fun p : ℝ × ℝ => (u p) ^ 2 * (ρ p.1 p.2) ^ 2)
      Work.FTS.EllipticEst.Q0) :
    LocallyIntegrableOn u Work.FTS.EllipticEst.Q0 volume := by
  intro x hx
  -- A small closed ball around `x`, entirely inside the open quadrant.
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp Work.FTS.EllipticEst.isOpen_Q0 x hx
  set r : ℝ := ε / 2 with hrdef
  have hrpos : 0 < r := by rw [hrdef]; linarith
  set K : Set (ℝ × ℝ) := Metric.closedBall x r with hKdef
  have hKsub : K ⊆ Work.FTS.EllipticEst.Q0 := by
    rw [hKdef]
    intro p hp
    refine hball ?_
    have hp' : dist p x ≤ r := by simpa only [Metric.mem_closedBall] using hp
    rw [Metric.mem_ball]
    have : dist p x < ε := by rw [hrdef] at hp'; linarith
    exact this
  have hKc : IsCompact K := by rw [hKdef]; exact isCompact_closedBall x r
  have hKne : K.Nonempty := by
    rw [hKdef]; exact Metric.nonempty_closedBall.mpr hrpos.le
  have hKmeas : MeasurableSet K := hKc.isClosed.measurableSet
  -- `ρ` attains a positive minimum `m` on the compact set `K`.
  have hρcontK : ContinuousOn (fun p : ℝ × ℝ => ρ p.1 p.2) K := hρcont.mono hKsub
  obtain ⟨p₀, hp₀K, hp₀min⟩ := hKc.exists_isMinOn hKne hρcontK
  set m : ℝ := ρ p₀.1 p₀.2 with hmdef
  have hmpos : 0 < m := hρpos p₀ (hKsub hp₀K)
  have hρge : ∀ p ∈ K, m ≤ ρ p.1 p.2 := fun p hp => hp₀min hp
  have hKmem : K ∈ 𝓝[Work.FTS.EllipticEst.Q0] x := by
    rw [hKdef]
    exact (Filter.le_def.mp nhdsWithin_le_nhds) _ (Metric.closedBall_mem_nhds x hrpos)
  refine ⟨K, hKmem, ?_⟩
  -- `u²ρ² ∈ L¹(K)`
  have hKint : IntegrableOn (fun p : ℝ × ℝ => (u p) ^ 2 * (ρ p.1 p.2) ^ 2) K :=
    hu.mono_set hKsub
  have hdom : Integrable (fun p : ℝ × ℝ => (u p) ^ 2 * (ρ p.1 p.2) ^ 2 / m ^ 2)
      (volume.restrict K) := hKint.div_const _
  -- hence `u² ∈ L¹(K)`, since `ρ ≥ m > 0` on `K`
  have hu2 : Integrable (fun p : ℝ × ℝ => (u p) ^ 2) (volume.restrict K) := by
    refine hdom.mono' ((hum.mono_measure ?_).pow 2) ?_
    · exact Measure.restrict_mono hKsub le_rfl
    · rw [ae_restrict_iff' hKmeas]
      refine Eventually.of_forall fun p hp => ?_
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      have h1 : m ^ 2 ≤ (ρ p.1 p.2) ^ 2 := by nlinarith [hρge p hp, hmpos]
      rw [le_div_iff₀ (by positivity)]
      exact mul_le_mul_of_nonneg_left h1 (sq_nonneg (u p))
  -- on the finite measure set `K`, `L² ⊆ L¹` via `|u| ≤ 1 + u²`
  have hfin : IsFiniteMeasure (volume.restrict K) :=
    isFiniteMeasure_restrict.mpr hKc.measure_lt_top.ne
  have hone : Integrable (fun _ : ℝ × ℝ => (1 : ℝ)) (volume.restrict K) :=
    (integrable_const_iff (c := (1 : ℝ))).mpr (Or.inr hfin)
  have hbdd : Integrable (fun p : ℝ × ℝ => 1 + (u p) ^ 2) (volume.restrict K) :=
    hone.add hu2
  refine hbdd.mono' (hum.mono_measure (Measure.restrict_mono hKsub le_rfl)) ?_
  refine Eventually.of_forall fun p => ?_
  rw [Real.norm_eq_abs]
  exact abs_le_one_add_sq (u p)

/-- **The requested statement.**  On the open quadrant `Q0`, a function `u` with integrable
weighted square `u²ρ²` (`ρ` continuous and positive on `Q0`) differs from a continuous function
`v` by a locally integrable function. -/
theorem locallyIntegrableOn_sub {ρ : ℝ → ℝ → ℝ}
    (hρpos : ∀ p ∈ Work.FTS.EllipticEst.Q0, 0 < ρ p.1 p.2)
    (hρcont : ContinuousOn (Function.uncurry ρ) Work.FTS.EllipticEst.Q0)
    {u v : ℝ × ℝ → ℝ}
    (hum : AEStronglyMeasurable u (volume.restrict Work.FTS.EllipticEst.Q0))
    (hu : IntegrableOn (fun p : ℝ × ℝ => (u p) ^ 2 * (ρ p.1 p.2) ^ 2)
      Work.FTS.EllipticEst.Q0)
    (hv : ContinuousOn v Work.FTS.EllipticEst.Q0) :
    LocallyIntegrableOn (fun p : ℝ × ℝ => u p - v p) Work.FTS.EllipticEst.Q0
      (volume.restrict Work.FTS.EllipticEst.Q0) := by
  have hu_loc : LocallyIntegrableOn u Work.FTS.EllipticEst.Q0
      (volume.restrict Work.FTS.EllipticEst.Q0) :=
    (locallyIntegrableOn_of_integrableOn_sq_mul_sq hρpos hρcont hum hu).mono_measure
      Measure.restrict_le_self
  have hv_loc : LocallyIntegrableOn v Work.FTS.EllipticEst.Q0
      (volume.restrict Work.FTS.EllipticEst.Q0) :=
    ContinuousOn.locallyIntegrableOn hv Work.FTS.EllipticEst.isOpen_Q0.measurableSet
  exact hu_loc.sub hv_loc

end Work.FTS.PhiStar.Honesty.SlotsLimit.WeightedLimitAux
