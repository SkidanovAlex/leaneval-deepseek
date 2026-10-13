/-
# `Work.FTS.PhiStar.Honesty.IoiTool` — two tools for the far-field half-line `(1,∞)`

Two measure-theoretic tools used by the far-field (`z → ∞`) half of the weighted `L²`-honesty of
the radial Green function `Work.FTS.PhiStar.Radial.radGreen`:

* `integrableOn_abs_mul_rpow_of_sq` — `∫_1^∞ |c t| t^{-p-1} dt < ∞` whenever `∫_1^∞ c² < ∞` and
  `p > -1/2` (pointwise AM–GM plus `∫_1^∞ t^{-2p-2} < ∞`).  This is the hypothesis `hinf` that all
  the `radGreen` differentiability lemmas of `Work.FTS.EllExist.Honesty` ask for.

* `integrableOn_Ioi_one_of_interval_bounds` — if a **nonnegative** function on `(1,∞)` is
  integrable on each `(1, n+1]` with uniformly bounded integrals `∫_{(1,n+1]} f ≤ T`, then it is
  integrable on `(1,∞)` with `∫_1^∞ f ≤ T`.  This is the standard "improper integral of a
  nonnegative function is the supremum of its compact-interval integrals" statement, proved by
  exhausting `(1,∞)` with the intervals `(1, n+1]` and applying `MeasureTheory.AECover`.  It is the
  exact analogue of `Work.FTS.EllExist.Honesty.integrableOn_Ioo_of_bounded_intervalIntegrals`
  ((0,1) version) and of `Work.FTS.ClassC.RopGen.PZB.integrableOn_Ioi_of_interval_bounds`
  ((0,∞) version), and it is what turns the energy-identity estimates `∫_1^y G² ≤ C` for the two
  Green pieces `G1`, `G2` of `radGreen` into integrability of `(G1)² w²` and `(G2)² w²` on `(1,∞)`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open MeasureTheory Set Filter
open scoped Topology

namespace Work.FTS.PhiStar.Honesty

/-- **`c² ∈ L¹(1,∞)` ⟹ `|c| t^{-p-1} ∈ L¹(1,∞)`** for `p > -1/2`.

Pointwise, `|c t| · t^{-p-1} ≤ ((c t)² + t^{-2p-2})/2` (AM–GM), and `∫_1^∞ t^{-2p-2} < ∞` because
`-2p - 2 < -1`.  This supplies the hypothesis `hinf` of the `radGreen` differentiability lemmas
(`G2_hasDerivAt`, `radPsi_hasDerivAt`, ...) from a plain `L²` far-field hypothesis on `c`. -/
theorem integrableOn_abs_mul_rpow_of_sq {p : ℝ} (hp : -1 / 2 < p) {c : ℝ → ℝ}
    (hc : ContinuousOn c (Set.Ioi 1))
    (hfar : MeasureTheory.IntegrableOn (fun t : ℝ => (c t) ^ 2) (Set.Ioi 1)) :
    MeasureTheory.IntegrableOn (fun t : ℝ => |c t| * t ^ (-p - 1)) (Set.Ioi 1) := by
  have hexp : -2 * p - 2 < -1 := by linarith
  have hdom : MeasureTheory.IntegrableOn
      (fun t : ℝ => 1 / 2 * (c t) ^ 2 + 1 / 2 * t ^ (-2 * p - 2)) (Set.Ioi 1) :=
    (hfar.const_mul (1 / 2)).add
      ((integrableOn_Ioi_rpow_of_lt hexp one_pos).const_mul (1 / 2))
  have hcont : ContinuousOn (fun t : ℝ => |c t| * t ^ (-p - 1)) (Set.Ioi 1) :=
    hc.abs.mul (continuous_id.continuousOn.rpow_const
      (fun t ht => Or.inl (ne_of_gt (lt_trans one_pos ht))))
  have hmeas : AEStronglyMeasurable (fun t : ℝ => |c t| * t ^ (-p - 1))
      (volume.restrict (Set.Ioi 1)) :=
    hcont.aestronglyMeasurable measurableSet_Ioi
  refine Integrable.mono' hdom hmeas ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht0 : 0 < t := lt_trans one_pos ht
  have h1 : 0 ≤ t ^ (-p - 1) := Real.rpow_nonneg ht0.le _
  have h2 : (t ^ (-p - 1)) ^ 2 = t ^ (-2 * p - 2) := by
    rw [sq, ← Real.rpow_add ht0]
    congr 1
    ring
  have h3 : |c t| * t ^ (-p - 1) ≤ (|c t| ^ 2 + (t ^ (-p - 1)) ^ 2) / 2 := by
    nlinarith [sq_nonneg (|c t| - t ^ (-p - 1))]
  rw [Real.norm_eq_abs, abs_mul, abs_abs, abs_of_nonneg h1]
  calc |c t| * t ^ (-p - 1) ≤ (|c t| ^ 2 + (t ^ (-p - 1)) ^ 2) / 2 := h3
    _ = 1 / 2 * (c t) ^ 2 + 1 / 2 * t ^ (-2 * p - 2) := by
        rw [h2, sq_abs]
        ring

/-- **Uniform interval bounds on `(1,∞)` give integrability.**

If `f` is nonnegative on `(1,∞)`, integrable on each `(1, n+1]`, and `∫_{(1,n+1]} f ≤ T` for every
`n`, then `f` is integrable on `(1,∞)` and `∫_1^∞ f ≤ T`.

The exhausting family is `s n = (1, n+1]`, which covers `(1,∞)` almost everywhere; the bound on the
partial integrals yields integrability via
`MeasureTheory.AECover.integrable_of_integral_bounded_of_nonneg_ae`, and then
`MeasureTheory.AECover.integral_tendsto_of_countably_generated` upgrades the bound on each partial
integral to the bound on the whole integral. -/
theorem integrableOn_Ioi_one_of_interval_bounds {f : ℝ → ℝ} {T : ℝ}
    (hfnn : ∀ z, 1 < z → 0 ≤ f z)
    (hfi : ∀ i : ℕ, MeasureTheory.IntegrableOn f (Set.Ioc (1 : ℝ) ((i : ℝ) + 1)))
    (hb : ∀ i : ℕ, (∫ z in Set.Ioc (1 : ℝ) ((i : ℝ) + 1), f z) ≤ T) :
    MeasureTheory.IntegrableOn f (Set.Ioi 1) ∧ (∫ z in Set.Ioi 1, f z) ≤ T := by
  have hsub : ∀ i : ℕ, Set.Ioc (1 : ℝ) ((i : ℝ) + 1) ⊆ Set.Ioi (1 : ℝ) :=
    fun i => Set.Ioc_subset_Ioi_self
  -- the exhausting family `(1, n+1]` of `(1,∞)`
  have hmem : ∀ᵐ z ∂volume, z ∈ Set.Ioi (1 : ℝ) →
      ∀ᶠ i : ℕ in atTop, z ∈ Set.Ioc (1 : ℝ) ((i : ℝ) + 1) := by
    refine ae_of_all volume fun z hz => ?_
    have htend : Tendsto (fun i : ℕ => ((i : ℝ) + 1)) atTop atTop :=
      tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop
    filter_upwards [htend.eventually (eventually_ge_atTop z)] with i hi
    exact ⟨hz, hi⟩
  have hcov : AECover (volume.restrict (Set.Ioi (1 : ℝ))) atTop
      (fun i : ℕ => Set.Ioc (1 : ℝ) ((i : ℝ) + 1)) :=
    aecover_restrict_of_ae_imp measurableSet_Ioi hmem fun _ => measurableSet_Ioc
  have hfi' : ∀ i : ℕ, IntegrableOn f (Set.Ioc (1 : ℝ) ((i : ℝ) + 1))
      (volume.restrict (Set.Ioi (1 : ℝ))) :=
    fun i => (hfi i).restrict
  have hnng : ∀ᵐ z ∂(volume.restrict (Set.Ioi (1 : ℝ))), 0 ≤ f z :=
    (ae_restrict_mem (s := Set.Ioi (1 : ℝ)) measurableSet_Ioi).mono fun z hz => hfnn z hz
  have hbounded : ∀ᶠ i : ℕ in atTop,
      (∫ z in Set.Ioc (1 : ℝ) ((i : ℝ) + 1), f z
        ∂(volume.restrict (Set.Ioi (1 : ℝ)))) ≤ T := by
    refine Eventually.of_forall fun i => ?_
    rw [Measure.restrict_restrict_of_subset (hsub i)]
    exact hb i
  have hInt : IntegrableOn f (Set.Ioi (1 : ℝ)) :=
    hcov.integrable_of_integral_bounded_of_nonneg_ae T hfi' hnng hbounded
  refine ⟨hInt, ?_⟩
  have htend := hcov.integral_tendsto_of_countably_generated hInt
  exact le_of_tendsto htend hbounded

end Work.FTS.PhiStar.Honesty
