import Mathlib
import Submission.Work.Drive.sideGermDefs
import Submission.Work.Drive.sideGerm_good_exists
import Submission.Work.Drive.sideGerm_parity_eq_of_close_loop
import Submission.Work.Drive.chartIsSmooth
import Submission.Work.Drive.parityCore_of_dense_count

/-!
# The germ route with the **loop-vs-plane** disjointness

`Submission/Work/Drive/sideGerm.lean` states the germ route of the wall (`ParityCore γ`) with the
hypothesis

> `hdisj : Disjoint (chartDisk Q) (rotCapping w '' chartDisk Q)`  (disk vs disk),

which is **not** a consequence of `w ∈ Zc γ` (the `cap ∩ w·cap` piece is a genuine condition on the
chart's cap — `SIDEGERM_SETTLEMENT.md` §1bis).  The minimal hypothesis under which the parity argument
runs is the *loop-vs-plane* form, which the chart lane supplies from `Zc γ`
(`Work.Drive.disjoint_range_coreLoop_rotCapping_chartDisk`,
`Submission/Work/Drive/coreLoop_disjoint_rotCapping.lean`), and the `havoid` clause has been proved in
that form (`Work.Drive.germHavoid_loop`, `Work.Drive.germHavoid_of_Zc`).

This file provides the three statements of `sideGerm.lean` in the loop form, so that the route can be
instantiated:

* **`Work.Drive.sideGerm_spec_loop`** — the germ value is locally constant in the angle, from the
  loop-vs-plane disjointness;
* **`Work.Drive.sideGerm_hn4_loop`** — its `hn4`-shaped corollary;
* **`Work.Drive.parityCore_of_sideGerm_loop`** — the wall from `hn2` and the dense functional identity;
* **`Work.Drive.parityCore_of_isPlaneChart`** — the same with the disjointness **discharged**: from an
  `IsPlaneChart` of an injective nonvanishing curve, the perturbation data, the level bound and the two
  counting clauses alone.  This is the form in which the counting lane should consume the wall.

Everything is `sorry`-free; the axiom audit is `Submission/Work/Drive/_s46/ax6.lean`.
-/

namespace Work.Drive

open Manifold Filter Set
open scoped Manifold ContDiff Topology

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace Work.Drive.projCharted

noncomputable section

/-- **The germ value is locally constant in the angle**, with the loop-vs-plane disjointness (the
minimal hypothesis of the parity argument). -/
theorem sideGerm_spec_loop {m : ℕ}
    (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace) (Q : ℂ → CappingSpace) (c : ℝ)
    (hΞ : ChartPert Q m Ξ) (hQ : IsChartData Q) (hc : 0 < c)
    (hcbot : ∀ p ∈ chartDisk Q, c < levelOf p)
    {w : UnitAddCircle}
    (hloop : Disjoint (Set.range (coreLoop Q)) (rotCapping w '' chartDisk Q)) :
    ∀ᶠ w' in 𝓝 w, sideGerm Ξ Q c w' = sideGerm Ξ Q c w :=
  sideGerm_localconst_of_exists_and_parity Ξ Q c w
    (fun w' => sideGerm_good_exists Ξ Q c hΞ (show IsSmoothChart Q from hQ.1) hc w')
    (sideGerm_parity_eq_of_close_loop Ξ Q c hΞ hQ hc hcbot w hloop)

/-- **`hn4` for the germ side value**, with the loop-vs-plane disjointness. -/
theorem sideGerm_hn4_loop {γ : Circle → ℝ × ℝ} {m : ℕ}
    (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace) (Q : ℂ → CappingSpace) (c : ℝ)
    (hΞ : ChartPert Q m Ξ) (hQ : IsChartData Q) (hc : 0 < c)
    (hcbot : ∀ p ∈ chartDisk Q, c < levelOf p)
    (hloop : ∀ x : Zc γ, Disjoint (Set.range (coreLoop Q))
      (rotCapping (x : UnitAddCircle) '' chartDisk Q)) :
    ∀ x : Zc γ, ∀ᶠ y : Zc γ in 𝓝 x,
      sideGerm Ξ Q c (y : UnitAddCircle) = sideGerm Ξ Q c (x : UnitAddCircle) := by
  intro x
  rw [nhds_subtype, Filter.eventually_comap]
  filter_upwards [sideGerm_spec_loop Ξ Q c hΞ hQ hc hcbot (hloop x)] with w hw a ha
  rw [ha]
  exact hw

/-- **The wall from the germ side value**, with the loop-vs-plane disjointness. -/
theorem parityCore_of_sideGerm_loop {γ : Circle → ℝ × ℝ}
    (hγ : IsSmoothEmbedding (𝓡 1) 𝓘(ℝ, ℝ × ℝ) ∞ γ) {m : ℕ}
    (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace) (Q : ℂ → CappingSpace) (c : ℝ)
    (hΞ : ChartPert Q m Ξ)
    (hQ : IsChartData Q) (hc : 0 < c) (hcbot : ∀ p ∈ chartDisk Q, c < levelOf p)
    (hloop : ∀ x : Zc γ, Disjoint (Set.range (coreLoop Q))
      (rotCapping (x : UnitAddCircle) '' chartDisk Q))
    (hn2 : ∀ u v : UnitAddCircle, v - u ∈ Zc γ →
      sideGerm Ξ Q c (v - u) + sideGerm Ξ Q c (u - v) = 1)
    (hdense : ∀ a c' : UnitAddCircle, a ∈ Zc γ → c' ∈ Zc γ → a + c' ∈ Zc γ →
      (a, c') ∈ closure {q : UnitAddCircle × UnitAddCircle |
        q.1 ∈ Zc γ ∧ q.2 ∈ Zc γ ∧ q.1 + q.2 ∈ Zc γ ∧
          sideGerm Ξ Q c q.1 * sideGerm Ξ Q c (q.1 + q.2)
            + sideGerm Ξ Q c (-q.1) * sideGerm Ξ Q c q.2
            + sideGerm Ξ Q c (-(q.1 + q.2)) * sideGerm Ξ Q c (-q.2) = 1}) :
    ParityCore γ := by
  refine parityCore_of_countOnZc_dense (γ := γ) hγ (fun u v => sideGerm Ξ Q c (v - u))
    (fun u v => by simp) ?_ ?_ ?_
  · intro u v hv
    simpa using hn2 u v hv
  · intro x
    simpa using sideGerm_hn4_loop Ξ Q c hΞ hQ hc hcbot hloop x
  · intro a c' ha hc' hac
    simpa using hdense a c' ha hc' hac

/-- **The wall from an `IsPlaneChart`, with the disjointness discharged.**  The germ route's two
counting clauses (`hn2`, `hdense`), the perturbation data, the level bound and the plane chart of an
injective nonvanishing closed curve are enough: the disjointness hypothesis `hdisj` of
`Work.Drive.parityCore_of_sideGerm` is *not* needed in the loop form, because the chart lane derives it
from `Zc γ`. -/
theorem parityCore_of_isPlaneChart {γ : Circle → ℝ × ℝ}
    (hγ : IsSmoothEmbedding (𝓡 1) 𝓘(ℝ, ℝ × ℝ) ∞ γ) {hγne : ∀ x : Circle, γ x ≠ 0}
    {Q : ℂ → CappingSpace} (hQ : IsPlaneChart γ hγne Q) {m : ℕ}
    (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace) (c : ℝ)
    (hΞ : ChartPert Q m Ξ) (hc : 0 < c) (hcbot : ∀ p ∈ chartDisk Q, c < levelOf p)
    (hn2 : ∀ u v : UnitAddCircle, v - u ∈ Zc γ →
      sideGerm Ξ Q c (v - u) + sideGerm Ξ Q c (u - v) = 1)
    (hdense : ∀ a c' : UnitAddCircle, a ∈ Zc γ → c' ∈ Zc γ → a + c' ∈ Zc γ →
      (a, c') ∈ closure {q : UnitAddCircle × UnitAddCircle |
        q.1 ∈ Zc γ ∧ q.2 ∈ Zc γ ∧ q.1 + q.2 ∈ Zc γ ∧
          sideGerm Ξ Q c q.1 * sideGerm Ξ Q c (q.1 + q.2)
            + sideGerm Ξ Q c (-q.1) * sideGerm Ξ Q c q.2
            + sideGerm Ξ Q c (-(q.1 + q.2)) * sideGerm Ξ Q c (-q.2) = 1}) :
    ParityCore γ :=
  parityCore_of_sideGerm_loop hγ Ξ Q c hΞ (IsChartData_of_isPlaneChart hQ) hc hcbot
    (fun x => disjoint_range_coreLoop_rotCapping_chartDisk hγne
      (fun a b hab => hγ.isEmbedding.injective hab) hQ x.2)
    hn2 hdense

end

end Work.Drive
