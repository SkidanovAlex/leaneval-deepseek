import Mathlib
import Submission.Work.Drive.sideGermDefs
import Submission.Work.Drive.parityCore_of_dense_count
import Submission.Work.Drive.sideGerm_good_exists
import Submission.Work.Drive.sideGerm_parity_eq_of_close
import Submission.Work.Drive.chartIsSmooth

/-!
# The germ side value `sideGerm`: the interface statements

The definitions (`chartDisk`, `IsSmoothChart`, `ChartPert`, `GoodPair`, `GoodAt`, `CntAt`, `sideGerm`)
and the germ bookkeeping live in `Submission/Work/Drive/sideGermDefs.lean` (sorry-free, so that
colleagues can import them without tainting).  This file contains the statements that are the route's
obligations:

* **`Work.Drive.sideGerm_spec`** — the item (a) of the lead's 14:15 message: for `w` at which the two
  capped planes are disjoint (and the truncation level admissible), the germ value is locally constant
  in the angle.  This is the `hn4` of the germ route.
* `Work.Drive.sideGerm_hn4` — its pointwise-`∀ᶠ` corollary on `Zc γ`.
* `Work.Drive.parityCore_of_sideGerm` — the wall-level glue: `hn2` and `hdense` for the germ count give
  `ParityCore γ` (via the proved `Work.Drive.parityCore_of_countOnZc_dense`).

## The settlement of §7 of `GEOMETRIC_LOCALITY_STATUS.md`

§7 left open whether the hypothesis `hdisj` (the two *capped planes* `chartDisk Q` and its rotation are
disjoint) is the right one, or whether one must instead assume the positive separation of the core loop
from the *whole sweep's image*.  **`hdisj` is the right hypothesis.**  The reason is that the two
phenomena are different:

* the sweep's image is the *cone* over the rotated plane, `clampedSweep c ψ P '' unitBox 2 = {p : ∃ y,
  class p = class (P y) ∧ c ≤ level p ≤ level (P y)}` (`Work.Drive.image_clampedSweep`), i.e. a
  *`3`-dimensional* set, whereas the rotated plane is the *`2`-dimensional* set `rotCapping w ''
  chartDisk Q`.  A meet of the loop with the sweep therefore occurs where the loop's class lies in the
  rotated plane **and** the loop's level is below the rotated plane's level there; the meet is
  *interior* in the radial coordinate of the sweep exactly when the level inequality is *strict*.  So
  the sweep's image is **not** contained in the rotated plane, and the meets are the intended ones —
  assuming the positive separation of the loop from the *whole* sweep's image would make the loop
  disjoint from the sweep, the count identically `0` and the germ vacuous;
* what `hdisj` does supply is precisely the avoidance of the **top face** of the sweep (`x 2 = 1`,
  i.e. the plane itself), because the loop lies in `chartDisk (Ξ t.1 ∘ Q)` and the top face of the
  sweep lies in the *rotated* disk `rotCapping w '' chartDisk (Ξ t.2 ∘ Q)`; by
  `Work.Drive.chartDisk_compact` the separation is positive, and by the smoothness of `Ξ` in the
  parameter the perturbed disks stay at positive distance.  The **bottom face** (`x 2 = 0`, the level
  `c`) is avoided by `hcbot` (the loop's levels are strictly above `c`).  These two exclusions are
  exactly the hypothesis `havoid` of the L6 family engine `Work.Drive.odd_coreSideCount_iff_of_famRegular_gen`
  (and of `Work.Drive.eventually_ncard_meetBox_eq`'s interiority clause in the radial coordinate);
* the *seam* faces (`x 0 ∈ {0,1}`, `x 1 ∈ {0,1}`) of the chain are a *genericity* condition, not a
  consequence of `hdisj`: they are excluded by the `GoodPair` guard (a meet on the seam is never
  transverse — the folded presentation `sqDisk ∘ foldBox` is singular there, so the sweep's
  differential has rank `≤ 2`), and the parametric Sard supplies parameters at which no meet is on the
  seam.  Likewise the *loop's* seam (`s ∈ {0,1}`) is excluded by the same Sard.

**The seam clause (a defect caught by the review/prover gate of this session).**  The route's chart
must satisfy the **seam clause** `∀ z, ‖z‖ = 1 → Q (-z) = Q z`, not merely smoothness: it is exactly
the statement that the core loop `Q ∘ (t ↦ exp (iπt))` is **closed**, and it gives the
`seamInv`-invariance of the chain presentation (`diskPlane_seamInv2`).  Both are inputs of the L6
family engine that computes the parity of the loop-vs-sweep count over `[0,1] × unitBox 2`; without the
closure a meet can leave the box through the *loop's* seam faces `a ∈ {0,1}` (which the box
parameterisation does not identify), and the parity of the count jumps between two good configurations.
A prover of the fleet proved the parity-locality statement *false* on smooth charts alone for this
reason.  The route therefore carries `Work.Drive.IsChartData Q` (smoothness **and** the seam clause,
`sideGermDefs.lean`), which is an immediate consequence of the chart lane's `IsPlaneChart`
(`Work.Drive.IsChartData_of_isPlaneChart`, `Submission/Work/Drive/chartIsSmooth.lean`), together with
`Work.Drive.IsChartData.coreLoop_zero_eq_one` for the loop's closure.

**The two remaining obligations of `sideGerm_spec`, in the exact form the proof needs (delegated).**

Both were read and approved by two mathematicians of the review gate, and are being proved in parallel
at `Submission/Work/Drive/sideGerm_good_exists.lean` and
`Submission/Work/Drive/sideGerm_parity_eq_of_close.lean`:

1. **`Work.Drive.sideGerm_good_exists`** (the *Sard existence*): for every angle `w`,
   `∃ᶠ t in 𝓝 0, GoodAt Ξ Q c w t`.  Content: the parametric Sard on the box `[0,1] × unitBox 2` for the
   charted difference system of the core loop and the clamped sweep (a square system: `4` parameters,
   `4` equations in the `4`-manifold `CappingSpace`), the parameter-derivative being onto at every zero
   because `t.1`, `t.2` are independently perturbed.  Bricks on disk:
   `Work.Drive.exists_forall_good_square_on_compact_ball` (`genericRegularizationSquare.lean`),
   `Work.Drive.avoid_zeroSet_open` (`avoid_zeroSet_open.lean`, for the box-boundary faces);
   `Work.Drive.classTripleAssembly` is the worked example.
2. **`Work.Drive.sideGerm_parity_eq_of_close`** (the *parity locality*): at `w` (with `hdisj`, `hcbot`)
   there are `ε, δ > 0` such that any two good configurations of norm `< ε` at angles within `δ` of `w`
   have the same count parity.  Content: at a `GoodPair` the box count is the parameterisation-free
   mod-2 pairing of the loop with the sweep's image (`HN4_SEAM_DEFECT.md` §1); `hdisj` gives the
   *top-face* margin and `hcbot` the *bottom-face* margin, so the loop never meets the swept plane
   during the deformation, and the parity is constant along the good paths produced by the same
   parametric Sard, by the L6 family engine `Work.Drive.odd_coreSideCount_iff_of_famRegular_gen`, the
   ends being moved by the local constancy `Work.Drive.eventually_ncard_meetBox_eq`.

**The assembly** is already proved, in `sideGermDefs.lean`:

> `Work.Drive.sideGerm_localconst_of_exists_and_parity` : (1) for every angle + (2) at the centre `w`
> ⟹ `∀ᶠ w' in 𝓝 w, sideGerm Ξ Q c w' = sideGerm Ξ Q c w`.

So `sideGerm_spec` below is, once the two children land, the three-line instantiation
`sideGerm_localconst_of_exists_and_parity Ξ Q c w (fun w' => sideGerm_good_exists … w') hC` (there is
no circularity: both child files import `sideGermDefs.lean` only).  The proof plan of the whole route,
the settlement of the open question of `GEOMETRIC_LOCALITY_STATUS.md` §7 (the hypothesis `hdisj` is the
right one and is *not* vacuous: the sweep's image is the *cone* over the rotated plane, not the rotated
plane, so the meets are genuine), the strengthening of `ChartPert`'s set argument and the signature
agreement with H4 are recorded in **`Submission/Work/Drive/SIDEGERM_SETTLEMENT.md`**.

**The hypothesis `hcbot` is discharged**: for a continuous chart `Q`,
`Work.Drive.exists_level_lt_chartDisk` (`Submission/Work/Drive/chartLevelBound.lean`) produces `c > 0`
with `c < levelOf p` for every `p ∈ chartDisk Q`, so `hcbot` is not an obstruction.
-/

namespace Work.Drive

open Manifold Filter
open scoped Manifold ContDiff Topology

attribute [local instance] Work.Drive.cappingCharted Work.Drive.isManifold_cappingCharted
  Work.Drive.t2Space_cappingSpace Work.Drive.projCharted

noncomputable section

/-- **The germ value is locally constant in the angle** (the lead's item (a)).  For a non-collision
angle `w` — more precisely, for an angle at which the two **capped planes** `Q '' closedBall 0 1` and
its rotation are **disjoint** — the parity of the count of every `GoodPair` chart perturbation near `0`
is the same on a neighbourhood of `w`, and equals `sideGerm Ξ Q c w'` for `w'` in that neighbourhood.

**Note on the hypothesis `hdisj` (the settlement of §7 of `GEOMETRIC_LOCALITY_STATUS.md`, recorded in
the module docstring).**  The margin argument (`exists_pos_dist_of_isCompact_disjoint`) needs two
*disjoint compact* sets.  Membership `w ∈ Zc γ` only gives that the two *configuration strips* `M` and
`w · M` are disjoint; the capping adds the cap disks, so the argument has to be run either on the
*capped* planes (the hypothesis `hdisj` below, which is exactly the "caps must be pairwise disjoint from
their rotations" obligation recorded in `ELEMENTARY_ORDER_ROUTE.md` §5–6) or with a separate treatment
of the caps.  Deriving `hdisj` from `w ∈ Zc γ` is the paper's Lemma 3 for this particular family and is
*not* available in the workspace; the statement below takes it as a hypothesis so that the proof is not
circular.  `hdisj` is *not* vacuous: the sweep's image is the cone over the rotated plane, not the
rotated plane itself, so the meets are genuine. -/
theorem sideGerm_spec {m : ℕ}
    (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace) (Q : ℂ → CappingSpace) (c : ℝ)
    (hΞ : ChartPert Q m Ξ)
    (hQ : IsChartData Q)
    {w : UnitAddCircle}
    (hc : 0 < c) (hcbot : ∀ p ∈ chartDisk Q, c < levelOf p)
    (hdisj : Disjoint (chartDisk Q) (rotCapping w '' chartDisk Q)) :
    ∀ᶠ w' in 𝓝 w, sideGerm Ξ Q c w' = sideGerm Ξ Q c w :=
  sideGerm_localconst_of_exists_and_parity Ξ Q c w
    (fun w' => sideGerm_good_exists Ξ Q c hΞ hQ.isSmoothChart hc w')
    (sideGerm_parity_eq_of_close Ξ Q c hΞ hQ hc hcbot w hdisj)

/-- **`hn4` for the germ side value**: it is locally constant as a function of the angle (`ZMod 2`
being discrete, local constancy is continuity), which is the hypothesis `hn4` of
`Work.Drive.parityCore_of_countOnZc_dense`.  The disjointness hypothesis is the one of
`Work.Drive.sideGerm_spec`, cf. the note there. -/
theorem sideGerm_hn4 {γ : Circle → ℝ × ℝ} {m : ℕ}
    (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace) (Q : ℂ → CappingSpace) (c : ℝ)
    (hΞ : ChartPert Q m Ξ)
    (hQ : IsChartData Q) (hc : 0 < c) (hcbot : ∀ p ∈ chartDisk Q, c < levelOf p)
    (hdisj : ∀ x : Zc γ, Disjoint (chartDisk Q) (rotCapping (x : UnitAddCircle) '' chartDisk Q)) :
    ∀ x : Zc γ, ∀ᶠ y : Zc γ in 𝓝 x,
      sideGerm Ξ Q c (y : UnitAddCircle) = sideGerm Ξ Q c (x : UnitAddCircle) := by
  intro x
  rw [nhds_subtype, Filter.eventually_comap]
  filter_upwards [sideGerm_spec Ξ Q c hΞ hQ hc hcbot (hdisj x)] with w hw a ha
  rw [ha]
  exact hw

/-- **The wall from the germ side value** (the lead's item (d)).  With `n 0 u := sideGerm Ξ Q c u`
(the translation invariance `hn1` is definitional, as in `Work.Drive.parityCore_of_designCount`), the
wall `ParityCore γ` follows from the antisymmetry `hn2` and the functional identity on a *dense* set of
triples `hdense` for the germ count — the `hn4` being `Work.Drive.sideGerm_hn4`. -/
theorem parityCore_of_sideGerm {γ : Circle → ℝ × ℝ}
    (hγ : IsSmoothEmbedding (𝓡 1) 𝓘(ℝ, ℝ × ℝ) ∞ γ) {m : ℕ}
    (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace) (Q : ℂ → CappingSpace) (c : ℝ)
    (hΞ : ChartPert Q m Ξ)
    (hQ : IsChartData Q) (hc : 0 < c) (hcbot : ∀ p ∈ chartDisk Q, c < levelOf p)
    (hdisj : ∀ x : Zc γ, Disjoint (chartDisk Q) (rotCapping (x : UnitAddCircle) '' chartDisk Q))
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
    simpa using sideGerm_hn4 Ξ Q c hΞ hQ hc hcbot hdisj x
  · intro a c' ha hc' hac
    simpa using hdense a c' ha hc' hac

/-- **`sideGerm_spec` reduced to the parity-locality input.**  With the Sard existence
`Work.Drive.sideGerm_good_exists` (proved, `Submission/Work/Drive/sideGerm_good_exists.lean`) supplying
its first hypothesis, the local constancy of the germ value at `w` follows from the parity-locality
statement alone — the conclusion of `Drive/sideGerm_parity_eq_of_close` (`hC` below, the second and last
ingredient of the route).  This is the whole content of `sideGerm_spec` minus that one input. -/
theorem sideGerm_localconst_of_parityData {m : ℕ}
    (Ξ : EuclideanSpace ℝ (Fin m) → CappingSpace → CappingSpace) (Q : ℂ → CappingSpace) (c : ℝ)
    (w : UnitAddCircle) (hΞ : ChartPert Q m Ξ) (hQ : IsChartData Q) (hc : 0 < c)
    (hC : ∃ ε δ : ℝ, 0 < ε ∧ 0 < δ ∧
      ∀ (t t' : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) (w' : UnitAddCircle),
        ‖t‖ < ε → ‖t'‖ < ε → dist w' w < δ →
        GoodAt Ξ Q c w t → GoodAt Ξ Q c w' t' →
          Odd (CntAt Ξ Q c w t) = Odd (CntAt Ξ Q c w' t')) :
    ∀ᶠ w' in 𝓝 w, sideGerm Ξ Q c w' = sideGerm Ξ Q c w :=
  sideGerm_localconst_of_exists_and_parity Ξ Q c w
    (fun w' => sideGerm_good_exists Ξ Q c hΞ hQ.isSmoothChart hc w')
    hC

/-- **The core loop's image lies in the chart's disk** (`coreLoop Q t = Q (exp (i π t))` and
`‖exp (i π t)‖ = 1`), so the *disk* disjointness `hdisj` of `Work.Drive.sideGerm_spec` implies the
*loop* disjointness which is the minimal hypothesis of the parity argument
(`Work.Drive.sideGerm_spec_loop`). -/
lemma coreLoop_mem_chartDisk (Q : ℂ → CappingSpace) :
    Set.range (coreLoop Q) ⊆ chartDisk Q := by
  rintro p ⟨t, rfl⟩
  refine ⟨Complex.exp (Real.pi * (t : ℂ) * Complex.I), ?_, rfl⟩
  rw [Metric.mem_closedBall, dist_zero_right, Complex.norm_exp]
  simp

end

end Work.Drive
