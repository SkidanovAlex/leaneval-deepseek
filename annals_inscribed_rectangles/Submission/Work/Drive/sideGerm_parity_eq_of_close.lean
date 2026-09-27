import Mathlib
import Submission.Work.Drive.sideGermDefs
import Submission.Work.Drive.chartIsSmooth
import Submission.Work.Drive.designCountLocalityGen
import Submission.Work.Drive.odd_ncard_famMeet_iff
import Submission.Work.Drive.genericRegularizationSquare
import Submission.Work.Drive.avoid_zeroSet_open
import Submission.Work.Drive.meetBoxEngine
import Submission.Work.Drive.geometricLocality
import Submission.Work.Drive.sideGermFamily
import Submission.Work.Drive.sideGerm_havoid_of_close
import Submission.Work.Drive.famMeet_regular_of_good_family
import Submission.Work.Drive.sideGerm_parity_local
import Submission.Work.Drive.sep_fam_regular

namespace Work.Drive

open Manifold Filter Set
open scoped Manifold ContDiff Topology

set_option maxHeartbeats 4000000

/-! ## SESSION PLAN for `sideGerm_parity_eq_of_close` (HISTORICAL — the node is CLOSED; see the note at the end of this file)

**Status of the statement.**  With the seam clause in the chart data (`IsChartData`) the statement is
mathematically **true**; what is missing is the machinery making the box count `coreSideCount` a
deformation invariant, namely the two halves of the L6 family engine together with the geometric
inputs.  The parity argument, precisely:

* a **joint family** over the five-box `Amb 4 = ℝ^5` (coordinates `p 0` = the path parameter `s`,
  `p 1` = the loop parameter, `p 2, p 3, p 4` = the three sweep parameters) with
  * `hloop` (`F (s,0) = F (s,1)`) — the **chart's seam clause**
    (`Work.Drive.IsChartData.coreLoop_zero_eq_one`),
  * `hseam` — the chain's seam invariance (`Work.Drive.diskPlane_seamInv2`,
    `clampedSweep_seamInv`),
  * `havoid` (**no meet with `p 4 ∈ {0,1}`** — the level `c` and the rotated plane),
  * `htrans` (`FamBox.Lf` surjective at every meet) and `hface` (at boundary meets exactly one face
    coordinate, with a crossing direction);
* then the meet set of the family inside the box is a compact `1`-manifold with boundary (regularity +
  the IFT), whose boundary is the set of *boundary meets*, of even cardinality.  Splitting that count
  by the face coordinate: `p 1 ∈ {0,1}` is paired by the closedness `hloop`
  (`Work.Drive.even_ncard_loopEnd`), `p 2, p 3 ∈ {0,1}` is paired by the seam invariance `hseam`
  (`Work.Drive.seamInv`), `p 4 ∈ {0,1}` is empty by `havoid`, so the remaining part — the meets at
  `p 0 ∈ {0,1}`, i.e. **the two ends of the path** — has even cardinality: *the two ends have the same
  parities of their box counts*.
* This is exactly `Work.Drive.odd_ncard_famMeet_iff` (`FamBox.famMeet_parity_of_even_boxBMeet` plus the
  two face pairings), consumed through `Work.Drive.coreMeet_ncard_eq_famMeet_gen`.

**The analytic inputs (delegated).**

1. `Work.Drive.sideGerm_havoid_of_close` — the two radial faces are avoided *uniformly* on
   `‖a‖ < ε`, `dist w' w < δ`: from `hcbot` (`clampedSweep_face_zero` + `levelOf_shadow`) and `hdisj`
   (`clampedSweep_face_one` + `range_diskPlane`, with the margin from `chartDisk_compact` and
   `chartDisk_disjoint_nhds`).
2. `Work.Drive.famMeet_regular_of_good_family` — the parametric Sard for a **joint** family in which
   the loop's chart moves with the Sard parameter too (the two proved siblings
   `famMeet_transHyp_of_good_family` / `famMeet_faceHyp_of_good_family` treat the fixed-loop case,
   which is *not* enough here: in the germ route both `Ξ a.1 ∘ Q` and `Ξ a.2 ∘ Q` move).
3. The Sard's chart-side hypotheses `hcontain`/`hsurj` for the concrete families
   `Lf t (mk2 s y) := coreLoop (Ξ (σ₁ s + t) ∘ Q) y` and
   `N t (famPt s x) := clampedSweep c (1 - t) (rotPresentation (Ξ (σ₂ s + t) ∘ Q) (ω s)) x`
   (`σ₁, σ₂, ω` the straight paths joining the given configurations' parameters and angles, `t : ℝ^m`
   the Sard shift): `hsurj` is *automatic*, because the `t`-derivative of the charted difference is
   the difference of the two chart-perturbation derivatives and each is onto by
   `Work.Drive.ChartPert` (surjectivity at *every* point of the CappingSpace), transported through
   `chr p` and through the cone map `q ↦ (level c + ρ (levelOf q - c), class q)`, which is a local
   diffeomorphism for `ρ ≠ 0`, i.e. off the radial faces, where `havoid` applies.

**Remaining glue (bookkeeping).**  Choose `K ⊇` the meet sets of the two given configurations and of
every small perturbation of them (a `Work.Drive.eventually_meetBox_cover`-style covering argument) and
one chart `p` containing them; apply the Sard `famMeet_regular_of_good_family` to get `t`; apply
`odd_ncard_famMeet_iff` with `havoid` from (1); identify the two ends with the `CntAt` of the shifted
configurations (`coreMeet_ncard_eq_famMeet_gen`); move the ends back to the given configurations by the
local constancy `Work.Drive.eventually_ncard_meetBox_eq`, whose base hypotheses are exactly the
`GoodPair` clauses of the two `GoodAt` hypotheses.

**The concrete families (design; the definitions to write next).**  For two given configurations
`a = (a.1, a.2)` at angle `w` and `b = (b.1, b.2)` at angle `w'`, and a Sard shift `t : ℝ^m`, put

```
pathL s = (1 - s) • a.1 + s • b.1        pathR s = (1 - s) • a.2 + s • b.2
pathW s = (1 - s) • w  + s • w'         (in UnitAddCircle)
Lf t : ℝ² → CappingSpace,   Lf t (mk2 s y) = coreLoop (Ξ (pathL s + t) ∘ Q) y
N t  : ℝ⁴ → CappingSpace,   N t (famPt s x) =
      clampedSweep c (fun u => 1 - u) (rotPresentation (Ξ (pathR s + t) ∘ Q) (pathW s)) x
```

so that `famLoop (Lf t) = chartLoopFam (fun s z => Ξ (pathL s + t) (Q z))` and
`famChain (N t) = sweepFam c (fun u => 1 - u) (fun s y => rotPresentation (Ξ (pathR s + t) ∘ Q) (pathW s))`.
The two slices of the box are then the shifted configurations: `famMeet (Lf t) (N t) 0` is the meet
set of `(Ξ (a.1+t) ∘ Q, rotPresentation (Ξ (a.2+t) ∘ Q) w)` and `famMeet (Lf t) (N t) 1` that of
`(Ξ (b.1+t) ∘ Q, rotPresentation (Ξ (b.2+t) ∘ Q) w')`; both are identified with
`coreMeet …` by `Work.Drive.coreMeet_ncard_eq_famMeet_gen`, and with `CntAt Ξ Q c w (· + t)` by
unfolding `CntAt`, `pertChart`, `rotPresentation`.

* `hloop` is `Work.Drive.IsChartData.coreLoop_zero_eq_one` (the seam clause);
* `hseam` is `diskPlane_seamInv2` transported through `clampedSweep` (the seam clause is preserved by
  `rotCapping`, hence by `rotPresentation`);
* `havoid` is `Work.Drive.sideGerm_havoid_of_close` (**proved this stretch**) after rewriting the
  `coreLoop`/`clampedSweep` meet into the `famLoop`/`famChain` one;
* `htrans`/`hface` come from `Work.Drive.famMeet_regular_of_good_family`;
* its hypothesis `hsurj` — and the chart containment `hcontain` — are the last analytic brick: the
  `t`-derivative of `FamBox.chartDif p (famLoop (Lf t')) (famChain (N t')) y` is the difference of the
  two chart-perturbation derivatives, each onto by `ChartPert` (surjectivity at *every* point) composed
  with the cone map `q ↦ (level c + ρ (levelOf q - c), class q)`, which is a local diffeomorphism for
  `ρ = 1 - x 2 ≠ 0`, i.e. off the radial faces where `havoid` applies.

**The two transfers, and the last missing engine.**  `Odd (famMeet (Lf t) (N t) 0).ncard)` must be
compared with `Odd (CntAt Ξ Q c w a)` — the Sard shift `t` moves the configuration by `(t, t)`.  Since
the given configuration is `GoodPair`, the count is locally constant in the *two-parameter* family
`t ↦ (Ξ (a.1 + t) ∘ Q, Ξ (a.2 + t) ∘ Q)`: this is the parity form of
`Work.Drive.eventually_ncard_meetBox_eq_fam` (`Submission/Work/Drive/eventually_ncard_meetBox_eq_fam.lean`,
still a `sorry`), which must be proved (or delegated) — with it the two ends collapse onto the two
given good configurations and the statement follows.  -/

/-- **Locality of the side value**: the parity of the count of a good configuration is independent of
the configuration and locally constant in the angle.

(Restated after a prover of the fleet returned the previous version as FALSE: the chart data must carry
the **seam clause** `∀ z, ‖z‖ = 1 → Q (-z) = Q z`, which is what makes the core loop
`Q ∘ (t ↦ exp (iπt))` closed — `Work.Drive.IsChartData.coreLoop_zero_eq_one` — and the chain
presentation `diskPlane Q` seam-invariant — `Work.Drive.diskPlane_seamInv2`.  Without it a meet can
leave the box through the loop's seam faces `a ∈ {0,1}`, which the box parameterisation does not
identify, and the parity jumps.  `Work.Drive.IsChartData Q` is exactly smoothness plus the seam clause,
and is implied by the chart lane's `IsPlaneChart` via `Work.Drive.IsChartData_of_isPlaneChart`.)

Mathematics of the proof (recorded for the prover):
* at a `GoodPair` the box count `coreSideCount` is the parameterisation-free mod-2 pairing of the core
  loop with the sweep's image (`HN4_SEAM_DEFECT.md` §1): the guard `GoodPair` forces every meet to be
  *interior* in the box and *transverse*;
* `hdisj` gives, with `chartDisk_compact` and the openness `chartDisk_disjoint_nhds`, a **positive
  margin** between the loop's disk and the rotated disk; since `Ξ` is jointly smooth with `Ξ 0 = id`,
  for `‖t‖ < ε` the perturbed disks stay in the margin, so the perturbed loop stays **off the rotated
  plane** — the *top face* (`x 2 = 1`) of the sweep; `hcbot` keeps it off the *bottom face*
  (`x 2 = 0`, the level `c`).  These are the `havoid` of the L6 family engine
  `Work.Drive.odd_coreSideCount_iff_of_famRegular_gen`; its `hloop` and `hseam` are the seam clause
  (`IsChartData`), its `htrans`/`hface` come from the parametric Sard;
* joining the two configurations to the centre by good paths produced by that Sard (with the path
  parameter as an extra box coordinate; the same brick as `Drive/sideGerm_good_exists`), the count
  parity is constant along the path by the L6 family engine, and the two ends are moved into the given
  configurations by the local constancy `Work.Drive.eventually_ncard_meetBox_eq`. -/

theorem sideGerm_parity_eq_of_close {m : ℕ}
    (Ξ : EuclideanSpace ℝ (Fin m) → Work.Drive.CappingSpace → Work.Drive.CappingSpace)
    (Q : ℂ → Work.Drive.CappingSpace)
    (c : ℝ) (hΞ : Work.Drive.ChartPert Q m Ξ) (hQ : Work.Drive.IsChartData Q) (hc : 0 < c)
    (hcbot : ∀ p ∈ Work.Drive.chartDisk Q, c < Work.Drive.levelOf p)
    (w : UnitAddCircle)
    (hdisj : Disjoint (Work.Drive.chartDisk Q)
      (Work.Drive.rotCapping w '' Work.Drive.chartDisk Q)) :
    ∃ ε δ : ℝ, 0 < ε ∧ 0 < δ ∧
      ∀ (t t' : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m)) (w' : UnitAddCircle),
        ‖t‖ < ε → ‖t'‖ < ε → dist w' w < δ →
        Work.Drive.GoodAt Ξ Q c w t → Work.Drive.GoodAt Ξ Q c w' t' →
          Odd (Work.Drive.CntAt Ξ Q c w t) = Odd (Work.Drive.CntAt Ξ Q c w' t') := by
  obtain ⟨εh, δh, hεh, hδh, hav⟩ := sideGerm_havoid_of_close Ξ Q c hΞ hQ hc hcbot w hdisj
  refine ⟨εh / 8, δh / 2, by linarith, by linarith, ?_⟩
  intro t t' w' ht ht' hw' hg hg'
  obtain ⟨ρ₁, hρ₁, hloc₁⟩ := sideGerm_parity_local Ξ Q c hΞ hQ w t hg
  obtain ⟨ρ₂, hρ₂, hloc₂⟩ := sideGerm_parity_local Ξ Q c hΞ hQ w' t' hg'
  obtain ⟨tR, t'R, htR, ht'R, hlift⟩ := sep_exists_lift_pair w w'
  set εs : ℝ := min (εh / 16) (min (ρ₁ / 4) (ρ₂ / 4)) with hεsdef
  have hεspos : 0 < εs := by
    rw [hεsdef]
    exact lt_min (by linarith) (lt_min (by linarith) (by linarith))
  have hεs16 : εs ≤ εh / 16 := by rw [hεsdef]; exact min_le_left _ _
  have hεs1 : εs ≤ ρ₁ / 4 := by
    rw [hεsdef]; exact le_trans (min_le_right _ _) (min_le_left _ _)
  have hεs2 : εs ≤ ρ₂ / 4 := by
    rw [hεsdef]; exact le_trans (min_le_right _ _) (min_le_right _ _)
  obtain ⟨τ₁, τ₂, hτ₁, hτ₂, hreg⟩ := sep_fam_regular Ξ Q c hΞ hQ.1 hc t t' tR t'R εs hεspos
  have hτ₁16 : ‖τ₁‖ < εh / 16 := lt_of_lt_of_le hτ₁ hεs16
  have hτ₂16 : ‖τ₂‖ < εh / 16 := lt_of_lt_of_le hτ₂ hεs16
  have hτ₁ρ₁ : ‖τ₁‖ < ρ₁ / 4 := lt_of_lt_of_le hτ₁ hεs1
  have hτ₂ρ₁ : ‖τ₂‖ < ρ₁ / 4 := lt_of_lt_of_le hτ₂ hεs1
  have hτ₁ρ₂ : ‖τ₁‖ < ρ₂ / 4 := lt_of_lt_of_le hτ₁ hεs2
  have hτ₂ρ₂ : ‖τ₂‖ < ρ₂ / 4 := lt_of_lt_of_le hτ₂ hεs2
  -- the three geometric clauses of the engine
  have hloop := sep_hloop Ξ Q hQ t t' τ₁
  have hseam := sep_hseam Ξ Q c tR t'R t t' τ₂ hQ
  have hsmall : ∀ s ∈ Set.Icc (0 : ℝ) 1,
      ‖(sepPathL t t' s + τ₁, sepPathR t t' s + τ₂)‖ < εh := by
    intro s hs
    obtain ⟨hs0, hs1⟩ := Set.mem_Icc.mp hs
    have ht1 : ‖t.1‖ < εh / 8 := lt_of_le_of_lt (norm_fst_le t) ht
    have ht2 : ‖t'.1‖ < εh / 8 := lt_of_le_of_lt (norm_fst_le t') ht'
    have hu1 : ‖t.2‖ < εh / 8 := lt_of_le_of_lt (norm_snd_le t) ht
    have hu2 : ‖t'.2‖ < εh / 8 := lt_of_le_of_lt (norm_snd_le t') ht'
    have e1 : ‖sepPathL t t' s + τ₁‖ < εh := by
      have hnl : ‖sepPathL t t' s‖ ≤ (1 - s) * ‖t.1‖ + s * ‖t'.1‖ := by
        rw [sepPathL]
        refine (norm_add_le _ _).trans ?_
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by linarith),
          abs_of_nonneg hs0]
      have hb : (1 - s) * ‖t.1‖ + s * ‖t'.1‖ ≤ εh / 8 := by nlinarith
      have := norm_add_le (sepPathL t t' s) τ₁
      linarith [hτ₁16]
    have e2 : ‖sepPathR t t' s + τ₂‖ < εh := by
      have hnl : ‖sepPathR t t' s‖ ≤ (1 - s) * ‖t.2‖ + s * ‖t'.2‖ := by
        rw [sepPathR]
        refine (norm_add_le _ _).trans ?_
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (by linarith),
          abs_of_nonneg hs0]
      have hb : (1 - s) * ‖t.2‖ + s * ‖t'.2‖ ≤ εh / 8 := by nlinarith
      have := norm_add_le (sepPathR t t' s) τ₂
      linarith [hτ₂16]
    rw [Prod.norm_def]
    exact max_lt e1 e2
  have hang : ∀ s ∈ Set.Icc (0 : ℝ) 1, dist (sepAngle tR t'R s) w < δh := by
    intro s hs
    have hs0 : (0 : ℝ) ≤ s := (Set.mem_Icc.mp hs).1
    have hs1 : s ≤ 1 := (Set.mem_Icc.mp hs).2
    have hd : sepAngle tR t'R s = (((1 - s) * tR + s * t'R : ℝ) : UnitAddCircle) := rfl
    rw [hd, ← htR]
    have hstep1 : dist (((1 - s) * tR + s * t'R : ℝ) : UnitAddCircle) ((tR : ℝ) : UnitAddCircle)
        ≤ |(1 - s) * tR + s * t'R - tR| := sep_dist_coe_coe_le _ _
    have hstep2 : |(1 - s) * tR + s * t'R - tR| ≤ |tR - t'R| := by
      rw [show (1 - s) * tR + s * t'R - tR = s * (t'R - tR) from by ring, abs_mul,
        abs_of_nonneg hs0, abs_sub_comm tR t'R]
      nlinarith [abs_nonneg (t'R - tR), hs1]
    have habs : |tR - t'R| = dist w' w := by rw [abs_sub_comm]; exact hlift
    calc dist (((1 - s) * tR + s * t'R : ℝ) : UnitAddCircle) ((tR : ℝ) : UnitAddCircle)
        ≤ |(1 - s) * tR + s * t'R - tR| := hstep1
      _ ≤ |tR - t'R| := hstep2
      _ = dist w' w := habs
      _ < δh := by linarith
  have havoid := sep_havoid Ξ Q c tR t'R w t t' τ₁ τ₂ hav hsmall hang
  have hiff := odd_coreSideCount_iff_of_famRegular_gen (sepQfam Ξ Q t t' τ₁) c
    (sepPfam Ξ Q tR t'R t t' τ₂) hreg.hL hreg.hN hloop hseam havoid hreg.htrans hreg.hface
  rw [sepCoreSideCount_zero_eq_CntAt Ξ Q c tR t'R t t' τ₁ τ₂,
    sepCoreSideCount_one_eq_CntAt Ξ Q c tR t'R t t' τ₁ τ₂, htR, ht'R] at hiff
  have hc1 : Odd (CntAt Ξ Q c w (t.1 + τ₁, t.2 + τ₂)) = Odd (CntAt Ξ Q c w t) := by
    have h := hloc₁ ((τ₁, τ₂) : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m))
      (by
        rw [Prod.norm_def]
        exact max_lt (lt_trans hτ₁ρ₁ (by linarith)) (lt_trans hτ₂ρ₁ (by linarith)))
    rw [show t + ((τ₁, τ₂) : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m))
        = (t.1 + τ₁, t.2 + τ₂) from rfl] at h
    exact h
  have hc2 : Odd (CntAt Ξ Q c w' (t'.1 + τ₁, t'.2 + τ₂)) = Odd (CntAt Ξ Q c w' t') := by
    have h := hloc₂ ((τ₁, τ₂) : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m))
      (by
        rw [Prod.norm_def]
        exact max_lt (lt_trans hτ₁ρ₂ (by linarith)) (lt_trans hτ₂ρ₂ (by linarith)))
    rw [show t' + ((τ₁, τ₂) : EuclideanSpace ℝ (Fin m) × EuclideanSpace ℝ (Fin m))
        = (t'.1 + τ₁, t'.2 + τ₂) from rfl] at h
    exact h
  rw [hc1, hc2] at hiff
  exact propext hiff


/-! ## STATE OF THIS NODE: CLOSED (sorry-free, axiom-clean)

`Work.Drive.sideGerm_parity_eq_of_close` is **proved** in this file.  `#print axioms` gives
`[propext, Classical.choice, Quot.sound]`.

**The proof, in the order in which the ingredients are used.**

1. `Work.Drive.sideGerm_havoid_of_close` (own file, proved) — the uniform radial-face avoidance
   `(εh, δh, hav)` from `hcbot` (`clampedSweep_face_zero`, `levelOf_shadow`) and `hdisj`
   (`clampedSweep_face_one`, `range_diskPlane`, `chartDisk_compact`, `chartDisk_disjoint_nhds`).
2. `Work.Drive.sideGerm_parity_local` (own file, proved) — the two local-constancy radii `ρ₁, ρ₂` at
   the two given good configurations.
3. `Work.Drive.sep_exists_lift_pair` (`sideGermSepDefs.lean`) — the angle lifts `tR, t'R` of `w, w'`
   with `|tR - t'R| = dist w' w`, so the interpolated angle stays in the `δh`-ball.
4. **`Work.Drive.sep_fam_regular`** (`sep_fam_regular.lean`, proved) — the parametric-Sard regularity
   `SepRegular Ξ Q c tR t'R t t' τ₁ τ₂` at the shifts
   `εs = min (εh/16) (min (ρ₁/4) (ρ₂/4))`, supplying **all four** engine clauses `hL`, `hN`, `htrans`,
   `hface` at once.  (The route through `Work.Drive.sideGerm_famRegular` also works — it is the same
   statement in `FamBox.Lf` form via `sep_fam_regular_core` — but `sep_fam_regular` additionally
   carries the *smoothness* clauses `hL`/`hN` in exactly the form the engine wants, so no separate
   smoothness obligation is needed.)
5. the three geometric clauses of the engine, phrased for the `sep` family (the `sideGerm` and `sep`
   families are **definitionally equal**: `sideGermQfam = sepQfam`, `sideGermPfam = sepPfam`,
   `sideGermLoopFam = chartLoopFam (sepQfam ·)`, `sideGermChainFam = sweepFam c (1-·) (sepPfam ·)`,
   all by `rfl`):
   * `sep_hloop` — the chart's seam clause makes the core loop closed;
   * `sep_hseam` — `seam_rotPresentation` (`diskPlane_seamInv2` for the rotated chart);
   * `sep_havoid` — fed by the `hav` of step 1, the `hsmall` of convexity of the two straight paths
     (`Prod.norm_def`) and the `hang` of step 3 (`sep_dist_coe_coe_le`).
6. `Work.Drive.odd_coreSideCount_iff_of_famRegular_gen` at `Q := sepQfam Ξ Q t t' τ₁`,
   `P := sepPfam Ξ Q tR t'R t t' τ₂`, then `sepCoreSideCount_zero/one_eq_CntAt` + `htR`, `ht'R` collapse
   the two ends onto `Odd (CntAt Ξ Q c w (t + (τ₁,τ₂)))` and
   `Odd (CntAt Ξ Q c w' (t' + (τ₁,τ₂)))`, steps 2 move them back to the *given* configurations, and
   `propext` closes.

**Why the shifts must be independent.**  The `(τ₁, τ₂)`-derivative of the charted difference is
`(T₁, −T₂)` with `T₁`, `T₂` each onto (`ChartPert`'s third conjunct, surjectivity at *every* point of
`CappingSpace`), hence onto; with one shared shift it would be a *difference* of onto maps, which need
not be onto.  In `SepRegular` the two shifts are separate parameters and `sep_fam_regular` returns
`τ₂ = 0` (only the loop's chart has to be shifted for the Sard).

**Reproduction.**  `lake build Submission.Work.Drive.sideGerm_parity_eq_of_close`.  The only `sorry`s
mentioned anywhere in this file are inside the historical docstrings of this and the previous session;
the module itself contains none. -/


end Work.Drive
