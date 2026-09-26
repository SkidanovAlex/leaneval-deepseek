import Mathlib
import Submission.Work.Drive.Mono.DataPackage
import Submission.Work.Drive.Mono.BoxWidth
import Submission.Work.Drive.Mono.BoxGenE
import Submission.Work.Drive.Final.GoodSweepData2

/-!
# The data bundle of the `BoxGenE` geometric producer `goodSweepGeom2_holds`

`Work.Drive.Mono.GoodSweepGeomAEG2` (`Mono/SweepGeom2.lean`) demands, at every crux configuration
and at almost every cutting level `u`, tilt data `(v, h, R, ℓ, exc, lam0, lam1)` satisfying
`Work.Drive.Mono.GoodDataPackage = DataPackage ∧ GoodSweepData2`.

The proof of `Work.Drive.Mono.goodSweepGeom2_holds` splits the obligation into

* the **data bundle** `Work.Drive.Mono.Geom2Data` below — everything in `DataPackage` and
  `GoodSweepData2` **except** the junction bundle `Work.Drive.Mono.JunctionGenC` (the stratified
  genericity of the trace at the junctions of the level): the tilt data, the thin-slab cutting, the
  window on the closed box, the face regularity, the non-grazing conditions of the knot, the level
  count, the `offK`/`knotGP` clauses and the three event clauses of the (L) route;
* the **junction clause** `Work.Drive.Mono.JunctionGenC` — the trace geometry at the junctions of the
  level, produced from the data bundle, `Work.Drive.Mono.BoxGenE` and the cutting transversality by
  `Work.Drive.Mono.junctionGenC_of_geom2Data`.

This module holds the definition and the monotonicity in `exc` which the assembly needs (each clause
is of the form “for `lam ∉ exc` …”, so enlarging `exc` only weakens the bundle).
-/

open LeanEval.KnotTheory.PardonDistortion
open Set
open scoped ENNReal

namespace Work.Drive.Mono

noncomputable section

/-- **The data bundle of the geometric producer, without the junction clause.**

Everything the two fields of the tilted sweep need at one datum *except* the junction genericity
`Work.Drive.Mono.JunctionGenC`:

* `tilt` — the tilt data (`TiltData`), i.e. the genericity of the sweep height, the unit norm and
  orthogonality conditions, the size condition `‖v - shiftVσ σ 1‖ R < h`, the box bound, the window
  conditions and the exceptional set inside the window;
* `winC` — the window on the **closed** box (the level-frontier genericity
  `Work.Drive.Mono.exists_levelFrontierGen` and the disjoint-sphere decomposition of the level
  frontier consume it);
* `slabCuts` — the slab really cuts the box (`SlabCutsBox`);
* `lne` — the wall functional kills no coordinate direction (the `ℓ (e_{σ i}) ≠ 0` clause of
  `Work.Drive.Final.GoodSweepData2`);
* `thin` — the slab is thin (`h + |u| < boxWidth`), `vclose` — the tilt direction is within `1/8` of
  `shiftVσ σ 1`, `traceBand` — the part of the surface on the box sphere inside the closed slab lies
  in the height band `|z (σ 2) - (c (σ 2) + u)| ≤ 2h` (the band in which the box trace is a finite
  family of arcs parametrised by the height), and `cornerSlab` — the surface meets the *edges* of the
  box sphere inside the closed slab in finitely many points (the finiteness of clause (c) of
  `Work.Drive.Mono.JunctionGenC`; it holds for a thin slab, where the horizontal edges of the box
  sphere lie outside the closed slab and only the finitely many vertical edge points of
  `Work.Drive.Mono.VertEdgeFinite` remain);
* `faceReg` — the slab faces meet the surface transversally inside the box;
* `nograz*` — the five non-grazing conditions of the knot which the level count
  `Work.Drive.Mono.ae_levelCount_lt_min` consumes;
* `count` — the level count itself (fewer than `min p q` knot parameters on the frontier of the
  level's removed set, off the exceptional levels);
* `offK`, `knotGP` — the two clauses of `Work.Drive.Final.GoodSweepData`;
* `evFace`, `evBend`, `evTriple` — the three event clauses of `Work.Drive.Final.GoodSweepData2`. -/
def Geom2Data (ψ : Submission.Diffeo) (K : Knot) (s u : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3))
    (v : R3) (h R : ℝ) (ℓ : R3 →L[ℝ] ℝ) (exc : Finset ℝ) (lam0 lam1 : ℝ) (p q : ℕ) : Prop :=
  Work.Drive.Mono.TiltData ψ s c σ u v h R ℓ exc lam0 lam1 ∧
  (∀ y ∈ closure (Submission.PBox s c σ), lam0 < ℓ y ∧ ℓ y < lam1) ∧
  Work.Drive.Mono.SlabCutsBox s c σ (inner ℝ v c + u) h v ∧
  (∀ i : Fin 3, ℓ (EuclideanSpace.single (σ i) (1 : ℝ)) ≠ 0) ∧
  (h + |u| < Work.Drive.Mono.boxWidth s σ v) ∧
  ‖v - Work.BoxShrink.shiftVσ σ 1‖ ≤ 1 / 8 ∧
  (∀ z : R3, z ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier → Submission.boxNorm c σ z = s →
      |inner ℝ v z - (inner ℝ v c + u)| ≤ h →
      |z (σ 2) - (c (σ 2) + u)| ≤ 2 * h) ∧
  ({z : R3 | z ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier ∧ Submission.boxNorm c σ z = s ∧
      |inner ℝ v z - (inner ℝ v c + u)| ≤ h ∧
      (∃ i j : Fin 3, i ≠ j ∧ |z (σ i) - c (σ i)| = Submission.boxSide i * s ∧
        |z (σ j) - c (σ j)| = Submission.boxSide j * s)}).Finite ∧
  (∀ z : R3, z ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier → z ∈ Submission.PBox s c σ →
      |inner ℝ v z - (inner ℝ v c + u)| = h →
      ∃ pp : ℝ × ℝ, Work.BoxShrink.Pinch.par ψ pp = z ∧
        fderiv ℝ (fun q : ℝ × ℝ => inner ℝ v (Work.BoxShrink.Pinch.par ψ q)) pp ≠ 0) ∧
  (∀ t : ℝ, Submission.boxNorm c σ (K.curve t) = s →
      h ≤ |inner ℝ v (K.curve t) - (inner ℝ v c + u)|) ∧
  (∀ t : ℝ, K.curve t ∈ Submission.PBox s c σ →
      deriv (fun r : ℝ => inner ℝ v (K.curve r)) t = 0 →
      h ≤ |inner ℝ v (K.curve t) - (inner ℝ v c + u)|) ∧
  (∀ t : ℝ, K.curve t ∈ Submission.PBox s c σ →
      |inner ℝ v (K.curve t) - (inner ℝ v c + u)| ≤ h →
      deriv (fun r : ℝ => ℓ (K.curve r)) t ≠ 0) ∧
  (∀ t : ℝ, K.curve t ∈ Submission.PBox s c σ →
      |inner ℝ v (K.curve t) - (inner ℝ v c + u)| = h →
      deriv (fun r : ℝ => inner ℝ v (K.curve r)) t ≠ 0) ∧
  (∀ t : ℝ, K.curve t ∈ Submission.PBox s c σ →
      |inner ℝ v (K.curve t) - (inner ℝ v c + u)| = h →
      ℓ (K.curve t) ∈ (exc : Set ℝ)) ∧
  (∀ lam ∈ Set.Icc lam0 lam1, lam ∉ (exc : Set ℝ) →
      Set.encard (Set.range K.curve ∩
        frontier (tiltedLevelRemoved s c σ u v h ℓ lam)) < (Nat.min p q : ℕ∞)) ∧
  (∀ p' : ℝ × ℝ, Work.BoxShrink.Pinch.par ψ p' ∈ Submission.PBox s c σ →
      Work.BoxShrink.Pinch.par ψ p' ∈
        Work.Drive.EpsForm.tiltedSlabClosed (inner ℝ v c + u) v h →
      fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ℓ) p' = 0 →
      ∀ t : ℝ, K.curve t ≠ Work.BoxShrink.Pinch.par ψ p') ∧
  (∀ t : ℝ, |inner ℝ v (K.curve t) - (inner ℝ v c + u)| = h →
      deriv (fun s : ℝ => inner ℝ v (K.curve s)) t ≠ 0) ∧
  (∀ p' : ℝ × ℝ, Work.Drive.Final.IsEvent ψ s c σ u v h ℓ p' →
      |Work.Drive.Final.slabFn c u v (Work.BoxShrink.Pinch.par ψ p')| < h) ∧
  (∀ p' : ℝ × ℝ, Work.Drive.Final.IsFaceEvent ψ s c σ u v h ℓ p' →
      ∃ t : ℝ, fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ℓ) p' =
          t • fderiv ℝ (Work.Drive.Final.slabFnPar ψ c u v) p' ∧
        ∀ w : ℝ × ℝ, w ≠ 0 → fderiv ℝ (Work.Drive.Final.slabFnPar ψ c u v) p' w = 0 →
          (fderiv ℝ (fderiv ℝ (fun q : ℝ × ℝ =>
            Work.Drive.EpsForm.sweepHeight ψ ℓ q - t * Work.Drive.Final.slabFnPar ψ c u v q)) p')
              w w ≠ 0) ∧
  (∀ p' : ℝ × ℝ, Work.Drive.Final.IsTriplePoint ψ s c σ u v h p' →
      fderiv ℝ (Work.Drive.EpsForm.sweepHeight ψ ℓ) p' ≠ 0)


/-- **The data bundle together with the height-parametrised family of trace arcs.**

`Work.Drive.Mono.Geom2Data` (the tilt data, the cutting, the window, the non-grazing conditions and
the level count, the `offK`/`knotGP` clauses and the three event clauses of
`Work.Drive.Final.GoodSweepData2`) together with:

* the finiteness of the points of the surface on the **edges** of the box sphere which lie on the
  **boundary of the slab** (the hypothesis `hnoCornerFace` of `Work.Drive.Mono.junctionGenC_of_arcs`:
  at a box-edge point of the box sphere the box norm is a `max` of two active face functions, hence
  not differentiable, so clause (b) of `Work.Drive.Mono.JunctionGenC` is unsatisfiable there);
* a finite family `γ : Fin N → ℝ → R3` of arcs, parametrised by the `σ 2`-height
  (`(γ k t) (σ 2) = c (σ 2) + u + t`), `C³` on `[-η, η]`, each lying on a signed face `i ≠ 2` of the
  box (`hγβ`, the local model of the box trace of `Work.Drive.Mono.gammaArcs_exist`);
* the **cover** of the box trace inside the closed slab, away from the box-edge points, by those arcs
  with the height parameter in `(-η, η) ∩ [-2h, 2h]` (`hcover`);
* the two **arc genericity** conditions `harcℓ` (the level functional `ℓ` is regular along the arcs)
  and `harcv` (the slab coordinate grows at speed `≥ 1/2` along the arcs).

These are exactly the purely geometric inputs of `Work.Drive.Mono.junctionGenC_of_arcs`, which turns
them into the junction bundle `Work.Drive.Mono.JunctionGenC`; hence the junction clause is
*bookkeeping* given this bundle (`Work.Drive.Mono.junctionGenC_of_geom2DataPlus`). -/
def Geom2DataPlus (ψ : Submission.Diffeo) (K : Knot) (s u : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3))
    (v : R3) (h R : ℝ) (ℓ : R3 →L[ℝ] ℝ) (exc : Finset ℝ) (lam0 lam1 : ℝ) (p q : ℕ) : Prop :=
  Geom2Data ψ K s u c σ v h R ℓ exc lam0 lam1 p q ∧
  (∃ (N : ℕ) (γ : Fin N → ℝ → R3) (η : ℝ), 0 < η ∧
    (∀ k, ContDiffOn ℝ 3 (γ k) (Set.Icc (-η) η)) ∧
    (∀ k, ∀ t ∈ Set.Icc (-η) η, (γ k t) (σ 2) = c (σ 2) + u + t) ∧
    (∀ k, ∃ i : Fin 3, i ≠ 2 ∧ ∃ ε : ℝ, (ε = 1 ∨ ε = -1) ∧ ∃ β : ℝ → ℝ × ℝ,
      ContDiffOn ℝ 3 β (Set.Icc (-η) η) ∧ ∀ t ∈ Set.Icc (-η) η,
        Work.BoxShrink.Pinch.par ψ (β t) = γ k t ∧
        (γ k t) (σ i) = c (σ i) + ε * Submission.boxSide i * s) ∧
    (∀ z : R3, z ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier → Submission.boxNorm c σ z = s →
      |inner ℝ v z - (inner ℝ v c + u)| ≤ h →
      (∀ j : Fin 3, j ≠ 2 → ∀ j' : Fin 3, j' ≠ 2 → j ≠ j' →
        ¬ (|z (σ j) - c (σ j)| = Submission.boxSide j * s ∧
           |z (σ j') - c (σ j')| = Submission.boxSide j' * s)) →
      ∃ k, ∃ t ∈ Set.Ioo (-η) η, z = γ k t ∧ |t| ≤ 2 * h) ∧
    (∀ k, ∀ t : ℝ, t ∈ Set.Ioo (-η) η → |t| ≤ 2 * h →
      deriv (fun r : ℝ => ℓ (γ k r)) t ≠ 0) ∧
    (∀ k, ∀ t : ℝ, t ∈ Set.Ioo (-η) η → |t| ≤ 2 * h →
      (1 / 2 : ℝ) ≤ inner ℝ v (deriv (γ k) t))) ∧
  (∀ z : R3, z ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier → Submission.boxNorm c σ z = s →
      |inner ℝ v z - (inner ℝ v c + u)| = h →
      (∃ i j : Fin 3, i ≠ j ∧ |z (σ i) - c (σ i)| = Submission.boxSide i * s ∧
        |z (σ j) - c (σ j)| = Submission.boxSide j * s) → False)

end

end Work.Drive.Mono
