import Mathlib
import Submission.Work.Drive.Mono.DichotomyB
import Submission.Work.Drive.Mono.AGSweep
import Submission.Work.Drive.Mono.JunctionGenC

/-!
# The data package of the tilted sweep, and the two fields of the sweep from it

`Work.Drive.Mono.TiltedSweepMonoAEG` (`Mono/AGSweep.lean`) is the honest residual of the
tilted-sweep route to the crux: the sweep, at almost every cutting level and at a box level in
general position, with the dichotomy field `(D)` and the no-jump field `(L)`.

The route splits into a **single** datum and two *per-datum* implications:

* `Work.Drive.Mono.DataPackage ψ K s u c σ v h R ℓ exc lam0 lam1 p q` — the bundle of hypotheses
  under which both the trace structure of the sweep's levels (clause 1 and clause 2 of the trace
  data) and the (L) argument are analysed: `TiltData`, the corrected junction genericity
  `JunctionGenC`, the face regularity of the slab faces, `SlabCutsBox`, the slicing of the box
  sphere, the disjoint-sphere decomposition `LevelSphereDecomposition` of the level frontier, and
  the level count;
* `Work.Drive.Mono.dichotomy_of_dataPackage` — **field `(D)`** at every non-exceptional level of
  the window, from the package alone (Pardon's dichotomy, through the corrected junction bundle
  `Mono/DichotomyB.lean`);
* `Work.Drive.Mono.SweepGeomAEG p q` — the *existence* of the package at a.e. cutting level, at a
  box level in general position.  This is the geometric obligation of the route; it is the
  composition of `Work.Drive.Mono.exists_junctionGood_tiltData` (the data), the disjoint-sphere
  geometry of the level frontier, the finite bookkeeping of the degenerate levels and the level
  count;
* `Work.Drive.Mono.tiltedSweepMonoAEG_of_geom_and_noJump` — the assembly: `SweepGeomAEG` together
  with the **per-datum** no-jump field `(L)` gives `TiltedSweepMonoAEG`, hence (through
  `Work.Drive.Mono.cruxCoreWdAEG_of_tiltedSweepMonoAEG`) the general-position crux, hence the
  challenge.

The point of the split is that field `(L)` is a statement about **one** datum whose hypotheses are
exactly the clauses of `DataPackage`, so its prover may work on the package rather than on the
existential, and the two fields are automatically at the *same* datum.
-/

open LeanEval.KnotTheory.PardonDistortion
open MeasureTheory Set
open scoped ENNReal

namespace Work.Drive.Mono

noncomputable section

/-- **The data package of the tilted sweep**: everything the analysis of the sweep's levels needs,
at one fixed datum.  Both field `(D)` (`Work.Drive.Mono.dichotomy_of_dataPackage`) and field `(L)`
(the no-jump, supplied by the consumer) are statements about a datum satisfying this package. -/
structure DataPackage (ψ : Submission.Diffeo) (K : Knot) (s u : ℝ) (c : R3)
    (σ : Equiv.Perm (Fin 3)) (v : R3) (h R : ℝ) (ℓ : R3 →L[ℝ] ℝ) (exc : Finset ℝ)
    (lam0 lam1 : ℝ) (p q : ℕ) : Prop where
  /-- the tilt data: the genericity of the sweep height, the size conditions, the window -/
  tilt : TiltData ψ s c σ u v h R ℓ exc lam0 lam1
  /-- the corrected stratified genericity at the junctions of the trace -/
  junc : JunctionGenC ψ s c σ u v h ℓ exc lam0 lam1
  /-- the slab faces meet the surface transversally inside the box -/
  faceReg : ∀ z : R3, z ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier →
      z ∈ Submission.PBox s c σ → |inner ℝ v z - (inner ℝ v c + u)| = h →
      ∃ pp : ℝ × ℝ, Work.BoxShrink.Pinch.par ψ pp = z ∧
        fderiv ℝ (fun qq : ℝ × ℝ => inner ℝ v (Work.BoxShrink.Pinch.par ψ qq)) pp ≠ 0
  /-- the slab really cuts the box -/
  slabCuts : SlabCutsBox s c σ (inner ℝ v c + u) h v
  /-- the slicing of the box sphere at the level -/
  slicing : Work.BoxShrink.SlicedSphere (Work.Drive.EpsSphere.torusOf ψ)
      {y : R3 | Submission.boxNorm c σ y = s}
  /-- the frontier of a level of the sweep is a finite disjoint union of embedded spheres -/
  spheres : LevelSphereDecomposition ψ s c σ u v h ℓ exc lam0 lam1
  /-- the level count: fewer than `min p q` knot points on the level frontier, off `exc` -/
  count : ∀ lam ∈ Set.Icc lam0 lam1, lam ∉ (exc : Set ℝ) →
      Set.encard (Set.range K.curve ∩
        frontier (tiltedLevelRemoved s c σ u v h ℓ lam)) < (Nat.min p q : ℕ∞)

/-- **Field `(D)`: Pardon's dichotomy at every non-exceptional level of the window**, from the
data package alone.  The trace structure of the level (clause 1) comes from the corrected junction
bundle `JunctionGenC` and the disjoint-sphere decomposition of the level frontier, and the
inessentiality of the trace curves from the level count; the dichotomy is then
`Work.Drive.Mono.windingSpan_bot_or_top_of_traceCurvesAt`. -/
theorem dichotomy_of_dataPackage (p q : ℕ) (hp : 0 < p) (hq : 0 < q) (hc : Nat.Coprime p q)
    {ψ : Submission.Diffeo} {K : Knot} {s u : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)}
    {v : R3} {h R : ℝ} {ℓ : R3 →L[ℝ] ℝ} {exc : Finset ℝ} {lam0 lam1 : ℝ}
    (himg : Set.range K.curve = Set.range
      (Work.CoreTopology.ClosedCurve.mapHomeomorph ψ.toHomeomorph
        (Work.CoreTopology.standardCurve p q)).γ)
    (hcl : Work.Drive.CleansDiscsWd (Work.Drive.EpsSphere.torusOf ψ))
    (hs : 0 < s) (hDP : DataPackage ψ K s u c σ v h R ℓ exc lam0 lam1 p q) :
    ∀ lam ∈ Set.Icc lam0 lam1, lam ∉ (exc : Set ℝ) →
      (Work.SurgeryInvariance.WindingSpan (Work.Drive.EpsSphere.torusOf ψ)
          (Work.Drive.Final.sweep (Work.Drive.EpsSphere.torusOf ψ) s c σ u v h ℓ lam) = ⊥ ∨
        Work.SurgeryInvariance.WindingSpan (Work.Drive.EpsSphere.torusOf ψ)
          (Work.Drive.Final.sweep (Work.Drive.EpsSphere.torusOf ψ) s c σ u v h ℓ lam) = ⊤) := by
  intro lam hlam hne
  have h := windingSpan_bot_or_top_of_levelSphereDecompositionB p q hp hq hc ψ K himg hcl hs
    hDP.tilt hDP.junc hDP.faceReg hDP.slicing hDP.spheres hDP.count lam hlam hne
  simpa only [Work.Drive.Final.sweep] using h

/-- **The geometric obligation of the tilted-sweep route**: at every crux configuration, at a box
level in general position, for almost every cutting level there are tilt data satisfying the whole
package `Work.Drive.Mono.DataPackage`.

This is the composition of the data producer (`Work.Drive.Mono.exists_junctionGood_tiltData`), the
disjoint-sphere geometry of the level frontier, the finite bookkeeping of the degenerate levels, and
the level count (`Work.Drive.Mono.ae_levelCount_lt_min`). -/
def SweepGeomAEG (p q : ℕ) : Prop :=
  ∀ (_hp : 0 < p) (_hq : 0 < q) (_hc : Nat.Coprime p q)
    (ψ : Submission.Diffeo) (K : Knot) (d : ℝ) (_hd : 0 ≤ d),
    Work.Sweep.IsDistortionBound K d →
    Set.range K.curve = Set.range
      (Work.CoreTopology.ClosedCurve.mapHomeomorph ψ.toHomeomorph
        (Work.CoreTopology.standardCurve p q)).γ →
    Submission.countConst * d < (Nat.min p q : ℝ) →
    Work.Drive.CleansDiscsWd (Work.Drive.EpsSphere.torusOf ψ) →
    ∀ (r : ℝ) (_hr : 0 < r) (c : R3) (σ : Equiv.Perm (Fin 3)),
      Submission.HasEssBox (Work.Drive.EpsSphere.torusOf ψ) r c σ →
      ∀ (s : ℝ) (_hrs : r < s) (_hs : s < (1 + Submission.eps) * r),
        Work.BoxShrink.SlicedSphere (Work.Drive.EpsSphere.torusOf ψ)
            {y : R3 | Submission.boxNorm c σ y = s} →
        BoxGen ψ c σ s →
        ((↑(Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
            Submission.boxNorm c σ (K.curve t) = s}) : ENNReal)
          ≤ ENNReal.ofReal (10 * (1 + Submission.eps) / Submission.eps * d)) →
        ∀ᵐ u ∂(MeasureTheory.volume : MeasureTheory.Measure ℝ),
          |u| < Submission.eps * r →
          ((↑(Set.encard {t : ℝ | t ∈ Set.Ico 0 (2 * Real.pi) ∧
              K.curve t ∈ Submission.PBox s c σ ∧
              (K.curve t) (σ 2) = c (σ 2) + u}) : ENNReal)
            ≤ ENNReal.ofReal (5 * (1 + Submission.eps) / Submission.eps * d)) →
          ∃ (v : R3) (h R : ℝ) (ℓ : R3 →L[ℝ] ℝ) (lam0 lam1 : ℝ) (exc : Finset ℝ),
            DataPackage ψ K s u c σ v h R ℓ exc lam0 lam1 p q

/-- **Field `(L)`, the no-jump, as a per-datum obligation.**  This is the second field of
`Work.Drive.Mono.TiltedSweepMonoAEG`, stated for a datum satisfying the package
`Work.Drive.Mono.DataPackage`: at every level of the window at which the span of the level's region
vanishes, no level just below carries the full span.  This is Pardon's `2`-surgery count at the
intermediate members of his pinching family. -/
def NoJumpInput (p q : ℕ) : Prop :=
  ∀ (ψ : Submission.Diffeo) (K : Knot) (s u : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (v : R3)
    (h R : ℝ) (ℓ : R3 →L[ℝ] ℝ) (exc : Finset ℝ) (lam0 lam1 : ℝ),
    DataPackage ψ K s u c σ v h R ℓ exc lam0 lam1 p q →
    ∀ lam ∈ Set.Icc lam0 lam1,
      Work.SurgeryInvariance.WindingSpan (Work.Drive.EpsSphere.torusOf ψ)
          (Work.Drive.Final.sweep (Work.Drive.EpsSphere.torusOf ψ) s c σ u v h ℓ lam) = ⊥ →
      ∃ mu0 : ℝ, mu0 < lam ∧ ∀ mu ∈ Set.Ico mu0 lam,
        Work.SurgeryInvariance.WindingSpan (Work.Drive.EpsSphere.torusOf ψ)
          (Work.Drive.Final.sweep (Work.Drive.EpsSphere.torusOf ψ) s c σ u v h ℓ mu) ≠ ⊤

/-- **The assembly of the tilted sweep from the two fields.**  `SweepGeomAEG` produces the datum;
field `(D)` is then `Work.Drive.Mono.dichotomy_of_dataPackage` and field `(L)` is the per-datum
no-jump hypothesis.  Since both are analysed at the *same* datum, this gives
`Work.Drive.Mono.TiltedSweepMonoAEG` in full (and hence, through
`Work.Drive.Mono.cruxCoreWdAEG_of_tiltedSweepMonoAEG`, the general-position crux). -/
theorem tiltedSweepMonoAEG_of_geom_and_noJump (hGeom : ∀ p q : ℕ, SweepGeomAEG p q)
    (hNoJump : ∀ p q : ℕ, NoJumpInput p q) :
    ∀ p q : ℕ, TiltedSweepMonoAEG p q := by
  intro p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice hBG hS
  refine Filter.Eventually.mono
    (hGeom p q hp hq hc ψ K d hd hbound himg hsmall hcl r hr c σ hbox s hrs hs hslice hBG hS) ?_
  intro u hdata hu hU
  obtain ⟨v, h, R, ℓ, lam0, lam1, exc, hDP⟩ := hdata hu hU
  obtain ⟨hgen, hv1, hℓne, hℓv, hsize, hh, hRbox, hlow, hhigh, hl, hexc⟩ := hDP.tilt
  exact ⟨v, h, R, ℓ, lam0, lam1, exc, hv1, hsize, hh, hRbox, hlow, hhigh, hl, hexc,
    dichotomy_of_dataPackage p q hp hq hc himg hcl (lt_trans hr hrs) hDP,
    hNoJump p q ψ K s u c σ v h R ℓ exc lam0 lam1 hDP⟩

end

end Work.Drive.Mono
