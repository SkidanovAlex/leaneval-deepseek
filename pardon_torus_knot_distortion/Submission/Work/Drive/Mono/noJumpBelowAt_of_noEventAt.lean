import Mathlib
import Submission.Work.Drive.Mono.SweepGeom3
import Submission.Work.Drive.Mono.Split
import Submission.Work.Drive.Mono.DichotomyB
import Submission.Work.Drive.Final.noJumpBelow_of_region
import Submission.Work.Drive.Final.AnyEventDefs
import Submission.Work.Drive.Mono.levelCount_lt_min_all
import Submission.Work.Drive.Mono.traceLocallyEuclidean_of_junctionGenC
import Submission.Work.Drive.Mono.frontier_tiltedLevelRemoved_sphereFace
import Submission.Work.Drive.Mono.trace_localModel_of_not_event

/-!
# The no-jump at a level of the tilted sweep which carries no event

(Project lead, `Submission/Work/Drive/Final/NOTES_LEAD_L4_L1.md` §4, the line L829: the non-event
levels of `Work.Drive.Mono.noJumpInput3_holds` are handled by `noJumpBelow_of_traceCurves`.)

The per-datum no-jump on the honest bundle `Work.Drive.Mono.GoodDataPackage3` splits on whether the
level carries an *event* of the sweep (`Work.Drive.Final.IsAnyEvent`).  This module is the half of
the split in which **no event lies at the level**: with that hypothesis the two clauses of the trace
data

* clause 1 (`Work.Drive.Mono.TraceCurvesAt`): the trace of the level — the surface's part of the
  frontier of the level's removed set — is the union of the ranges of finitely many pairwise disjoint
  simple *inessential* closed curves of the surface;
* clause 2 (`Work.Drive.Mono.AboveGenericAt`): every point of the surface in the closed box and the
  closed slab at the level is a limit of points of the level's region or lies on that trace,

both hold, and the resident lemma `Work.Drive.Mono.noJumpBelow_of_traceCurves` turns them, together
with the vanishing of the winding span at the level, into the conclusion: no level of a
left-neighbourhood of `lam` carries the full span.

## The two ingredients

* **The event-free hypothesis is as good as "the level is non-exceptional".**  Every clause of
  `Work.Drive.Final.TiltedGenericity` and of `Work.Drive.Mono.JunctionGenC` whose hypothesis is
  "the level is not in `exc`" fails at a level carrying no event only by producing an event of one of
  the three types at that level.  Hence both bundles survive the *erasure* of the level from the
  exceptional set, `exc ↦ exc.erase lam`, and the resident lemmas
  `Work.Drive.Mono.traceLocallyEuclidean_of_junctionGenC` and
  `Work.Drive.Mono.aboveGenericAt_of_junctionGenC` apply at `lam` verbatim.  This erasure is proved in
  `Submission/Work/Drive/Mono/trace_localModel_of_not_event.lean`
  (`tiltedGenericity_erase_of_no_event`, `tiltData_erase_of_no_event`,
  `junctionGenC_erase_of_no_event`), whose main theorem is exactly the pointwise local models of the
  trace at an event-free level; the present module consumes it for clause 1.
* **The inessentiality of the trace comes from the counting.**  The sphere cover `SphereCoverAt` of
  `Work.Drive.Final.GoodSweepData3` (a conjunct of `GoodDataPackage3`) writes the level frontier as a
  finite union of embedded spheres, pairwise disjoint on the surface.  Slicing each sphere by the
  surface and spending the level count of `GoodDataPackage3` through Pardon's Lemma 2
  (`Work.EpsW.trace_inessential_of_slicing_of_countsWd`) makes every sphere's trace inessential; a
  loop of the frontier lying in the union of the spheres lies in one of them (the spheres are closed
  and pairwise disjoint on the surface), whence the frontier carries no essential loop.

## Layout

* `Work.Drive.Mono.isAnyEvent_level_ne_of_no_event` — the event-free hypothesis in pointwise form;
* `Work.Drive.Mono.isOpenInSet_of_sphereCoverAt` — a member of a finite closed cover, pairwise
  disjoint on the surface, is relatively open in the surface's part of the union;
* `Work.Drive.Mono.not_containsEssentialLoop_of_sphereCoverAt` — the inessentiality of the frontier;
* `Work.Drive.Mono.aboveGenericAt_of_noEventAt_aux` / `traceCurvesAt_of_noEventAt_aux` — clauses 2
  and 1 at an event-free level;
* `Work.Drive.Mono.noJumpBelowAt_of_noEventAt` — the target.
-/

namespace Work.Drive.Mono

open LeanEval.KnotTheory.PardonDistortion Set
open scoped ENNReal

noncomputable section

/-! ## 1. The event-free hypothesis in pointwise form -/

/-- The absence of an event at the level, in the pointwise form consumed by the erasure lemmas of
`Submission/Work/Drive/Mono/trace_localModel_of_not_event.lean`. -/
theorem isAnyEvent_level_ne_of_no_event {ψ : Submission.Diffeo} {s u : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {v : R3} {h : ℝ} {ℓ : R3 →L[ℝ] ℝ} {lam : ℝ}
    (hnoev : ¬ ∃ pp : ℝ × ℝ, Work.Drive.Final.IsAnyEvent ψ s c σ u v h ℓ pp ∧
      ℓ (Work.BoxShrink.Pinch.par ψ pp) = lam) :
    ∀ pp : ℝ × ℝ, Work.Drive.Final.IsAnyEvent ψ s c σ u v h ℓ pp →
      ℓ (Work.BoxShrink.Pinch.par ψ pp) ≠ lam :=
  fun pp hp heq => hnoev ⟨pp, hp, heq⟩

/-! ## 2. A member of a sphere cover is relatively open in the surface's part of the union -/

/-- **A member of a finite cover of a set by closed pieces pairwise disjoint on the surface is
relatively open in the surface's part of the union.** -/
theorem isOpenInSet_of_sphereCoverAt
    {P : Work.CoreTopology.ParamTorus} {m : ℕ} {Ss : Fin m → Set R3}
    (hcl : ∀ i, IsClosed (Ss i))
    (hdisj : ∀ i j : Fin m, i ≠ j →
      Disjoint (Ss i ∩ P.carrier) (Ss j ∩ P.carrier)) (i : Fin m) :
    Work.Smooth.OneManifold.IsOpenInSet (P.carrier ∩ ⋃ j, Ss j) (Ss i ∩ P.carrier) := by
  classical
  have hopen : IsOpen ((⋃ j ∈ (Finset.univ.filter (fun j : Fin m => j ≠ i)), Ss j)ᶜ) :=
    (isClosed_biUnion_finset (fun j _ => hcl j)).isOpen_compl
  have h1 : (Subtype.val ⁻¹' (Ss i ∩ P.carrier) : Set ↥(P.carrier ∩ ⋃ j, Ss j)) =
      Subtype.val ⁻¹' (⋃ j ∈ (Finset.univ.filter (fun j : Fin m => j ≠ i)), Ss j)ᶜ := by
    ext x
    constructor
    · intro hx
      rw [Set.mem_preimage, Set.mem_compl_iff, Set.mem_iUnion₂]
      rintro ⟨j, hj, hxj⟩
      exact (Set.disjoint_left.mp (hdisj i j (Ne.symm (Finset.mem_filter.mp hj).2)))
        hx ⟨hxj, x.2.1⟩
    · intro hx
      rw [Set.mem_preimage] at hx
      rw [Set.mem_preimage]
      have hxU : (x : R3) ∈ ⋃ j, Ss j := x.2.2
      obtain ⟨j, hxj⟩ := Set.mem_iUnion.mp hxU
      have hji : j = i := by
        by_contra hne
        exact hx (Set.mem_iUnion₂.mpr ⟨j, Finset.mem_filter.mpr ⟨Finset.mem_univ j, hne⟩, hxj⟩)
      rw [hji] at hxj
      exact ⟨hxj, x.2.1⟩
  rw [Work.Smooth.OneManifold.IsOpenInSet, h1]
  exact hopen.preimage continuous_subtype_val

/-! ## 3. The inessentiality of the level's trace from the sphere cover and the count -/

/-- **The inessentiality of the level's trace from a sphere cover of the level frontier and the
level count.**  If the frontier of the level's removed set is the union of finitely many embedded
spheres, pairwise disjoint on the surface, each of whose traces is locally Euclidean, and if the knot
meets the frontier in fewer than `min p q` points (Pardon's Lemma 2, in the weak-cleaning vocabulary
`Work.EpsW.trace_inessential_of_slicing_of_countsWd`), then no essential loop of the surface lies in
that frontier.

This is the extraction of the corresponding part of
`Work.Drive.Mono.traceCurvesAt_of_sphereDecomposition`, which asks for *ambient* disjointness of the
spheres; the cover `Work.Drive.Final.SphereCoverAt` of `GoodSweepData3` provides only disjointness on
the surface, which suffices because a loop of the frontier lying in the union of the spheres lies in
a single one of them. -/
theorem not_containsEssentialLoop_of_sphereCoverAt
    (p q : ℕ) (hp : 0 < p) (hq : 0 < q) (hc : Nat.Coprime p q)
    (ψ : Submission.Diffeo) (K : LeanEval.KnotTheory.PardonDistortion.Knot)
    (himg : Set.range K.curve = Set.range
      (Work.CoreTopology.ClosedCurve.mapHomeomorph ψ.toHomeomorph
        (Work.CoreTopology.standardCurve p q)).γ)
    (hcl : Work.Drive.CleansDiscsWd (Work.Drive.EpsSphere.torusOf ψ))
    {s u h lam : ℝ} {c v : R3} {σ : Equiv.Perm (Fin 3)} {ℓ : R3 →L[ℝ] ℝ}
    {m : ℕ} {Ss : Fin m → Set R3}
    (hdecomp : frontier (Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ lam) = ⋃ i, Ss i)
    (hdisj : ∀ i j : Fin m, i ≠ j →
      Disjoint (Ss i ∩ (Work.Drive.EpsSphere.torusOf ψ).carrier)
        (Ss j ∩ (Work.Drive.EpsSphere.torusOf ψ).carrier))
    (hsph : ∀ i, Work.InnermostDisk.IsEmbeddedSphere (Ss i))
    (hlocI : ∀ i, Work.Smooth.OneManifold.IsLocallyEuclidean
      (Ss i ∩ (Work.Drive.EpsSphere.torusOf ψ).carrier))
    (hcount : Set.encard (Set.range K.curve ∩
      frontier (Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ lam)) < (Nat.min p q : ℕ∞)) :
    ¬ (Work.Drive.EpsSphere.torusOf ψ).ContainsEssentialLoop
      (frontier (Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ lam)) := by
  classical
  set P := Work.Drive.EpsSphere.torusOf ψ with hP
  have hsub_i : ∀ i, Ss i ⊆
      frontier (Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ lam) := by
    intro i
    rw [hdecomp]
    exact Set.subset_iUnion _ i
  have hcomp_i : ∀ i, IsCompact (Ss i ∩ P.carrier) := by
    intro i
    obtain ⟨e, -, he⟩ := hsph i
    have hcomp' : IsCompact (Ss i) := by
      rw [← he]
      exact isCompact_range e.continuous
    exact hcomp'.inter_right (Work.Smooth.Morse.Surface.isCompact_torus ψ).isClosed
  have hclosed_i : ∀ i, IsClosed (Ss i ∩ P.carrier) := fun i => (hcomp_i i).isClosed
  have hnoess_i : ∀ i, ¬ P.ContainsEssentialLoop (Ss i) := by
    intro i
    obtain ⟨Sl⟩ := sphereSlicing_of_isEmbeddedSphere_of_localModels (P := P) (S := Ss i)
      (hsph i) (hcomp_i i) (hlocI i)
    refine Work.EpsW.trace_inessential_of_slicing_of_countsWd p q hp hq hc ψ K himg Sl hcl ?_
    refine lt_of_le_of_lt (Set.encard_le_encard ?_) hcount
    rintro x ⟨hxK, hxS⟩
    exact ⟨hxK, hsub_i i hxS⟩
  rintro ⟨γ, hγess, hγ⟩
  have hsub : Set.range γ.γ ⊆ ⋃ i, (Ss i ∩ P.carrier) := by
    rintro x ⟨t, rfl⟩
    have hx : γ.γ t ∈ frontier (Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ lam) := hγ t
    rw [hdecomp] at hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
    exact Set.mem_iUnion.mpr ⟨i, hi, γ.mem t⟩
  have hpre : IsPreconnected (Set.range γ.γ) := by
    rw [Work.CoreTopology.ClosedCurve.range_eq_image P γ]
    exact isPreconnected_Ico.image γ.γ γ.cont.continuousOn
  obtain ⟨i, hi⟩ := Work.InnermostDisk.exists_subset_of_preconnected_iUnion hpre
    ⟨γ.γ 0, ⟨0, rfl⟩⟩ (fun i => Ss i ∩ P.carrier) hclosed_i
    (fun i j hij => hdisj i j hij) hsub
  exact hnoess_i i ⟨γ, hγess, fun t => (hi ⟨t, rfl⟩).1⟩

/-! ## 4. Clause 2 of the trace data at an event-free level -/

/-- **Clause 2 at a level carrying no event**, from the third bundle: the junction bundle and the
tilt data at the exceptional set with the level erased give
`Work.Drive.Mono.aboveGenericAt_of_junctionGenC`. -/
theorem aboveGenericAt_of_noEventAt_aux
    (p q : ℕ)
    {ψ : Submission.Diffeo} {K : LeanEval.KnotTheory.PardonDistortion.Knot} {s u : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {v : R3} {h R : ℝ} {ℓ : R3 →L[ℝ] ℝ} {exc : Finset ℝ}
    {lam0 lam1 : ℝ}
    (hDP : GoodDataPackage3 ψ K s u c σ v h R ℓ exc lam0 lam1 p q)
    {lam : ℝ} (hlam : lam ∈ Set.Icc lam0 lam1)
    (hnoev : ¬ ∃ pp : ℝ × ℝ, Work.Drive.Final.IsAnyEvent ψ s c σ u v h ℓ pp ∧
      ℓ (Work.BoxShrink.Pinch.par ψ pp) = lam) :
    Work.Drive.Mono.AboveGenericAt (Work.Drive.EpsSphere.torusOf ψ) s c σ u v h ℓ lam := by
  obtain ⟨hdata, hG3, -⟩ := hDP
  obtain ⟨hGS2, hEF, hBelt, hSBCR, hGT, hFRC, hCorner, hOffK, hOne, hSph⟩ := hG3
  obtain ⟨-, -, -, -, -, -, -, -, -, hl, -⟩ := hdata.tilt
  have hn := isAnyEvent_level_ne_of_no_event (ψ := ψ) (s := s) (u := u) (c := c) (σ := σ)
    (v := v) (h := h) (ℓ := ℓ) (lam := lam) hnoev
  have hs : 0 < s := by
    obtain ⟨y, hy, -⟩ := hdata.slabCuts.1
    have h1 : Submission.boxNorm c σ y < s := (Submission.mem_PBox_iff s c σ y).mp hy
    have h2 : 0 ≤ Submission.boxNorm c σ y := Submission.boxNorm_nonneg c σ y
    linarith
  exact aboveGenericAt_of_junctionGenC (ψ := ψ) (s := s) (u := u) (c := c) (σ := σ) (v := v)
    (h := h) (R := R) (ℓ := ℓ) (exc := exc.erase lam) (lam0 := lam0) (lam1 := lam1)
    (lam := lam) hs (tiltData_erase_of_no_event hdata.tilt hn)
    (junctionGenC_erase_of_no_event hs hdata.junc hl hGT hEF hn) hlam
    (fun hmem => (Finset.mem_erase.mp (Finset.mem_coe.mp hmem)).1 rfl)

/-! ## 5. Clause 1 of the trace data at an event-free level -/

/-- **Clause 1 at a level carrying no event**, from the third bundle: the pointwise local models of
the trace (the erasure of the level from `exc`, `trace_localModel_of_not_event`), the sphere cover
`SphereCoverAt`, and the level count (Pardon's Lemma 2). -/
theorem traceCurvesAt_of_noEventAt_aux
    (p q : ℕ) (hp : 0 < p) (hq : 0 < q) (hc : Nat.Coprime p q)
    (ψ : Submission.Diffeo) (K : LeanEval.KnotTheory.PardonDistortion.Knot)
    (himg : Set.range K.curve = Set.range
      (Work.CoreTopology.ClosedCurve.mapHomeomorph ψ.toHomeomorph
        (Work.CoreTopology.standardCurve p q)).γ)
    (hcl : Work.Drive.CleansDiscsWd (Work.Drive.EpsSphere.torusOf ψ))
    {s u : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {v : R3} {h R : ℝ} {ℓ : R3 →L[ℝ] ℝ}
    {exc : Finset ℝ} {lam0 lam1 : ℝ}
    (hDP : GoodDataPackage3 ψ K s u c σ v h R ℓ exc lam0 lam1 p q)
    {lam : ℝ} (hlam : lam ∈ Set.Icc lam0 lam1)
    (hnoev : ¬ ∃ pp : ℝ × ℝ, Work.Drive.Final.IsAnyEvent ψ s c σ u v h ℓ pp ∧
      ℓ (Work.BoxShrink.Pinch.par ψ pp) = lam) :
    Work.Drive.Mono.TraceCurvesAt (Work.Drive.EpsSphere.torusOf ψ) s c σ u v h ℓ lam := by
  have hlocZ : Work.Smooth.OneManifold.IsLocallyEuclidean
      ((Work.Drive.EpsSphere.torusOf ψ).carrier ∩
        frontier (Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ lam)) :=
    isLocallyEuclidean_trace_of_local_models
      (trace_localModel_of_not_event (ψ := ψ) (K := K) (s := s) (u := u) (c := c) (σ := σ)
        (v := v) (h := h) (R := R) (ℓ := ℓ) (exc := exc) (lam0 := lam0) (lam1 := lam1)
        (p := p) (q := q) hDP hlam hnoev)
  obtain ⟨hdata, hG3, hcount3⟩ := hDP
  obtain ⟨hGS2, hEF, hBelt, hSBCR, hGT, hFRC, hCorner, hOffK, hOne, hSph⟩ := hG3
  obtain ⟨m, Ss, hsph, hdisj, hdecomp⟩ := hSph lam hlam
  have hsub_i : ∀ i, Ss i ⊆
      frontier (Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ lam) := by
    intro i
    rw [hdecomp]
    exact Set.subset_iUnion _ i
  have hclosed_i : ∀ i, IsClosed (Ss i) := by
    intro i
    obtain ⟨e, -, he⟩ := hsph i
    rw [← he]
    exact (isCompact_range e.continuous).isClosed
  have hlocU : Work.Smooth.OneManifold.IsLocallyEuclidean
      ((Work.Drive.EpsSphere.torusOf ψ).carrier ∩ ⋃ i, Ss i) := by
    rw [← hdecomp]
    exact hlocZ
  have hlocI : ∀ i, Work.Smooth.OneManifold.IsLocallyEuclidean
      (Ss i ∩ (Work.Drive.EpsSphere.torusOf ψ).carrier) := fun i =>
    Work.Smooth.OneManifold.IsLocallyEuclidean.of_isOpenIn
      (Z := (Work.Drive.EpsSphere.torusOf ψ).carrier ∩ ⋃ j, Ss j)
      (V := Ss i ∩ (Work.Drive.EpsSphere.torusOf ψ).carrier)
      (fun x hx => ⟨hx.2, by rw [← hdecomp]; exact hsub_i i hx.1⟩)
      (isOpenInSet_of_sphereCoverAt hclosed_i hdisj i) hlocU
  exact traceCurvesAt_of_isLocallyEuclidean
    (isCompact_trace_torusOf ψ s u c σ v h ℓ lam) hlocZ
    (not_containsEssentialLoop_of_sphereCoverAt p q hp hq hc ψ K himg hcl hdecomp hdisj hsph hlocI
      (hcount3 lam hlam))

/-! ## 6. The no-jump at a level carrying no event -/

theorem noJumpBelowAt_of_noEventAt
    (p q : ℕ) (hp : 0 < p) (hq : 0 < q) (hc : Nat.Coprime p q)
    (ψ : Submission.Diffeo) (K : LeanEval.KnotTheory.PardonDistortion.Knot)
    (himg : Set.range K.curve = Set.range
      (Work.CoreTopology.ClosedCurve.mapHomeomorph ψ.toHomeomorph
        (Work.CoreTopology.standardCurve p q)).γ)
    (hcl : Work.Drive.CleansDiscsWd (Work.Drive.EpsSphere.torusOf ψ))
    {s u : ℝ} {c : LeanEval.KnotTheory.PardonDistortion.R3} {σ : Equiv.Perm (Fin 3)}
    {v : LeanEval.KnotTheory.PardonDistortion.R3} {h R : ℝ}
    {ℓ : LeanEval.KnotTheory.PardonDistortion.R3 →L[ℝ] ℝ} {exc : Finset ℝ} {lam0 lam1 : ℝ}
    (hDP : Work.Drive.Mono.GoodDataPackage3 ψ K s u c σ v h R ℓ exc lam0 lam1 p q)
    {lam : ℝ} (hlam : lam ∈ Set.Icc lam0 lam1)
    (hnoev : ¬ ∃ pp : ℝ × ℝ, Work.Drive.Final.IsAnyEvent ψ s c σ u v h ℓ pp ∧
      ℓ (Work.BoxShrink.Pinch.par ψ pp) = lam)
    (hbot : Work.SurgeryInvariance.WindingSpan (Work.Drive.EpsSphere.torusOf ψ)
      (Work.Drive.Final.sweep (Work.Drive.EpsSphere.torusOf ψ) s c σ u v h ℓ lam) = ⊥) :
    ∃ mu0 : ℝ, mu0 < lam ∧ ∀ mu ∈ Set.Ico mu0 lam,
      Work.SurgeryInvariance.WindingSpan (Work.Drive.EpsSphere.torusOf ψ)
        (Work.Drive.Final.sweep (Work.Drive.EpsSphere.torusOf ψ) s c σ u v h ℓ mu) ≠ ⊤ := by
  obtain ⟨-, hv1, hℓne, hℓv, -⟩ := hDP.1.tilt
  have hv : v ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hv1
    exact one_ne_zero hv1.symm
  exact noJumpBelow_of_traceCurves (P := Work.Drive.EpsSphere.torusOf ψ) (s := s) (c := c)
    (σ := σ) (u := u) (v := v) (h := h) (ℓ := ℓ) (lam := lam) hv hℓv hℓne
    (traceCurvesAt_of_noEventAt_aux p q hp hq hc ψ K himg hcl hDP hlam hnoev)
    (aboveGenericAt_of_noEventAt_aux p q hDP hlam hnoev) hbot

end

end Work.Drive.Mono
