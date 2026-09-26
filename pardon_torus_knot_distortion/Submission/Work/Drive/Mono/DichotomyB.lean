import Mathlib
import Submission.Work.Drive.Mono.TiltedTraceDataWExists_holds
import Submission.Work.Drive.Mono.traceLocallyEuclidean_of_junctionGenC
import Submission.Work.Drive.Mono.aboveGenericAt_of_junctionGenC

/-!
# Field `(D)` of the tilted sweep from the corrected junction bundle

The chain of `Submission/Work/Drive/Mono/TiltedTraceDataWExists_holds.lean` derives clause 1
(`TraceCurvesAt`) from the *geometric input* `LevelSphereDecomposition` plus the pointwise local
models of the trace.  Its local models come from the bundle `Work.Drive.Mono.JunctionGen`, whose
clause (c) is **not satisfiable** (see `Mono/NOTES_JunctionGen_OBSTRUCTIONS.md` §2); the corrected
bundle is `Work.Drive.Mono.JunctionGenC`, whose local-model assembly is
`Work.Drive.Mono.traceLocallyEuclidean_of_junctionGenC`.

This module re-runs that chain with `JunctionGenC`, so that the data produced by the corrected
genericity package (`Work.Drive.Mono.exists_junctionGood_tiltData`) can actually be used:

* `Work.Drive.Mono.traceCurvesAt_of_levelSphereDecompositionB` — clause 1 at every non-exceptional
  level of the window, from `TiltData`, `JunctionGenC`, the face regularity, the slicing of the box
  sphere, the disjoint-sphere decomposition of the level frontier and the level count;
* `Work.Drive.Mono.windingSpan_bot_or_top_of_levelSphereDecompositionB` — **field `(D)`**: Pardon's
  dichotomy `W (region lam) = ⊥ ∨ W (region lam) = ⊤` at every non-exceptional level.

Also here: the *monotonicity in the exceptional set* of the two bundles `TiltData` and
`JunctionGenC` (`Work.Drive.Mono.tiltData_mono_exc`, `Work.Drive.Mono.junctionGenC_mono_exc`), which
is what lets the disjoint-sphere bookkeeping enlarge `exc` without destroying the data.
-/

namespace Work.Drive.Mono

open LeanEval.KnotTheory.PardonDistortion Set
open scoped ENNReal

noncomputable section

/-! ## Monotonicity in the exceptional set -/

/-- **`TiltedGenericity` is monotone in `exc`**: its first two clauses quantify over levels outside
`exc`, its third *concludes* membership in `exc`, and its fourth does not mention `exc`. -/
theorem tiltedGenericity_mono_exc {ψ : Submission.Diffeo} {s u : ℝ} {c : R3}
    {σ : Equiv.Perm (Fin 3)} {v : R3} {h : ℝ} {ℓ : R3 →L[ℝ] ℝ} {exc B : Finset ℝ}
    (hG : Work.Drive.Final.TiltedGenericity ψ s c σ u v h ℓ exc) :
    Work.Drive.Final.TiltedGenericity ψ s c σ u v h ℓ (exc ∪ B) := by
  obtain ⟨h1, h2, h3, h4⟩ := hG
  refine ⟨?_, ?_, ?_, h4⟩
  · intro lam hlam
    exact h1 lam (fun hmem => hlam (coe_subset_union exc B hmem))
  · intro lam hlam
    exact h2 lam (fun hmem => hlam (coe_subset_union exc B hmem))
  · intro p hp hpS hd
    exact ⟨(h3 p hp hpS hd).1, Finset.mem_union_left B (h3 p hp hpS hd).2⟩

/-- **`TiltData` is monotone in `exc`**, provided the levels added to `exc` lie in the window. -/
theorem tiltData_mono_exc {ψ : Submission.Diffeo} {s u : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)}
    {v : R3} {h R : ℝ} {ℓ : R3 →L[ℝ] ℝ} {exc B : Finset ℝ} {lam0 lam1 : ℝ}
    (hT : TiltData ψ s c σ u v h R ℓ exc lam0 lam1)
    (hB : ∀ t ∈ B, lam0 < t ∧ t < lam1) :
    TiltData ψ s c σ u v h R ℓ (exc ∪ B) lam0 lam1 := by
  obtain ⟨hgen, hv1, hℓne, hℓv, hsize, hh, hRbox, hlow, hhigh, hl, hexc⟩ := hT
  refine ⟨tiltedGenericity_mono_exc hgen, hv1, hℓne, hℓv, hsize, hh, hRbox, hlow, hhigh, hl, ?_⟩
  intro t ht
  rw [Finset.mem_union] at ht
  rcases ht with ht | ht
  · exact hexc t ht
  · exact hB t ht

/-! ## Clause 1 and field `(D)` from `JunctionGenC` -/

/-- **Clause 1 at every non-exceptional level of the window, from the corrected junction bundle.**
This is `Work.Drive.Mono.traceCurvesAt_of_levelSphereDecomposition` with `JunctionGen` replaced by
`JunctionGenC` (the local models are supplied by
`Work.Drive.Mono.traceLocallyEuclidean_of_junctionGenC`, and everything else is unchanged). -/
theorem traceCurvesAt_of_levelSphereDecompositionB
    (p q : ℕ) (hp : 0 < p) (hq : 0 < q) (hc : Nat.Coprime p q)
    (ψ : Submission.Diffeo) (K : Knot)
    (himg : Set.range K.curve = Set.range
      (Work.CoreTopology.ClosedCurve.mapHomeomorph ψ.toHomeomorph
        (Work.CoreTopology.standardCurve p q)).γ)
    (hcl : Work.Drive.CleansDiscsWd (Work.Drive.EpsSphere.torusOf ψ))
    {s u : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {v : R3} {h R : ℝ} {ℓ : R3 →L[ℝ] ℝ}
    {exc : Finset ℝ} {lam0 lam1 : ℝ} (hs : 0 < s)
    (hT : TiltData ψ s c σ u v h R ℓ exc lam0 lam1)
    (hJ : JunctionGenC ψ s c σ u v h ℓ exc lam0 lam1)
    (hfaceReg : ∀ z : R3, z ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier →
      z ∈ Submission.PBox s c σ → |inner ℝ v z - (inner ℝ v c + u)| = h →
      ∃ p : ℝ × ℝ, Work.BoxShrink.Pinch.par ψ p = z ∧
        fderiv ℝ (fun q : ℝ × ℝ => inner ℝ v (Work.BoxShrink.Pinch.par ψ q)) p ≠ 0)
    (hslice : Nonempty (Work.InnermostDisk.SphereSlicing (Work.Drive.EpsSphere.torusOf ψ)
      {y : R3 | Submission.boxNorm c σ y = s}))
    (hD : LevelSphereDecomposition ψ s c σ u v h ℓ exc lam0 lam1)
    (hcount : ∀ lam ∈ Set.Icc lam0 lam1, lam ∉ (exc : Set ℝ) →
      Set.encard (Set.range K.curve ∩
        frontier (tiltedLevelRemoved s c σ u v h ℓ lam)) < (Nat.min p q : ℕ∞)) :
    ∀ lam ∈ Set.Icc lam0 lam1, lam ∉ (exc : Set ℝ) →
      TraceCurvesAt (Work.Drive.EpsSphere.torusOf ψ) s c σ u v h ℓ lam := by
  intro lam hlam hne
  obtain ⟨n, Ss, hsph, hdisj, hdecomp⟩ := hD lam hlam hne
  refine traceCurvesAt_of_sphereDecomposition' p q hp hq hc ψ K himg hcl
    (isCompact_trace_torusOf ψ s u c σ v h ℓ lam) ?_ hdecomp hdisj hsph (hcount lam hlam hne)
  exact traceLocallyEuclidean_of_junctionGenC hs hslice hfaceReg hT hJ hlam hne

/-- **Field `(D)` (Pardon's dichotomy) at every non-exceptional level of the window**, from the
corrected junction bundle, the geometric input, the slicing and the level count. -/
theorem windingSpan_bot_or_top_of_levelSphereDecompositionB
    (p q : ℕ) (hp : 0 < p) (hq : 0 < q) (hc : Nat.Coprime p q)
    (ψ : Submission.Diffeo) (K : Knot)
    (himg : Set.range K.curve = Set.range
      (Work.CoreTopology.ClosedCurve.mapHomeomorph ψ.toHomeomorph
        (Work.CoreTopology.standardCurve p q)).γ)
    (hcl : Work.Drive.CleansDiscsWd (Work.Drive.EpsSphere.torusOf ψ))
    {s u : ℝ} {c : R3} {σ : Equiv.Perm (Fin 3)} {v : R3} {h R : ℝ} {ℓ : R3 →L[ℝ] ℝ}
    {exc : Finset ℝ} {lam0 lam1 : ℝ} (hs : 0 < s)
    (hT : TiltData ψ s c σ u v h R ℓ exc lam0 lam1)
    (hJ : JunctionGenC ψ s c σ u v h ℓ exc lam0 lam1)
    (hfaceReg : ∀ z : R3, z ∈ (Work.Drive.EpsSphere.torusOf ψ).carrier →
      z ∈ Submission.PBox s c σ → |inner ℝ v z - (inner ℝ v c + u)| = h →
      ∃ p : ℝ × ℝ, Work.BoxShrink.Pinch.par ψ p = z ∧
        fderiv ℝ (fun q : ℝ × ℝ => inner ℝ v (Work.BoxShrink.Pinch.par ψ q)) p ≠ 0)
    (hslice : Nonempty (Work.InnermostDisk.SphereSlicing (Work.Drive.EpsSphere.torusOf ψ)
      {y : R3 | Submission.boxNorm c σ y = s}))
    (hD : LevelSphereDecomposition ψ s c σ u v h ℓ exc lam0 lam1)
    (hcount : ∀ lam ∈ Set.Icc lam0 lam1, lam ∉ (exc : Set ℝ) →
      Set.encard (Set.range K.curve ∩
        frontier (tiltedLevelRemoved s c σ u v h ℓ lam)) < (Nat.min p q : ℕ∞)) :
    ∀ lam ∈ Set.Icc lam0 lam1, lam ∉ (exc : Set ℝ) →
      (Work.SurgeryInvariance.WindingSpan (Work.Drive.EpsSphere.torusOf ψ)
          (Work.Drive.EpsFormSphere.openTiltedSweepRegion (Work.Drive.EpsSphere.torusOf ψ)
            s c σ u v h ℓ lam) = ⊥ ∨
        Work.SurgeryInvariance.WindingSpan (Work.Drive.EpsSphere.torusOf ψ)
          (Work.Drive.EpsFormSphere.openTiltedSweepRegion (Work.Drive.EpsSphere.torusOf ψ)
            s c σ u v h ℓ lam) = ⊤) := by
  have hv1 : ‖v‖ = 1 := hT.2.1
  have hℓv : ℓ v = 0 := hT.2.2.2.1
  have hℓne : ℓ ≠ 0 := hT.2.2.1
  have hv : v ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hv1
    exact one_ne_zero hv1.symm
  intro lam hlam hne
  exact windingSpan_bot_or_top_of_traceCurvesAt (P := Work.Drive.EpsSphere.torusOf ψ) hv hℓv hℓne
    (traceCurvesAt_of_levelSphereDecompositionB p q hp hq hc ψ K himg hcl
      hs hT hJ hfaceReg hslice hD hcount lam hlam hne)

end

end Work.Drive.Mono
