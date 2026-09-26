import Mathlib
import Submission.Work.Smooth.OneManifold.Defs
import Submission.Work.Smooth.OneManifold.Basic
import Submission.Work.Smooth.OneManifold.Classify
import Submission.Work.Smooth.OneManifold.exists_finite_component_decomposition
import Submission.Work.Smooth.SphereJordan.LocalArc.compactPreconnectedLocallyArc_isCircle
import Submission.Work.CoreTopology.Basic
import Submission.Work.CoreTopology.Disk
import Submission.Work.InnermostDisk.Slicing

namespace Work.EpsW

open LeanEval.KnotTheory.PardonDistortion
open Set

noncomputable section

/-- **A compact connected locally Euclidean subset of an arbitrary parametrised torus is a
circle.**

This is `Work.Smooth.OneManifold.exists_closedCurve_of_component` with the fixed surface
`Work.Smooth.Morse.torus ψ` replaced by an arbitrary `Work.CoreTopology.ParamTorus P`.  The only
place where the fixed surface entered the original proof is the membership `C ⊆ (torus ψ).carrier`,
which here is the hypothesis `hCsub : C ⊆ P.carrier`; the parametrisation itself plays no role in
the classification of compact connected `1`-manifolds.

`C` is parametrised by a continuous `2π`-periodic map which is injective on a fundamental period
and whose range is exactly `C`; since `C ⊆ P.carrier`, this is a `Work.CoreTopology.ClosedCurve` of
`P`, and it is simple in the sense of `Work.CoreTopology.IsSimple`. -/
theorem exists_closedCurve_of_component_param (P : Work.CoreTopology.ParamTorus) {C : Set R3}
    (hCsub : C ⊆ P.carrier) (hCcomp : IsCompact C) (hCpre : IsPreconnected C)
    (hCne : C.Nonempty) (hCloc : Work.Smooth.OneManifold.IsLocallyEuclidean C) :
    ∃ γ : Work.CoreTopology.ClosedCurve P,
      Work.CoreTopology.IsSimple P γ ∧ Set.range γ.γ = C := by
  haveI : CompactSpace C := isCompact_iff_compactSpace.mp hCcomp
  haveI : PreconnectedSpace C := Subtype.preconnectedSpace hCpre
  haveI : Nonempty C := hCne.to_subtype
  obtain ⟨γ, hcont, hper, hinj, hrange⟩ :=
    Work.Smooth.SphereJordan.LocalArc.compactPreconnectedLocallyArc_isCircle (X := C) hCloc
  let γc : Work.CoreTopology.ClosedCurve P :=
    { γ := fun t => (γ t : R3)
      cont := continuous_subtype_val.comp hcont
      periodic := fun t => congrArg Subtype.val (hper t)
      mem := fun t => hCsub (γ t).2 }
  have hsimplec : Work.CoreTopology.IsSimple P γc := by
    intro t ht t' ht' h
    exact hinj ht ht' (Subtype.ext h)
  have hrangec : Set.range γc.γ = C := by
    show Set.range (fun t : ℝ => (γ t : R3)) = C
    rw [show (fun t : ℝ => (γ t : R3)) = (fun y : C => (y : R3)) ∘ γ from
        funext fun t => rfl,
      Set.range_comp, hrange, Subtype.coe_image_univ]
  exact ⟨γc, hsimplec, hrangec⟩

open LeanEval.KnotTheory.PardonDistortion in
/-- **The classification of compact one-dimensional subsets of a parametrised torus.**  Let `P` be a parametrised torus and `Z ⊆ P.carrier` a compact subset which is locally Euclidean of dimension one.  Then `Z` is the union of the ranges of finitely many pairwise disjoint simple closed curves of `P`.

This is `Work.Smooth.OneManifold.isCircleUnion_of_isCompact_of_isLocallyEuclidean` with the fixed surface `Work.Smooth.Morse.torus ψ` replaced by an arbitrary `Work.CoreTopology.ParamTorus`: decompose `Z` into finitely many compact preconnected locally Euclidean pieces (`Work.Smooth.OneManifold.exists_finite_component_decomposition`), parametrise each piece by an injective `2π`-periodic curve (`Work.Smooth.SphereJordan.LocalArc.compactPreconnectedLocallyArc_isCircle`) and reassemble, exactly as `Work.Smooth.OneManifold.exists_closedCurve_of_component` does for `torus ψ` (the only difference being that the membership in `P.carrier` comes from `hZ`). -/
theorem exists_family_of_isCompact_of_isLocallyEuclidean {P : Work.CoreTopology.ParamTorus}
    {Z : Set R3} (hZ : Z ⊆ P.carrier) (hcomp : IsCompact Z)
    (hloc : Work.Smooth.OneManifold.IsLocallyEuclidean Z) :
    ∃ (n : ℕ) (γ : Fin n → Work.CoreTopology.ClosedCurve P),
      (∀ i : Fin n, Work.CoreTopology.IsSimple P (γ i)) ∧
      (∀ i j : Fin n, i ≠ j → Disjoint (Set.range (γ i).γ) (Set.range (γ j).γ)) ∧
      Z = ⋃ i, Set.range (γ i).γ := by
  obtain ⟨n, C, hCsub, hCne, hCpre, hCcomp, hCloc, hCdisj, hCcover⟩ :=
    Work.Smooth.OneManifold.exists_finite_component_decomposition hcomp hloc
  choose γ hγsimple hγrange using fun i =>
    exists_closedCurve_of_component_param P ((hCsub i).trans hZ) (hCcomp i) (hCpre i) (hCne i)
      (hCloc i)
  refine ⟨n, γ, hγsimple, ?_, ?_⟩
  · intro i j hij
    rw [hγrange i, hγrange j]
    exact hCdisj i j hij
  · rw [hCcover]
    exact Set.iUnion_congr fun i => (hγrange i).symm

end

end Work.EpsW
