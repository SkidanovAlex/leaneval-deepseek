import Mathlib
import Submission.Work.Drive.Final.AnyEventDefs
import Submission.Work.Drive.Final.dentOut_trace
import Submission.Work.Smooth.OneManifold.isLocallyEuclidean_of_forall

/-!
# The trace family of the deformed level at a dent

This module supplies the family `cs` of `Work.Drive.Final.DentOutResolved` from the sphere cover of
the *undeformed* level and Pardon's counting, at an event of any of the three types.

The mathematical content is in `Work.Drive.Final.dentOut_trace`:

* `Work.Drive.Final.dentOut_trace_noEssential_of_sphereCover` — the trace
  `carrier ∩ frontier (D.deform ⁻¹' tiltedLevelRemoved …)` carries no essential loop;
* `Work.Drive.Final.exists_family_of_not_containsEssentialLoop` — a compact, locally Euclidean trace
  with no essential loop is the union of finitely many pairwise disjoint simple inessential closed
  curves.

What is added here is the *topological* bookkeeping: the trace is a finite union of the traces of
the pulled-back spheres (the deformation is a homeomorphism), hence compact and locally Euclidean
(a finite union of pairwise disjoint closed locally Euclidean pieces).
-/

namespace Work.Drive.Final

open LeanEval.KnotTheory.PardonDistortion Set

noncomputable section

/-! ## A finite disjoint union of locally Euclidean pieces -/

/-- **A finite family of pairwise disjoint closed locally Euclidean pieces of the surface has a
locally Euclidean union.**

At a point `x` of the piece `F i`, the union of the *other* pieces is closed and does not contain
`x`, so its complement `U` is an open neighbourhood of `x` with `U ∩ ⋃ j, F j = F i`; the local
structure of the union at `x` is thus that of `F i`. -/
theorem isLocallyEuclidean_iUnion_of_isClosed_pairwise_disjoint {ψ : Submission.Diffeo}
    {ι : Type*} [Fintype ι] {F : ι → Set R3}
    (hsub : ∀ i, F i ⊆ (Work.Drive.EpsSphere.torusOf ψ).carrier)
    (hclosed : ∀ i, IsClosed (F i))
    (hdisj : ∀ i j : ι, i ≠ j → Disjoint (F i) (F j))
    (hloc : ∀ i, Work.Smooth.OneManifold.IsLocallyEuclidean (F i)) :
    Work.Smooth.OneManifold.IsLocallyEuclidean (⋃ i, F i) := by
  classical
  refine Work.Smooth.OneManifold.isLocallyEuclidean_of_forall_exists
    (Z := ⋃ i, F i) (Set.iUnion_subset hsub) ?_
  rintro ⟨x, hx⟩
  obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
  refine ⟨(⋃ j : {j : ι // j ≠ i}, F j.1)ᶜ, ?_, ?_, ?_⟩
  · exact ((isClosed_iUnion_of_finite (fun j : {j : ι // j ≠ i} => hclosed j.1)).isOpen_compl).preimage
      continuous_subtype_val
  · intro hxU
    obtain ⟨j, hxj⟩ := Set.mem_iUnion.mp hxU
    exact (Set.disjoint_left.mp (hdisj i j.1 (Ne.symm j.2)) hxi) hxj
  · have heq : F i = (⋃ j : {j : ι // j ≠ i}, F j.1)ᶜ ∩ (⋃ k, F k) := by
      ext y
      constructor
      · intro hyi
        refine ⟨?_, Set.mem_iUnion.mpr ⟨i, hyi⟩⟩
        intro hyU
        obtain ⟨j, hyj⟩ := Set.mem_iUnion.mp hyU
        exact (Set.disjoint_left.mp (hdisj i j.1 (Ne.symm j.2)) hyi) hyj
      · rintro ⟨hyU, hyZ⟩
        obtain ⟨j, hyj⟩ := Set.mem_iUnion.mp hyZ
        by_cases hji : j = i
        · rwa [hji] at hyj
        · exact absurd (Set.mem_iUnion.mpr ⟨⟨j, hji⟩, hyj⟩) hyU
    exact Work.Smooth.OneManifold.isLocallyEuclidean_of_eq heq (hloc i)

/-! ## The trace of the deformed level -/

/-- **The trace of the deformed level is compact.**

The deformation is a homeomorphism of `ℝ³`, so the frontier of the preimage of the removed set is
the preimage of its frontier, which is the union of the pulled-back spheres; each of these has
compact trace on the surface and the surface itself is closed. -/
theorem isCompact_carrier_inter_frontier_deform_preimage {ψ : Submission.Diffeo} {K : Knot}
    {s u h R : ℝ} {c v : R3} {σ : Equiv.Perm (Fin 3)} {ℓ : R3 →L[ℝ] ℝ} {U : Set R3}
    (D : AnyDentDatum ψ K s c σ u v h R ℓ U) (ha' : |D.a'| * D.κ < D.r)
    {m : ℕ} {Ss : Fin m → Set R3}
    (hfront : frontier (Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ (ℓ D.centre)) =
      ⋃ i, Ss i)
    (htame : ∀ i, IsCompact ((D.deform ⁻¹' Ss i) ∩
      (Work.Drive.EpsSphere.torusOf ψ).carrier)) :
    IsCompact ((Work.Drive.EpsSphere.torusOf ψ).carrier ∩
      frontier (D.deform ⁻¹' Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ (ℓ D.centre))) := by
  obtain ⟨Φ, hΦ⟩ := dentDeform_homeomorph D.κ_pos D.r_pos (le_of_eq D.d_norm) D.χ_diff
    D.χ_deriv_bound ha'
  have hdeform : D.deform = ⇑Φ := funext (fun z => (hΦ z).symm)
  have hfront' : frontier (D.deform ⁻¹'
      Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ (ℓ D.centre)) = ⋃ i, Φ ⁻¹' Ss i := by
    rw [hdeform, frontier_preimage_homeomorph, hfront, Set.preimage_iUnion]
  rw [hfront', Set.inter_iUnion]
  exact isCompact_iUnion (fun i => by simpa [hdeform, Set.inter_comm] using htame i)

/-- **The trace of the deformed level is locally Euclidean.**

It is the finite union of the traces of the pulled-back spheres, which are pairwise disjoint,
closed, compact and locally Euclidean by hypothesis. -/
theorem isLocallyEuclidean_carrier_inter_frontier_deform_preimage {ψ : Submission.Diffeo}
    {K : Knot} {s u h R : ℝ} {c v : R3} {σ : Equiv.Perm (Fin 3)} {ℓ : R3 →L[ℝ] ℝ} {U : Set R3}
    (D : AnyDentDatum ψ K s c σ u v h R ℓ U) (ha' : |D.a'| * D.κ < D.r)
    {m : ℕ} {Ss : Fin m → Set R3}
    (hsph : ∀ i, Work.InnermostDisk.IsEmbeddedSphere (Ss i))
    (hdisj : ∀ i j : Fin m, i ≠ j → Disjoint ((D.deform ⁻¹' Ss i) ∩
      (Work.Drive.EpsSphere.torusOf ψ).carrier)
      ((D.deform ⁻¹' Ss j) ∩ (Work.Drive.EpsSphere.torusOf ψ).carrier))
    (hfront : frontier (Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ (ℓ D.centre)) =
      ⋃ i, Ss i)
    (htame : ∀ i : Fin m,
      IsCompact ((D.deform ⁻¹' Ss i) ∩ (Work.Drive.EpsSphere.torusOf ψ).carrier) ∧
      Work.Smooth.OneManifold.IsLocallyEuclidean
        ((D.deform ⁻¹' Ss i) ∩ (Work.Drive.EpsSphere.torusOf ψ).carrier)) :
    Work.Smooth.OneManifold.IsLocallyEuclidean ((Work.Drive.EpsSphere.torusOf ψ).carrier ∩
      frontier (D.deform ⁻¹' Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ (ℓ D.centre))) := by
  obtain ⟨Φ, hΦ⟩ := dentDeform_homeomorph D.κ_pos D.r_pos (le_of_eq D.d_norm) D.χ_diff
    D.χ_deriv_bound ha'
  have hdeform : D.deform = ⇑Φ := funext (fun z => (hΦ z).symm)
  have hfront' : frontier (D.deform ⁻¹'
      Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ (ℓ D.centre)) = ⋃ i, Φ ⁻¹' Ss i := by
    rw [hdeform, frontier_preimage_homeomorph, hfront, Set.preimage_iUnion]
  have hunion : (Work.Drive.EpsSphere.torusOf ψ).carrier ∩
      frontier (D.deform ⁻¹' Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ (ℓ D.centre)) =
      ⋃ i, (Φ ⁻¹' Ss i ∩ (Work.Drive.EpsSphere.torusOf ψ).carrier) := by
    rw [hfront', Set.inter_iUnion]
    exact Set.iUnion_congr (fun i => Set.inter_comm _ _)
  have hU : Work.Smooth.OneManifold.IsLocallyEuclidean
      (⋃ i, (Φ ⁻¹' Ss i ∩ (Work.Drive.EpsSphere.torusOf ψ).carrier)) := by
    refine isLocallyEuclidean_iUnion_of_isClosed_pairwise_disjoint (ψ := ψ)
      (F := fun i => Φ ⁻¹' Ss i ∩ (Work.Drive.EpsSphere.torusOf ψ).carrier)
      (fun i => Set.inter_subset_right) (fun i => ?_) (fun i j hij => ?_) (fun i => ?_)
    · exact ((isClosed_of_isEmbeddedSphere (hsph i)).preimage Φ.continuous).inter
        (Work.CoreTopology.isClosed_carrier _)
    · have h := hdisj i j hij
      rwa [hdeform] at h
    · have h := htame i
      rw [← hdeform]
      exact h.2
  exact Work.Smooth.OneManifold.isLocallyEuclidean_of_eq hunion.symm hU

/-! ## The family -/

theorem exists_dentOut_trace_family {ψ : Submission.Diffeo} {K : Knot} {s u h R : ℝ}
    {c v : R3} {σ : Equiv.Perm (Fin 3)} {ℓ : R3 →L[ℝ] ℝ} {U : Set R3}
    (p q : ℕ) (hp : 0 < p) (hq : 0 < q) (hc : Nat.Coprime p q)
    (himg : Set.range K.curve = Set.range
      (Work.CoreTopology.ClosedCurve.mapHomeomorph ψ.toHomeomorph
        (Work.CoreTopology.standardCurve p q)).γ)
    (hcl : Work.Drive.CleansDiscsWd (Work.Drive.EpsSphere.torusOf ψ))
    (D : Work.Drive.Final.AnyDentDatum ψ K s c σ u v h R ℓ U) (ha' : |D.a'| * D.κ < D.r)
    {m : ℕ} {Ss : Fin m → Set R3}
    (hsph : ∀ i, Work.InnermostDisk.IsEmbeddedSphere (Ss i))
    (hdisj : ∀ i j : Fin m, i ≠ j → Disjoint ((D.deform ⁻¹' Ss i) ∩
      (Work.Drive.EpsSphere.torusOf ψ).carrier)
      ((D.deform ⁻¹' Ss j) ∩ (Work.Drive.EpsSphere.torusOf ψ).carrier))
    (hfront : frontier (Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ (ℓ D.centre)) = ⋃ i, Ss i)
    (hcount : (Set.range K.curve ∩ frontier (Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ
      (ℓ D.centre))).encard < (Nat.min p q : ℕ∞))
    (htame : ∀ i : Fin m,
      IsCompact ((D.deform ⁻¹' Ss i) ∩ (Work.Drive.EpsSphere.torusOf ψ).carrier) ∧
      Work.Smooth.OneManifold.IsLocallyEuclidean
        ((D.deform ⁻¹' Ss i) ∩ (Work.Drive.EpsSphere.torusOf ψ).carrier)) :
    ∃ (n : ℕ) (cs : Fin n → Work.CoreTopology.ClosedCurve (Work.Drive.EpsSphere.torusOf ψ)),
      (∀ i, Work.CoreTopology.IsSimple (Work.Drive.EpsSphere.torusOf ψ) (cs i)) ∧
      (∀ i, ¬ Work.CoreTopology.IsEssential (Work.Drive.EpsSphere.torusOf ψ) (cs i)) ∧
      (∀ i j : Fin n, i ≠ j → Disjoint (Set.range (cs i).γ) (Set.range (cs j).γ)) ∧
      ((Work.Drive.EpsSphere.torusOf ψ).carrier ∩
        frontier (D.deform ⁻¹' Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ (ℓ D.centre)) =
        ⋃ i, Set.range (cs i).γ) := by
  have hcomp : IsCompact ((Work.Drive.EpsSphere.torusOf ψ).carrier ∩
      frontier (D.deform ⁻¹' Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ (ℓ D.centre))) :=
    isCompact_carrier_inter_frontier_deform_preimage D ha' hfront (fun i => (htame i).1)
  have hloc : Work.Smooth.OneManifold.IsLocallyEuclidean ((Work.Drive.EpsSphere.torusOf ψ).carrier ∩
      frontier (D.deform ⁻¹' Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ (ℓ D.centre))) :=
    isLocallyEuclidean_carrier_inter_frontier_deform_preimage D ha' hsph hdisj hfront htame
  have hnoF : ¬ (Work.Drive.EpsSphere.torusOf ψ).ContainsEssentialLoop
      (frontier (D.deform ⁻¹'
        Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ (ℓ D.centre))) :=
    dentOut_trace_noEssential_of_sphereCover p q hp hq hc himg hcl D ha' hsph hdisj hfront
      hcount htame
  have hno : ¬ (Work.Drive.EpsSphere.torusOf ψ).ContainsEssentialLoop
      ((Work.Drive.EpsSphere.torusOf ψ).carrier ∩ frontier (D.deform ⁻¹'
        Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ (ℓ D.centre))) :=
    fun h => hnoF (Work.CoreTopology.ParamTorus.containsEssentialLoop_mono _
      Set.inter_subset_right h)
  obtain ⟨n, cs, hsimple, hess, hdisj', hcover⟩ :=
    exists_family_of_not_containsEssentialLoop (P := Work.Drive.EpsSphere.torusOf ψ)
      (Z := (Work.Drive.EpsSphere.torusOf ψ).carrier ∩ frontier (D.deform ⁻¹'
        Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ (ℓ D.centre)))
      Set.inter_subset_left hcomp hloc hno
  exact ⟨n, cs, hsimple, hess, hdisj', hcover⟩

end

end Work.Drive.Final
