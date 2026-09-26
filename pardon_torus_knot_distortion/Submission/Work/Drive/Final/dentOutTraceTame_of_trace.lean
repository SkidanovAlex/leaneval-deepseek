import Mathlib
import Submission.Work.Drive.Final.dentOut_trace
import Submission.Work.Drive.Final.dentOut_hgen
import Submission.Work.Smooth.OneManifold.Basic

/-!
# L4b, reduced to the tameness of the whole trace

`Work.Drive.Final.DentOutTraceTame D Ss` — L4b, the tameness of the trace of each pulled-back sphere —
follows from the tameness of the **whole** trace of the deformed removed set, together with the facts
that the pulled-back spheres cover its frontier and are pairwise disjoint on the surface.

The proof is finite-disjoint-union bookkeeping: the trace is the finite union of the pieces
`D.deform ⁻¹' Ss i ∩ carrier` (the homeomorphism `D.deform` carries the frontier to the union of the
spheres), each piece is closed (an embedded sphere is closed and the deformation is continuous) and
hence **compact** as a closed subset of the compact trace, and each is **open in the trace** (its
complement in the trace is the union of the other, closed, pieces), so it is locally Euclidean by
`Work.Smooth.OneManifold.IsLocallyEuclidean.of_isOpenIn`.
-/

open LeanEval.KnotTheory.PardonDistortion Set

namespace Work.Drive.Final

noncomputable section

/-! ## A finite disjoint closed cover: each piece is open in the union -/

/-- **In a finite cover by pairwise disjoint closed sets, every piece is open in the union.** -/
theorem isOpenInSet_of_isClosed_pairwiseDisjoint_iUnion {ι : Type*} [Fintype ι]
    {P : ι → Set R3} {Z : Set R3} (hclosed : ∀ i, IsClosed (P i))
    (hdisj : Pairwise fun i j => Disjoint (P i) (P j))
    (hZ : Z = ⋃ i, P i) (i : ι) :
    Work.Smooth.OneManifold.IsOpenInSet Z (P i) := by
  classical
  set O : Set R3 := ⋃ j ∈ (Finset.univ.erase i), P j with hO
  have hOclosed : IsClosed O := by
    rw [hO]
    exact isClosed_biUnion_finset fun j _ => hclosed j
  have hPeq : (Subtype.val ⁻¹' P i : Set Z) = (Subtype.val ⁻¹' O : Set Z)ᶜ := by
    ext z
    rw [Set.mem_preimage, Set.mem_compl_iff, Set.mem_preimage, hO]
    constructor
    · intro hz hmem
      obtain ⟨j, hj, hzj⟩ := Set.mem_iUnion₂.mp hmem
      have hji : j ≠ i := (Finset.mem_erase.mp hj).1
      exact Set.disjoint_left.mp (hdisj hji) hzj hz
    · intro hz
      by_contra hPi
      set x : R3 := (z : R3) with hx
      have hxZ : x ∈ Z := z.2
      rw [hZ] at hxZ
      obtain ⟨j, hzj⟩ := Set.mem_iUnion.mp hxZ
      have hji : j ≠ i := by rintro rfl; exact hPi hzj
      have hmemO : x ∈ O :=
        Set.mem_iUnion₂.mpr ⟨j, Finset.mem_erase.mpr ⟨hji, Finset.mem_univ j⟩, hzj⟩
      exact hz hmemO
  show IsOpen (Subtype.val ⁻¹' (P i) : Set Z)
  rw [hPeq]
  simpa [Set.preimage_compl] using
    (hOclosed.isOpen_compl.preimage continuous_subtype_val)
    -- `IsOpen ((Subtype.val ⁻¹' O)ᶜ)`

/-- **L4b from the tameness of the whole trace.** -/
theorem dentOutTraceTame_of_trace {ψ : Submission.Diffeo} {K : Knot} {s u h R : ℝ} {c v : R3}
    {σ : Equiv.Perm (Fin 3)} {ℓ : R3 →L[ℝ] ℝ} {U : Set R3}
    (D : AnyDentDatum ψ K s c σ u v h R ℓ U) {m : ℕ} {Ss : Fin m → Set R3}
    (hsph : ∀ i, Work.InnermostDisk.IsEmbeddedSphere (Ss i))
    (ha : |D.a'| * D.κ < D.r)
    (hfront : frontier (Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ (ℓ D.centre)) = ⋃ i, Ss i)
    (hpd : ∀ i j : Fin m, i ≠ j →
      Disjoint ((D.deform ⁻¹' Ss i) ∩ (Work.Drive.EpsSphere.torusOf ψ).carrier)
        ((D.deform ⁻¹' Ss j) ∩ (Work.Drive.EpsSphere.torusOf ψ).carrier))
    (hT : IsCompact ((Work.Drive.EpsSphere.torusOf ψ).carrier ∩
        frontier (D.deform ⁻¹' Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ (ℓ D.centre))) ∧
      Work.Smooth.OneManifold.IsLocallyEuclidean ((Work.Drive.EpsSphere.torusOf ψ).carrier ∩
        frontier (D.deform ⁻¹' Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ (ℓ D.centre)))) :
    DentOutTraceTame D Ss := by
  classical
  obtain ⟨Φ, hΦ⟩ := dentDeform_homeomorph D.κ_pos D.r_pos (le_of_eq D.d_norm) D.χ_diff
    D.χ_deriv_bound ha
  have hdeform : D.deform = ⇑Φ := by
    funext z; exact (hΦ z).symm
  -- the trace is the union of the pieces
  have hunion : (Work.Drive.EpsSphere.torusOf ψ).carrier ∩
      frontier (D.deform ⁻¹' Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ (ℓ D.centre)) =
      ⋃ i, ((D.deform ⁻¹' Ss i) ∩ (Work.Drive.EpsSphere.torusOf ψ).carrier) := by
    rw [hdeform, frontier_preimage_homeomorph, hfront, Set.preimage_iUnion]
    ext z
    simp only [Set.mem_inter_iff, Set.mem_iUnion, Set.mem_preimage]
    constructor
    · rintro ⟨hz, i, hi⟩
      exact ⟨i, hi, hz⟩
    · rintro ⟨i, hi, hz⟩
      exact ⟨hz, i, hi⟩
  intro i
  have hTsub : ((D.deform ⁻¹' Ss i) ∩ (Work.Drive.EpsSphere.torusOf ψ).carrier) ⊆
      (Work.Drive.EpsSphere.torusOf ψ).carrier ∩
      frontier (D.deform ⁻¹' Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ (ℓ D.centre)) := by
    rw [hunion]
    exact Set.subset_iUnion (fun j => (D.deform ⁻¹' Ss j) ∩
      (Work.Drive.EpsSphere.torusOf ψ).carrier) i
  have hTic : IsClosed ((D.deform ⁻¹' Ss i) ∩
      (Work.Drive.EpsSphere.torusOf ψ).carrier) :=
    ((isClosed_of_isEmbeddedSphere (hsph i)).preimage (continuous_anyDentDatum_deform D)).inter
      (Work.CoreTopology.isClosed_carrier _)
  have hcomp : IsCompact ((D.deform ⁻¹' Ss i) ∩
      (Work.Drive.EpsSphere.torusOf ψ).carrier) := hT.1.of_isClosed_subset hTic hTsub
  have hclosed : ∀ j : Fin m, IsClosed ((D.deform ⁻¹' Ss j) ∩
      (Work.Drive.EpsSphere.torusOf ψ).carrier) := fun j =>
    ((isClosed_of_isEmbeddedSphere (hsph j)).preimage (continuous_anyDentDatum_deform D)).inter
      (Work.CoreTopology.isClosed_carrier _)
  have hopen : Work.Smooth.OneManifold.IsOpenInSet
      ((Work.Drive.EpsSphere.torusOf ψ).carrier ∩
        frontier (D.deform ⁻¹' Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ (ℓ D.centre)))
      ((D.deform ⁻¹' Ss i) ∩ (Work.Drive.EpsSphere.torusOf ψ).carrier) :=
    isOpenInSet_of_isClosed_pairwiseDisjoint_iUnion
      (P := fun j : Fin m => (D.deform ⁻¹' Ss j) ∩ (Work.Drive.EpsSphere.torusOf ψ).carrier)
      (Z := (Work.Drive.EpsSphere.torusOf ψ).carrier ∩
        frontier (D.deform ⁻¹' Work.Drive.Mono.tiltedLevelRemoved s c σ u v h ℓ (ℓ D.centre)))
      hclosed (fun j k hjk => hpd j k hjk) hunion i
  exact ⟨hcomp, hT.2.of_isOpenIn hTsub hopen⟩

end

end Work.Drive.Final
