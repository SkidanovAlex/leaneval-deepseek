import Mathlib
import Submission.Work.Noncompact.CompressionTube.Defs
import Submission.Work.Noncompact.CompressionTube.FromTubeSetup
import Submission.Work.Noncompact.CompressionTube.tubePhi_injective
import Submission.Work.Compat.MFDerivCongrV433

/-!
# The compression of the domain from the tube datum

`Work.Noncompact.CompressionTube.fromTube`: given a non-compact smooth `n`-manifold
(`n ≥ 2`) together with the tube datum `T : CompressionTube n M B` (a locally finite family of
pairwise disjoint tubes to infinity, one through every point of `B`), there is a smooth
self-embedding `φ : M → M` whose derivative is injective everywhere and whose image's closure
avoids `B`.

The map is `Work.Noncompact.CompressionTube.tubePhi T` of `FromTubeSetup.lean`: it is the identity
outside the tubes and the conjugate `tube i ∘ F ∘ (tube i)⁻¹` of the shear
`F (u,s) = (u, (1 - χ u) s + χ u g s)` on the tube `i`.  Since `F` is the identity for
`‖u‖ ≥ 1` and the frontier of a tube is approached only with `‖u‖ > 1` (this is
`tubePhi_eventuallyEq_id_of_notMem_thin`, which uses `escapes` and `T2Space M`), the map is
smooth; the shear is injective and an immersion, so `tubePhi T` is injective and an immersion, and
being injective and open it is an embedding.  Finally the shear sends the core `u = 0` of every
tube into `|s| < 1/2`, so the tube-wise open set `{‖u‖ < 1/2, |s| > 1/2}`, which contains `B` by
`covers`, is disjoint from the image of `tubePhi T`.
-/

namespace Work.Noncompact.CompressionTube

open scoped Manifold ContDiff
open Topology Set Function

theorem fromTube {n : ℕ} (hn : 2 ≤ n) {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    [T2Space M]
    {B : Set M} (T : Work.Noncompact.CompressionTube n M B) :
    ∃ φ : M → M,
      ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
        (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) φ ∧
      Topology.IsEmbedding φ ∧
      (∀ x, Function.Injective
        (mfderiv (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n)))
          (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) φ x)) ∧
      B ∩ closure (Set.range φ) = ∅ := by
  classical
  have hn1 : 1 ≤ n := by omega
  -- ## Smoothness
  have hsm : ContMDiff (𝓡 n) (𝓡 n) ((⊤ : ℕ∞) : WithTop ℕ∞) (tubePhi T) := by
    intro x
    by_cases hx : x ∈ ⋃ i, tubeThin T i
    · obtain ⟨i, p, hp1, hyp⟩ := Set.mem_iUnion.mp hx
      subst hyp
      obtain ⟨Ψ, hsrc, hpoint⟩ := tubePhi_exists_localInverse T hn1 i p
      have hat : ContMDiffAt (𝓡 n) (𝓡 n) ∞ (fun y => T.tube i (tubeF n (Ψ y)))
          (T.tube i p) :=
        (T.contMDiff_tube i).contMDiffAt.comp (T.tube i p)
          ((tubeF_contMDiff n).contMDiffAt.comp (T.tube i p)
            (Ψ.contMDiffOn.contMDiffAt (Ψ.open_source.mem_nhds hsrc)))
      refine hat.congr_of_eventuallyEq ?_
      exact Filter.eventuallyEq_of_mem (Ψ.open_source.mem_nhds hsrc) hpoint
    · have heq : tubePhi T =ᶠ[𝓝 x] id := tubePhi_eventuallyEq_id_of_notMem_thin T hx
      exact contMDiffAt_id.congr_of_eventuallyEq heq
  -- ## Immersion
  have himm : ∀ x : M, Function.Injective (mfderiv (𝓡 n) (𝓡 n) (tubePhi T) x) := by
    intro x
    by_cases hx : x ∈ ⋃ i, tubeThin T i
    · obtain ⟨i, p, hp1, hyp⟩ := Set.mem_iUnion.mp hx
      subst hyp
      obtain ⟨Ψ, hsrc, hpoint⟩ := tubePhi_exists_localInverse T hn1 i p
      have heq : tubePhi T =ᶠ[𝓝 (T.tube i p)] (fun y => T.tube i (tubeF n (Ψ y))) :=
        Filter.eventuallyEq_of_mem (Ψ.open_source.mem_nhds hsrc) hpoint
      have hΨat : IsLocalDiffeomorphAt (𝓡 n) ((𝓡 (n - 1)).prod 𝓘(ℝ, ℝ)) ∞ Ψ (T.tube i p) :=
        PartialDiffeomorph.isLocalDiffeomorphAt (𝓡 n) ((𝓡 (n - 1)).prod 𝓘(ℝ, ℝ)) ∞ Ψ hsrc
      have hFat : IsLocalDiffeomorphAt ((𝓡 (n - 1)).prod 𝓘(ℝ, ℝ))
          ((𝓡 (n - 1)).prod 𝓘(ℝ, ℝ)) ∞ (tubeF n) (Ψ (T.tube i p)) :=
        tubeF_isLocalDiffeomorph n _
      have hTat : IsLocalDiffeomorphAt ((𝓡 (n - 1)).prod 𝓘(ℝ, ℝ)) (𝓡 n) ∞ (T.tube i)
          (tubeF n (Ψ (T.tube i p))) := tube_isLocalDiffeomorph T hn1 i _
      have hcomp : IsLocalDiffeomorphAt (𝓡 n) (𝓡 n) ∞
          (fun y => T.tube i (tubeF n (Ψ y))) (T.tube i p) :=
        (hΨat.comp ((𝓡 (n - 1)).prod 𝓘(ℝ, ℝ))
            (EuclideanSpace ℝ (Fin (n - 1)) × ℝ) hFat).comp (𝓡 n) M hTat
      have hinj : Function.Injective
          (mfderiv (𝓡 n) (𝓡 n) (fun y => T.tube i (tubeF n (Ψ y))) (T.tube i p)) :=
        (hcomp.mfderivToContinuousLinearEquiv (by norm_num)).injective
      rwa [← heq.mfderiv_eq_v433] at hinj
    · have heq : tubePhi T =ᶠ[𝓝 x] id := tubePhi_eventuallyEq_id_of_notMem_thin T hx
      rw [heq.mfderiv_eq_v433, mfderiv_id]
      exact fun a b hab => hab
  -- ## Openness
  have hopen : IsOpenMap (tubePhi T) := by
    intro W hW
    rw [isOpen_iff_mem_nhds]
    rintro z ⟨y, hyW, rfl⟩
    by_cases hy : y ∈ ⋃ i, tubeThin T i
    · obtain ⟨i, p, hp1, hyp⟩ := Set.mem_iUnion.mp hy
      subst hyp
      obtain ⟨Ψ, hsrc, hpoint⟩ := tubePhi_exists_localInverse T hn1 i p
      have hW' : IsOpen (W ∩ Ψ.source) := hW.inter Ψ.open_source
      have himg1 : IsOpen (Ψ '' (W ∩ Ψ.source)) :=
        Ψ.toOpenPartialHomeomorph.isOpen_image_of_subset_source hW' inter_subset_right
      have himg2 : IsOpen (tubeF n '' (Ψ '' (W ∩ Ψ.source))) :=
        (tubeF_isLocalDiffeomorph n).isOpenMap _ himg1
      have himg3 : IsOpen (T.tube i '' (tubeF n '' (Ψ '' (W ∩ Ψ.source)))) :=
        (tube_isLocalDiffeomorph T hn1 i).isOpenMap _ himg2
      refine Filter.mem_of_superset (himg3.mem_nhds ?_) ?_
      · exact ⟨tubeF n (Ψ (T.tube i p)),
          ⟨Ψ (T.tube i p), ⟨T.tube i p, ⟨hyW, hsrc⟩, rfl⟩, rfl⟩, (hpoint _ hsrc).symm⟩
      · rintro z ⟨q, ⟨r, ⟨s, hs, rfl⟩, rfl⟩, rfl⟩
        exact ⟨s, hs.1, hpoint s hs.2⟩
    · have heq : tubePhi T =ᶠ[𝓝 y] id := tubePhi_eventuallyEq_id_of_notMem_thin T hy
      obtain ⟨s, hs, hEqOn⟩ := Filter.eventuallyEq_iff_exists_mem.mp heq
      obtain ⟨O, hOs, hOopen, hyO⟩ := mem_nhds_iff.mp hs
      have hyφ : tubePhi T y = y := hEqOn (hOs hyO)
      rw [hyφ]
      refine Filter.mem_of_superset ((hOopen.inter hW).mem_nhds ⟨hyO, hyW⟩) ?_
      rintro z ⟨hzO, hzW⟩
      exact ⟨z, hzW, hEqOn (hOs hzO)⟩
  -- ## The omission
  have homit : B ∩ closure (Set.range (tubePhi T)) = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    rintro b ⟨hbB, hbcl⟩
    -- `b` lies on the core `u = 0` of a tube, at height `|s| ≥ 1`
    obtain ⟨i, q, hq, hqb⟩ := Set.mem_iUnion.mp (T.covers hbB)
    obtain ⟨hq1, hq2⟩ := hq
    -- the open piece of the tube `i` around `b`
    set Q : Set (EuclideanSpace ℝ (Fin (n - 1)) × ℝ) := {p | ‖p.1‖ < 1 / 2 ∧ 1 / 2 < |p.2|}
      with hQ
    have hQopen : IsOpen Q := by
      rw [hQ]
      exact (isOpen_lt (continuous_norm.comp continuous_fst) continuous_const).inter
        (isOpen_lt continuous_const (continuous_abs.comp continuous_snd))
    have hqQ : q ∈ Q := by
      refine ⟨?_, ?_⟩
      · rw [hq1]; norm_num
      · linarith [hq2]
    have hbQ : b ∈ T.tube i '' Q := ⟨q, hqQ, hqb⟩
    have hOopen : IsOpen (T.tube i '' Q) := (tube_isLocalDiffeomorph T hn1 i).isOpenMap _ hQopen
    -- the image of the compression misses that piece
    have hdisj : ∀ y : M, tubePhi T y ∉ T.tube i '' Q := by
      intro y hy
      obtain ⟨r, hrQ, hrtube⟩ := hy
      have hyr : ∃ j : T.ι, y ∈ Set.range (T.tube j) := by
        by_contra hcon
        have hcon' : ∀ j : T.ι, y ∉ Set.range (T.tube j) := fun j hj => hcon ⟨j, hj⟩
        rw [tubePhi_eq_self_of_notMem_range T hcon'] at hrtube
        exact hcon ⟨i, ⟨r, hrtube⟩⟩
      obtain ⟨j, hj⟩ := hyr
      obtain ⟨s, hjs⟩ := hj
      have hji : j = i := by
        by_contra hne
        have hmem : T.tube i r ∈ Set.range (T.tube i) ∩ Set.range (T.tube j) :=
          ⟨⟨r, rfl⟩, ⟨tubeF n s, by
            rw [← tubePhi_apply_tube T j s, hjs]
            exact hrtube.symm⟩⟩
        exact (Set.disjoint_left.mp (T.disjoint i j (fun h : i = j => hne h.symm))) hmem.1 hmem.2
      rw [hji] at hjs
      -- so `y = tube i s` and `tube i r = tubePhi T y = tube i (tubeF n s)`
      have hr_eq : tubeF n s = r := by
        have h1 : tubePhi T y = T.tube i (tubeF n s) := by
          rw [← hjs]; exact tubePhi_apply_tube T i s
        exact ((T.isEmbedding_tube i).injective (hrtube.trans h1)).symm
      have hs1 : ‖s.1‖ < 1 / 2 := by
        rw [← tubeF_fst n s, hr_eq]
        exact hrQ.1
      have hr2 : |r.2| < 1 / 2 := by
        rw [← hr_eq, tubeF_eq_small n (le_of_lt hs1)]
        exact tubeG_abs_lt _
      exact absurd hrQ.2 (not_lt.mpr (le_of_lt hr2))
    have hOdisj : (T.tube i '' Q) ∩ Set.range (tubePhi T) = ∅ := by
      rw [Set.eq_empty_iff_forall_notMem]
      rintro z ⟨hzO, hzr⟩
      obtain ⟨y, rfl⟩ := hzr
      exact hdisj y hzO
    have hsub : Set.range (tubePhi T) ⊆ (T.tube i '' Q)ᶜ := by
      intro z hz
      rw [Set.mem_compl_iff]
      intro hzO
      exact (Set.eq_empty_iff_forall_notMem.mp hOdisj) z ⟨hzO, hz⟩
    exact ((closure_minimal hsub hOopen.isClosed_compl) hbcl) hbQ
  exact ⟨tubePhi T, hsm,
    (IsOpenEmbedding.of_continuous_injective_isOpenMap hsm.continuous (tubePhi_injective T)
      hopen).isEmbedding,
    himm, homit⟩

end Work.Noncompact.CompressionTube
