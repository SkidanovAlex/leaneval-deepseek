import Mathlib
import Submission.Work.Drive.TParity.Basic
import Submission.Work.Drive.TParity.LocalGraph
import Submission.Work.Drive.TParity.ChartDeriv

/-!
# The face condition along the triple intersection set

`Work.Drive.TParity.face_data_K3`: for three smooth chains `D 0, D 1, D 2` in a smooth `4`-manifold
which meet transversally (`transHyp`) and which cross the faces of the nine-box in the prescribed
way (`faceHyp`), every field `V` along the triple intersection set which is tangential (`Vtan`) and
nowhere zero (`Vne`) crosses the face of the nine-box at every boundary triple intersection
(`Vface`).

The point of the proof is that at a triple intersection point `b` the charted difference map
`chartDiff3 p D` is a submersion `ℝ⁹ → ℝ⁸` (transversality), so its kernel is one-dimensional; both
`V b` (`Vtan`) and the common direction `mk3 v` supplied by `faceHyp` lie in that kernel, hence they
are proportional, and the proportionality constant is non-zero because `V b ≠ 0` (`Vne`).  The
`i`-th coordinate of a common direction being non-zero (the transversality part of `faceHyp`) is
therefore inherited by `V b`.
-/

namespace Work.Drive.TParity

open scoped Manifold ContDiff Topology
open Manifold Set

noncomputable section

/-- **Two vectors in the kernel of a surjective map between finite-dimensional spaces whose
dimensions differ by one are proportional.**  The kernel of such a map is one-dimensional, so any
non-zero kernel vector spans it. -/
theorem eq_smul_of_mem_ker {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    (L : E →L[ℝ] F) (hL : Function.Surjective L)
    (hdim : Module.finrank ℝ E = Module.finrank ℝ F + 1)
    {w v : E} (hw : L w = 0) (hv : L v = 0) (hne : v ≠ 0) : ∃ c : ℝ, w = c • v := by
  have hran : LinearMap.range (L : E →ₗ[ℝ] F) = ⊤ := LinearMap.range_eq_top.mpr hL
  have h1 := LinearMap.finrank_range_add_finrank_ker (L : E →ₗ[ℝ] F)
  rw [hran, finrank_top] at h1
  have hk : Module.finrank ℝ ↥(LinearMap.ker (L : E →ₗ[ℝ] F)) = 1 := by omega
  have hvK : v ∈ LinearMap.ker (L : E →ₗ[ℝ] F) := LinearMap.mem_ker.mpr hv
  have hspan_le : ℝ ∙ v ≤ LinearMap.ker (L : E →ₗ[ℝ] F) := by
    rw [Submodule.span_le]
    simpa using hvK
  have hfin : Module.finrank ℝ ↥(ℝ ∙ v) =
      Module.finrank ℝ ↥(LinearMap.ker (L : E →ₗ[ℝ] F)) := by
    rw [finrank_span_singleton hne, hk]
  have heq := Submodule.eq_of_le_of_finrank_eq hspan_le hfin
  have hwK : w ∈ LinearMap.ker (L : E →ₗ[ℝ] F) := LinearMap.mem_ker.mpr hw
  have hwv : w ∈ ℝ ∙ v := heq ▸ hwK
  rw [Submodule.mem_span_singleton] at hwv
  obtain ⟨c, hc⟩ := hwv
  exact ⟨c, hc.symm⟩

/-- The kernel of the derivative of the charted difference map of the nine-box at any point of the
chart region at which it is a submersion (`ℝ⁹ → ℝ⁸`) is one-dimensional; hence any two of its
kernel vectors with one of them non-zero are proportional. -/
theorem eq_smul_of_mem_ker_chartDiff3 {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    (D : Fin 3 → EuclideanSpace ℝ (Fin 3) → M)
    (p : M) (b : Amb 8)
    (hsurj : Function.Surjective (fderiv ℝ (chartDiff3 p D) b))
    {w v : Amb 8} (hw : fderiv ℝ (chartDiff3 p D) b w = 0)
    (hv : fderiv ℝ (chartDiff3 p D) b v = 0) (hne : v ≠ 0) : ∃ c : ℝ, w = c • v := by
  refine eq_smul_of_mem_ker _ hsurj ?_ hw hv hne
  rw [finrank_euclideanSpace, finrank_euclideanSpace]
  simp

theorem face_data_K3 {M : Type*} [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanSpace ℝ (Fin 4)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    (D : Fin 3 → EuclideanSpace ℝ (Fin 3) → M)
    (hD : ∀ k, ContMDiff (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 3)))
      (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 4))) ((⊤ : ℕ∞) : WithTop ℕ∞) (D k))
    (htrans : Work.Drive.TParity.transHyp D) (hface : Work.Drive.TParity.faceHyp D)
    (V : Work.Drive.Amb 8 → Work.Drive.Amb 8)
    (hVtan : Work.Drive.TParity.Vtan D V) (hVne : Work.Drive.TParity.Vne D V) :
    Work.Drive.TParity.Vface D V := by
  intro b hbK hbBdry
  obtain ⟨hbox, hmeet⟩ := mem_K3.mp hbK
  obtain ⟨k, i', hbi, hinside, hinside', v, hvcd, hvi⟩ := hface b hbox hmeet hbBdry
  refine ⟨Work.Drive.bIdx k i', hbi, ?_, ?_⟩
  · -- every other coordinate of the nine-box is strictly inside
    intro j hj
    obtain ⟨k', j', hkj⟩ : ∃ (k' j' : Fin 3), Work.Drive.bIdx k' j' = j :=
      ⟨⟨j.val / 3, by omega⟩, ⟨j.val % 3, by omega⟩, by
        ext
        rw [Work.Drive.bIdx_val]
        have h := Nat.mod_add_div j.val 3
        omega⟩
    rw [← hkj]
    by_cases hkk : k' = k
    · subst hkk
      exact hinside j' (fun h => hj (by rw [← hkj, h]))
    · exact hinside' k' hkk j'
  · -- the coordinate of the common direction survives to `V b`
    set i := Work.Drive.bIdx k i' with hi
    have hp : b ∈ Work.Drive.TParity.region3 (D 0 (Work.Drive.TParity.bPartC 0 b)) D :=
      Work.Drive.TParity.mem_region3_self D hmeet
    have hsurj : Function.Surjective
        (fderiv ℝ (Work.Drive.TParity.chartDiff3 (D 0 (Work.Drive.TParity.bPartC 0 b)) D) b) :=
      Work.Drive.TParity.chartDiff3_surj D hD hp hmeet (htrans b hbox hmeet)
    have hVker : fderiv ℝ (Work.Drive.TParity.chartDiff3 (D 0 (Work.Drive.TParity.bPartC 0 b)) D) b
        (V b) = 0 := hVtan b hbK (D 0 (Work.Drive.TParity.bPartC 0 b)) hp
    have hzker : fderiv ℝ (Work.Drive.TParity.chartDiff3 (D 0 (Work.Drive.TParity.bPartC 0 b)) D) b
        (Work.Drive.TParity.mk3 v) = 0 :=
      Work.Drive.TParity.chartDiff3_eq_zero_of_commonDir (D 0 (Work.Drive.TParity.bPartC 0 b)) D
        hD hp hmeet hvcd
    have hzne : Work.Drive.TParity.mk3 v ≠ 0 :=
      (Work.Drive.TParity.mk3_ne_zero_iff v).mpr ⟨k, i', hvi⟩
    obtain ⟨c, hc⟩ :=
      Work.Drive.TParity.eq_smul_of_mem_ker_chartDiff3 D _ b hsurj hVker hzker hzne
    have hcne : c ≠ 0 := by
      intro h0
      exact hVne b hbK (by rw [hc, h0, zero_smul])
    have hcoord : (V b) i = c * (Work.Drive.TParity.mk3 v) i := by
      rw [hc]
      rfl
    rw [hcoord, Work.Drive.TParity.mk3_bIdx]
    exact mul_ne_zero hcne hvi

end

end Work.Drive.TParity
