import Mathlib
import Submission.Work.Noncompact.CompressionTube.Defs
import Submission.Work.Noncompact.CompressionTube.FromTubeSetup

namespace Work.Noncompact.CompressionTube

/-- The compression `tubePhi T : M → M` is injective: outside the tubes it is the identity, on the
tube `i` it is the conjugate of the injective shear `F` (`tubePhi_apply_tube`), and the tubes have
pairwise disjoint images. -/
theorem tubePhi_injective {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin n))) ((⊤ : ℕ∞) : WithTop ℕ∞) M]
    {B : Set M} (T : Work.Noncompact.CompressionTube n M B) :
    Function.Injective (Work.Noncompact.CompressionTube.tubePhi T) := by
  intro x y hxy
  -- The image of a point of the tube `i` lies again on the tube `i` (`tubePhi_apply_tube`), so
  -- `tubePhi T` maps the union of the tubes into itself and its complement into itself.
  by_cases hx : ∃ i : T.ι, x ∈ Set.range (T.tube i)
  · by_cases hy : ∃ j : T.ι, y ∈ Set.range (T.tube j)
    · -- both points on tubes: use the injectivity of the shear, and disjointness of the tubes
      obtain ⟨i, p, rfl⟩ := hx
      obtain ⟨j, q, rfl⟩ := hy
      rw [tubePhi_apply_tube T i p, tubePhi_apply_tube T j q] at hxy
      rcases eq_or_ne i j with hij | hij
      · subst hij
        have hF : tubeF n p = tubeF n q := (T.isEmbedding_tube i).injective hxy
        have hpq : p = q := tubeF_injective n hF
        rw [hpq]
      · exact ((Set.disjoint_left.mp (T.disjoint i j hij))
          ⟨tubeF n p, rfl⟩ ⟨tubeF n q, hxy.symm⟩).elim
    · push Not at hy
      -- `tubePhi T y = y` lies on no tube, while `tubePhi T x` lies on the tube `i`
      rw [tubePhi_eq_self_of_notMem_range T hy] at hxy
      obtain ⟨i, p, hp⟩ := hx
      rw [← hp, tubePhi_apply_tube T i p] at hxy
      exact absurd ⟨tubeF n p, hxy⟩ (hy i)
  · push Not at hx
    rw [tubePhi_eq_self_of_notMem_range T hx] at hxy
    by_cases hy : ∃ j : T.ι, y ∈ Set.range (T.tube j)
    · -- `tubePhi T x = x` lies on no tube, while `tubePhi T y` lies on the tube `j`
      obtain ⟨j, q, hq⟩ := hy
      rw [← hq, tubePhi_apply_tube T j q] at hxy
      exact absurd ⟨tubeF n q, hxy.symm⟩ (hx j)
    · -- both points lie on no tube: `tubePhi` is the identity on both
      push Not at hy
      rw [tubePhi_eq_self_of_notMem_range T hy] at hxy
      exact hxy

end Work.Noncompact.CompressionTube
