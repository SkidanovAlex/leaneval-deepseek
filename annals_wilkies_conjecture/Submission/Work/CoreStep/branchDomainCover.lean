/-
  `Work.CoreStep.branchDomainCover`: the branch through `u` covers the branch through `u'`
  locally, from a pair stratum of full dimension (used by `Work.CoreStep.branchDomain_open`).
-/
import Mathlib
import Submission.Work.CoreStep.branchDomainPairDim
import Submission.Work.WilE7.DimAPI.openMap_of_equalDim
import Submission.Work.CoreStep.hcof_of_pairCovers

set_option autoImplicit false
noncomputable section
open Classical Filter Topology
open WilkiesDesign WilkiesDesign.E
namespace Work.CoreStep

open Work.WilE7 Work.WilE7.CoreStep

/-- **The branch through `u` covers the branch through `u'` locally.**  If the pair point of two
points `u, u'` of `T.X.set` over the same base point lies in a `Good` stratum `W` of the pair set
with `dim W = dim T`, then every point of `absSet T` near `absPtInv u'` has the same base point as
some point of `absSet T` near `absPtInv u`. -/
theorem branch_covers_of_good_pair {n m : ℕ} (T : Stratum 0 (n + (m + 1)))
    (hT : T.Good) (hrank : ∀ z ∈ T.X.set, MainDesign.projRank T z = n + (m + 1) - T.j)
    (W : Stratum 0 (pPair n m)) (hWgood : W.Good)
    (hWsub : W.X.set ⊆ (absPairSet T).set)
    (u u' : Fin (pDim n m) → ℝ) (hu : u ∈ T.X.set) (hu' : u' ∈ T.X.set)
    (hbase : projFirst n (m + 1) (absPtInv u) = projFirst n (m + 1) (absPtInv u'))
    (hWmem : pairPtUp u u' ∈ W.X.set)
    (hdim : pPair n m - W.j = n + (m + 1) - T.j)
    (V : Set (Fin (n + (m + 1)) → ℝ)) (hV : V ∈ nhds (absPtInv u)) :
    ∃ O ∈ nhds (absPtInv u'), ∀ z' ∈ MainDesign.absSet T, z' ∈ O →
      ∃ z ∈ MainDesign.absSet T, z ∈ V ∧ projFirst n (m + 1) z = projFirst n (m + 1) z' := by
  classical
  -- an open neighbourhood of `absPtInv u` inside `V`
  obtain ⟨V₀, hV₀sub, hV₀open, hV₀mem⟩ := mem_nhds_iff.mp hV
  -- the neighbourhood of the pair point whose first halves lie in `V₀`
  set U : Set (Fin (pPair n m) → ℝ) := {y | projFirst (n + (m + 1)) (n + (m + 1)) y ∈ V₀}
    with hU
  have hUmem : U ∈ nhds (MainDesign.absPt (pairPtUp u u')) := by
    have hcont : Continuous (projFirst (n + (m + 1)) (n + (m + 1))) :=
      Work.CoreStep.continuous_projFirst' _ _
    rw [hU, absPt_pairPtUp]
    have hmem : projFirst (n + (m + 1)) (n + (m + 1)) (pairPt u u') ∈ V₀ := by
      rw [projFirst_pairPt]; exact hV₀mem
    exact (hcont.continuousAt).preimage_mem_nhds (hV₀open.mem_nhds hmem)
  have hcov := Work.WilE7.DimAPI.openMap_of_equalDim T W hT hWgood
    (linProjSnd (n + (m + 1)) (n + (m + 1))) (hmap_of_pair T W hWsub)
    (hinj_of_pair T hT hrank W hWgood hWsub) hdim (pairPtUp u u') hWmem U hUmem
  -- rewrite the base point of the covering statement
  have hbasept : linProjSnd (n + (m + 1)) (n + (m + 1))
      (MainDesign.absPt (pairPtUp u u')) = absPtInv u' := by
    rw [linProjSnd_apply, absPt_pairPtUp, projSnd_pairPt]
  rw [hbasept] at hcov
  obtain ⟨O, hO, hOprop⟩ := Filter.eventually_iff_exists_mem.mp hcov
  refine ⟨O, hO, fun z' hz'A hz'O => ?_⟩
  obtain ⟨y, hyWU, hyeq⟩ := hOprop z' hz'O hz'A
  obtain ⟨hyW, hyU⟩ := hyWU
  obtain ⟨w, hw, hwy⟩ := hyW
  -- the first half of the pair point
  refine ⟨projFirst (n + (m + 1)) (n + (m + 1)) (MainDesign.absPt w), ?_, ?_, ?_⟩
  · -- it is a point of `absSet T`
    have hparts := (absPairSet_mem_iff T w).mp (hWsub hw)
    exact ⟨absPtUp (n := n) (m := m) (projFirst (n + (m + 1)) (n + (m + 1))
      (MainDesign.absPt w)), hparts.1,
      (Work.WilE7.DimAPI.absPt_absPtInv (n + (m + 1)) _).symm⟩
  · -- it lies in `V`
    have hyV₀ : projFirst (n + (m + 1)) (n + (m + 1)) y ∈ V₀ := by
      have h := hyU
      rwa [hU] at h
    have hwy' : projFirst (n + (m + 1)) (n + (m + 1)) (MainDesign.absPt w) =
        projFirst (n + (m + 1)) (n + (m + 1)) y := by rw [hwy]
    exact hV₀sub (hwy' ▸ hyV₀)
  · -- it has the same base point
    have hparts := (absPairSet_mem_iff T w).mp (hWsub hw)
    have hLw : projSnd (n + (m + 1)) (n + (m + 1)) (MainDesign.absPt w) = z' := by
      have h : projSnd (n + (m + 1)) (n + (m + 1)) y = z' := by
        rw [← linProjSnd_apply]
        exact hyeq
      rw [hwy]
      exact h
    rw [hparts.2.2, hLw]

end Work.CoreStep
