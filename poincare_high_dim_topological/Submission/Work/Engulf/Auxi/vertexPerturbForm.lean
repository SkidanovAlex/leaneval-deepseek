import Mathlib
import Submission.Work.Engulf.Basic
import Submission.Work.Engulf.Vpf.Defs
import Submission.Work.Engulf.Vpf.vpfApplyNotMem

open Set Metric PL

namespace Work.Engulf.Aux

/-! ## Auxiliary facts about the explicit perturbation `Work.Engulf.Vpf.vpfG'`

These are the two facts about the candidate perturbation `Work.Engulf.Vpf.vpfG' K Z g y` which
`vertexPerturbForm` needs besides the agreement lemmas in `Submission.Work.Engulf.Vpf.Defs`. -/

/-- `Work.Engulf.Vpf.vpfG'` stays within `η` of `g` on `K.space`. -/
theorem dist_vpfG_le {N n : ℕ} {K : Cx N} {Z : Finset (E N)} {g y : E N → E n} {η : ℝ}
    (hglin : ∀ s ∈ K.faces, (∃ v ∈ s, v ∈ Z) → ∃ A : E N →ᵃ[ℝ] E n, EqOn g A (simp s))
    (hη : 0 ≤ η) (hy : ∀ v ∈ Z, dist (y v) (g v) ≤ η) {x : E N} (hx : x ∈ K.space) :
    dist (Work.Engulf.Vpf.vpfG' K Z g y x) (g x) ≤ η := by
  obtain ⟨s, hs, hxs⟩ := (Geometry.SimplicialComplex.mem_space_iff (K := K)).mp hx
  by_cases hZ : ∃ v ∈ s, v ∈ Z
  · obtain ⟨w, hw0, hw1, hwx⟩ := Finset.mem_convexHull'.mp hxs
    obtain ⟨G, hG⟩ := hglin s hs hZ
    have hGx : g x = ∑ v ∈ s, w v • g v := by
      rw [hG hxs, ← hwx, Work.Engulf.Vpf.affineMap_map_sum_smul (A := G) hw1]
      exact Finset.sum_congr rfl fun v hv => by rw [hG (Work.Engulf.subset_simp hv)]
    have hA : ∑ v ∈ s, w v • Work.Engulf.Vpf.vpfA K (Work.Engulf.Vpf.vpfC Z g y) s v
        = ∑ v ∈ s, w v • Work.Engulf.Vpf.vpfC Z g y v :=
      Finset.sum_congr rfl fun v hv => by rw [Work.Engulf.Vpf.vpfA_apply hs hv]
    rw [Work.Engulf.Vpf.vpfG'_apply_of_mem hs hZ hxs, hGx, ← hwx,
      Work.Engulf.Vpf.affineMap_map_sum_smul
        (A := Work.Engulf.Vpf.vpfA K (Work.Engulf.Vpf.vpfC Z g y) s) hw1, hA]
    exact Work.Engulf.Vpf.dist_weighted_sum_le hw0 hw1 fun v hv => by
      by_cases hvZ : v ∈ Z
      · rw [Work.Engulf.Vpf.vpfC_apply_of_mem hvZ]; exact hy v hvZ
      · rw [Work.Engulf.Vpf.vpfC_apply_of_notMem hvZ, dist_self]; exact hη
  · rw [Work.Engulf.Vpf.vpfApplyNotMem hglin hs (fun v hv hvZ => hZ ⟨v, hv, hvZ⟩) hxs,
      dist_self]
    exact hη

/-- `Work.Engulf.Vpf.vpfG'` is continuous on the space of a finite complex. -/
theorem continuousOn_vpfG {N n : ℕ} {K : Cx N} (hK : K.faces.Finite) {Z : Finset (E N)}
    {g y : E N → E n} (hgcont : ContinuousOn g K.space)
    (hglin : ∀ s ∈ K.faces, (∃ v ∈ s, v ∈ Z) → ∃ A : E N →ᵃ[ℝ] E n, EqOn g A (simp s)) :
    ContinuousOn (Work.Engulf.Vpf.vpfG' K Z g y) K.space := by
  refine Work.Engulf.Vpf.continuousOn_of_continuousOn_faces hK fun s hs => ?_
  by_cases hZ : ∃ v ∈ s, v ∈ Z
  · have h1 : ContinuousOn (Work.Engulf.Vpf.vpfA K (Work.Engulf.Vpf.vpfC Z g y) s) (simp s) :=
      (AffineMap.continuous_of_finiteDimensional
        (Work.Engulf.Vpf.vpfA K (Work.Engulf.Vpf.vpfC Z g y) s)).continuousOn
    exact h1.congr fun x hx => Work.Engulf.Vpf.vpfG'_apply_of_mem hs hZ hx
  · have h1 : ContinuousOn g (simp s) :=
      hgcont.mono (Geometry.SimplicialComplex.convexHull_subset_space (K := K) hs)
    exact h1.congr fun x hx =>
      Work.Engulf.Vpf.vpfApplyNotMem hglin hs (fun v hv hvZ => hZ ⟨v, hv, hvZ⟩) hx

/-- **`vertexPerturbForm`** (contract §7.2, aux Hx8): realises the general position statement `G6a'` by editing only the free vertices.  (The definition `Work.Engulf.VertexPerturbForm` was corrected after review: it now carries the two hypotheses `∀ v ∈ Z, ∃ s ∈ K.faces, v ∈ s` (`Z` consists of vertices of `K`, true at the use site in `E4`) and `0 ≤ η`; without them the statement is false.)  For a finite complex `K`, a finite set `Z ⊆ ⋃ K.faces` of vertices, and a map `g : ℝᴺ → ℝⁿ` that is continuous on `K.space` and affine on every face containing a `Z`-vertex, any perturbation `y` of `g` on `Z` at distance `≤ η` extends to a map `g'` that is `y` on `Z`, agrees with `g` on faces with no `Z`-vertex, is affine on faces with a `Z`-vertex with the same values as `g` on the non-`Z` vertices, and stays within `η` of `g`.  Suggested proof: on each face `simp s` containing a `Z`-vertex take the affine map determined by the new values on `s ∩ Z` and the old values on `s ∖ Z` (using `K.indep` and that `g` is affine on `simp s`), and keep `g` on faces with no `Z`-vertex; the two prescriptions agree on intersections because `simp s ∩ simp t = PL.simp (s ∩ t)` (`PL.simp_inter`), giving continuity, and the distance bound follows from `dist (Σ λᵥ y v) (Σ λᵥ g v) ≤ Σ λᵥ dist (y v) (g v) ≤ η` for the convex coefficients `λ` of the point in `simp s`. -/
theorem vertexPerturbForm (N n : ℕ) : Work.Engulf.VertexPerturbForm N n := by
  intro K hK Z g hgcont hZsub hglin y η hη hy
  refine ⟨Work.Engulf.Vpf.vpfG' K Z g y, continuousOn_vpfG hK hgcont hglin,
    fun v hv => Work.Engulf.Vpf.vpfG'_apply_of_mem_Z hZsub hv, ?_, ?_, ?_⟩
  · intro s hs hnoZ x hx
    exact Work.Engulf.Vpf.vpfApplyNotMem hglin hs hnoZ hx
  · intro s hs hZ
    exact ⟨Work.Engulf.Vpf.vpfA K (Work.Engulf.Vpf.vpfC Z g y) s,
      fun x hx => Work.Engulf.Vpf.vpfG'_apply_of_mem hs hZ hx,
      fun v hv hvZ => by
        rw [Work.Engulf.Vpf.vpfA_apply hs hv, Work.Engulf.Vpf.vpfC_apply_of_notMem hvZ]⟩
  · intro x hx
    exact dist_vpfG_le hglin hη hy hx

end Work.Engulf.Aux
