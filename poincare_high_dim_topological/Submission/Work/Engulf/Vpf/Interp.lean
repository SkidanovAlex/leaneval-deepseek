import Mathlib
import Submission.Work.Engulf.Basic

/-!
# Auxiliary geometry for `Work.Engulf.Aux.vertexPerturbForm`

Elementary facts about affine maps on simplices, used to realise the vertex perturbation
`VertexPerturbForm` (contract §7.2, aux Hx8):

* an affine map `Eᴺ →ᵃ[ℝ] Eⁿ` is determined by its values on the vertices of a convex hull
  (`eqOn_convexHull_of_eqOn_vertices`) and respects affine combinations
  (`affineMap_map_sum_smul`);
* a linear map may be prescribed on a linearly independent family
  (`exists_linearMap_of_linearIndependent`), whence an affine map may be prescribed on the
  vertices of any face of a simplicial complex (`exists_affineMap_eqOn_of_mem_faces`);
* a distance bound for convex combinations (`dist_weighted_sum_le`);
* continuity on a finite simplicial complex is checked on its faces
  (`continuousOn_of_continuousOn_faces`).
-/

open Set Metric PL

namespace Work.Engulf.Vpf

variable {N n : ℕ}

/-! ## Affine maps and convex combinations -/

/-- An affine map takes an affine combination with weights summing to one to the corresponding
combination of the images. -/
theorem affineMap_map_sum_smul {A : E N →ᵃ[ℝ] E n} {s : Finset (E N)} {w : E N → ℝ}
    (hw : ∑ v ∈ s, w v = 1) : A (∑ v ∈ s, w v • v) = ∑ v ∈ s, w v • A v := by
  have h1 : ∀ x : E N, A x = A.linear x + A 0 := by
    intro x
    simpa using AffineMap.map_vadd A (0 : E N) x
  calc A (∑ v ∈ s, w v • v) = A.linear (∑ v ∈ s, w v • v) + A 0 := h1 _
    _ = (∑ v ∈ s, w v • A.linear v) + A 0 := by
        rw [map_sum]
        congr 1
        exact Finset.sum_congr rfl fun v _ => map_smul A.linear (w v) v
    _ = (∑ v ∈ s, w v • A.linear v) + (∑ v ∈ s, w v) • A 0 := by rw [hw, one_smul]
    _ = (∑ v ∈ s, w v • A.linear v) + ∑ v ∈ s, w v • A 0 := by rw [Finset.sum_smul]
    _ = ∑ v ∈ s, (w v • A.linear v + w v • A 0) := by rw [Finset.sum_add_distrib]
    _ = ∑ v ∈ s, w v • (A.linear v + A 0) := by
        exact Finset.sum_congr rfl fun v _ => (smul_add (w v) (A.linear v) (A 0)).symm
    _ = ∑ v ∈ s, w v • A v := by
        exact Finset.sum_congr rfl fun v _ => by rw [h1 v]

/-- Two affine maps which agree on the vertices of `s` agree on the convex hull of `s`. -/
theorem eqOn_convexHull_of_eqOn_vertices {A B : E N →ᵃ[ℝ] E n} {s : Finset (E N)}
    (h : ∀ v ∈ s, A v = B v) : EqOn A B (convexHull ℝ (s : Set (E N))) := by
  intro x hx
  obtain ⟨w, _, hw1, hwx⟩ := Finset.mem_convexHull'.mp hx
  rw [← hwx, affineMap_map_sum_smul (A := A) hw1, affineMap_map_sum_smul (A := B) hw1]
  exact Finset.sum_congr rfl fun v hv => by rw [h v hv]

/-! ## Prescribing affine maps -/

/-- A linear map may be prescribed on a linearly independent family. -/
theorem exists_linearMap_of_linearIndependent {ι : Type*} {v : ι → E N} {c : ι → E n}
    (h : LinearIndependent ℝ v) : ∃ L : E N →ₗ[ℝ] E n, ∀ i, L (v i) = c i := by
  classical
  have hspos : LinearIndepOn ℝ id (Set.range v) := h.linearIndepOn_id
  let b := Module.Basis.extend hspos
  let φ : ↥(hspos.extend (Set.subset_univ _)) → E n := fun z =>
    if hz : ∃ i, v i = (z : E N) then c hz.choose else 0
  refine ⟨(b.constr ℝ) φ, ?_⟩
  intro i
  have hmem : v i ∈ hspos.extend (Set.subset_univ _) :=
    hspos.subset_extend (Set.subset_univ _) (Set.mem_range_self i)
  have hb : b ⟨v i, hmem⟩ = v i := Module.Basis.extend_apply_self hspos ⟨v i, hmem⟩
  rw [← hb, Module.Basis.constr_basis]
  simp only [φ]
  split_ifs with hz
  · exact congrArg c (h.injective hz.choose_spec)
  · exact absurd ⟨i, rfl⟩ hz

/-- **Affine interpolation on a face.**  On any face of a simplicial complex one may prescribe the
values of an affine map at the vertices. -/
theorem exists_affineMap_eqOn_of_mem_faces (K : Cx N) (c : E N → E n) {s : Finset (E N)}
    (hs : s ∈ K.faces) : ∃ A : E N →ᵃ[ℝ] E n, ∀ v ∈ s, A v = c v := by
  classical
  rcases s.eq_empty_or_nonempty with rfl | hne
  · exact ⟨0, by simp⟩
  obtain ⟨v₀, hv₀⟩ := hne
  have hind : AffineIndependent ℝ ((↑) : ↥s → E N) := K.indep hs
  have hlin : LinearIndependent ℝ
      (fun i : {x : ↥s // x ≠ ⟨v₀, hv₀⟩} => ((i.1 : ↥s) : E N) - v₀) :=
    (affineIndependent_iff_linearIndependent_vsub ℝ ((↑) : ↥s → E N) ⟨v₀, hv₀⟩).mp hind
  obtain ⟨L, hL⟩ := exists_linearMap_of_linearIndependent
    (v := fun i : {x : ↥s // x ≠ ⟨v₀, hv₀⟩} => ((i.1 : ↥s) : E N) - v₀)
    (c := fun i : {x : ↥s // x ≠ ⟨v₀, hv₀⟩} => c ((i.1 : ↥s) : E N) - c v₀) hlin
  refine ⟨AffineMap.mk' (fun x => L (x - v₀) + c v₀) L v₀ ?_, ?_⟩
  · intro x; simp
  · intro v hv
    rw [AffineMap.coe_mk']
    by_cases hvv : v = v₀
    · subst hvv; simp
    · have h1 := hL ⟨⟨v, hv⟩, by simpa using hvv⟩
      simp only at h1
      rw [h1]
      abel

/-! ## Distance and continuity -/

/-- Convex combinations with the same weights and vertexwise distances `≤ η` are at distance
`≤ η`. -/
theorem dist_weighted_sum_le {s : Finset (E N)} {w : E N → ℝ}
    (hw0 : ∀ v ∈ s, 0 ≤ w v) (hw1 : ∑ v ∈ s, w v = 1) {f₁ f₂ : E N → E n} {η : ℝ}
    (hη : ∀ v ∈ s, dist (f₁ v) (f₂ v) ≤ η) :
    dist (∑ v ∈ s, w v • f₁ v) (∑ v ∈ s, w v • f₂ v) ≤ η := by
  calc dist (∑ v ∈ s, w v • f₁ v) (∑ v ∈ s, w v • f₂ v)
      ≤ ∑ v ∈ s, dist (w v • f₁ v) (w v • f₂ v) := dist_sum_sum_le s _ _
    _ = ∑ v ∈ s, w v * dist (f₁ v) (f₂ v) := by
        refine Finset.sum_congr rfl fun v hv => ?_
        rw [dist_smul₀, Real.norm_eq_abs, abs_of_nonneg (hw0 v hv)]
    _ ≤ ∑ v ∈ s, w v * η :=
        Finset.sum_le_sum fun v hv => mul_le_mul_of_nonneg_left (hη v hv) (hw0 v hv)
    _ = (∑ v ∈ s, w v) * η := (Finset.sum_mul s _ η).symm
    _ = η := by rw [hw1, one_mul]

/-- A map which is continuous on every face of a finite simplicial complex is continuous on its
space. -/
theorem continuousOn_of_continuousOn_faces {K : Cx N} (hK : K.faces.Finite) {f : E N → E n}
    (hf : ∀ s ∈ K.faces, ContinuousOn f (simp s)) : ContinuousOn f K.space := by
  have hspace : K.space = ⋃ s ∈ hK.toFinset, simp s := by
    rw [Geometry.SimplicialComplex.space]
    ext x
    simp only [Set.mem_iUnion, exists_prop, hK.mem_toFinset, simp]
  have key : ∀ T : Finset (Finset (E N)), T ⊆ hK.toFinset →
      ContinuousOn f (⋃ s ∈ T, simp s) := by
    intro T
    induction T using Finset.induction with
    | empty => intro _; simp
    | insert a T ha ih =>
        intro hsub
        rw [Finset.set_biUnion_insert]
        exact ContinuousOn.union_of_isClosed
          (hf a (hK.mem_toFinset.mp (hsub (Finset.mem_insert_self a T))))
          (ih fun s hs => hsub (Finset.mem_insert_of_mem hs))
          (isClosed_simp a)
          (T.finite_toSet.isClosed_biUnion fun s _ => isClosed_simp s)
  rw [hspace]
  exact key hK.toFinset Subset.rfl

end Work.Engulf.Vpf
