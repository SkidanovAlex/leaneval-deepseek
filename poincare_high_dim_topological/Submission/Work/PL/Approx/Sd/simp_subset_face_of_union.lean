import Mathlib
import Submission.Work.PL.Approx.Defs

/-!
# A simplex covered by faces of a simplicial complex lies in one of them

If `u` is a face of a (geometric) simplicial complex `M` and the simplex `PL.simp u` is covered
by the simplices `PL.simp t` of a finite family `T` of faces of `M`, then `M`-gluing forces `u`
to be contained in a single `t ∈ T`.

The proof takes the barycentre `x = u.centerMass 1 id` of `u`.  For the face `t` whose simplex
contains `x`, the gluing axiom gives `x ∈ convexHull (u ∩ t)`; but `x` is an interior point of
`convexHull u`, so it cannot lie in the convex hull of a proper sub-face `u ∩ t ⊊ u`.  The latter
is the content of `barycenter_eq_of_mem_convexHull`, proved from the affine independence of the
vertices of `u` (`Finset.mem_convexHull'` + `AffineIndependent.eq_of_sum_eq_sum_subtype`).
-/

namespace Work.PL.Approx.Sd

open Set

/-- If `s ⊆ u` are vertex sets, `u` has affinely independent vertices and the barycentre of `u`
lies in `convexHull ℝ s`, then `s = u`: the barycentre is a point of the relative interior of the
simplex spanned by `u`, and relative interiors of faces are disjoint. -/
lemma barycenter_eq_of_mem_convexHull {N : ℕ} {u s : Finset (PL.E N)}
    (hu : AffineIndependent ℝ ((↑) : u → PL.E N)) (hne : u.Nonempty) (hsu : s ⊆ u)
    (h : u.centerMass (fun _ : PL.E N => (1 : ℝ)) id ∈ convexHull ℝ (s : Set (PL.E N))) :
    s = u := by
  classical
  rw [Finset.mem_convexHull'] at h
  obtain ⟨w, _hw0, hw1, hw2⟩ := h
  have hucard : (u.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Finset.card_ne_zero.mpr hne)
  have hcm : u.centerMass (fun _ : PL.E N => (1 : ℝ)) id = (u.card : ℝ)⁻¹ • ∑ i ∈ u, i := by
    simp only [Finset.centerMass, one_smul, id_eq]
    congr 1
    rw [Finset.sum_const, nsmul_eq_mul, mul_one]
  refine Finset.Subset.antisymm hsu (fun v hv => ?_)
  have heq : (fun _ : PL.E N => (u.card : ℝ)⁻¹) v
      = (fun x : PL.E N => if x ∈ s then w x else 0) v := by
    refine hu.eq_of_sum_eq_sum_subtype (w₁ := fun _ : PL.E N => (u.card : ℝ)⁻¹)
      (w₂ := fun x : PL.E N => if x ∈ s then w x else 0) ?_ ?_ v hv
    · rw [Finset.sum_const, nsmul_eq_mul, mul_inv_cancel₀ hucard]
      rw [← Finset.sum_subset hsu (fun x _ hx => by simp [hx]), ← hw1]
      refine Finset.sum_congr rfl (fun x hx => ?_)
      rw [ite_eq_left hx]
    · rw [← Finset.smul_sum, ← hcm, ← hw2]
      rw [← Finset.sum_subset hsu (fun x _ hx => by simp [hx])]
      refine Finset.sum_congr rfl (fun x hx => ?_)
      rw [ite_eq_left hx]
  by_contra hvs
  have hzero : (u.card : ℝ)⁻¹ = 0 := by simpa [hvs] using heq
  exact (inv_ne_zero hucard) hzero

lemma simp_subset_face_of_union {N : ℕ} (M : PL.Cx N) (T : Finset (Finset (PL.E N)))
    (hT : ∀ t ∈ T, t ∈ M.faces) {u : Finset (PL.E N)} (hu : u ∈ M.faces)
    (hsub : PL.simp u ⊆ ⋃ t ∈ T, PL.simp t) : ∃ t ∈ T, u ⊆ t := by
  classical
  have hu_ne : u.Nonempty := M.nonempty_of_mem_faces hu
  have hxu : u.centerMass (fun _ : PL.E N => (1 : ℝ)) id ∈ PL.simp u :=
    Finset.centerMass_id_mem_convexHull u (fun _ _ => by norm_num)
      (by rw [Finset.sum_const, nsmul_eq_mul, mul_one]
          exact_mod_cast Finset.card_pos.mpr hu_ne)
  obtain ⟨t, htT, hxt⟩ : ∃ t ∈ T, u.centerMass (fun _ : PL.E N => (1 : ℝ)) id ∈ PL.simp t := by
    simpa only [Set.mem_iUnion, exists_prop] using hsub hxu
  refine ⟨t, htT, ?_⟩
  have ht : t ∈ M.faces := hT t htT
  have hmem : u.centerMass (fun _ : PL.E N => (1 : ℝ)) id ∈ PL.simp (u ∩ t) := by
    show u.centerMass (fun _ : PL.E N => (1 : ℝ)) id ∈
      convexHull ℝ ((u ∩ t : Finset (PL.E N)) : Set (PL.E N))
    rw [Finset.coe_inter, ← M.convexHull_inter_convexHull hu ht]
    exact ⟨hxu, hxt⟩
  have hinter : u ∩ t = u := barycenter_eq_of_mem_convexHull (M.indep hu) hu_ne
    Finset.inter_subset_left hmem
  exact Finset.inter_eq_left.mp hinter

end Work.PL.Approx.Sd
