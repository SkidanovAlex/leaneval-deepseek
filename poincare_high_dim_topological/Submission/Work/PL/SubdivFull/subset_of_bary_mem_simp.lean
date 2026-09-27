import Mathlib
import Submission.Work.PL.Subdiv

/-!
# The barycenter of a face detects subfaces

If `ρ` is a face of a simplicial complex `K` and `u` is a face of `K` whose closed simplex
contains the barycenter of `ρ`, then `ρ` is a face of `u` (`ρ ⊆ u` as vertex sets).

Mathematically: `bary ρ` lies in the relative interior of `simp ρ`, while
`simp ρ ∩ simp u = simp (ρ ∩ u)` because the faces of a simplicial complex glue nicely
(`Geometry.SimplicialComplex.convexHull_inter_convexHull`).  Hence `bary ρ` is a convex
combination of the *vertices* of `ρ ∩ u` only; writing `bary ρ` as the (equal-weight) convex
combination of the affinely independent vertices of `ρ`, uniqueness of the barycentric
coordinates (`AffineIndependent.eq_of_sum_eq_sum_subtype`) shows that no vertex of `ρ` is
missing from `u`.

This is the `SubdivFull`-area step feeding fullness of face unions.
-/

namespace Work.PL.SubdivFull

open Set Metric
open scoped BigOperators

theorem subset_of_bary_mem_simp {N : ℕ} {K : PL.Cx N} {ρ u : Finset (PL.E N)}
    (hρ : ρ ∈ K.faces) (hu : u ∈ K.faces) (h : Work.PL.Subdiv.bary ρ ∈ PL.simp u) : ρ ⊆ u := by
  classical
  have hne : ρ.Nonempty := K.nonempty_of_mem_faces hρ
  have hcard : (ρ.card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Finset.card_ne_zero.mpr hne)
  -- `bary ρ` lies in `simp ρ ∩ simp u = simp (ρ ∩ u)`
  have hmem : Work.PL.Subdiv.bary ρ ∈
      convexHull ℝ ((ρ ∩ u : Finset (PL.E N)) : Set (PL.E N)) := by
    rw [Finset.coe_inter, ← K.convexHull_inter_convexHull hρ hu]
    exact ⟨Work.PL.Subdiv.bary_mem_simp hne, h⟩
  -- so it is a convex combination of the vertices of `ρ ∩ u`
  obtain ⟨w, _hw0, hw1, hwsum⟩ := Finset.mem_convexHull'.mp hmem
  -- extend the weights by `0` away from `ρ ∩ u` so that they can be compared on all of `ρ`
  set c : PL.E N → ℝ := fun _ => (ρ.card : ℝ)⁻¹
  set w' : PL.E N → ℝ := fun y => if y ∈ ρ ∩ u then w y else 0
  have hzero : ∀ y ∈ ρ, y ∉ ρ ∩ u → w' y = 0 := by
    intro y _ hy'; simp only [w', hy', ite_false]
  have hcongr : ∀ y ∈ ρ ∩ u, w' y = w y := by
    intro y hy; simp only [w', hy, ite_true]
  have hsum_w' : ∑ y ∈ ρ, w' y = 1 := by
    have h1 : ∑ y ∈ ρ, w' y = ∑ y ∈ ρ ∩ u, w' y :=
      (Finset.sum_subset Finset.inter_subset_left hzero).symm
    rw [h1, Finset.sum_congr rfl hcongr]
    exact hw1
  have hsumw'ν : ∑ y ∈ ρ, w' y • y = Work.PL.Subdiv.bary ρ := by
    have h1 : ∑ y ∈ ρ, w' y • y = ∑ y ∈ ρ ∩ u, w' y • y :=
      (Finset.sum_subset Finset.inter_subset_left (fun y hy hy' => by
        simp only [w', hy', ite_false, zero_smul])).symm
    rw [h1, Finset.sum_congr rfl (fun y hy => by rw [hcongr y hy])]
    exact hwsum
  -- the equal-weight combination giving the barycenter
  have hsum_c : ∑ y ∈ ρ, c y = 1 := by
    simp only [c, Finset.sum_const, nsmul_eq_mul]
    exact mul_inv_cancel₀ hcard
  have hsumcν : ∑ y ∈ ρ, c y • y = Work.PL.Subdiv.bary ρ := by
    simp only [c]
    rw [← Finset.smul_sum, ← Work.PL.Subdiv.bary_eq_smul_sum]
  -- uniqueness of barycentric coordinates on the affinely independent face `ρ`
  have hweights : ∀ y ∈ ρ, w' y = c y :=
    AffineIndependent.eq_of_sum_eq_sum_subtype (k := ℝ) (s := ρ) (w₁ := w') (w₂ := c)
      (K.indep hρ) (by rw [hsum_w', hsum_c]) (by rw [hsumw'ν, hsumcν])
  intro y hy
  by_contra hyu
  have h0 : w' y = 0 := by
    have : y ∉ ρ ∩ u := fun hmem => hyu (Finset.mem_of_mem_inter_right hmem)
    simp only [w', this, ite_false]
  have hcy : c y = 0 := by rw [← hweights y hy, h0]
  simp only [c] at hcy
  exact hcard (inv_eq_zero.mp hcy)

end Work.PL.SubdivFull
