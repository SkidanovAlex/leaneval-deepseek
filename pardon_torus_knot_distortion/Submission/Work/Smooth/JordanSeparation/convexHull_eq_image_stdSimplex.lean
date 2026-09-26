import Mathlib
import Submission.Work.Smooth.JordanSeparation.EmbeddingTransferFin3

/-!
# The convex hull of a planar set is a union of triangles (Carathéodory in the plane)

Carathéodory's theorem for `ℂ` viewed as a two-dimensional real vector space: every point of the
convex hull of a set `K ⊆ ℂ` is a convex combination of at most three points of `K`.  Concretely,

`convexHull ℝ K` is the image of `stdSimplex ℝ (Fin 3) × K³` under the weighted-sum map.

The `⊇` direction is immediate (a convex combination of points of a convex set lies in it).  For the
`⊆` direction we use Mathlib's Carathéodory theorem in the form
`eq_pos_convex_span_of_mem_convexHull`, which writes a point of the convex hull as a convex
combination of a *positive*-weighted affine-independent family.  An affine-independent family in a
`2`-dimensional space has at most `3` elements (`AffineIndependent.card_le_finrank_succ`), and
`exists_fin_three_transfer` re-indexes the combination by `Fin 3`, padding with a base point.
-/

namespace Work.Smooth.JordanSeparation

open Set

theorem convexHull_eq_image_stdSimplex (K : Set ℂ) :
    convexHull ℝ K =
      (fun p : (Fin 3 → ℝ) × (Fin 3 → ℂ) => ∑ i, p.1 i • p.2 i)
        '' ((stdSimplex ℝ (Fin 3)) ×ˢ (Set.univ.pi (fun _ : Fin 3 => K))) := by
  apply Set.Subset.antisymm
  · -- `convexHull ℝ K ⊆ image`: Carathéodory in the plane.
    intro x hx
    rcases K.eq_empty_or_nonempty with hK | ⟨k0, hk0⟩
    · subst hK
      rw [convexHull_empty] at hx
      exact hx.elim
    · -- write `x` as a positive convex combination of an affine-independent family
      obtain ⟨ι, hιinst, z, w, hrange, haff, hwpos, hwsum, hwz⟩ :=
        eq_pos_convex_span_of_mem_convexHull hx
      let _ : Fintype ι := hιinst
      classical
      -- an affine-independent family in `ℂ` has at most `finrank ℝ ℂ + 1 = 3` elements
      have hcard : Fintype.card ι ≤ 3 := by
        have h1 := haff.card_le_finrank_succ
        have h2 : Module.finrank ℝ ↥(vectorSpan ℝ (Set.range z)) ≤ 2 := by
          calc Module.finrank ℝ ↥(vectorSpan ℝ (Set.range z))
              ≤ Module.finrank ℝ ℂ := Submodule.finrank_le _
            _ = 2 := Complex.finrank_real_complex
        omega
      let e : ι ↪ Fin 3 := (Fintype.equivFin ι).toEmbedding.trans (Fin.castLEEmb hcard)
      obtain ⟨w', f, hfK, hw'nn, hw'sum, hw'z⟩ :=
        exists_fin_three_transfer hk0 e w z (fun j => hrange (Set.mem_range_self j))
          (fun j => le_of_lt (hwpos j))
      refine ⟨(w', f), ?_, ?_⟩
      · rw [Set.mem_prod]
        exact ⟨⟨hw'nn, by rw [hw'sum, hwsum]⟩,
          by rw [Set.mem_pi]; intro i _; exact hfK i⟩
      · show (∑ i, w' i • f i) = x
        rw [hw'z, hwz]
  · -- `image ⊆ convexHull ℝ K`: a convex combination of points of `K` lies in its convex hull.
    rintro x ⟨p, hp, rfl⟩
    rw [Set.mem_prod] at hp
    obtain ⟨hp1, hp2⟩ := hp
    rw [mem_convexHull_iff_exists_fintype]
    refine ⟨Fin 3, inferInstance, p.1, p.2, hp1.1, hp1.2, ?_, rfl⟩
    intro i
    exact Set.mem_pi.mp hp2 i (Set.mem_univ i)

end Work.Smooth.JordanSeparation
