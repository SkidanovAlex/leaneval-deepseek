import Mathlib
import Submission.Work.PL.SubdivFull.Defs

namespace Work.PL.SubdivFull

/-- The simplex spanned by the intersection of two faces of `K` is the intersection of the two
simplices (Mathlib's `SimplicialComplex.convexHull_inter_convexHull`, restated in `PL.simp`
vocabulary and with the `Finset`/`Set` coe of the intersection identified). -/
theorem simp_inter_of_faces {N : ℕ} {K : PL.Cx N} {s t : Finset (PL.E N)}
    (hs : s ∈ K.faces) (ht : t ∈ K.faces) :
    PL.simp (s ∩ t) = PL.simp s ∩ PL.simp t := by
  rw [PL.simp, PL.simp, PL.simp, Finset.coe_inter]
  exact (Geometry.SimplicialComplex.convexHull_inter_convexHull hs ht).symm

/-- The intersection of two unions of closed faces of `K` is again a union of closed faces of `K`.

Indeed if `x` lies in faces `s ⊆ L` and `t ⊆ M`, then `x` lies in the face `s ∩ t` (nonempty,
because `simp (s ∩ t) = simp s ∩ simp t ∋ x`), and `simp (s ∩ t) = simp s ∩ simp t ⊆ L ∩ M`. -/
theorem isFaceUnion_inter {N : ℕ} {K : PL.Cx N} {L M : Set (PL.E N)}
    (hL : IsFaceUnion K L) (hM : IsFaceUnion K M) : IsFaceUnion K (L ∩ M) := by
  refine ⟨fun x hx => hL.1 hx.1, ?_⟩
  rintro x ⟨hxL, hxM⟩
  obtain ⟨s, hs, hxs, hsL⟩ := hL.2 x hxL
  obtain ⟨t, ht, hxt, htM⟩ := hM.2 x hxM
  have hsimp := simp_inter_of_faces hs ht
  have hxst : x ∈ PL.simp (s ∩ t) := by
    rw [hsimp]; exact ⟨hxs, hxt⟩
  have hne : (s ∩ t).Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty] at h
    rw [h] at hxst
    simp [PL.simp] at hxst
  refine ⟨s ∩ t, K.down_closed hs Finset.inter_subset_left hne, hxst, ?_⟩
  intro y hy
  rw [hsimp] at hy
  exact ⟨hsL hy.1, htM hy.2⟩

end Work.PL.SubdivFull
