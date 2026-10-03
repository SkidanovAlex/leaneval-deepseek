import Mathlib
import Submission.Work.ORBassSerre.Action.QuotientGroupOrbitV
import Submission.Work.ORDunwoody.Lemmas.ofQuiverTree

namespace Work.ORBassSerre.QuotientTree

universe u

open Quiver

/-- If the quotient graph `V ⧸ N` is a tree, then the stabilizer of an edge of the quotient (i.e.
the intersection of the stabilizers of its two endpoints) is the image of the stabilizer of the
corresponding edge of `V`: an element of `G ⧸ N` that fixes both endpoint orbits maps the edge
orbit to an edge orbit with the same endpoints, and a tree has at most one arrow between two
vertices.  Build on `Work.ORBassSerre.quotient_smul_mk` and on
`Work.ORDunwoody.Lemmas.subsingleton_hom_of_isTree`. -/
theorem inf_stabilizer_eq_map {G V : Type u} [Group G] [Quiver V]
    [Quiver.HasInvolutiveReverse V] [MulAction G V] [GraphAction G V] (N : Subgroup G)
    [N.Normal] (hQ : Work.ORBassSerre.IsTree (Work.ORBassSerre.orbitV N V))
    {A B : Work.ORBassSerre.orbitV N V} {a b : V}
    (ha : (Quotient.mk'' a : Work.ORBassSerre.orbitV N V) = A)
    (hb : (Quotient.mk'' b : Work.ORBassSerre.orbitV N V) = B) (hab : Nonempty (a ⟶ b)) :
    MulAction.stabilizer (G ⧸ N) A ⊓ MulAction.stabilizer (G ⧸ N) B =
      (MulAction.stabilizer G a ⊓ MulAction.stabilizer G b).map (QuotientGroup.mk' N) := by
  subst A
  subst B
  apply le_antisymm
  · -- `stab A ⊓ stab B ≤ (stab a ⊓ stab b).map π`
    intro q hq
    rw [Subgroup.mem_inf] at hq
    obtain ⟨hqA, hqB⟩ := hq
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N q
    rw [MulAction.mem_stabilizer_iff] at hqA hqB
    rw [Work.ORBassSerre.quotient_smul_mk] at hqA hqB
    -- `hqA : mk'' (g • a) = mk'' a`, `hqB : mk'' (g • b) = mk'' b`
    obtain ⟨e⟩ := hab
    let T : Quiver.Total V := Quiver.Total.mk a b e
    have hTleft : (g • T).left = g • a := by
      simpa [T] using Work.ORBassSerre.GraphAction.smul_mk_left (G := G) (V := V) g e
    have hTright : (g • T).right = g • b := by
      simpa [T] using Work.ORBassSerre.GraphAction.smul_mk_right (G := G) (V := V) g e
    have hleft : (Quotient.mk'' (g • T).left : Work.ORBassSerre.orbitV N V) =
        Quotient.mk'' a := by
      rw [hTleft]
      exact hqA
    have hright : (Quotient.mk'' (g • T).right : Work.ORBassSerre.orbitV N V) =
        Quotient.mk'' b := by
      rw [hTright]
      exact hqB
    let E2 : (Quotient.mk'' a : Work.ORBassSerre.orbitV N V) ⟶ Quotient.mk'' b :=
      ⟨Quotient.mk'' (g • T), g • T, rfl, hleft, hright⟩
    haveI : Subsingleton
        ((Quotient.mk'' a : Work.ORBassSerre.orbitV N V) ⟶ Quotient.mk'' b) :=
      Work.ORDunwoody.Lemmas.subsingleton_hom_of_isTree hQ _ _
    have hval : (Quotient.mk'' T : Work.ORBassSerre.orbitE ↥N V) = Quotient.mk'' (g • T) := by
      have hE : (Work.ORBassSerre.orbitArrow (G := ↥N) e) = E2 := Subsingleton.elim _ _
      have hcv := congrArg Subtype.val hE
      simpa [E2, Work.ORBassSerre.orbitArrow_val, T] using hcv
    -- `mk'' T = mk'' (g • T)`, i.e. `T` and `g • T` are in the same `N`-orbit
    have hrel : MulAction.orbitRel ↥N (Quiver.Total V) T (g • T) := Quotient.exact hval
    rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at hrel
    obtain ⟨n, hn⟩ := hrel
    have hn' : ((n : G) * g) • T = T := by
      simpa [Subgroup.smul_def, mul_smul] using hn
    have hann : ((n : G) * g) • a = a := by
      have h2 : (((n : G) * g) • T).left = ((n : G) * g) • a := by
        simpa [T] using
          Work.ORBassSerre.GraphAction.smul_mk_left (G := G) (V := V) ((n : G) * g) e
      have h := congrArg Quiver.Total.left hn'
      rw [h2] at h
      simpa [T] using h
    have hbnn : ((n : G) * g) • b = b := by
      have h2 : (((n : G) * g) • T).right = ((n : G) * g) • b := by
        simpa [T] using
          Work.ORBassSerre.GraphAction.smul_mk_right (G := G) (V := V) ((n : G) * g) e
      have h := congrArg Quiver.Total.right hn'
      rw [h2] at h
      simpa [T] using h
    have hn1 : (QuotientGroup.mk' N) (n : G) = 1 := by
      rw [QuotientGroup.mk'_apply]
      exact (QuotientGroup.eq_one_iff (n : G)).2 n.2
    have hπ : (QuotientGroup.mk' N) ((n : G) * g) = (QuotientGroup.mk' N) g := by
      rw [map_mul, hn1, one_mul]
    rw [Subgroup.mem_map]
    exact ⟨(n : G) * g,
      Subgroup.mem_inf.mpr ⟨MulAction.mem_stabilizer_iff.mpr hann,
        MulAction.mem_stabilizer_iff.mpr hbnn⟩, hπ⟩
  · -- `(stab a ⊓ stab b).map π ≤ stab A ⊓ stab B`
    intro x hx
    rw [Subgroup.mem_map] at hx
    obtain ⟨h, hh, rfl⟩ := hx
    rw [Subgroup.mem_inf]
    refine ⟨?_, ?_⟩
    · rw [MulAction.mem_stabilizer_iff, Work.ORBassSerre.quotient_smul_mk,
        MulAction.mem_stabilizer_iff.mp (Subgroup.mem_inf.mp hh).1]
    · rw [MulAction.mem_stabilizer_iff, Work.ORBassSerre.quotient_smul_mk,
        MulAction.mem_stabilizer_iff.mp (Subgroup.mem_inf.mp hh).2]

end Work.ORBassSerre.QuotientTree
