import Mathlib
import Submission.Work.KMTPlan.A6.ConcAux.Defs

-- v4.35 port: restore the v4.34 instance-unification behaviour (respectTransparency) in this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.KMTPlan.A6.ConcAux

open Polynomial Work.KMTPlan.A6.ConcAux

/-- The sum of the root multiplicities of the reduction of `H` modulo `p`, taken over the
representatives in `[0, p)` of the roots of `H` mod `p`, is at most the degree of the reduction.

Indeed the reduction `P = H.map (Int.castRingHom (ZMod p))` has, at each of its roots, root
multiplicity equal to the multiplicity of that root in the multiset `P.roots`; hence the sum is
the `ℕ`-cardinality of the multiset of roots of a nonzero polynomial, which is bounded by its
degree (`Polynomial.card_roots'`). -/
theorem sum_rootMultiplicity_le_natDegree (p : ℕ) [Fact p.Prime] (H : ℤ[X])
    (hH : H.map (Int.castRingHom (ZMod p)) ≠ 0) :
    ∑ r ∈ roots p H, (H.map (Int.castRingHom (ZMod p))).rootMultiplicity (r : ZMod p)
      ≤ (H.map (Int.castRingHom (ZMod p))).natDegree := by
  set P : (ZMod p)[X] := H.map (Int.castRingHom (ZMod p)) with hP
  have hP0 : P ≠ 0 := by rw [hP]; exact hH
  -- the map `r ↦ r` is injective on the roots in `[0, p)`
  have hinj : Set.InjOn (fun r : ℕ => (r : ZMod p)) ↑(roots p H) := by
    intro r hr s hs hrs
    rw [Finset.mem_coe, mem_roots] at hr hs
    exact ((ZMod.natCast_eq_natCast_iff r s p).mp hrs).eq_of_lt_of_lt hr.1 hs.1
  -- every representative of a root of `H` mod `p` is a root of `P`
  have hroot : ∀ r ∈ roots p H, (r : ZMod p) ∈ P.roots.toFinset := by
    intro r hr
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hP0, Polynomial.IsRoot.def]
    rw [mem_roots] at hr
    rw [hP, Polynomial.eval_map, Polynomial.eval₂_at_natCast]
    obtain ⟨k, hk⟩ := hr.2
    rw [hk]
    simp
  have hsum_image : ∑ a ∈ (roots p H).image (fun r : ℕ => (r : ZMod p)),
      P.rootMultiplicity a = ∑ r ∈ roots p H, P.rootMultiplicity (r : ZMod p) :=
    Finset.sum_image hinj
  rw [← hsum_image]
  calc ∑ a ∈ (roots p H).image (fun r : ℕ => (r : ZMod p)), P.rootMultiplicity a
      = ∑ a ∈ (roots p H).image (fun r : ℕ => (r : ZMod p)), P.roots.count a := by
        refine Finset.sum_congr rfl ?_
        intro a _
        rw [Polynomial.count_roots]
    _ ≤ ∑ a ∈ P.roots.toFinset, P.roots.count a := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
        · intro a ha
          simp only [Finset.mem_image] at ha
          obtain ⟨r, hr, rfl⟩ := ha
          exact hroot r hr
        · intro a _ _
          exact Nat.zero_le _
    _ = P.roots.card := Multiset.toFinset_sum_count_eq _
    _ ≤ P.natDegree := Polynomial.card_roots' P

end Work.KMTPlan.A6.ConcAux
