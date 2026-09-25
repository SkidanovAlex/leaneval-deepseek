import Mathlib
import Submission.NK.GlobalCFTdeep.AbstractH0

namespace NK.GlobalCFTdeep.SecondInequality

/-- `H0` is invariant under a `MulEquiv` of the acting groups with the same action: if `e : G ≃* G'` and the actions of `G` and `G'` on the commutative group `M` agree through `e`, then `Nat.card (H0 G M) = Nat.card (H0 G' M)`.  This is the transport that lets the subgroup action of `↥S` on `C_L` be replaced by the isomorphic direct action of `Gal(L/L^S)`.

Proof: the hypothesis identifies `fixedSubgroup G M` with `fixedSubgroup G' M` (use `Subgroup.ext` and the surjectivity of `e`), and reindexing the finite product along `e.toEquiv` (`Fintype.prod_equiv`) identifies `normHom G M` with `normHom G' M`; rewriting the two subgroup equalities makes the quotient types identical, so `Nat.card` agrees (`rw` then `rfl`, or `Nat.card_congr` of an explicit `MulEquiv` of quotients). -/
theorem natCard_H0_eq_of_mulEquiv {G G' M : Type*} [Group G] [Fintype G] [Group G']
    [Fintype G'] [CommGroup M] [MulDistribMulAction G M] [MulDistribMulAction G' M] (e : G ≃* G')
    (h : ∀ (g : G) (m : M),
      (MulDistribMulAction.toMulAut G' M (e g)) m = (MulDistribMulAction.toMulAut G M g) m) :
    Nat.card (NK.GlobalCFTdeep.H0 G M) = Nat.card (NK.GlobalCFTdeep.H0 G' M) := by
  -- The hypothesis, read as a statement about the two `smul` actions.
  have hsmul : ∀ (g : G) (m : M), e g • m = g • m := fun g m => h g m
  -- The two fixed-point subgroups are equal (surjectivity of `e` transports the condition).
  have hfix : NK.GlobalCFTdeep.fixedSubgroup G M = NK.GlobalCFTdeep.fixedSubgroup G' M := by
    ext x
    rw [NK.GlobalCFTdeep.mem_fixedSubgroup, NK.GlobalCFTdeep.mem_fixedSubgroup]
    constructor
    · intro hx g'
      obtain ⟨g, rfl⟩ := e.surjective g'
      rw [hsmul g x]
      exact hx g
    · intro hx g
      rw [← hsmul g x]
      exact hx (e g)
  -- The two norm maps are equal (reindex the product along `e`).
  have hnorm : NK.GlobalCFTdeep.normHom G M = NK.GlobalCFTdeep.normHom G' M := by
    ext x
    rw [NK.GlobalCFTdeep.normHom_apply, NK.GlobalCFTdeep.normHom_apply]
    exact Fintype.prod_equiv e.toEquiv _ _ (fun g => (hsmul g x).symm)
  -- Hence the two quotient types are literally the same type, so `Nat.card` agrees.
  have htype : (NK.GlobalCFTdeep.H0 G M : Type _) = NK.GlobalCFTdeep.H0 G' M := by
    unfold NK.GlobalCFTdeep.H0
    rw [hfix, hnorm]
  rw [htype]

end NK.GlobalCFTdeep.SecondInequality
