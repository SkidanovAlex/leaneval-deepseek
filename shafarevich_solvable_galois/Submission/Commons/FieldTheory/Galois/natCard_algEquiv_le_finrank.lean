import Mathlib.FieldTheory.SeparableDegree
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Commons.FieldTheory.Galois

/-- A finite-dimensional field extension `L / K` has at most `[L : K]` `K`-algebra automorphisms.
This strengthens `Commons.FieldTheory.Galois.card_algEquiv_le_finrank`, which assumes in addition
that `L / K` is separable: the injection `Aut_K(L) ↪ Emb_K(L, K̄)` is available in general, and
the separable degree is at most the degree for any finite extension. -/
theorem natCard_algEquiv_le_finrank {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] : Nat.card (L ≃ₐ[K] L) ≤ Module.finrank K L := by
  calc Nat.card (L ≃ₐ[K] L)
      ≤ Nat.card (L →ₐ[K] AlgebraicClosure L) := by
        refine Nat.card_le_card_of_injective
          (fun σ : L ≃ₐ[K] L => (IsScalarTower.toAlgHom K L (AlgebraicClosure L)).comp σ.toAlgHom) ?_
        intro σ τ h
        ext x
        have hx := AlgHom.congr_fun h x
        exact (algebraMap L (AlgebraicClosure L)).injective hx
    _ = Field.finSepDegree K L := rfl
    _ ≤ Module.finrank K L := Field.finSepDegree_le_finrank K L

end Commons.FieldTheory.Galois
