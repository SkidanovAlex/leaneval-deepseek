import Mathlib.FieldTheory.SeparableDegree
import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

namespace Commons.FieldTheory.Galois

/-- The number of `K`-algebra automorphisms of a finite-dimensional field extension `L/K`
is at most the degree `[L : K]`. This holds without any separability assumption.

The proof is elementary: composing with the canonical embedding `L → Ā` (the algebraic closure
of `L`) gives an injection from `Aut_K(L)` into the (finite) set `Field.Emb K L` of `K`-algebra
embeddings `L → Ā`, whose cardinality is the separable degree `Field.finSepDegree K L`, which is
at most `[L : K]`. -/
theorem card_algEquiv_le_finrank {K L : Type*} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] [Algebra.IsSeparable K L] :
    Nat.card (L ≃ₐ[K] L) ≤ Module.finrank K L := by
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