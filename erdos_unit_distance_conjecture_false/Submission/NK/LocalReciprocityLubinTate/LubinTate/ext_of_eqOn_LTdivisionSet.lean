import Mathlib
import Submission.NK.LocalReciprocityLubinTate.LubinTate.EisFactor

namespace NK.LocalReciprocityLubinTate.LubinTate

universe u

/-- **An automorphism of a Lubin–Tate level is determined by its values on the division points.**

The Lubin–Tate level `K_n = F(Λ_n)` is generated over `F` by the set `Λ_n` of `π^n`-division
points (`NK.LocalReciprocityLubinTate.LTdivisionSet`).  Consequently two `F`-algebra
automorphisms of `K_n` which agree on `Λ_n` are equal: they agree on a generating set, hence
everywhere, since additive, multiplicative and inversion structure plus `F`-linearity rebuild the
whole field.  (The hypothesis `hq : 2 ≤ q` is not needed for this purely field-theoretic
statement; it is kept so that the lemma can be applied directly at the Lubin–Tate levels.) -/
theorem ext_of_eqOn_LTdivisionSet (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] (π : F) (q n : ℕ) (hq : 2 ≤ q)
    {σ τ : ↥(NK.LocalReciprocityLubinTate.LTLevel F π q n) ≃ₐ[F]
      ↥(NK.LocalReciprocityLubinTate.LTLevel F π q n)}
    (h : ∀ x : ↥(NK.LocalReciprocityLubinTate.LTLevel F π q n),
      ((x : AlgebraicClosure F) ∈ NK.LocalReciprocityLubinTate.LTdivisionSet F π q n) →
      σ x = τ x) :
    σ = τ := by
  have hhom : σ.toAlgHom = τ.toAlgHom :=
    IntermediateField.adjoin_algHom_ext (F := F)
      (s := NK.LocalReciprocityLubinTate.LTdivisionSet F π q n)
      (fun x hx => h ⟨x, IntermediateField.subset_adjoin F _ hx⟩ hx)
  exact AlgEquiv.ext fun x => AlgHom.congr_fun hhom x

end NK.LocalReciprocityLubinTate.LubinTate
