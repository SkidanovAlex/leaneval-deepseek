import Mathlib
import Submission.Work.Kunneth.EZAWTensor
import Submission.Work.Kunneth.AWAux
import Submission.Work.Kunneth.EZMap
import Submission.Work.Kunneth.AW

/-!
# The model complexes for the Eilenberg–Zilber homotopy `ezMap ≫ awMap ≃ 𝟙`

This file sets up the vocabulary of the acyclic-models argument for the second Eilenberg–Zilber
chain homotopy, i.e. that the composite `ezMap ≫ awMap` on `C_*(X) ⊗_ℤ C_*(Y)` is chain homotopic
to the identity.

* `SdS n` — the standard `n`-simplex `Δ[n]` as a simplicial set;
* `sMod n = C_*(Δ[n])` and `tMod p q = C_*(Δ[p]) ⊗_ℤ C_*(Δ[q])`, the `(p,q)`-model;
* `univS n` — the universal `n`-simplex of `Δ[n]`;
* `U p q` — the universal element `σ_p ⊗ τ_q` of the model, in degree `p+q`;
* `Ezaw X Y = ezMap X Y ≫ awMap X Y : tChain X Y ⟶ tChain X Y`;
* `Em p q` — the defect `(EZ∘AW)(U p q) - U p q` of the model.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open scoped MonoidalCategory TensorProduct Simplicial

namespace Work.Kunneth

noncomputable section

attribute [-instance] AddCommGroup.toIntModule

/-- The standard `n`-simplex, as a simplicial set. -/
abbrev SdS (n : ℕ) : SSet := SSet.stdSimplex.obj ⦋n⦌

/-- The singular chains of the standard `n`-simplex. -/
abbrev sMod (n : ℕ) : ChainComplex (ModuleCat ℤ) ℕ := sChain (SdS n)

/-- **The `(p,q)`-model**: the Koszul tensor product of the chain complexes of `Δ[p]` and
`Δ[q]`. -/
abbrev tMod (p q : ℕ) : ChainComplex (ModuleCat ℤ) ℕ := tpC (sMod p) (sMod q)

/-- The universal `n`-simplex `id_n` of the standard simplex `Δ[n]`. -/
noncomputable def univS (n : ℕ) : (SdS n) _⦋n⦌ := SSet.stdSimplex.objEquiv.symm (𝟙 ⦋n⦌)

/-- **The universal element `σ_p ⊗ τ_q`** of the `(p,q)`-model, in total degree `p + q`. -/
noncomputable def U (p q : ℕ) : ↥((tMod p q).X (p + q)) :=
  tpLof (sMod p) (sMod q) (p + q) ⟨(p, q), rfl⟩
    (genCh (SdS p) (univS p) ⊗ₜ[ℤ] genCh (SdS q) (univS q))

/-- **The composite `ezMap ≫ awMap`** as a chain map `C_*(X) ⊗_ℤ C_*(Y) ⟶ C_*(X) ⊗_ℤ C_*(Y)`. -/
def Ezaw (X Y : SSet) : tChain X Y ⟶ tChain X Y := ezMap X Y ≫ awMap X Y

/-- The `n`-th component of `Ezaw`, on elements. -/
noncomputable def EzawLin (X Y : SSet) (n : ℕ) :
    ↥((tChain X Y).X n) →ₗ[ℤ] ↥((tChain X Y).X n) := ((Ezaw X Y).f n).hom

/-- The `n`-th component of `Ezaw`, on the underlying direct sum. -/
lemma EzawLin_apply (X Y : SSet) (n : ℕ) (z : ↥((tChain X Y).X n)) :
    EzawLin X Y n z = ((Ezaw X Y).f n).hom z := rfl

/-- The chain map on the tensor complexes induced by a pair of simplicial maps `f`, `g`. -/
noncomputable def ind {X X' Y Y' : SSet} (f : X ⟶ X') (g : Y ⟶ Y') :
    tChain X Y ⟶ tChain X' Y' :=
  tpMap (sChain X) (sChain X') (sChain Y) (sChain Y')
    (SSet.chainComplexMap f zz) (SSet.chainComplexMap g zz)

/-- The `i`-th coface map of the `(p,q)`-model in the first variable:
`(Δ[p]⊗Δ[q]) ⟶ (Δ[p+1]⊗Δ[q])`. -/
noncomputable def phiMod (p q : ℕ) (i : Fin (p + 2)) : tMod p q ⟶ tMod (p + 1) q :=
  ind (SSet.stdSimplex.map (SimplexCategory.δ i)) (𝟙 (SdS q))

/-- The `j`-th coface map of the `(p,q)`-model in the second variable:
`(Δ[p]⊗Δ[q]) ⟶ (Δ[p]⊗Δ[q+1])`. -/
noncomputable def psiMod (p q : ℕ) (j : Fin (q + 2)) : tMod p q ⟶ tMod p (q + 1) :=
  ind (𝟙 (SdS p)) (SSet.stdSimplex.map (SimplexCategory.δ j))

/-- **The defect of the `(p,q)`-model**: `(EZ∘AW)(σ_p ⊗ τ_q) - σ_p ⊗ τ_q`. -/
noncomputable def Em (p q : ℕ) : ↥((tMod p q).X (p + q)) :=
  EzawLin (SdS p) (SdS q) (p + q) (U p q) - U p q

end

end Work.Kunneth
