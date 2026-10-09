import Mathlib
import Submission.Work.SSGRoute.PTDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `pushClass`: pushing a level-`K` coefficient class to a higher level `L`

Vocabulary shared by the pieces of `Work.SSGRoute.phi0_trivial_epi` (node E4 of
`DESIGN_EXT.md`).

For `k ⊆ K ⊆ L` (number fields, `K/k` finite Galois) and a `Gal(K/k)`-module `V`, a class
`c : 𝔽_p ⟶ C_K` (i.e. `c ∈ Ext⁰_{Gal(K/k)}(V, C_K)`, equivalently `c(1) ∈ C_k[p]`) pushes
forward to the class
`pushClass k K L V c : V ⟶ C_L`
as `V ≅ res V --res c--> res C_K --classIncl--> C_L`.

This is the coefficient map appearing in the conclusion of `phi0_trivial_epi`: the level-`L`
value of the family determined by `c` is the level-`L` Yoneda product with `pushClass k K L c`.
-/

namespace Work.SSGRoute

open SSGRoute.PTExt CategoryTheory

/-- Push a level-`K` coefficient class to the level `L ⊇ K`: the underlying map is the identity
from the trivial module, followed by the restriction of `c` and the canonical inclusion of idèle
class groups `C_K → C_L`. -/
noncomputable def pushClass (k K L : Type) [Field k] [NumberField k] [Field K] [NumberField K]
    [Field L] [NumberField L]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [FiniteDimensional k K] [IsGalois k K]
    (V : Type) [AddCommGroup V] [Module Coeff V]
    (c : Rep.trivial Coeff (K ≃ₐ[k] K) V ⟶ classesK k K) :
    Rep.trivial Coeff (L ≃ₐ[k] L) V ⟶ classesK k L :=
  trivRes (galRes k K L) V ≫ (Rep.resFunctor (galRes k K L)).map c ≫ classIncl k K L

/-- `pushClass` at the level `K` itself is the identity (up to the canonical identifications). -/
lemma pushClass_self (k K : Type) [Field k] [NumberField k] [Field K] [NumberField K]
    [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (V : Type) [AddCommGroup V] [Module Coeff V]
    (c : Rep.trivial Coeff (K ≃ₐ[k] K) V ⟶ classesK k K) :
    pushClass k K K V c
      = trivRes (galRes k K K) V ≫ (Rep.resFunctor (galRes k K K)).map c ≫ classIncl k K K :=
  rfl

/-- `phiTriv` at the level `L` of a level-`K` coefficient class is the level-`L` Yoneda pairing with
the pushed-forward class `pushClass k K L c`.  (Both sides are composite `Ext` classes; the
coincidence is the associativity of Yoneda composition and the fact that the two maps between
`𝔽_p` and its restriction are inverse to each other.) -/
theorem phiTriv_mk₀_pushClass (p : ℕ) [Fact p.Prime] (k K L : Type) [Field k] [NumberField k]
    [Field K] [NumberField K] [Field L] [NumberField L]
    [Algebra k K] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [FiniteDimensional k K] [IsGalois k K] [FiniteDimensional k L] [IsGalois k L]
    (c : Rep.trivial Coeff (K ≃ₐ[k] K) (ZMod p) ⟶ classesK k K)
    (h : extH (Rep.trivial Coeff (L ≃ₐ[k] L) (ZMod p)) 2) :
    phiTriv (k := k) (K := K) (L := L) (ZMod p) (Abelian.Ext.mk₀ c) h
      = pairK (k := k) (K := L) (Abelian.Ext.mk₀ (pushClass k K L (ZMod p) c)) h := by
  simp only [phiTriv, phiAt, levelPair, pairK, yonedaPair, pushClass, extRes,
    Abelian.Ext.mapExactFunctor_mk₀,
    Abelian.Ext.mk₀_comp_mk₀,
    Abelian.Ext.comp_assoc_of_second_deg_zero]

end Work.SSGRoute
