import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RepresentationTheory.Rep.Res
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Submission.Work.SSGRoute.lde_stabIncl
import Submission.Work.SSGRoute.local_pTorsion_card
import Submission.Work.SSGRoute.nonempty_extH_addEquiv_mulEquiv
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `p`-torsion of the local Brauer group at a Sylow level

The local input of the Poitou–Tate assembly: for a subgroup `S` of a decomposition group of a place,
the `p`-torsion of `H²(S, L_{w'}ˣ)` has `p` elements as soon as `p ∣ |S|`.

The group `S` occurring in the statement is
`S = (P.comap (decompK w).subtype).comap f ≤ D_{w'} ≤ Gal(L/k)`, i.e. the level-`w'` incarnation of
the subgroup `P ≤ D_w` of the decomposition group at the lower level `K`; in the intended
application `P` is a Sylow `p`-subgroup of `D_w`, whence `p ∣ |S|`.

The proof is the base change `k ⊆ k' = K^P`, the fixed field of `P`: the level-`w'` group `S` is the
decomposition group of `w'` over `k'` (`Work.SSGRoute.stabInclEquivL`), the local units
representation restricted along that group isomorphism is the local units representation at the
level `k'` (`Work.SSGRoute.res_stabIncl_localUnitsRep_eq`, definitionally), and at a single level the
`p`-torsion of the local Brauer group `H²(D_{w'}, L_{w'}ˣ)` has `p` elements as soon as
`p ∣ |D_{w'}|` (`Work.SSGRoute.local_pTorsion_card`).
-/

set_option linter.style.haveILetI false

namespace Work.SSGRoute

open SSGRoute.PTExt CategoryTheory

/-- **`p`-torsion is invariant under additive equivalence**: an additive equivalence `A ≃+ B`
induces an equivalence of `p`-torsion subgroups `{x : A // p • x = 0} ≃ {y : B // p • y = 0}`,
hence an equality of their cardinalities. -/
theorem natCard_pTorsion_congr_addEquiv {A B : Type} [AddCommGroup A] [AddCommGroup B]
    (e : A ≃+ B) (p : ℕ) :
    Nat.card {x : A // p • x = 0} = Nat.card {y : B // p • y = 0} :=
  Nat.card_congr (Equiv.subtypeEquiv e.toEquiv (fun x => by
    show p • x = 0 ↔ p • (e : A → B) x = 0
    rw [← map_nsmul e p x, AddEquiv.map_eq_zero_iff]))

theorem pTorsion_card_sylowLevel (p : ℕ) [Fact p.Prime] (k K : Type) [Field k] [NumberField k]
    [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (w : NK.GlobalCFT.Place K) (P : Subgroup (K ≃ₐ[k] K))
    (hPD : P ≤ SSGRoute.PTExt.decompK (k := k) w)
    (L : Type) [Field L] [NumberField L] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
      [FiniteDimensional k L] [IsGalois k L]
    (w' : NK.GlobalCFT.Place L) (hw' : NK.GlobalCFT.Place.LiesOver w' w)
    (f : MulAction.stabilizer (L ≃ₐ[k] L) w' →* SSGRoute.PTExt.decompK (k := k) w)
    (hf : ∀ σ, ((f σ : SSGRoute.PTExt.decompK (k := k) w) : K ≃ₐ[k] K)
      = SSGRoute.PTExt.galRes k K L (σ : L ≃ₐ[k] L))
    (hpS : p ∣ Nat.card (((P.comap (SSGRoute.PTExt.decompK (k := k) w).subtype).comap f))) :
    Nat.card {x : SSGRoute.PTExt.extH (Rep.res (((P.comap
        (SSGRoute.PTExt.decompK (k := k) w).subtype).comap f).subtype)
        (NK.HassePrinciple.localUnitsRep k L w')) 2 // p • x = 0} = p := by
  classical
  -- `L/k'` is again Galois, since `L/k` is and `k ⊆ k' = K^P`
  haveI hgal : IsGalois ↥(IntermediateField.fixedField P) L :=
    IsGalois.tower_top_of_isGalois k ↥(IntermediateField.fixedField P) L
  -- `p` divides the order of the decomposition group of `w'` over `k'`
  have hp' : p ∣ Nat.card (decompK (k := ↥(IntermediateField.fixedField P)) w') := by
    rw [Nat.card_congr (stabInclEquivL k K L P w hPD w' hw' f hf).toEquiv]
    exact hpS
  -- the local units module at the level `k'` is, definitionally, the restriction of the local
  -- units module at the level `k` along the group isomorphism `D_{w'}(L/k') ≃* S`
  have hmod : Rep.res (stabInclEquivL k K L P w hPD w' hw' f hf).toMonoidHom
      (Rep.res ((P.comap (decompK (k := k) w).subtype).comap f).subtype
        (NK.HassePrinciple.localUnitsRep k L w'))
      = NK.HassePrinciple.localUnitsRep ↥(IntermediateField.fixedField P) L w' := rfl
  -- change of groups along that isomorphism on `Ext²`
  obtain ⟨f₂⟩ := nonempty_extH_addEquiv_mulEquiv (stabInclEquivL k K L P w hPD w' hw' f hf)
    (Rep.res ((P.comap (decompK (k := k) w).subtype).comap f).subtype
      (NK.HassePrinciple.localUnitsRep k L w')) 2
  rw [hmod] at f₂
  -- hence the `p`-torsion cardinalities agree; and at the level `k'` the count is `p`
  exact (natCard_pTorsion_congr_addEquiv f₂ p).trans
    (local_pTorsion_card p ↥(IntermediateField.fixedField P) L w' hp')

end Work.SSGRoute
