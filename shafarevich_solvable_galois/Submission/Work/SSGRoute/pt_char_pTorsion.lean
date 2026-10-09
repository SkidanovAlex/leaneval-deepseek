import Mathlib
import Submission.Work.SSGRoute.PTDefs
import Submission.Work.SSGRoute.e0b_bridge
import Submission.NK.NUV2.LC.unitsLevelH2_addOrderOf_realization
import Submission.NK.CFTLib.fundamentalClassElement
import Submission.NK.GlobalCFTdeep.SecondInequality.FundamentalClass
import Submission.Work.SSGRoute.pTorsion_zmod
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

open CategoryTheory

/-- **The `Ext`-cohomology of the idèle class group is group cohomology.**  For a finite Galois
extension `k ⊆ L` of number fields there is an additive isomorphism
`extH (classesK k L) 2 ≃+ H²(Gal(L/k), C_L)`, obtained by composing

* the `E0b` bridge `Work.SSGRoute.Bridge.E` between Mathlib's group cohomology and `Ext`-cohomology
  (`groupCohomology A 2 ≃+ extH A 2`), and
* the coefficient-ring transfer `NK.NUV2.LC.nonempty_addEquiv_groupCohomology_two_coeffTransfer`
  from the `CoeffInt = ULift ℤ`-coefficients of `PTDefs.classesK` to the `ℤ`-coefficients of
  `NK.GlobalCFT.IdeleClassGroup.rep` — the same carrier with the same `Gal(L/k)`-action, so the
  groups of inhomogeneous `2`-cocycles modulo `2`-coboundaries agree; and
* the definitional identification `NK.GlobalCFT.IdeleClassGroup.rep k L =
  Rep.ofDistribMulAction ℤ (L ≃ₐ[k] L) (Additive (IdeleClassGroup L))`.

This lets every theorem of `NK` about `H²(Gal(L/k), C_L)` — in particular the fundamental class
and the order computation — be transported to the `Ext`-vocabulary of the Poitou–Tate core. -/
theorem extH_classesK_two_addEquiv (k : Type) [Field k] [NumberField k]
    (L : Type) [Field L] [NumberField L] [Algebra k L] [FiniteDimensional k L] [IsGalois k L] :
    Nonempty (SSGRoute.PTExt.extH (SSGRoute.PTExt.classesK k L) 2 ≃+
      ↑(groupCohomology (NK.GlobalCFT.IdeleClassGroup.rep k L) 2)) := by
  obtain ⟨e₂⟩ := NK.NUV2.LC.nonempty_addEquiv_groupCohomology_two_coeffTransfer
    (k := SSGRoute.PTExt.Coeff) (k' := ℤ) (G := L ≃ₐ[k] L)
    (V := Additive (NK.GlobalCFT.IdeleClassGroup L))
  exact ⟨(Work.SSGRoute.Bridge.E 2 (L ≃ₐ[k] L) (SSGRoute.PTExt.classesK k L)).symm.trans e₂⟩

/-- **The `p`-torsion of the class-formation `H²` is `𝔽_p`.**  For a finite Galois `k ⊆ K ⊆ L`
whose degree `[L:k]` is divisible by `p`, the `p`-torsion subgroup of `H²(Gal(L/k), C_L)`
(`= extH (classesK k L) 2`) is cyclic of order `p`, hence isomorphic to `ZMod p`: there is an
additive subgroup `P` cut out by `p • v = 0` and an additive bijection `P ≃+ ZMod p`.

Guidance.  By the class formation (`NK.HassePrinciple.ideleShortComplex_shortExact`), the invariant
map and NK's `fundamentalClassElement` together with
`natCard_groupCohomology_two_le_card` give `H²(Gal(L/k), C_L) ≅+ ℤ/[L:k]`, a *cyclic* group of
order `[L:k]`.  Its `p`-torsion subgroup is therefore cyclic of order `p` when `p ∣ [L:k]`.  Note
this subgroup must be taken as a subgroup: for `[L:k] = p²m` a surjection onto `ZMod p` defined on
the *whole* group kills the `p`-torsion, so no `χ` defined on `extH … 2` itself can be injective on
the `p`-torsion — the subgroup form is the correct one (and it is the form the consumer
`Work.SSGRoute.tatePoitouEmbedding` needs: the Poitou–Tate pairing values are `p`-torsion).
The `K`-hypotheses are unused (the statement concerns only `L/k`) but are kept for uniformity with
the sibling nodes; `K := k` shows they are satisfiable. -/
theorem pt_char_pTorsion (p : ℕ) [Fact p.Prime] (k K : Type) [Field k] [NumberField k]
    [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (L : Type) [Field L] [NumberField L] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [FiniteDimensional k L] [IsGalois k L] (hp : p ∣ Module.finrank k L) :
    ∃ (P : AddSubgroup (SSGRoute.PTExt.extH (SSGRoute.PTExt.classesK k L) 2))
      (χ : P →+ ZMod p),
      (∀ v : SSGRoute.PTExt.extH (SSGRoute.PTExt.classesK k L) 2, v ∈ P ↔ p • v = 0) ∧
      Function.Bijective χ := by
  -- Hasse's fundamental class `HasseFundamentalClass` (Milne, CFT VIII.4.7): `H²(Gal(L/k), C_L)`
  -- has order `[L:k]` and contains an element of that order.
  have hFC := NK.GlobalCFTdeep.hasseFundamentalClass_of_fundamentalClassElement
    NK.CFTLib.fundamentalClassElement
  -- the `Ext`-cohomology of the class formation is the group cohomology of `C_L`.
  obtain ⟨e⟩ := extH_classesK_two_addEquiv k L
  -- the fundamental class, transported to `extH (classesK k L) 2`.
  obtain ⟨α, hα⟩ := hFC.fundamentalClass (K := k) (L := L)
  have ha : addOrderOf (e.symm α) = Nat.card (L ≃ₐ[k] L) :=
    (AddEquiv.addOrderOf_eq e.symm α).trans hα
  have hcard : Nat.card (SSGRoute.PTExt.extH (SSGRoute.PTExt.classesK k L) 2) =
      Nat.card (L ≃ₐ[k] L) := by
    rw [Nat.card_congr e.toEquiv, hFC.order]
  have hn : Nat.card (L ≃ₐ[k] L) ≠ 0 := Nat.card_ne_zero.mpr ⟨⟨1⟩, inferInstance⟩
  have hp' : p ∣ Nat.card (L ≃ₐ[k] L) := by
    rw [IsGalois.card_aut_eq_finrank k L]; exact hp
  exact Work.SSGRoute.pTorsion_zmod (SSGRoute.PTExt.extH (SSGRoute.PTExt.classesK k L) 2) p
    (Nat.card (L ≃ₐ[k] L)) hn hp' (e.symm α) ha hcard

end Work.SSGRoute
