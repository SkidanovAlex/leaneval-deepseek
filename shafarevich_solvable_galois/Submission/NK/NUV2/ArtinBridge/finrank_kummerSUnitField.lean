import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Submission.NK.GlobalCFTdeep.SecondInequality.tUnits_index_powSubgroup
import Submission.NK.NUV2.ArtinBridge.KummerSUnitField
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.NUV2.ArtinBridge

/-- The degree of the Kummer `S`-field `K(U(S)^{1/p})` over `K` is `p ^ |S|`.

Route: `finrank_kummerAdjoin_of_le` reduces the degree to the index of `Kˣ^p` in
`TUnits S ⊔ Kˣ^p`, which by `index_sup_mul_index_inf` (applied with `A = TUnits S`,
`B = (TUnits S)^p`, `C = Kˣ^p`) and `tUnits_inf_powSubgroup` equals `[TUnits S : (TUnits S)^p]`,
which `tUnits_index_powSubgroup` computes as `p ^ Nat.card S`. -/
theorem finrank_kummerSUnitField {K : Type} [Field K] [NumberField K] {Ω : Type*} [Field Ω]
    [Algebra K Ω] [IsSepClosure K Ω] {p : ℕ} (hp : p.Prime) {ζ : K} (hζ : IsPrimitiveRoot ζ p)
    (S : Finset (NK.GlobalCFT.Place K))
    (hSinf : ∀ w : NumberField.InfinitePlace K, NK.GlobalCFT.Place.ofInfinite w ∈ S) :
    Module.finrank K ↥(NK.NUV2.ArtinBridge.kummerSUnitField K Ω p S) = p ^ S.card := by
  classical
  -- Write `U = U(S) = TUnits S` and `P = (Kˣ)^p`; the Kummer field is `K(U^{1/p})` for the
  -- subgroup `U ⊔ P`, and `finrank_kummerAdjoin_of_le` computes its degree as the index of
  -- `P` in `U ⊔ P`.
  set U : Subgroup Kˣ := NK.GlobalCFTdeep.TUnits (L := K) (S : Set (NK.GlobalCFT.Place K))
    with hU
  set P : Subgroup Kˣ := NK.LocalAnabelian.powSubgroup p K with hP
  have hSP : NK.NUV2.ArtinBridge.sUnitKummerGroup (K := K) p S = U ⊔ P := by
    rw [NK.NUV2.ArtinBridge.sUnitKummerGroup, hU, hP]
  have hfield : NK.NUV2.ArtinBridge.kummerSUnitField K Ω p S
      = NK.GlobalCFTdeep.SecondInequality.kummerAdjoin (K' := Ω) p (U ⊔ P) := by
    rw [NK.NUV2.ArtinBridge.kummerSUnitField_eq_kummerAdjoin, hSP]
  rw [hfield]
  rw [NK.GlobalCFTdeep.SecondInequality.finrank_kummerAdjoin_of_le (K' := Ω) hp hζ (U ⊔ P)
    le_sup_right]
  rw [← hP]
  -- The index of `P` in `U ⊔ P` is (second isomorphism theorem) the index of `U ⊓ P` in `U`.
  have h1 : (P.subgroupOf (U ⊔ P)).index = ((U ⊓ P).subgroupOf U).index := by
    show P.relIndex (U ⊔ P) = (U ⊓ P).relIndex U
    rw [sup_comm, Subgroup.relIndex_sup_left]
    exact (Subgroup.inf_relIndex_left U P).symm
  -- And `U ⊓ P = U^p`, since a `p`-th power which is an `S`-unit is a `p`-th power of an
  -- `S`-unit.
  have h2 : ((U ⊓ P).subgroupOf U).index
      = ((Subgroup.map (powMonoidHom p) U).subgroupOf U).index := by
    have hUP : U ⊓ P = Subgroup.map (powMonoidHom p) U := by
      rw [hU, hP]
      exact NK.NUV2.ArtinBridge.tUnits_inf_powSubgroup (K := K) hp S
    rw [hUP]
  -- Finally `[U : U^p] = p ^ |S|` (Dirichlet's `S`-unit theorem plus the `p`-torsion of `U`).
  have h3 : ((Subgroup.map (powMonoidHom p) U).subgroupOf U).index = p ^ S.card := by
    have hTinf : ∀ w : NK.GlobalCFT.Place K, w.IsInfinite → w ∈ S := by
      intro w hw
      obtain ⟨w', rfl⟩ := NK.GlobalCFT.Place.isInfinite_iff.mp hw
      exact hSinf w'
    have h := NK.GlobalCFTdeep.SecondInequality.tUnits_index_powSubgroup (K := K) p hp hζ S
      hTinf
    rw [hU, h]
    simp
  rw [h1, h2, h3]

end NK.NUV2.ArtinBridge
