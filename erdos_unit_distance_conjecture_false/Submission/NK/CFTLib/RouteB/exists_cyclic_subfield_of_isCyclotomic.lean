import Mathlib

namespace NK.CFTLib.RouteB

open IntermediateField

/-- **A cyclotomic extension contains a prescribed cyclic subfield.**  Let `L / K` be a finite
extension with `IsCyclotomicExtension {q} K L` for a prime `q`, and let `n ∣ Nat.card Gal(L/K)`.
Then `L` has an intermediate field `M` with `M / K` finite Galois, cyclic, of degree `n`
(`Nat.card Gal(M/K) = n`).

Proof sketch.  `IsCyclotomicExtension.isGalois` makes `L/K` Galois, and
`IsPrimitiveRoot.autToPow_injective` (with `μ := IsCyclotomicExtension.zeta q K L`,
`IsCyclotomicExtension.zeta_spec`) embeds `Gal(L/K)` into `(ZMod q)ˣ`, which is cyclic since `q` is
prime (`IsCyclic (ZMod q)ˣ`, `Mathlib/RingTheory/ZMod/UnitsCyclic.lean`).  Hence `Gal(L/K)` is a
finite cyclic (commutative) group.  Take `H := (powMonoidHom n).range ≤ Gal(L/K)`; its index is
`(Nat.card Gal(L/K)).gcd n = n` (`IsCyclic.index_powMonoidHom_range`).  As the group is commutative
`H` is normal, so `M := IntermediateField.fixedField H` is Galois over `K`
(`IsGalois.of_fixedField_normal_subgroup`) and `Gal(M/K) ≃ Gal(L/K) ⧸ H`
(`IsGalois.normalAutEquivQuotient`), a quotient of a cyclic group, hence cyclic of order `n`. -/
theorem exists_cyclic_subfield_of_isCyclotomic {K L : Type} [Field K] [Field L] [Algebra K L]
    [FiniteDimensional K L] {q n : ℕ} [NeZero q] (hq : Nat.Prime q)
    (hcyc : IsCyclotomicExtension {q} K L) (hn : n ∣ Nat.card Gal(L/K)) :
    ∃ M : IntermediateField K L, IsGalois K ↥M ∧ IsCyclic (↥M ≃ₐ[K] ↥M) ∧
      Nat.card (↥M ≃ₐ[K] ↥M) = n := by
  -- `L/K` is Galois (cyclotomic extensions are Galois).
  have : IsGalois K L := IsCyclotomicExtension.isGalois {q} K L
  -- A primitive `q`-th root of unity in `L`, giving the embedding `Gal(L/K) ↪ (ZMod q)ˣ`.
  have hμ : IsPrimitiveRoot (IsCyclotomicExtension.zeta q K L) q :=
    IsCyclotomicExtension.zeta_spec q K L
  have : IsCyclic (ZMod q)ˣ := ZMod.isCyclic_units_prime hq
  have hG : IsCyclic Gal(L/K) :=
    isCyclic_of_injective (IsPrimitiveRoot.autToPow K hμ)
      (IsPrimitiveRoot.autToPow_injective K hμ)
  -- A cyclic group is commutative (in particular all its subgroups are normal).
  let : CommGroup Gal(L/K) := IsCyclic.commGroup
  -- The subgroup of `n`-th powers.
  set H : Subgroup Gal(L/K) := (powMonoidHom n).range with hH
  have hHidx : H.index = n := by
    have h := IsCyclic.index_powMonoidHom_range Gal(L/K) n
    rw [hH, h, Nat.gcd_eq_right hn]
  -- The fixed field of the subgroup of `n`-th powers.
  let M : IntermediateField K L := IntermediateField.fixedField H
  refine ⟨M, IsGalois.of_fixedField_normal_subgroup H, ?_, ?_⟩
  · -- `Gal(M/K) ≃ Gal(L/K) ⧸ H` is a quotient of the cyclic group `Gal(L/K)`.
    have he : Gal(L/K) ⧸ H ≃* Gal(↥M/K) := IsGalois.normalAutEquivQuotient H
    have h1 : IsCyclic (Gal(L/K) ⧸ H) :=
      isCyclic_of_surjective (QuotientGroup.mk' H) (QuotientGroup.mk'_surjective H)
    exact (MulEquiv.isCyclic he).mp h1
  · -- Its order is the index of `H`, i.e. `n`.
    rw [← Nat.card_congr (IsGalois.normalAutEquivQuotient H).toEquiv, ← Subgroup.index_eq_card]
    exact hHidx

end NK.CFTLib.RouteB
