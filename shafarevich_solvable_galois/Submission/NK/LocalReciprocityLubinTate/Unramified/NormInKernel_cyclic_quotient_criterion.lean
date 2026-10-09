import Mathlib
import Submission.NK.LocalReciprocityLubinTate.Unramified.TowerSymbol
import Submission.NK.LocalReciprocityLubinTate.GroupTheory.subgroup_eq_of_forall_map_eq_of_isCyclic_quotient
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The norm-compatibility of the Artin symbol is detected in the cyclic quotients of the level

`NK.LocalReciprocityLubinTate.NormInKernel` — the canonical Artin symbol of the Lubin–Tate tower
kills norms — is a statement about a subgroup of the level's Galois group: the statement at a level
`E_{m,n}` and a subfield `L` is exactly

`Φ(N_{L/F} Lˣ) = Gal(E_{m,n}/L)`,   `Φ = T.symbol m n`,

and both sides are subgroups of `Gal(E_{m,n}/F)`.

This file records the *canonicity criterion* for that identity, as a theorem: by
`NK.LocalReciprocityLubinTate.GroupTheory.subgroup_eq_of_forall_map_eq_of_isCyclic_quotient` a
subgroup of a finite abelian group is determined by its images in the **cyclic** quotients of the
group.  Consequently

* `NK.LocalReciprocityLubinTate.normInKernel_at_of_cyclic_quotients` — the norm-compatibility of
  the symbol at a level `(m,n)` *follows from* the statement that the images of `N_{L/F} Lˣ` and of
  `Gal(E_{m,n}/L)` agree in every cyclic quotient of `Gal(E_{m,n}/F)`.

Equivalently (and this is how the statement is used in the chapter's README §21): the residue
`NormInKernel` may be replaced by the same statement "at all cyclic quotients of the level", i.e. at
the subextensions `M ⊆ E_{m,n}` whose Galois group is cyclic.  This is a *strict sharpening of the
residue*: it removes from it all the non-cyclic part of the level's Galois group.

## Main result

* `NK.LocalReciprocityLubinTate.normInKernel_at_of_cyclic_quotients`.
-/

open scoped Classical

namespace NK.LocalReciprocityLubinTate

universe u v

set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

variable {F : Type u} {F' : Type v} [Field F] [Field F'] [Algebra F F'] [IsGalois F F']
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

/-- **Norm-compatibility is detected in the cyclic quotients of the level's Galois group.**

Let `T` be a Lubin–Tate symbol tower and `(m,n)` a level.  Suppose that for every subgroup `H` of
`Gal(E_{m,n}/F)` with cyclic quotient `Gal(E_{m,n}/F) ⧸ H`, the images of the norm group
`N_{L/F} Lˣ` and of the stabiliser `Gal(E_{m,n}/L)` of a finite abelian subfield `L ≤ E_{m,n}` under
the quotient map agree.  Then the canonical symbol kills norms at `L`: for `x ∈ N_{L/F} Lˣ` the
automorphism `T.symbol m n x` fixes `L` pointwise.

The proof is the canonicity criterion
`NK.LocalReciprocityLubinTate.GroupTheory.subgroup_eq_of_forall_map_eq_of_isCyclic_quotient`: the
image `Φ(N_L)` of the norm group and the stabiliser `Gal(E/L)` are subgroups of the finite abelian
group `Gal(E/F)` whose images agree in every cyclic quotient, hence they are equal. -/
theorem normInKernel_at_of_cyclic_quotients
    {π : Fˣ} {a : ℕ → ℕ} {q : ℕ} (T : LubinTateSymbolTower F F' π a (higherUnits F) q)
    (m n : ℕ)
    (L : IntermediateField F (NK.LocalReciprocity.maxAbelianSubext F F'))
    [FiniteDimensional F L] [Normal F L]
    (hLE : L ≤ T.level m n)
    (B : Subgroup (↥(T.level m n) ≃ₐ[F] ↥(T.level m n)))
    (hB : ∀ σ : ↥(T.level m n) ≃ₐ[F] ↥(T.level m n),
      σ ∈ B ↔ ∀ y : ↥L, σ ⟨y.1, hLE y.2⟩ = ⟨y.1, hLE y.2⟩)
    (h : ∀ (H : Subgroup (↥(T.level m n) ≃ₐ[F] ↥(T.level m n))) [H.Normal],
        IsCyclic ((↥(T.level m n) ≃ₐ[F] ↥(T.level m n)) ⧸ H) →
        Subgroup.map (QuotientGroup.mk' H)
            (Subgroup.map (T.symbol m n) (NK.LocalReciprocity.normGroup F ↥L)) =
          Subgroup.map (QuotientGroup.mk' H) B) :
    ∀ x ∈ NK.LocalReciprocity.normGroup F ↥L,
      ∀ y : ↥L, (T.symbol m n x) ⟨y.1, hLE y.2⟩ = ⟨y.1, hLE y.2⟩ := by
  classical
  haveI hfdE : FiniteDimensional F ↥(T.level m n) := T.finiteDimensional m n
  haveI hnormE : Normal F ↥(T.level m n) := T.normal m n
  -- the level's Galois group is abelian, so the canonicity criterion applies
  letI : CommGroup (↥(T.level m n) ≃ₐ[F] ↥(T.level m n)) :=
    { (inferInstance : Group (↥(T.level m n) ≃ₐ[F] ↥(T.level m n))) with
      mul_comm := T.commutative m n }
  have hAB : Subgroup.map (T.symbol m n) (NK.LocalReciprocity.normGroup F ↥L) = B :=
    NK.LocalReciprocityLubinTate.GroupTheory.subgroup_eq_of_forall_map_eq_of_isCyclic_quotient
      _ _
      (fun H hcyc => h H hcyc)
  intro x hx y
  have hxmem : T.symbol m n x ∈ B := by
    rw [← hAB]
    exact Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
  exact (hB (T.symbol m n x)).mp hxmem y

end NK.LocalReciprocityLubinTate
