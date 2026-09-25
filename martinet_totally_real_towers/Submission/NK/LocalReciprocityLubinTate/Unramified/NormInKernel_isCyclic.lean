import Mathlib
import Submission.NK.LocalReciprocityLubinTate.Unramified.TowerSymbol
import Submission.Commons.GroupTheory.SpecificGroups.Cyclic.subgroup_eq_of_card_eq
import Submission.NK.LocalCFT.NormGroup.normGroup_le_iff

/-!
# The norm-compatibility of the Artin symbol at a level with cyclic Galois group

`NK.LocalReciprocityLubinTate.NormInKernel` is the classical statement that the canonical Artin
symbol of the Lubin–Tate tower kills norms: if `L ≤ E_{m,n}` is a finite abelian level and `x` lies in
the norm group `N_{L/F} Lˣ`, then the symbol at the level `E_{m,n}` acts trivially on `L`.  See the
discussion in `Unramified/TowerSymbol.lean`.

This file proves the statement **unconditionally** whenever the Galois group of the level is
**cyclic**:

* `NK.LocalReciprocityLubinTate.normInKernel_of_level_isCyclic` — for a single level `E_{m,n}` with
  `IsCyclic Gal(E_{m,n}/F)`, the symbol kills norms at every subfield `L ≤ E_{m,n}`;
* `NK.LocalReciprocityLubinTate.NormInKernel.of_isCyclic` — the same, assembled into the full
  `NormInKernel` statement for a tower all of whose levels have cyclic Galois group.

## Why cyclicity is enough

The point is that the norm group sees only *cardinalities*.  Write `Φ = symbol m n`, so that `Φ` is a
surjection `Fˣ ↠ Gal(E/F)` with kernel `N_{E/F} Eˣ` (`T.symbol_surjective`, `T.symbol_ker`), and put
`A := Φ(N_{L/F} Lˣ)`, `B := Gal(E/L)`.  Then

* `|A| = [N_L : N_E] = [E : L]` (the norm index theorem `NK.LocalArtin.NormIndex`, which is a
  *theorem* for `Q.adicCompletion K`, together with the multiplicativity of the index), and
* `|B| = [E : L]` (Galois theory),

so `A` and `B` are subgroups of `Gal(E/F)` of the same cardinality.  If `Gal(E/F)` is **cyclic** there
is only one subgroup of each cardinality, so `A = B`
(`Commons.GroupTheory.SpecificGroups.Cyclic.subgroup_eq_of_card_eq`), which is exactly the assertion
that `Φ` maps `N_L` onto `Gal(E/L)`, i.e. that `Φ(x)` fixes `L` for `x ∈ N_L`.

For a `p`-adic field `F` with residue degree `1` (e.g. `F = ℚ_[p]` with `p` odd) the Lubin–Tate levels
`K_n = F(Λ_n)` do have cyclic Galois group `≅ (𝒪[F]/π^n)^× = (ℤ/p^n)^×`, so this covers them; for a
general level `E_{m,n} = F^{ur}_{a m}·K_{n+1}` the group is the product
`ℤ/(a m) × (𝒪[F]/π^{n+1})^×` and need not be cyclic, which is where the classical theorem remains open
in this chapter (`README.md` §21).

## Main results

* `NK.LocalReciprocityLubinTate.normInKernel_of_level_isCyclic`;
* `NK.LocalReciprocityLubinTate.NormInKernel.of_isCyclic`.
-/

open scoped Classical

namespace NK.LocalReciprocityLubinTate

universe u v

set_option linter.style.haveILetI false
set_option maxHeartbeats 800000

variable {F : Type u} {F' : Type v} [Field F] [Field F'] [Algebra F F'] [IsGalois F F']
  [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

/-- **The symbol at a level with cyclic Galois group kills norms.**

Let `T` be a Lubin–Tate symbol tower, `(m,n)` a level whose Galois group
`Gal(E_{m,n}/F) = ↥(T.level m n) ≃ₐ[F] ↥(T.level m n)` is cyclic, and `L ≤ E_{m,n}` a finite abelian
level.  Then the symbol `T.symbol m n` maps the norm group `N_{L/F} Lˣ` into `Gal(E_{m,n}/L)`: for
every `x ∈ N_{L/F} Lˣ` the automorphism `T.symbol m n x` fixes `L` pointwise.

The proof is the cardinality argument of the module docstring: the image of `N_L` under the symbol and
the fixing subgroup of `L` are subgroups of the cyclic group `Gal(E_{m,n}/F)` of the same cardinality
`[E_{m,n} : L]`, hence equal.  The norm index theorem `NK.LocalArtin.NormIndex` is required (it is a
theorem for `Q.adicCompletion K`). -/
theorem normInKernel_of_level_isCyclic
    {π : Fˣ} {a : ℕ → ℕ} {q : ℕ} (T : LubinTateSymbolTower F F' π a (higherUnits F) q)
    (hidx : NK.LocalArtin.NormIndex F F') (m n : ℕ)
    (hcyc : IsCyclic (↥(T.level m n) ≃ₐ[F] ↥(T.level m n)))
    (L : IntermediateField F (NK.LocalReciprocity.maxAbelianSubext F F'))
    [FiniteDimensional F L] [Normal F L]
    (hLE : L ≤ T.level m n) :
    ∀ x ∈ NK.LocalReciprocity.normGroup F ↥L,
      ∀ y : ↥L, (T.symbol m n x) ⟨y.1, hLE y.2⟩ = ⟨y.1, hLE y.2⟩ := by
  classical
  haveI hfdE : FiniteDimensional F ↥(T.level m n) := T.finiteDimensional m n
  haveI hnormE : Normal F ↥(T.level m n) := T.normal m n
  haveI hgalE : IsGalois F ↥(T.level m n) := inferInstance
  letI : Algebra ↥L ↥(T.level m n) := RingHom.toAlgebra (Subsemiring.inclusion hLE)
  haveI hSTL : IsScalarTower F ↥L ↥(T.level m n) :=
    IsScalarTower.of_algebraMap_eq (congrFun rfl)
  have hle : NK.LocalReciprocity.normGroup F ↥(T.level m n) ≤
      NK.LocalReciprocity.normGroup F ↥L :=
    NK.LocalCFT.normGroup_le_of_le hLE
  intro x hx y
  -- the two subgroups of `Gal(E/F)`
  set φ : Fˣ →* (↥(T.level m n) ≃ₐ[F] ↥(T.level m n)) := T.symbol m n with hφdef
  set A : Subgroup (↥(T.level m n) ≃ₐ[F] ↥(T.level m n)) :=
    Subgroup.map φ (NK.LocalReciprocity.normGroup F ↥L) with hAdef
  set B : Subgroup (↥(T.level m n) ≃ₐ[F] ↥(T.level m n)) :=
    (AlgEquiv.restrictNormalHom (F := F) (K₁ := ↥(T.level m n)) ↥L).ker with hBdef
  -- ### cardinality of `A`
  have hkerφ : φ.ker = NK.LocalReciprocity.normGroup F ↥(T.level m n) := T.symbol_ker m n
  have hkercomp : (φ.comp (NK.LocalReciprocity.normGroup F ↥L).subtype).ker
      = (NK.LocalReciprocity.normGroup F ↥(T.level m n)).subgroupOf
          (NK.LocalReciprocity.normGroup F ↥L) := by
    ext z
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, Subgroup.mem_subgroupOf, ← hkerφ,
      MonoidHom.mem_ker]
    rfl
  have hcardA : Nat.card ↥A * Module.finrank F ↥L = Module.finrank F ↥(T.level m n) := by
    have h1 : A = (φ.comp (NK.LocalReciprocity.normGroup F ↥L).subtype).range := by
      rw [hAdef, MonoidHom.range_comp, Subgroup.subtype_range]
    have h2 : Nat.card ↥A = (NK.LocalReciprocity.normGroup F ↥(T.level m n)).relIndex
        (NK.LocalReciprocity.normGroup F ↥L) := by
      rw [h1, ← Subgroup.index_ker, hkercomp]
      rfl
    rw [h2, ← hidx L, Subgroup.relIndex_mul_index hle, hidx (T.level m n)]
  -- ### cardinality of `B`
  have hsurj : Function.Surjective ⇑(AlgEquiv.restrictNormalHom (F := F) (K₁ := ↥(T.level m n)) ↥L) :=
    AlgEquiv.restrictNormalHom_surjective ↥(T.level m n)
  have hcardB : Nat.card ↥B * Module.finrank F ↥L = Module.finrank F ↥(T.level m n) := by
    have h2 : B.index = Module.finrank F ↥L := by
      rw [hBdef, Subgroup.index_ker, MonoidHom.range_eq_top.mpr hsurj, Subgroup.card_top,
        IsGalois.card_aut_eq_finrank F ↥L]
    have h3 := Subgroup.card_mul_index B
    rw [h2, IsGalois.card_aut_eq_finrank F ↥(T.level m n)] at h3
    exact h3
  have hcards : Nat.card ↥A = Nat.card ↥B :=
    Nat.mul_right_cancel (Module.finrank_pos (R := F)) (by rw [hcardA, hcardB])
  -- ### the two subgroups agree by cyclicity
  have hcyc' : IsCyclic (↥(T.level m n) ≃ₐ[F] ↥(T.level m n)) := hcyc
  have hAB : A = B :=
    Commons.GroupTheory.SpecificGroups.Cyclic.subgroup_eq_of_card_eq A B hcards
  have hxmem : φ x ∈ B := by
    rw [← hAB]
    exact Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
  have hfix : (AlgEquiv.restrictNormalHom ↥L) (φ x) = 1 := hxmem
  have hrn : (φ x).restrictNormal ↥L = 1 := hfix
  have happ := AlgEquiv.restrictNormal_commutes (χ := φ x) (E := ↥L) y
  rw [hrn] at happ
  simp only [AlgEquiv.one_apply] at happ
  have hmap : (algebraMap ↥L ↥(T.level m n)) y = ⟨y.1, hLE y.2⟩ := rfl
  rw [← hmap]
  exact happ.symm


/-- **`NormInKernel` holds whenever every level of the tower has cyclic Galois group.**

The tower-level form of `NK.LocalReciprocityLubinTate.normInKernel_of_level_isCyclic`: if for every
level `(m,n)` the group `Gal(E_{m,n}/F)` is cyclic, then the canonical symbol kills norms at every
finite abelian subfield of every level, i.e. `NK.LocalReciprocityLubinTate.NormInKernel` holds. -/
theorem normInKernel_of_isCyclic
    {π : Fˣ} {a : ℕ → ℕ} {q : ℕ} (T : LubinTateSymbolTower F F' π a (higherUnits F) q)
    (hidx : NK.LocalArtin.NormIndex F F')
    (hcyc : ∀ m n, IsCyclic (↥(T.level m n) ≃ₐ[F] ↥(T.level m n))) :
    NormInKernel F F' π a q T := by
  intro m n L _ _ _ hLE x hx y
  exact normInKernel_of_level_isCyclic T hidx m n (hcyc m n) L hLE x hx y

end NK.LocalReciprocityLubinTate

namespace NK.LocalReciprocityLubinTate

universe u

open IsDedekindDomain
