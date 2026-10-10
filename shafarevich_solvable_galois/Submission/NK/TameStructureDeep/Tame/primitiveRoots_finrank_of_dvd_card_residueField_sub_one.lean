import Mathlib.RingTheory.Henselian
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.FieldTheory.Galois.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.RamificationGroup
import Submission.NK.TameStructureDeep.Tame.InertiaFieldAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.TameStructureDeep.Tame

set_option linter.style.haveILetI false

/-- **`#k - 1` is a unit of `R`** when `k` is the finite residue field of a local ring `R`.

Indeed `#k` maps to `0` in `k`, so the residue of the natural number `#k - 1` is `-1 ≠ 0`; an
element of a local ring whose residue is nonzero is a unit. -/
theorem isUnit_natCast_card_residueField_sub_one {R : Type*} [CommRing R] [IsLocalRing R]
    [Finite (IsLocalRing.ResidueField R)] :
    IsUnit (((Nat.card (IsLocalRing.ResidueField R) - 1 : ℕ)) : R) := by
  classical
  haveI : Fintype (IsLocalRing.ResidueField R) := Fintype.ofFinite _
  have hcard : Nat.card (IsLocalRing.ResidueField R) = Fintype.card (IsLocalRing.ResidueField R) :=
    Nat.card_eq_fintype_card
  have h1k : 1 ≤ Nat.card (IsLocalRing.ResidueField R) := by
    rw [hcard]; exact le_of_lt Fintype.one_lt_card
  have hcard0 : (Nat.card (IsLocalRing.ResidueField R) : IsLocalRing.ResidueField R) = 0 := by
    rw [hcard]; exact FiniteField.cast_card_eq_zero _
  rw [← IsLocalRing.residue_ne_zero_iff_isUnit]
  have hres : (IsLocalRing.residue R) (((Nat.card (IsLocalRing.ResidueField R) - 1 : ℕ)) : R) = -1 := by
    rw [map_natCast, Nat.cast_sub h1k, hcard0, Nat.cast_one]
    simp
  rw [hres]
  exact neg_ne_zero.mpr one_ne_zero

/-- **The inertia field contains the `e`-th roots of unity when `e ∣ #(A/𝔪_A) - 1`.**

Let `A` be a Henselian discrete valuation ring with finite residue field, and let
`F = M^{G_0}` be the fixed field of the inertia subgroup `G_0 = ramificationSubgroup A 0` inside
`Gal(M/κ)`.  Then `F` contains a primitive `e`-th root of unity for every `e ≥ 1` dividing
`#(A/𝔪_A) - 1`.

Indeed a Teichmüller lift `ω` of a generator of `(A/𝔪_A)^×` is a primitive `(#(A/𝔪_A)-1)`-st root
of unity inside `A ⊆ M` (`exists_isPrimitiveRoot_residueField_card_sub_one`), every inertia
element fixes it (`inertiaSubgroup_apply_isPrimitiveRoot`, using that `#(A/𝔪_A) - 1` is a unit of
`A`), so `ω ∈ F`; and `ω ^ ((#(A/𝔪_A)-1)/e)` is a primitive `e`-th root of unity. -/
theorem primitiveRoots_finrank_of_dvd_card_residueField_sub_one
    {κ M : Type*} [Field κ] [Field M] [Algebra κ M]
    (A : ValuationSubring M) [IsDiscreteValuationRing A] [HenselianLocalRing A]
    [Finite (IsLocalRing.ResidueField A)]
    {e : ℕ} (he0 : 0 < e) (he : e ∣ Nat.card (IsLocalRing.ResidueField A) - 1) :
    (primitiveRoots e ↥(IntermediateField.fixedField
      ((NK.Ramification.ramificationSubgroup (K := κ) A 0).map
        (A.decompositionSubgroup κ).subtype))).Nonempty := by
  classical
  -- ## Residue field bookkeeping: `#k ≥ 2` and `#k - 1` is a unit of `A`
  haveI : Fintype (IsLocalRing.ResidueField ↥A) := Fintype.ofFinite _
  have hcard : Nat.card (IsLocalRing.ResidueField ↥A) = Fintype.card (IsLocalRing.ResidueField ↥A) :=
    Nat.card_eq_fintype_card
  have h2k : 2 ≤ Nat.card (IsLocalRing.ResidueField ↥A) := by
    rw [hcard]; exact Fintype.one_lt_card
  have hNunit : IsUnit (((Nat.card (IsLocalRing.ResidueField ↥A) - 1 : ℕ)) : ↥A) :=
    isUnit_natCast_card_residueField_sub_one
  -- ## The inertia subgroup of `A` inside `Gal(M/κ)`
  let H : Subgroup (M ≃ₐ[κ] M) := (NK.Ramification.ramificationSubgroup (K := κ) A 0).map
      (A.decompositionSubgroup κ).subtype
  let F : IntermediateField κ M := IntermediateField.fixedField H
  change (primitiveRoots e F).Nonempty
  -- ## A Teichmüller root of unity `ζA ∈ A` of order `N = #k - 1`
  set N : ℕ := Nat.card (IsLocalRing.ResidueField A) - 1 with hN
  have hNpos : 0 < N := by rw [hN]; omega
  obtain ⟨ζA, hζA⟩ := exists_isPrimitiveRoot_residueField_card_sub_one A
  have hζA' : IsPrimitiveRoot ζA N := by rw [hN]; exact hζA
  have hζM : IsPrimitiveRoot ((ζA : ↥A) : M) N :=
    IsPrimitiveRoot.map_of_injective (f := ValuationSubring.subtype A) hζA' Subtype.val_injective
  -- ## Every element of the inertia subgroup fixes `ζA`
  have hfix : ∀ σ ∈ H, σ ((ζA : ↥A) : M) = ((ζA : ↥A) : M) := by
    intro σ hσ
    rw [Subgroup.mem_map] at hσ
    obtain ⟨τ, hτ, rfl⟩ := hσ
    have hτ' : τ ∈ A.inertiaSubgroup κ := by
      rw [← NK.Ramification.ramificationSubgroup_zero (K := κ) A]
      exact hτ
    exact inertiaSubgroup_apply_isPrimitiveRoot A hNunit ⟨τ, hτ'⟩ hζM
  -- ## The `(N/e)`-th power of `ζA` is a primitive `e`-th root of unity, still fixed
  set k : ℕ := N / e with hk
  have he' : e ∣ N := by rw [hN]; exact he
  have hNe : N = k * e := by rw [hk, Nat.div_mul_cancel he']
  let u : ↥A := ζA ^ k
  have huprim : IsPrimitiveRoot u e := IsPrimitiveRoot.pow hNpos hζA' hNe
  have huM : IsPrimitiveRoot ((u : ↥A) : M) e :=
    IsPrimitiveRoot.map_of_injective (f := ValuationSubring.subtype A) huprim Subtype.val_injective
  have huF : ((u : ↥A) : M) ∈ F := by
    rw [IntermediateField.mem_fixedField_iff H]
    intro σ hσ
    have h1 : σ ((ζA : ↥A) : M) = ((ζA : ↥A) : M) := hfix σ hσ
    have hu_eq : ((u : ↥A) : M) = ((ζA : ↥A) : M) ^ k := by simp [u]
    rw [hu_eq, map_pow, h1]
  -- ## Conclude
  refine ⟨⟨((u : ↥A) : M), huF⟩, ?_⟩
  rw [mem_primitiveRoots he0]
  exact (IsPrimitiveRoot.coe_submonoidClass_iff (N := F) (ζ := (⟨((u : ↥A) : M), huF⟩ : F))).mp huM

end NK.TameStructureDeep.Tame
