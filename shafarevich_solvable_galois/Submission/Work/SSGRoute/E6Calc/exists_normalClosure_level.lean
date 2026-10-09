import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.style.haveILetI false

namespace Work.SSGRoute.E6Calc

/-- Given a finite extension `L/k` inside an algebraically closed field `Ω`, with `k ⊆ k' ⊆ K ⊆ L`
(`k`, `k'` number fields), there is a finite extension `L'` of `K` inside `Ω`, containing `L`, which is
a number field and is Galois over both `k` and `k'`.

The construction takes the normal closure `N` of `L` over `k` inside `Ω`; it is finite over `k`
(hence over `k'`), normal over `k` (hence over `k'`, since every `k'`-embedding is a `k`-embedding),
and separable because `k` has characteristic zero.  Since the image of `K` in `Ω` is contained in
`N`, the latter may be regarded as an intermediate field `K → Ω`. -/
theorem exists_normalClosure_level {k k' K Ω : Type} [Field k] [NumberField k] [Field k']
    [NumberField k'] [Field K] [Field Ω] [IsAlgClosed Ω] [Algebra k K] [Algebra k' K] [Algebra k k']
    [IsScalarTower k k' K] [Algebra K Ω] [Algebra k Ω] [Algebra k' Ω] [IsScalarTower k K Ω]
    [IsScalarTower k' K Ω] [IsScalarTower k k' Ω]
    (L : IntermediateField K Ω) [FiniteDimensional k ↥L] :
    ∃ L' : IntermediateField K Ω, L ≤ L' ∧ Nonempty (NumberField ↥L') ∧
      Nonempty (FiniteDimensional k ↥L') ∧ Nonempty (IsGalois k ↥L') ∧
      Nonempty (FiniteDimensional k' ↥L') ∧ Nonempty (IsGalois k' ↥L') := by
  -- `M = L` viewed over the base `k`.
  let M : IntermediateField k Ω := L.restrictScalars k
  haveI hMfin : FiniteDimensional k ↥M := inferInstanceAs (FiniteDimensional k ↥L)
  haveI hMalg : Algebra.IsAlgebraic k ↥M := Algebra.IsAlgebraic.of_finite k ↥M
  -- The normal closure of `M/k` inside `Ω`.
  let N : IntermediateField k Ω := IntermediateField.normalClosure k ↥M Ω
  haveI hNfin : FiniteDimensional k ↥N := normalClosure.is_finiteDimensional k ↥M Ω
  have hMN : M ≤ N := IntermediateField.le_normalClosure M
  have hIN : IsNormalClosure k ↥M ↥N :=
    Algebra.IsAlgebraic.isNormalClosure_normalClosure (fun z => IsAlgClosed.splits _)
  haveI hNnorm : Normal k ↥N := hIN.normal
  haveI hNint : Algebra.IsIntegral k ↥N := Algebra.IsIntegral.of_finite k ↥N
  haveI hNsep : Algebra.IsSeparable k ↥N := Algebra.IsSeparable.of_integral k ↥N
  haveI hNgal : IsGalois k ↥N := isGalois_iff.mpr ⟨hNsep, hNnorm⟩
  -- `N` contains the image of `K` in `Ω`, so it is an intermediate field `K → Ω`.
  have hKN : (⊥ : IntermediateField K Ω).restrictScalars k ≤ N := by
    have h1 : (⊥ : IntermediateField K Ω).restrictScalars k ≤ L.restrictScalars k := by
      rw [IntermediateField.restrictScalars_le_iff]; exact bot_le
    exact le_trans h1 hMN
  have hmemL' : ∀ t : K, algebraMap K Ω t ∈ (N : Set Ω) := fun t =>
    hKN (by rw [IntermediateField.mem_restrictScalars]; exact IntermediateField.mem_bot.mpr ⟨t, rfl⟩)
  let L' : IntermediateField K Ω := { N.toSubfield with algebraMap_mem' := hmemL' }
  haveI hL'fin : FiniteDimensional k L' := inferInstanceAs (FiniteDimensional k ↥N)
  haveI hL'gal : IsGalois k L' := inferInstanceAs (IsGalois k ↥N)
  haveI hL'cz : CharZero L' := inferInstanceAs (CharZero ↥N)
  haveI hL'fdq : FiniteDimensional ℚ L' := FiniteDimensional.trans ℚ k L'
  haveI hL'NF : NumberField L' := NumberField.mk
  have hLM : L.restrictScalars k ≤ M := le_rfl
  have hLL : L ≤ L' := fun z hz => hMN (hLM hz)
  -- The `k'`-structure on `L'`, transported from `Ω` along the scalar tower `k → k' → Ω`.
  haveI hST : IsScalarTower k k' ↥L' :=
    IsScalarTower.of_algebraMap_eq fun x => Subtype.ext (IsScalarTower.algebraMap_apply k k' Ω x)
  haveI hL'gal' : IsGalois k' ↥L' := IsGalois.tower_top_of_isGalois k k' ↥L'
  haveI hL'fin' : FiniteDimensional k' ↥L' := Module.Finite.of_restrictScalars_finite k k' ↥L'
  exact ⟨L', hLL, ⟨hL'NF⟩, ⟨hL'fin⟩, ⟨hL'gal⟩, ⟨hL'fin'⟩, ⟨hL'gal'⟩⟩

end Work.SSGRoute.E6Calc
