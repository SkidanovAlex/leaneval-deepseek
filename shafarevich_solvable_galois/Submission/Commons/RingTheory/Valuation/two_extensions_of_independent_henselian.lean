import Mathlib.Order.CompletePartialOrder
import Mathlib.RingTheory.Henselian
import Mathlib.FieldTheory.PurelyInseparable.Basic
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.ValuationSubring
import Submission.Commons.FieldTheory.SeparableClosure.nonempty_algHom_of_isSepClosure
import Submission.Commons.RingTheory.Valuation.exists_two_prolongations_of_stabilizer_eq_bot
import Submission.Commons.RingTheory.Valuation.henselianLocalRing_comap_decompositionField
import Submission.Commons.RingTheory.Valuation.henselianLocalRing_of_isAlgebraic
import Submission.Commons.RingTheory.Valuation.isSepClosed_of_two_independent_henselian_alt
import Submission.Commons.RingTheory.Valuation.valuation_mem_range_of_mem_decompositionField
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped Pointwise

namespace Commons.RingTheory.Valuation

/-- **Independence lifts to an immediate extension.**  If `v ⊥ C` on `F` and `K/F` is an
extension whose valuation restricts to `C` on `F` without changing the value group
(`A.valuation` on `K` takes only values of `C` on `F`), then `v` stays independent from it. -/
lemma independent_of_immediate_A {F K E : Type*} [Field F] [Field K] [Field E]
    [Algebra F K] [Algebra F E] [Algebra K E] [IsScalarTower F K E]
    (A : ValuationSubring E) (C : ValuationSubring F) (hC : A.comap (algebraMap F E) = C)
    (v : ValuationSubring F) (hind : ∀ D : ValuationSubring F, v ≤ D → C ≤ D → D = ⊤)
    (vK : ValuationSubring K) (hvK : vK.comap (algebraMap F K) = v)
    (himm : ∀ x : K, ∃ y : F, A.valuation (algebraMap K E x) = A.valuation (algebraMap F E y)) :
    ∀ D' : ValuationSubring K, vK ≤ D' → A.comap (algebraMap K E) ≤ D' → D' = ⊤ := by
  intro D' hvD hwD
  rw [eq_top_iff]
  have hcomap : D'.comap (algebraMap F K) = ⊤ := by
    have h1 : v ≤ D'.comap (algebraMap F K) := by
      rw [← hvK]; intro x hx; rw [ValuationSubring.mem_comap] at hx ⊢; exact hvD hx
    have h2 : C ≤ D'.comap (algebraMap F K) := by
      rw [← hC]; intro x hx
      rw [ValuationSubring.mem_comap] at hx
      apply hwD
      rw [ValuationSubring.mem_comap, ← IsScalarTower.algebraMap_apply F K E]
      exact hx
    exact hind _ h1 h2
  intro x _
  by_cases hx : x = 0
  · subst hx; exact D'.zero_mem
  · obtain ⟨y, hy⟩ := himm x
    have hxE : algebraMap K E x ≠ 0 := by simpa using hx
    have hval_ne : A.valuation (algebraMap F E y) ≠ 0 := fun h => by
      rw [h] at hy; exact hxE ((Valuation.zero_iff A.valuation).mp hy)
    have hy0 : y ≠ 0 := by
      intro h; subst h
      rw [map_zero, map_zero] at hy
      exact hxE ((Valuation.zero_iff A.valuation).mp hy)
    have hmem_y : algebraMap F K y ∈ D' := by
      have hmem : y ∈ D'.comap (algebraMap F K) := by rw [hcomap]; exact ValuationSubring.mem_top y
      rwa [ValuationSubring.mem_comap] at hmem
    have hmem_q : x * (algebraMap F K y)⁻¹ ∈ D' := by
      apply hwD
      rw [ValuationSubring.mem_comap, ← ValuationSubring.valuation_le_one_iff]
      have h1 : algebraMap K E (x * (algebraMap F K y)⁻¹)
          = algebraMap K E x * (algebraMap F E y)⁻¹ := by
        rw [map_mul, map_inv₀]
        exact congrArg (fun t => algebraMap K E x * t⁻¹)
          (IsScalarTower.algebraMap_apply F K E y).symm
      rw [h1, Valuation.map_mul, Valuation.map_inv, hy, mul_inv_cancel₀ hval_ne]
    have hxeq : x = (x * (algebraMap F K y)⁻¹) * (algebraMap F K y) := by
      rw [mul_assoc, inv_mul_cancel₀ (by simpa using hy0), mul_one]
    rw [hxeq]
    exact mul_mem hmem_q hmem_y

/-- **The decomposition group of an independent valuation is trivial** (Endler–Engler). -/
theorem stabilizer_eq_bot {F : Type*} [Field F] (C₁ C₂ : ValuationSubring F)
    [HenselianLocalRing C₁] (h₁ : C₁ ≠ ⊤) (h₂ : C₂ ≠ ⊤)
    (hind : ∀ D : ValuationSubring F, C₁ ≤ D → C₂ ≤ D → D = ⊤)
    {E : Type*} [Field E] [Algebra F E] [IsSepClosure F E]
    (A : ValuationSubring E) (hA : A.comap (algebraMap F E) = C₂) :
    MulAction.stabilizer (E ≃ₐ[F] E) A = ⊥ := by
  set D : Subgroup (E ≃ₐ[F] E) := MulAction.stabilizer (E ≃ₐ[F] E) A with hD
  set K : IntermediateField F E := IntermediateField.fixedField D with hK
  set wK : ValuationSubring K := A.comap (algebraMap K E) with hwK
  haveI : HenselianLocalRing wK := henselianLocalRing_comap_decompositionField A
  obtain ⟨vK, hvK⟩ := exists_valuationSubring_comap_eq (K := F) (L := K) C₁
  haveI : HenselianLocalRing vK :=
    henselianLocalRing_of_isAlgebraic
      (inferInstance : Algebra.IsAlgebraic F K) C₁ vK hvK
  have himm : ∀ x : K, ∃ y : F, A.valuation (algebraMap K E x) = A.valuation (algebraMap F E y) := by
    intro x
    obtain ⟨y, hy⟩ := valuation_mem_range_of_mem_decompositionField A x
    exact ⟨y, hy⟩
  have hindK : ∀ D' : ValuationSubring K, vK ≤ D' → wK ≤ D' → D' = ⊤ :=
    independent_of_immediate_A A C₂ hA C₁ hind vK hvK himm
  have hvKne : vK ≠ ⊤ := by intro h; exact h₁ (by rw [← hvK, h]; rfl)
  have hwKne : wK ≠ ⊤ := by
    intro h
    apply h₂
    have h1 : C₂ = wK.comap (algebraMap F K) := by
      rw [← hA, hwK, ValuationSubring.comap_comap, IsScalarTower.algebraMap_eq F K E]
    rw [h1, h]
    ext x
    simp [ValuationSubring.mem_comap]
  have hsep : IsSepClosed K :=
    isSepClosed_of_two_independent_henselian_alt vK wK hvKne hwKne hindK inferInstance inferInstance
  have hKtop : K = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hbij := IsSepClosed.algebraMap_bijective (k := K) (K := E)
    obtain ⟨y, hy⟩ := hbij.2 x
    rw [← hy]; exact y.2
  have hle : D ≤ K.fixingSubgroup := by
    intro σ hσ
    rw [IntermediateField.mem_fixingSubgroup_iff]
    intro x hx
    rw [hK] at hx
    exact (IntermediateField.mem_fixedField_iff D x).mp hx σ hσ
  have hbot : K.fixingSubgroup = ⊥ := by
    rw [hKtop]; exact IntermediateField.fixingSubgroup_top
  exact le_bot_iff.mp (hbot ▸ hle)

theorem two_extensions_of_independent_henselian {F F' : Type*} [Field F] [Field F'] [Algebra F F']
    [FiniteDimensional F F'] [Algebra.IsSeparable F F']
    (C₁ C₂ : ValuationSubring F) (h₁ : C₁ ≠ ⊤) (h₂ : C₂ ≠ ⊤)
    (hind : ∀ D : ValuationSubring F, C₁ ≤ D → C₂ ≤ D → D = ⊤) [HenselianLocalRing C₁]
    (hdim : 1 < Module.finrank F F') :
    ∃ B₁ B₂ : ValuationSubring F', B₁ ≠ B₂ ∧ B₁.comap (algebraMap F F') = C₂ ∧ B₂.comap (algebraMap F F') = C₂ := by
  let E := SeparableClosure F
  obtain ⟨A, hA⟩ := exists_valuationSubring_comap_eq (K := F) (L := E) C₂
  have hD : MulAction.stabilizer (E ≃ₐ[F] E) A = ⊥ :=
    stabilizer_eq_bot C₁ C₂ h₁ h₂ hind A hA
  obtain ⟨ι⟩ := Commons.FieldTheory.SeparableClosure.nonempty_algHom_of_isSepClosure (F := F) (F' := F') (E := E)
  obtain ⟨B₁, B₂, hne, h1, h2⟩ := exists_two_prolongations_of_stabilizer_eq_bot A hD hdim ι
  exact ⟨B₁, B₂, hne, by rw [h1, hA], by rw [h2, hA]⟩

end Commons.RingTheory.Valuation
