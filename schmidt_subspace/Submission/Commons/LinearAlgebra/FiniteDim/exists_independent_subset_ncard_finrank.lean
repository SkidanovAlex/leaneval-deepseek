import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal

set_option linter.style.haveILetI false

namespace Commons.LinearAlgebra.FiniteDim

/-- A spanning set contains a finite linearly independent subset of cardinality `finrank`. -/
lemma exists_independent_subset_ncard_finrank {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] (s : Set V) (hs : Submodule.span K s = ⊤) :
    ∃ t : Set V, t ⊆ s ∧ t.Finite ∧ t.ncard = Module.finrank K V ∧
      LinearIndependent K (Subtype.val : t → V) := by
  classical
  obtain ⟨I, hIli, hImax⟩ := exists_maximal_linearIndepOn K (Subtype.val : s → V)
  have hlin : LinearIndependent K (Subtype.val : ((Subtype.val : s → V) '' I : Set V) → V) :=
    (linearIndependent_subtype_iff).mpr
      ((linearIndepOn_iff_image (Subtype.coe_injective.injOn)).mp hIli)
  have hspan : Submodule.span K ((Subtype.val : s → V) '' I) = ⊤ := by
    have hle : Submodule.span K s ≤ Submodule.span K ((Subtype.val : s → V) '' I) := by
      apply Submodule.span_le.mpr
      rintro x hx
      by_cases hxI : (⟨x, hx⟩ : s) ∈ I
      · exact Submodule.subset_span ⟨⟨x, hx⟩, hxI, rfl⟩
      · obtain ⟨a, ha, hax⟩ := hImax ⟨x, hx⟩ hxI
        have hx'a : x = a⁻¹ • (a • x) := by rw [inv_smul_smul₀ ha]
        rw [hx'a]
        exact Submodule.smul_mem _ _ hax
    rw [hs] at hle
    exact le_antisymm le_top hle
  refine ⟨(Subtype.val : s → V) '' I, ?_, ?_, ?_, hlin⟩
  · rintro y ⟨x, -, rfl⟩; exact x.2
  · exact hlin.setFinite
  · letI : Fintype ((Subtype.val : s → V) '' I : Set V) := hlin.setFinite.fintype
    have hb : Module.Basis ((Subtype.val : s → V) '' I) K V :=
      Module.Basis.mk hlin (by rw [Subtype.range_val]; exact hspan.ge)
    rw [← Set.fintypeCard_eq_ncard, Module.finrank_eq_card_basis hb]

end Commons.LinearAlgebra.FiniteDim