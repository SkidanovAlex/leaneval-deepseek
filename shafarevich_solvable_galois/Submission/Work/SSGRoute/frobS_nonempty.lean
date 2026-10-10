import Mathlib.FieldTheory.KrullTopology
import Mathlib.RingTheory.Henselian
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.ValuationSubring
import Submission.Work.SSGRoute.FrobLiftSetup2
import Submission.Work.SSGRoute.decomp_mod_inertia_cyclic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `frobS A L` is nonempty

For a finite place `A` of `Ω` over `k` and a finite normal level `L ⊆ Ω`, the set
`frobS A L ⊆ D_A` of elements whose image generates the cyclic quotient
`D_A ⧸ frobK A L` is nonempty.  Indeed `D_A ⧸ frobK A L` is cyclic by
`Work.SSGRoute.decomp_mod_inertia_cyclic` (applied to the open subgroup
`frobV A L = I_A ⊔ G_L`), so it has a generator.
-/

open scoped Pointwise

namespace Work.SSGRoute

open _root_.SSGRoute

set_option linter.unusedSectionVars false

theorem frobS_nonempty (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω]
    [IsAlgClosure k Ω] (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (i : FrobIndex k Ω) : (frobS A i).Nonempty := by
  -- `D_A ⧸ frobK A i` is cyclic, with a generator `g` of `D_A` modulo the open subgroup
  -- `frobV A i = I_A ⊔ G_L`.
  obtain ⟨g, hg, hgen⟩ :=
    decomp_mod_inertia_cyclic k Ω A hA (frobV A i ⊓ decomp k A)
      ⟨frobV A i, frobV_isOpen A i, rfl⟩
      (fun σ hσ => ⟨Subgroup.mem_sup_left (show σ ∈ inertiaSub k Ω A from hσ), hσ.1⟩)
  refine ⟨⟨g, hg⟩, fun δ => ?_⟩
  obtain ⟨m, hm⟩ := hgen δ δ.2
  refine ⟨m, ?_⟩
  rw [frobK, Subgroup.mem_subgroupOf]
  show ((δ⁻¹ * (⟨g, hg⟩ : ↥(decomp k A)) ^ m : ↥(decomp k A)) : Ω ≃ₐ[k] Ω) ∈ frobV A i
  rw [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_zpow]
  exact hm.1

end Work.SSGRoute
