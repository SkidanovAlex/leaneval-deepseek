import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


universe u

set_option linter.style.haveILetI false

namespace Work.SymQuot.DivOf

open IntermediateField

/-- A finite-dimensional field extension is not the union of finitely many proper
intermediate fields.

If the base field `K` is infinite this is the classical fact that a vector space over an
infinite field is not a finite union of proper subspaces; if `K` is finite then `E` is a
finite field and has a primitive element, which lies in no proper intermediate field. -/
theorem notMem_iUnion_intermediateField {K E : Type u} [Field K] [Field E] [Algebra K E]
    [FiniteDimensional K E] {ι : Type*} [Finite ι] (B : ι → IntermediateField K E)
    (hB : ∀ i, B i ≠ ⊤) : ∃ x : E, ∀ i, x ∉ B i := by
  by_cases hK : Finite K
  · -- `K` finite: `E` is a finite field, so it is a simple extension of `K` and a primitive
    -- element lies in no proper intermediate field.
    haveI : Finite K := hK
    obtain ⟨α, hα⟩ := Field.exists_primitive_element_of_finite_bot K E
    refine ⟨α, fun i hαi => hB i ?_⟩
    have hle : (⊤ : IntermediateField K E) ≤ B i := by
      rw [← hα]
      exact adjoin_simple_le_iff.mpr hαi
    exact top_le_iff.mp hle
  · -- `K` infinite: view `E` as a `K`-vector space and use that a finite union of proper
    -- subspaces is improper.
    haveI : Infinite K := not_finite_iff_infinite.mp hK
    let p : ι → Submodule K E := fun i => Subalgebra.toSubmodule (B i).toSubalgebra
    have hp : ∀ i, p i ≠ ⊤ := by
      intro i h
      have h' : Subalgebra.toSubmodule (B i).toSubalgebra = ⊤ := h
      have h₁ : (B i).toSubalgebra = ⊤ :=
        Subalgebra.toSubmodule_injective (by simpa using h')
      exact hB i (IntermediateField.toSubalgebra_injective (by simpa using h₁))
    obtain ⟨x, hx⟩ := Submodule.exists_forall_notMem_of_forall_ne_top p hp
    refine ⟨x, fun i hxi => hx i ?_⟩
    simpa [p] using hxi

end Work.SymQuot.DivOf
