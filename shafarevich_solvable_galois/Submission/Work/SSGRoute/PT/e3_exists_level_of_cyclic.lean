import Mathlib
import Submission.Work.SSGRoute.PTDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.PT

/-- **Every finite Galois extension of `k` occurs inside `Ω` as a level of `k`.**

Node `E3`, transfer step: an arbitrary cyclic degree-`p` extension `L/k` (given as a type) is,
up to `k`-isomorphism, the intermediate field `L₀ = L.map ι ⊆ Ω` cut out by a `k`-algebra embedding
`ι : L → Ω` (which exists because `Ω` is algebraically closed and `L/k` is finite); the degree is
carried along.  The caller then forms the compositum `K ⊔ L₀ ⊆ Ω`, which *is* a level over `K`, so
that the `Ω`-indexed pairing hypothesis `PhiOneVanishesIn Ω` becomes available for it, and descends
to `L₀` by inflation compatibility of the pairing. -/
theorem e3_exists_level_of_cyclic (p : ℕ) [Fact p.Prime] (k Ω : Type) [Field k] [NumberField k]
    [Field Ω] [Algebra k Ω] [IsAlgClosed Ω] (K : IntermediateField k Ω)
    (L : Type) [Field L] [NumberField L] [Algebra k L] [FiniteDimensional k L] [IsGalois k L]
    (hdeg : Module.finrank k L = p) :
    ∃ L₀ : IntermediateField k Ω, Nonempty (L ≃ₐ[k] L₀) ∧ Module.finrank k L₀ = p := by
  haveI : Algebra.IsAlgebraic k L := Algebra.IsAlgebraic.of_finite k L
  -- A `k`-algebra embedding of the finite extension `L/k` into the algebraically closed `Ω`.
  let ι : L →ₐ[k] Ω := IsAlgClosed.lift
  refine ⟨ι.fieldRange, ⟨AlgHom.equivFieldRange ι⟩, ?_⟩
  -- The degree is carried along the `k`-algebra isomorphism `L ≃ₐ[k] ι.fieldRange`.
  rw [← hdeg, LinearEquiv.finrank_eq (AlgHom.equivFieldRange ι).toLinearEquiv]

end Work.SSGRoute.PT
