import Mathlib
import Submission.Work.AbsoluteKummer.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.AbsoluteKummer.Factorisation

open scoped Topology

/-- A locally constant function on the absolute Galois group `Gal(k̄/k)` is constant on the
fixing subgroup of a finite Galois intermediate field.

This is the statement that the fixing subgroups of finite Galois intermediate fields form a
neighbourhood basis of the identity in the Krull topology. -/
theorem exists_finiteGalois_le_ker {k : Type*} [Field k] [IsGalois k (AlgebraicClosure k)] {M : Type*} {f : (AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) → M} (hf : Work.AbsoluteKummer.IsLocallyConstant f) : ∃ L : FiniteGaloisIntermediateField k (AlgebraicClosure k), ∀ σ : AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k, σ ∈ L.fixingSubgroup → f σ = f 1 := by
  obtain ⟨U, hUopen, h1U, hconst⟩ := hf 1
  have hmem : U ∈ 𝓝 (1 : AlgebraicClosure k ≃ₐ[k] AlgebraicClosure k) := hUopen.mem_nhds h1U
  obtain ⟨L, hL⟩ :=
    (InfiniteGalois.krullTopology_mem_nhds_one_iff_of_isGalois (k := k)
      (K := AlgebraicClosure k) U).mp hmem
  exact ⟨L, fun σ hσ => hconst σ (hL hσ)⟩

end Work.AbsoluteKummer.Factorisation
