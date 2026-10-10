import Mathlib.FieldTheory.Galois.Profinite
import Submission.Work.AbsoluteKummer.Coefficients
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.AbsoluteKummer.Factorisation

open scoped Topology
open Filter

theorem exists_finiteGalois_le_ker_pair {k : Type*} [Field k] [IsGalois k (AlgebraicClosure k)] {M : Type*} {f : Work.AbsoluteKummer.G k × Work.AbsoluteKummer.G k → M} (hf : Work.AbsoluteKummer.IsLocallyConstant f) : ∃ L : FiniteGaloisIntermediateField k (AlgebraicClosure k), ∀ p : Work.AbsoluteKummer.G k × Work.AbsoluteKummer.G k, p.1 ∈ L.fixingSubgroup → p.2 ∈ L.fixingSubgroup → f p = f (1, 1) := by
  obtain ⟨U, hUo, h1U, hconst⟩ := hf (1, 1)
  have hUmem : U ∈ 𝓝 ((1, 1) : Work.AbsoluteKummer.G k × Work.AbsoluteKummer.G k) :=
    hUo.mem_nhds h1U
  rw [nhds_prod_eq] at hUmem
  obtain ⟨U₁, hU₁, U₂, hU₂, hsub⟩ := Filter.mem_prod_iff.mp hUmem
  have hmem : U₁ ∩ U₂ ∈ 𝓝 (1 : Work.AbsoluteKummer.G k) := Filter.inter_mem hU₁ hU₂
  obtain ⟨L, hL⟩ :=
    (InfiniteGalois.krullTopology_mem_nhds_one_iff_of_isGalois (k := k)
      (K := AlgebraicClosure k) (U₁ ∩ U₂)).mp hmem
  exact ⟨L, fun p hp1 hp2 => hconst p (hsub ⟨(hL hp1).1, (hL hp2).2⟩)⟩

end Work.AbsoluteKummer.Factorisation
