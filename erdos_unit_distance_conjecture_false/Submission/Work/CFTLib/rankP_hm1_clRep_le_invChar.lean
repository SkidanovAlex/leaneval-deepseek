import Mathlib
import Submission.Work.CFTLib.RelShafReps
import Submission.Work.CFTLib.RelShafDefs
import Submission.Work.CFTLib.InvRepDefs
import Submission.Work.CFTLib.rankP_le_rankP_of_injective
import Submission.Work.CFTLib.finrank_invariantHoms_eq_rankP
import Submission.Work.CFT.Ledger.tateCohomology_neg_one_iso_Hm1Quotient
import Submission.Work.CFT.ClassFormation.rankP_eq_of_addEquiv
import Submission.Work.CFT.ClassFormation.Schur.finrank_homology_fp_eq

/-!
# The class-group term of the relative Shafarevich bound

For a finite Galois extension `K/F` of number fields, `p` a prime, `G = Gal(K/F)` and
`M = Cl(𝓞 K)` with its canonical `G`-action (`clRep F K`), the `p`-rank of the `(-1)`-st Tate
cohomology `Ĥ⁻¹(G, M)` is bounded by the dimension of the space of `G`-invariant characters
`M → 𝔽_p` (`clInvariantChar F K p`).

The bound is a general fact about finite `ℤ[G]`-modules: `Ĥ⁻¹(G, M) = ker N / I_G M` is a
subquotient of `M / I_G M`, and `dim_𝔽_p (𝔽_p ⊗ M / I_G M)` equals `dim (Hom_ℤ(M, 𝔽_p)^G)`, the
dimension of the space of invariant characters.  Consequently the whole `p`-rank of `Ĥ⁻¹(G, M)`
is bounded by the class-group contribution `c = dim (Cl_K ⊗ 𝔽_p)^G` of the idèle computation.

## Main result

* `Work.CFTLib.rankP_hm1_clRep_le_invChar`
-/

open NumberField CategoryTheory

namespace Work.CFTLib

/-- **`Ĥ⁻¹(G, A)` has `p`-rank at most that of the coinvariants `A ⧸ I_G A`.**  For a
`ℤ`-representation `A` of a finite group `G` with finite underlying abelian group, the `(-1)`-st
Tate cohomology `Ĥ⁻¹(G, A) = ker N_A ⧸ I_G A` is a quotient of the kernel of the norm, hence
maps injectively into the coinvariant quotient `A ⧸ I_G A`; monotonicity of `rankP` under
injective additive homomorphisms (`rankP_le_rankP_of_injective`) bounds its `p`-rank by
`rankP p (A ⧸ I_G A)`. -/
theorem rankP_tateCohomology_neg_one_le {G : Type} [Group G] [Fintype G] (A : Rep ℤ G)
    [Finite A.V] [Module.Finite ℤ A.V] (p : ℕ) [Fact p.Prime] :
    Work.CFT.ClassFormation.rankP p ↑(tateCohomology A (-1))
      ≤ Work.CFT.ClassFormation.rankP p (A.V ⧸ Work.CFT.Ledger.augIdeal A) := by
  obtain ⟨e⟩ := Work.CFT.Ledger.tateCohomology_neg_one_iso_Hm1Quotient A
  rw [Work.CFT.ClassFormation.rankP_eq_of_addEquiv p e]
  refine rankP_le_rankP_of_injective p ?_ ?_
  · exact QuotientAddGroup.lift (Work.CFT.Ledger.Hm1Sub A)
      ((QuotientAddGroup.mk' (Work.CFT.Ledger.augIdeal A)).comp (AddSubgroup.subtype _))
      (by
        intro x hx
        rw [AddMonoidHom.mem_ker]
        exact (QuotientAddGroup.eq_zero_iff x.1).mpr ((Work.CFT.Ledger.mem_Hm1Sub).mp hx))
  · rw [← AddMonoidHom.ker_eq_bot_iff]
    rw [QuotientAddGroup.ker_lift]
    rw [eq_bot_iff]
    intro x hx
    rw [AddSubgroup.mem_map] at hx
    obtain ⟨y, hy, rfl⟩ := hx
    rw [AddSubgroup.mem_bot]
    rw [AddMonoidHom.mem_ker] at hy
    exact (QuotientAddGroup.eq_zero_iff y).mpr
      ((Work.CFT.Ledger.mem_Hm1Sub).mpr ((QuotientAddGroup.eq_zero_iff y.1).mp hy))

/-- **The `p`-rank of `Ĥ⁻¹(G, Cl(𝓞 K))` is bounded by the class-group contribution of the
idèle computation.**

`clInvariantChar F K p` is the space of `Gal(K/F)`-invariant additive characters of `Cl(𝓞 K)`;
by `finrank_invariantHoms_eq_rankP` its dimension is the `p`-rank of the coinvariants
`Cl(𝓞 K) ⧸ I_G Cl(𝓞 K)`, where `I_G` is the augmentation subgroup of the canonical action
`clRep F K`.  The `(-1)`-st Tate cohomology `Ĥ⁻¹(G, Cl(𝓞 K))` is a subquotient of those
coinvariants, so its `p`-rank is no larger (`rankP_tateCohomology_neg_one_le`). -/
theorem rankP_hm1_clRep_le_invChar {F K : Type} [Field F] [NumberField F] [Field K]
    [NumberField K] [Algebra F K] [FiniteDimensional F K] [IsGalois F K] (p : ℕ) [Fact p.Prime] :
    Work.CFT.ClassFormation.rankP p
        ↑(tateCohomology (Work.CFTLib.clRep F K) (-1))
      ≤ Module.finrank (ZMod p) (Work.CFTLib.clInvariantChar F K p) := by
  -- finiteness of the class group of `K`, hence of the coefficient module of `clRep F K`
  haveI hCg : Finite (ClassGroup (𝓞 K)) := inferInstance
  haveI hAd : Finite (Additive (ClassGroup (𝓞 K))) := inferInstance
  haveI hF : Finite ↥(Work.CFTLib.clRep F K) := hAd
  haveI hM : Module.Finite ℤ ↥(Work.CFTLib.clRep F K) := Module.Finite.of_finite
  -- `Ĥ⁻¹(G, Cl_K)` is a subquotient of the coinvariants `Cl_K ⧸ I_G Cl_K`
  have hC := rankP_tateCohomology_neg_one_le (Work.CFTLib.clRep F K) p
  -- the invariant characters of `Cl_K` are exactly the dual of the coinvariants
  have hB := finrank_invariantHoms_eq_rankP (Work.CFTLib.clRep F K) p
  have hB' : Work.CFT.ClassFormation.rankP p
      ((Work.CFTLib.clRep F K).V ⧸ Work.CFT.Ledger.augIdeal (Work.CFTLib.clRep F K))
      = Module.finrank (ZMod p) (Work.CFTLib.clInvariantChar F K p) := hB.symm
  linarith

end Work.CFTLib
