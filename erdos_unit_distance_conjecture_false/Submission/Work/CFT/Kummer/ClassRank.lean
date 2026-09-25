import Mathlib
import Submission.Work.CFT.Kummer.Defs
import Submission.Work.CFT.Kummer.Hypotheses
import Submission.Work.CFT.Kummer.Estimate
import Submission.Work.CFT.Kummer.finrank_kummerClasses_empty
import Submission.Work.CFT.Kummer.finite_kummerClasses

/-!
# The `p`-rank of the class group as the generator rank of the maximal unramified pro-`p` group

The Kummer-theoretic computation of `Work.CFT.Kummer.finrank_kummerClasses_empty`,
`dim_{𝔽_p} V_∅/K^{×p} = dim_{𝔽_p} Cl_K[p] + (r₁+r₂-1) + δ_{K,p}`, together with the H¹ rank
formula (b) of Koch's Chapter 11 (`Work.CFT.Kummer.UnramifiedShafarevich.rank_formula`), which reads
`dim_{𝔽_p} 𝓒_∅ = dim_{𝔽_p} H¹(G_∅,𝔽_p) + (r₁+r₂-1) + δ_{K,p}`, identifies the two:
the generator rank `dim_{𝔽_p} H¹(G_∅,𝔽_p)` of the maximal everywhere-unramified pro-`p` Galois
group is the `p`-rank `dim_{𝔽_p} Cl_K[p]` of the class group — the classical statement whose proof
via class field theory (Artin reciprocity) is the content of the H¹ rank formula.
-/

open scoped nonZeroDivisors
open NumberField

noncomputable section

attribute [local instance] Classical.propDecidable

namespace Work.CFT.Kummer

variable (K : Type*) [Field K] [NumberField K] (p : ℕ) [Fact p.Prime]

/-- `𝓒_∅ = Hom(V_∅/K^{×p}, 𝔽_p)` has the same dimension as `V_∅/K^{×p}` (finite-dimensional
duality), so the Kummer computation of `dim V_∅/K^{×p}` is a computation of `dim 𝓒_∅`. -/
theorem finrank_kummerDual_empty :
    Module.finrank (ZMod p) (kummerDual K p ∅) =
      Module.finrank (ZMod p) (classGroupTorsion K p) +
        NumberField.Units.rank K + deltaK K p := by
  rw [Subspace.dual_finrank_eq, finrank_kummerClasses_empty K p (Fact.out : p.Prime)]

/-- The Kummer character group `𝓒_S = Hom(V_S/K^{×p}, 𝔽_p)` is finite-dimensional, since
`V_S/K^{×p}` is finite (`Work.CFT.Kummer.finite_kummerClasses`) and duality preserves finite
dimension. -/
theorem finite_kummerDual (S : Finset (IsDedekindDomain.HeightOneSpectrum (𝓞 K))) :
    Module.Finite (ZMod p) (kummerDual K p S) := by
  haveI := finite_kummerClasses K p (Fact.out : p.Prime) S
  infer_instance

variable (G : Type) [Group G]

/-- **The `p`-rank of the class group is the generator rank of the maximal unramified pro-`p`
group**: from the H¹ rank formula (b) and the Kummer computation
`dim 𝓒_∅ = dim Cl_K[p] + (r₁+r₂-1) + δ_{K,p}`, the two `𝔽_p`-dimensions
`dim H¹(G_∅,𝔽_p)` and `dim Cl_K[p]` agree. -/
theorem finrank_H1Fp_eq_finrank_classGroupTorsion [h : UnramifiedShafarevich K p G] :
    Module.finrank (ZMod p) (H1Fp p G) =
      Module.finrank (ZMod p) (classGroupTorsion K p) := by
  have h1 := h.rank_formula
  have h2 := finrank_kummerDual_empty K p
  omega


/-- **The two formulations of the input at `S = ∅` are equivalent.**  Given `UnramifiedShafarevich`
(the injection (a) plus the H¹ rank formula (b)), (b′) follows by the Kummer computation
`finrank_kummerDual_empty`. -/
noncomputable def unramifiedShafarevich_to_classGroup [h : UnramifiedShafarevich K p G] :
    UnramifiedShafarevichClassGroup K p G where
  sha := h.sha
  sha_injective := h.sha_injective
  h1_eq_classGroupRank := by
    have h1 := h.rank_formula
    have h2 := finrank_kummerDual_empty K p
    omega

/-- Conversely, the primitive input (a) + (b′) implies the H¹ rank formula (b), again by the
Kummer computation of `dim 𝓒_∅`. -/
noncomputable def classGroup_to_unramifiedShafarevich [h : UnramifiedShafarevichClassGroup K p G] :
    UnramifiedShafarevich K p G where
  sha := h.sha
  sha_injective := h.sha_injective
  rank_formula := by
    rw [h.h1_eq_classGroupRank]
    have h2 := finrank_kummerDual_empty K p
    omega

/-- **Shafarevich's estimate from the primitive inputs** (a) and (b′): the injection
`Ш²_∅ ↪ 𝓒_∅` and the identification `dim H¹(G_∅,𝔽_p) = dim Cl_K[p]` together give
`dim H²(G_∅,𝔽_p) ≤ dim H¹(G_∅,𝔽_p) + (r₁+r₂-1) + δ_{K,p}`. -/
theorem finrank_H2Fp_le_H1Fp_add_of_classGroupRank
    [h : UnramifiedShafarevichClassGroup K p G] :
    Module.finrank (ZMod p) (H2Fp p G) ≤
      Module.finrank (ZMod p) (H1Fp p G) + NumberField.Units.rank K + deltaK K p := by
  have h1 : Module.finrank (ZMod p) (H2Fp p G) ≤ Module.finrank (ZMod p) (kummerDual K p ∅) :=
    LinearMap.finrank_le_finrank_of_injective h.sha_injective
  have h2 := finrank_kummerDual_empty K p
  rw [h.h1_eq_classGroupRank]
  omega

end Work.CFT.Kummer
