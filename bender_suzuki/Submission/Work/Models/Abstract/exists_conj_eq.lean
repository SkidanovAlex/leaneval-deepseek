import Mathlib
import Submission.Work.Models.Port.BenderSetup
import Submission.Work.Models.Basic
import Submission.Work.Models.Abstract.isCoatom_B
import Submission.Work.Models.Port.Commons.GroupTheory.StronglyEmbedded.exists_conj_eq_of_isStronglyEmbedded
import Submission.Work.Models.Port.Commons.GroupTheory.Subgroup.isCoatom_map_mulAut_conj

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Models.Abstract

/-- The monoid endomorphism attached to `MulAut.conj g` by the (pointwise) action on subgroups
is the monoid homomorphism `MulAut.conj g`. -/
lemma toMonoidEnd_mulAut_conj {G : Type*} [Group G] (g : G) :
    MulDistribMulAction.toMonoidEnd (MulAut G) G (MulAut.conj g)
      = (MulAut.conj g).toMonoidHom := by
  ext x
  rfl

/-- **Every strongly embedded subgroup of a Bender group is a conjugate of the Borel.**

A strongly embedded subgroup `H` contains a Sylow `2`-subgroup of `G`, and (because the
normalizer of an even-order subgroup of `H` lies in `H`) `H` is the normalizer of every Sylow
`2`-subgroup it contains.  In a Bender group the normalizer of every Sylow `2`-subgroup is a
coatom (`N(U) = B` and `U` is Sylow), so `H` is the normalizer of a Sylow `2`-subgroup, and
Sylow subgroups are conjugate. -/
theorem exists_conj_eq {G : Type*} [Group G] [Finite G] (P : Submission.BenderPair G)
    {H : Subgroup G} (hH : LeanEval.GroupTheory.Defs.IsStronglyEmbedded H) :
    ∃ g : G, H = Submission.Blueprint.conj g P.B := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmax : ∀ T : Sylow 2 G,
      IsCoatom (Subgroup.normalizer (((T : Subgroup G) : Set G))) := by
    intro T
    obtain ⟨S₀, hS₀⟩ := P.exists_sylow_eq_U
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S₀ T
    have hT : (T : Subgroup G)
        = (S₀ : Subgroup G).map (MulAut.conj g).toMonoidHom := by
      rw [← hg, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def, toMonoidEnd_mulAut_conj]
    rw [hT, Commons.GroupTheory.Subgroup.normalizer_map_mulAut_conj, hS₀, P.normalizer_U]
    exact Commons.GroupTheory.Subgroup.isCoatom_map_mulAut_conj (isCoatom_B P) g
  exact Commons.GroupTheory.StronglyEmbedded.exists_conj_eq_of_isStronglyEmbedded P.B H
    P.hSemb.1 P.hSemb.2.1 P.hSemb.2.2 hH.1 hH.2.1 hH.2.2 hmax

end Work.Models.Abstract
