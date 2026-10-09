import Mathlib
import Submission.NK.BrauerTwist.Profinite
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

universe u

namespace NK.Indecomposed

open CategoryTheory

/-- **The local level cohomology of a trivial local group is a point.**

If the local group `U ⊓ D_A` is trivial, then at every finite level `L` the local level group
`(U ⊓ D_A) ⧸ ((U ⊓ D_A) ⊓ Gal(K'/L))` is trivial, so the local level cohomology
`H²((U ⊓ D_A) ⧸ ((U ⊓ D_A) ⊓ Gal(K'/L)), μ_p(L))` is the second cohomology of the trivial group
with coefficients in `μ_p(L)` — and `Hⁿ(1, M) = 0` for `n ≥ 1`
(Mathlib's `isZero_groupCohomology_succ_of_subsingleton`). -/
private theorem subsingleton_localLevelH2_of_inf_eq_bot {K K' : Type u} [Field K] [Field K']
    [Algebra K K'] [IsSepClosure K K'] (p : ℕ) (U : Subgroup Gal(K'/K))
    (A : ValuationSubring K') (h : U ⊓ NK.BrauerTwist.stabSubgroup A = ⊥)
    (L : FiniteGaloisIntermediateField K K') :
    Subsingleton (NK.BrauerTwist.LocalLevelH2 (K := K) (K' := K') p U A L) := by
  have hsub : Subsingleton ↥(U ⊓ NK.BrauerTwist.stabSubgroup A) := by
    rw [h]
    infer_instance
  have hgrp : Subsingleton (NK.BrauerHasse.LocalLevelGroup U A L) := inferInstance
  refine ModuleCat.subsingleton_of_isZero ?_
  have hzero := isZero_groupCohomology_succ_of_subsingleton
    (NK.BrauerTwist.localLevelRep (K := K) (K' := K') p U A L) 1
  exact hzero

/-- **The local twisted cohomology at a place is a point when the local group is trivial.**

`NK.BrauerTwist.LocalH2Twist p U A` is the filtered colimit of the local level cohomologies
`H²((U ⊓ D_A) ⧸ ((U ⊓ D_A) ⊓ Gal(K'/L)), μ_p(L))`.  If `U ⊓ D_A = ⊥` every level is a point
(`subsingleton_localLevelH2_of_inf_eq_bot`), and then so is the colimit: two classes represented at
levels `L` and `L'` are identified after inflation to the common dominating level `L ⊔ L'`, where
there is only one element. -/
theorem subsingleton_localH2Twist_of_inf_eq_bot {K K' : Type u} [Field K] [Field K']
    [Algebra K K'] [IsSepClosure K K'] (p : ℕ) (U : Subgroup Gal(K'/K))
    (A : ValuationSubring K')
    (h : U ⊓ NK.BrauerTwist.stabSubgroup A = ⊥) :
    Subsingleton (NK.BrauerTwist.LocalH2Twist (K := K) (K' := K') p U A) := by
  refine ⟨fun x y => ?_⟩
  obtain ⟨L, a, rfl⟩ := NK.BrauerTwist.LocalH2Twist.ofLevel_surjective p U A x
  obtain ⟨L', b, rfl⟩ := NK.BrauerTwist.LocalH2Twist.ofLevel_surjective p U A y
  rw [NK.BrauerTwist.LocalH2Twist.ofLevel_eq_iff]
  exact ⟨L ⊔ L', le_sup_left, le_sup_right,
    @Subsingleton.elim _
      (subsingleton_localLevelH2_of_inf_eq_bot p U A h (L ⊔ L')) _ _⟩

end NK.Indecomposed
