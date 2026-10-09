import Mathlib
import Submission.NK.BrauerTwist.Profinite
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

universe u

namespace NK.Indecomposed

/-!
# The local component of a twisted class is carried by the decomposition group

If the localisation `NK.BrauerTwist.H2Twist.loc p U x A` of a twisted cohomology class `x` at the
place `A` is non-zero, then the decomposition group of `A` meets `U` non-trivially:

`U ⊓ D_A ≠ ⊥`.

Equivalently: at a place `A` that is *decompletely decomposed* in `K'/U K` (so that the local group
`U ⊓ D_A` is trivial), the localisation of *every* class vanishes.  The proof is the direct one:
if `U ⊓ D_A = ⊥` then every local level group
`(U ⊓ D_A) / ((U ⊓ D_A) ∩ Gal(K'/L))` is a subsingleton group, hence so is the local level
cohomology `LocalLevelH2 p U A L = H²((U ⊓ D_A)/(…), μ_p(L))`
(Mathlib's `isZero_groupCohomology_succ_of_subsingleton`), and a filtered colimit of subsingletons
is a subsingleton.
-/

open NK.BrauerTwist

/-- A filtered colimit of subsingletons is a subsingleton: two classes are represented at finite
levels, and after pushing both to a common dominating level they coincide. -/
private lemma subsingleton_colim_of_subsingleton_obj {K K' : Type u} [Field K] [Field K']
    [Algebra K K'] (S : NK.BrauerTwist.LevelSystem K K') (h : ∀ L, Subsingleton (S.obj L)) :
    Subsingleton S.Colim := by
  refine ⟨fun x y => ?_⟩
  obtain ⟨L, a, rfl⟩ := S.ofLevel_surjective x
  obtain ⟨L', b, rfl⟩ := S.ofLevel_surjective y
  rw [S.ofLevel_eq_iff a b]
  refine ⟨L ⊔ L', le_sup_left, le_sup_right, ?_⟩
  haveI := h (L ⊔ L')
  exact Subsingleton.elim _ _

/-- If `U ⊓ D_A = ⊥` then every local level cohomology `LocalLevelH2 p U A L` is a subsingleton:
the local level group is a quotient of the trivial group `↥(U ⊓ D_A)`, and the cohomology of a
trivial group vanishes in degree `2 = 1 + 1`. -/
private lemma subsingleton_localLevelH2_of_inf_eq_bot {K K' : Type u} [Field K] [Field K']
    [Algebra K K'] [IsSepClosure K K'] (p : ℕ) (U : Subgroup Gal(K'/K))
    (A : ValuationSubring K') (h : U ⊓ NK.BrauerTwist.stabSubgroup A = ⊥)
    (L : FiniteGaloisIntermediateField K K') :
    Subsingleton (NK.BrauerTwist.LocalLevelH2 (K := K) (K' := K') p U A L) := by
  haveI hsub : Subsingleton ↥(U ⊓ NK.BrauerTwist.stabSubgroup A) :=
    h ▸ (inferInstance : Subsingleton ↥(⊥ : Subgroup Gal(K'/K)))
  haveI : Subsingleton (NK.BrauerHasse.LocalLevelGroup U A L) := inferInstance
  have hz : CategoryTheory.Limits.IsZero
      (groupCohomology (NK.BrauerTwist.localLevelRep (K := K) (K' := K') p U A L) 2) :=
    isZero_groupCohomology_succ_of_subsingleton
      (NK.BrauerTwist.localLevelRep (K := K) (K' := K') p U A L) 1
  exact (ModuleCat.isZero_iff_subsingleton).mp hz

theorem inf_stabSubgroup_ne_bot_of_loc_ne_zero {K K' : Type u} [Field K] [NumberField K]
    [Field K'] [Algebra K K'] [IsSepClosure K K'] (p : ℕ) (U : Subgroup Gal(K'/K))
    (A : NK.BrauerTwist.OverFinitePrime K K')
    {x : NK.BrauerTwist.H2Twist (K := K) (K' := K') p U}
    (hx : NK.BrauerTwist.H2Twist.loc p U x A ≠ 0) :
    U ⊓ NK.BrauerTwist.stabSubgroup A.1 ≠ ⊥ := by
  intro h
  apply hx
  haveI : Subsingleton (NK.BrauerTwist.LocalH2Twist (K := K) (K' := K') p U A.1) :=
    subsingleton_colim_of_subsingleton_obj
      (NK.BrauerTwist.localTwistSystem (K := K) (K' := K') p U A.1)
      (fun L => subsingleton_localLevelH2_of_inf_eq_bot p U A.1 h L)
  exact Subsingleton.elim _ _

end NK.Indecomposed
