import Mathlib
import Submission.NK.BrauerHasse.Profinite
import Submission.NK.BrauerHasse.ofLevel_eq_iff

namespace NK.Indecomposed

open CategoryTheory Representation

universe u

/-- **The second cohomology of a group with at most one element is a subsingleton.**

`NK.BrauerHasse.H2 p G = H²(G, Z/p)` is the cohomology of the trivial representation; for the
trivial group it vanishes in positive degrees (Mathlib's
`isZero_groupCohomology_succ_of_subsingleton`), in particular in degree `2 = 1 + 1`.  The
vanishing is turned into the type-level statement by `ModuleCat.isZero_iff_subsingleton`. -/
lemma subsingleton_H2_of_subsingleton {p : ℕ} {G : Type u} [Group G] [Subsingleton G] :
    Subsingleton (NK.BrauerHasse.H2 p G) := by
  refine (ModuleCat.isZero_iff_subsingleton).mp ?_
  show Limits.IsZero
    (groupCohomology (Rep.trivial (NK.BrauerHasse.Coeff p) G (NK.BrauerHasse.Coeff p)) 2)
  exact isZero_groupCohomology_succ_of_subsingleton _ 1

/-- **The level cohomology is a subsingleton when the subgroup is.**

The level of `H²(U, Z/p)` attached to a finite Galois intermediate field `L` is the cohomology
`H²(U/(U ∩ Gal(K'/L)), Z/p)` of the finite quotient `NK.BrauerHasse.LevelGroup U L`, which is a
quotient of the (subsingleton) type `↥U` and therefore itself a subsingleton. -/
lemma subsingleton_LevelH2_of_subsingleton {K K' : Type u} [Field K] [Field K']
    [Algebra K K'] [IsSepClosure K K'] (p : ℕ) {U : Subgroup Gal(K'/K)} [Subsingleton ↥U]
    (L : FiniteGaloisIntermediateField K K') :
    Subsingleton (NK.BrauerHasse.LevelH2 (K := K) (K' := K') p U L) :=
  subsingleton_H2_of_subsingleton

/-- **`H²(U, Z/p)` is a subsingleton for a subgroup `U` with at most one element.**

`H2Profinite p U` is the colimit of the level cohomologies `H²(U/(U ∩ Gal(K'/L)), Z/p)` over the
finite Galois intermediate fields `L`.  If `↥U` is a subsingleton then so is every level group, so
by `subsingleton_LevelH2_of_subsingleton` every level cohomology is a subsingleton.  Since the
finite Galois intermediate fields are *directed* (two levels have the common upper bound `L ⊔ L'`),
the description `NK.BrauerHasse.ofLevel_eq_iff` of equality in the colimit shows that any two
classes of `H²(U, Z/p)` agree: they agree already on the common dominating level. -/
theorem subsingleton_h2Profinite_of_subsingleton {K K' : Type u} [Field K] [Field K']
    [Algebra K K'] [IsSepClosure K K'] (p : ℕ) {U : Subgroup Gal(K'/K)} [Subsingleton ↥U] :
    Subsingleton (NK.BrauerHasse.H2Profinite (K := K) (K' := K') p U) := by
  refine ⟨fun x y => ?_⟩
  obtain ⟨L, a, rfl⟩ :=
    NK.BrauerHasse.H2Profinite.ofLevel_surjective (p := p) (U := U) x
  obtain ⟨L', b, rfl⟩ :=
    NK.BrauerHasse.H2Profinite.ofLevel_surjective (p := p) (U := U) y
  rw [NK.BrauerHasse.ofLevel_eq_iff]
  refine ⟨L ⊔ L', le_sup_left, le_sup_right, ?_⟩
  have hsub : Subsingleton (NK.BrauerHasse.LevelH2 (K := K) (K' := K') p U (L ⊔ L')) :=
    subsingleton_LevelH2_of_subsingleton (K := K) (K' := K') p (L ⊔ L')
  exact Subsingleton.elim _ _

end NK.Indecomposed
