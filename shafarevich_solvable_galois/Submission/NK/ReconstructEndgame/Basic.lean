import Submission.NK.Reconstruct.exists_sigma_of_localCorrespondence
import Submission.NeukirchUchida.Core
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The endgame of Neukirch–Uchida via the Shimizu route: the `ℚ`-structure on a separable closure

This file is the foundation of the assembly chapter `Submission/Work/ReconstructEndgame/`.

The Shimizu route of `Submission/Work/Reconstruct/exists_sigma_of_localCorrespondence.lean`
produces the existence half of Neukirch–Uchida from

* the σ-free local (place) correspondence `a : NK.Reconstruct.LocalCorrespondence ϕ`,
* the σ-free Frobenius correspondence `b : NK.Reconstruct.FrobeniusCorrespondencePlace ϕ he a`,
* a prime `ℓ`, the three rank inputs of Shimizu's §4 (`HausRankInput K₁' ℓ`,
  `RankStrictMonoLevelInputGen K₁' ℓ`, `ResRankInputGen K₁' ℓ`) and Čebotarev
  (`ChebotarevInput ℚ K₁'`),

and the last four hypotheses are predicates on `K₁'` *as a `ℚ`-algebra*.

The fields of the challenge theorem only carry `[NumberField K₁] [Algebra K₁ K₁']
[IsSepClosure K₁ K₁']`, from which the `ℚ`-algebra structure on `K₁'` (and the facts that `K₁'` is a
separable closure of `ℚ` and that `K₁'/ℚ` is Galois) are **not** typeclass instances but have to be
*derived*.  This file performs that derivation:

* `NK.ReconstructEndgame.ratAlgebra` — the `ℚ`-algebra structure on `K'`, obtained by composing
  `ℚ → K` with the given `K`-algebra structure `K → K'`;
* `NK.ReconstructEndgame.isScalarTower_rat_of_numberField` — the tower relation `ℚ → K → K'`, for
  *any* `ℚ`-algebra structure on `K'` (both `algebraMap ℚ K'` and the composite are ring maps out of
  the prime field `ℚ`, so they agree);
* `NK.ReconstructEndgame.isSepClosure_rat_of_numberField` — `K'` is a separable closure of `ℚ`
  (it is separably closed as a separable closure of `K`, and `ℚ → K'` is algebraic, being the
  composite of `ℚ → K` and `K → K'`, hence separable because `ℚ` is perfect), again for any
  `ℚ`-algebra structure on `K'`;
* `NK.ReconstructEndgame.isGalois_rat_of_numberField` — consequently `K'/ℚ` is Galois.

Finally, for a number field `K` with separable closure `K'` this file provides the `ℚ`-algebra
*forms* of the four Shimizu inputs of the reconstruction,

`HausRankInputDerived`, `RankStrictMonoLevelInputGenDerived`, `ResRankInputGenDerived`,
`ChebotarevInputDerived`,

each of which is *definitionally* `NK.Reconstruct.HausRankInput K' ℓ` (etc.) with the `ℚ`-algebra
structure on `K'` and the derived `IsSepClosure ℚ K'` supplied by `letI`.  A caller who does not
want to carry the `ℚ`-structure hypotheses can state the Shimizu inputs with these names; a caller
who already has an `Algebra ℚ K'` in scope can use the plain forms (any two `ℚ`-algebra structures
on a field are equal, so there is no loss).
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option warn.classDefReducibility false

universe u v

namespace NK.ReconstructEndgame

/-- **The `ℚ`-algebra structure on a separable closure `K'` of a number field `K`.**

`NumberField K` supplies the `ℚ`-algebra structure on `K`; composing the corresponding ring map
`ℚ →+* K` with the given `K`-algebra structure `K →+* K'` makes `K'` a `ℚ`-algebra.  It is the
canonical such structure: any `Algebra ℚ K'` has the same `algebraMap`, because there is only one
ring homomorphism `ℚ →+* K'`. -/
noncomputable def ratAlgebra (K : Type u) (K' : Type v) [Field K] [NumberField K] [Field K'] [Algebra K K'] :
    Algebra ℚ K' :=
  ((algebraMap K K').comp (algebraMap ℚ K)).toAlgebra

/-- **Canonicity of the derived `ℚ`-algebra structure.**  Any `ℚ`-algebra structure on `K'` agrees
with `ratAlgebra K K'`: there is only one, since a ring homomorphism out of the prime field `ℚ` is
unique (`Subsingleton (Algebra ℚ R)`).  Consequently the `ℚ`-algebra form of a Shimizu input
(`HausRankInputDerived`, ...) and its plain form differ only by a propositionally — and, for
`HausRankInput`, definitionally — equal instance, and the `ℚ`-algebra structure on `K'` may be
chosen freely. -/
theorem ratAlgebra_eq (K : Type u) (K' : Type v) [Field K] [NumberField K] [Field K']
    [Algebra K K'] [Algebra ℚ K'] : (inferInstance : Algebra ℚ K') = ratAlgebra K K' :=
  Subsingleton.elim _ _

/-- **The tower relation holds for *any* `ℚ`-algebra structure on a finite extension of `ℚ`**:
both `algebraMap ℚ K'` and `algebraMap K K' ∘ algebraMap ℚ K` are ring homomorphisms `ℚ →+* K'`,
and there is only one of those. -/
theorem isScalarTower_rat_of_numberField (K : Type u) (K' : Type v) [Field K] [NumberField K] [Field K']
    [Algebra K K'] [Algebra ℚ K'] : IsScalarTower ℚ K K' :=
  NK.Reconstruct.isScalarTower_rat_of_numberField

/-- **`K'` is a separable closure of `ℚ`, for any `ℚ`-algebra structure on `K'`.**

`K'` is separably closed because it is a separable closure of `K`, and `ℚ → K'` is algebraic
(composite of the finite `ℚ → K` and the algebraic `K → K'`), hence separable since `ℚ` is
perfect. -/
theorem isSepClosure_rat_of_numberField (K : Type u) (K' : Type v) [Field K] [NumberField K] [Field K']
    [Algebra K K'] [IsSepClosure K K'] [Algebra ℚ K'] : IsSepClosure ℚ K' := by
  haveI : IsScalarTower ℚ K K' := isScalarTower_rat_of_numberField K K'
  refine ⟨IsSepClosure.sep_closed K, ?_⟩
  have halg : Algebra.IsAlgebraic ℚ K' := Algebra.IsAlgebraic.trans (R := ℚ) (S := K) (A := K')
  exact halg.isSeparable_of_perfectField

/-- Consequently `K'/ℚ` is Galois, for any `ℚ`-algebra structure on `K'`. -/
theorem isGalois_rat_of_numberField (K : Type u) (K' : Type v) [Field K] [NumberField K] [Field K']
    [Algebra K K'] [IsSepClosure K K'] [Algebra ℚ K'] : IsGalois ℚ K' := by
  haveI : IsSepClosure ℚ K' := isSepClosure_rat_of_numberField K K'
  exact IsSepClosure.isGalois

/-! ## The Shimizu inputs in `ℚ`-algebra form

For a number field `K` with separable closure `K'`, the four hypotheses of the Shimizu route that
are predicates on `K'` as a `ℚ`-algebra.  Each of the four definitions below is *definitionally*
the corresponding `NK.Reconstruct` predicate with the `ℚ`-algebra structure `ratAlgebra K K'` on
`K'` and the derived instance `IsSepClosure ℚ K'`, so a caller who states a hypothesis with these
names can feed it to `NK.Reconstruct.exists_sigma_of_localCorrespondence` directly (inside a
`letI` block), while a caller who already has a `ℚ`-algebra structure in scope can use the plain
`NK.Reconstruct` forms. -/

/-- **Shimizu's rank input `NK.Reconstruct.HausRankInput K' ℓ`, with the `ℚ`-algebra structure on
`K'` derived from the number field `K`.** -/
def HausRankInputDerived (K : Type u) (K' : Type v) [Field K] [NumberField K] [Field K'] [Algebra K K']
    [IsSepClosure K K'] (ℓ : ℕ) [Fact ℓ.Prime] : Prop :=
  letI : Algebra ℚ K' := ratAlgebra K K'
  letI : IsSepClosure ℚ K' := isSepClosure_rat_of_numberField K K'
  NK.Reconstruct.HausRankInput K' ℓ

/-- **Shimizu's Lemma 4f.2 (`RankStrictMonoLevelInputGen`), with the `ℚ`-algebra structure on `K'`
derived from the number field `K`.** -/
def RankStrictMonoLevelInputGenDerived (K : Type u) (K' : Type v) [Field K] [NumberField K] [Field K']
    [Algebra K K'] [IsSepClosure K K'] (ℓ : ℕ) [Fact ℓ.Prime] : Prop :=
  letI : Algebra ℚ K' := ratAlgebra K K'
  letI : IsSepClosure ℚ K' := isSepClosure_rat_of_numberField K K'
  NK.Reconstruct.RankStrictMonoLevelInputGen K' ℓ

/-- **Shimizu's rank computation of Proposition 4f.5 (`ResRankInputGen`), with the `ℚ`-algebra
structure on `K'` derived from the number field `K`.** -/
def ResRankInputGenDerived (K : Type u) (K' : Type v) [Field K] [NumberField K] [Field K'] [Algebra K K']
    [IsSepClosure K K'] (ℓ : ℕ) [Fact ℓ.Prime] : Prop :=
  letI : Algebra ℚ K' := ratAlgebra K K'
  letI : IsSepClosure ℚ K' := isSepClosure_rat_of_numberField K K'
  NK.Reconstruct.ResRankInputGen K' ℓ

/-- **Čebotarev's density theorem in the finite-level form `NK.Reconstruct.ChebotarevInput ℚ K'`,
with the `ℚ`-algebra structure on `K'` derived from the number field `K`.** -/
def ChebotarevInputDerived (K : Type u) (K' : Type v) [Field K] [NumberField K] [Field K'] [Algebra K K']
    [IsSepClosure K K'] : Prop :=
  letI : Algebra ℚ K' := ratAlgebra K K'
  NK.Reconstruct.ChebotarevInput ℚ K'

end NK.ReconstructEndgame
