import Mathlib
import Submission.Work.SSGRoute.ZDataMup.ArtinReciprocity.IdealModulus.CoreId
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# A congruent-`1` unit has a principal ideal coprime to the modulus

Let `𝔪 ≠ ⊥` be an ideal modulus of the number field `K` and let `a : Kˣ` satisfy Lang's
congruence `a ≡ 1 mod* 𝔪` (`CongrOneId 𝔪 a`), i.e. at every prime `𝔭 | 𝔪` the `𝔭`-adic value of
`a - 1` is at most the level `exp (-(count 𝔭 𝔪))`, and `a` is positive at the real places.

Because `𝔭 | 𝔪` with `𝔪 ≠ ⊥` forces `1 ≤ count 𝔭 𝔪`, the level is `< 1`, so the congruence says
that `a - 1` lies in the maximal ideal of the completion at `𝔭`; then `a = 1 + (a - 1)` is a local
unit there (`Valuation.map_add_eq_of_lt_left`), i.e. `v_𝔭(a) = 1`, and translating back through
`valued_algebraMap_eq_exp_neg_count_spanSingleton` gives `count 𝔭 (a) = 0`.  Hence the principal
fractional ideal `(a)` has no prime factor dividing `𝔪`.

All the components of this argument are available in `IdealModulus/CoreId.lean`: the idèlic
statement is `count_idealOf_eq_zero_of_congruenceId`, the dictionary between the ideal-theoretic
congruence and membership of the principal idèle in the congruence subgroup is
`principalIdele_mem_congruenceSubgroupId_iff`, and the principal ideal `(a)` is the ideal of the
principal idèle (`Idele.idealOf_principalIdele`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open scoped NumberField nonZeroDivisors
open NumberField IsDedekindDomain

noncomputable section

namespace Work.SSGRoute.ZDataMup.ArtinReciprocity.IdealModulus

open NK.CFTLib.ArtinReciprocityIdeal

/-- **A unit congruent to `1` modulo `𝔪` spans a fractional ideal coprime to `𝔪`.**

Since `a ≡ 1 mod* 𝔪` forces `a` to be a local unit at every `𝔭 | 𝔪`, the principal ideal `(a)`
has no prime factor dividing the modulus: `FracCoprimeId 𝔪 (spanUnit a)`. -/
theorem fracCoprimeId_spanUnit {K : Type} [Field K] [NumberField K]
    (𝔪 : Ideal (NumberField.RingOfIntegers K)) (h𝔪 : 𝔪 ≠ ⊥) {a : Kˣ}
    (ha : NK.CFTLib.ArtinReciprocityIdeal.CongrOneId 𝔪 a) :
    NK.CFTLib.ArtinReciprocityIdeal.FracCoprimeId 𝔪
      (NK.CFTLib.ArtinReciprocityIdeal.spanUnit a) := by
  intro 𝔭 h𝔭
  -- the principal ideal `(a)` is the ideal of the principal idèle of `a`
  rw [coe_spanUnit, ← NK.GlobalCFT.Idele.idealOf_principalIdele]
  -- `a ≡ 1 mod* 𝔪` says exactly that the principal idèle lies in the congruence subgroup
  refine count_idealOf_eq_zero_of_congruenceId
    ((principalIdele_mem_congruenceSubgroupId_iff h𝔪 a).mpr ha) 𝔭 ?_
  -- and `𝔭 | 𝔪` (with `𝔪 ≠ ⊥`) says that the level at `𝔭` is at least `1`
  exact (dvdPrime_iff_one_le_count h𝔪 𝔭).mp h𝔭

end Work.SSGRoute.ZDataMup.ArtinReciprocity.IdealModulus
