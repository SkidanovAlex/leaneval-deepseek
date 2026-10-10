import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.Topology.Algebra.RestrictedProduct.Basic
import Submission.NK.GlobalCFT.Inclusion.globalCFT_fixed_idele_mem_range
import Submission.NK.GlobalCFTdeep.Herbrand.TUnitsRank
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The normalized `Q`-adic valuation of a local unit, and the statement's `expUnit`

The main theorem `NK.CFTLib.normPrincipalPreimage_iff_expUnit` characterises the elements
`x : Fˣ` whose principal idèle is a norm of an idèle of `K` by the divisibility conditions

`f_v ∣ v(x)`  (`v` running over the finite places of `F`),

where `f_v` is the inertia degree and `v(x) = NK.GlobalCFTdeep.expUnit v x`.

This file collects the vocabulary used to state the local lemmas:

* `NK.CFTLib.finVal F Q z` — the `Q`-adic valuation of a unit `z` of the completion `F_Q`, in
  additive coordinates (`- log (Valued.v z)`), so that `finVal F Q` is an additive function of `z`;
* `finVal_principalIdele` — the compatibility with `expUnit`: the value of the principal idèle of
  `x` at the finite place `Q` has valuation `expUnit Q x`;
* `finVal_mul`, `finVal_one`, `finVal_pow`, `finVal_prod` — additivity of `finVal`;
* `finVal_eq_zero_iff_mem_localUnits` — `finVal F Q z = 0` iff `z` is a local unit at `Q`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

open scoped NumberField RestrictedProduct
open NumberField IsDedekindDomain

noncomputable section

namespace NK.CFTLib

/-- The normalized `Q`-adic valuation of a unit `z` of the completion `F_Q`, in additive
coordinates: the integer `n` with `Valued.v z = exp (-n)`. -/
noncomputable def finVal (F : Type) [Field F] [NumberField F]
    (Q : HeightOneSpectrum (𝓞 F)) (z : (Q.adicCompletion F)ˣ) : ℤ :=
  - WithZero.log (Valued.v (z : Q.adicCompletion F))

/-- The valuation of the principal idèle of `x` at the finite place `Q` is `expUnit Q x`. -/
theorem finVal_principalIdele {F K : Type} [Field F] [NumberField F] [Field K] [NumberField K]
    [Algebra F K] [FiniteDimensional F K] (Q : HeightOneSpectrum (𝓞 F)) (x : Fˣ) :
    finVal F Q ((NK.GlobalCFT.Idele.principalIdele F x)
        (NK.GlobalCFT.Place.ofFinite Q)) = NK.GlobalCFTdeep.expUnit Q x := by
  have h : ((NK.GlobalCFT.Idele.principalIdele F x) (NK.GlobalCFT.Place.ofFinite Q) :
      (Q.adicCompletion F)ˣ) = Units.map (algebraMap F (Q.adicCompletion F)) x := rfl
  rw [finVal, h, NK.GlobalCFTdeep.expUnit, Units.coe_map]
  exact congrArg (fun z => - (WithZero.log z))
    (Commons.NumberTheory.NumberField.val_algebraMap_adicCompletion_eq Q (x : F))

@[simp] theorem finVal_one (F : Type) [Field F] [NumberField F] (Q : HeightOneSpectrum (𝓞 F)) :
    finVal F Q 1 = 0 := by
  rw [finVal, Units.val_one, map_one, WithZero.log_one, neg_zero]

theorem finVal_mul (F : Type) [Field F] [NumberField F] (Q : HeightOneSpectrum (𝓞 F))
    (z w : (Q.adicCompletion F)ˣ) :
    finVal F Q (z * w) = finVal F Q z + finVal F Q w := by
  have hz : Valued.v (z : Q.adicCompletion F) ≠ 0 := by
    rw [Valuation.ne_zero_iff]; exact Units.ne_zero z
  have hw : Valued.v (w : Q.adicCompletion F) ≠ 0 := by
    rw [Valuation.ne_zero_iff]; exact Units.ne_zero w
  rw [finVal, finVal, finVal, Units.val_mul, map_mul, WithZero.log_mul hz hw]
  ring

theorem finVal_pow (F : Type) [Field F] [NumberField F] (Q : HeightOneSpectrum (𝓞 F))
    (z : (Q.adicCompletion F)ˣ) (n : ℕ) :
    finVal F Q (z ^ n) = n * finVal F Q z := by
  rw [finVal, finVal, Units.val_pow_eq_pow_val, map_pow, WithZero.log_pow]
  simp

theorem finVal_prod (F : Type) [Field F] [NumberField F] (Q : HeightOneSpectrum (𝓞 F))
    {ι : Type} [DecidableEq ι] (s : Finset ι) (z : ι → (Q.adicCompletion F)ˣ) :
    finVal F Q (∏ i ∈ s, z i) = ∑ i ∈ s, finVal F Q (z i) := by
  induction s using Finset.induction with
  | empty => simp [finVal_one]
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, finVal_mul, ih]

theorem finVal_eq_zero_iff_mem_localUnits (F : Type) [Field F] [NumberField F]
    (Q : HeightOneSpectrum (𝓞 F)) (z : (Q.adicCompletion F)ˣ) :
    finVal F Q z = 0 ↔
      z ∈ NK.GlobalCFT.Place.localUnits F (NK.GlobalCFT.Place.ofFinite Q) := by
  rw [NK.GlobalCFT.Place.mem_localUnits_ofFinite_iff_valued_eq_one]
  rw [finVal, neg_eq_zero, ← WithZero.exp_eq_one,
    WithZero.exp_log (by rw [Valuation.ne_zero_iff]; exact Units.ne_zero z)]

end NK.CFTLib
