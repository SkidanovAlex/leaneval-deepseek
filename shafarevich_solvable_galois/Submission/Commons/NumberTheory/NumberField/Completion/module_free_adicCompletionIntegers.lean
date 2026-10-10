import Mathlib.RingTheory.Henselian
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Submission.Commons.NumberTheory.NumberField.Completion.isIntegralClosure_adicCompletionIntegers_extension
import Submission.Commons.NumberTheory.NumberField.Completion.module_finite_adicCompletion
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The ring of integers of the `q`-adic completion is a free module over the ring of
integers of the `Q`-adic completion

Let `L / K` be an extension of number fields, `Q` a height-one prime of `𝓞 K` and `q` a
height-one prime of `𝓞 L` lying over `Q`.  Then the ring of integers `q.adicCompletionIntegers L`
of the `q`-adic completion of `L` is a *free* module over the ring of integers
`Q.adicCompletionIntegers K` of the `Q`-adic completion of `K`.

This is the integral refinement of the local fundamental identity
`[L_q : K_Q] = e · f`: the resulting free module has rank equal to the local degree.

The proof is the general structure theorem for integral closures over a principal ideal domain.
Regard `A = Q.adicCompletionIntegers K` as a discrete valuation ring with fraction field
`K_Q = Q.adicCompletion K`; it is a principal ideal ring (`IsPrincipalIdealRing`).  The ring
`C = q.adicCompletionIntegers L` is the integral closure of `A` in the finite separable
extension `L_q = q.adicCompletion L`
(`Commons.NumberTheory.NumberField.Completion.isIntegralClosure_adicCompletionIntegers_extension`),
and `L_q` is a finite-dimensional `K_Q`-vector space
(`Commons.NumberTheory.NumberField.Completion.module_finite_adicCompletion`).  Hence Mathlib's
theorem `IsIntegralClosure.module_free` applies and yields `Module.Free A C`.
-/

open scoped NumberField

set_option autoImplicit false
set_option linter.style.haveILetI false

noncomputable section

namespace Commons.NumberTheory.NumberField.Completion

open IsDedekindDomain.HeightOneSpectrum

theorem module_free_adicCompletionIntegers {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hq : q.asIdeal.LiesOver Q.asIdeal) :
    letI : Algebra (Q.adicCompletionIntegers K) (q.adicCompletionIntegers L) :=
      RingHom.toAlgebra (((Commons.RingTheory.Henselian.adicCompletionMap Q q hq).comp
          (Q.adicCompletionIntegers K).subtype).codRestrict (q.adicCompletionIntegers L)
        (fun x => Commons.RingTheory.Henselian.adicCompletionMap_mem_integers Q q hq x.2))
    Module.Free (Q.adicCompletionIntegers K) (q.adicCompletionIntegers L) := by
  -- The algebra structure on the *field* `q.adicCompletion L` induced by the completion map.
  letI : Algebra (Q.adicCompletionIntegers K) (q.adicCompletion L) :=
    RingHom.toAlgebra ((Commons.RingTheory.Henselian.adicCompletionMap Q q hq).comp
      (Q.adicCompletionIntegers K).subtype)
  -- The algebra structure on the ring of integers `q.adicCompletionIntegers L`.
  letI : Algebra (Q.adicCompletionIntegers K) (q.adicCompletionIntegers L) :=
    RingHom.toAlgebra (((Commons.RingTheory.Henselian.adicCompletionMap Q q hq).comp
        (Q.adicCompletionIntegers K).subtype).codRestrict (q.adicCompletionIntegers L)
      (fun x => Commons.RingTheory.Henselian.adicCompletionMap_mem_integers Q q hq x.2))
  -- The algebra structure of the completed field `q.adicCompletion L` over `Q.adicCompletion K`.
  letI : Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q hq)
  -- The two towers `A → K_Q → L_q` and `A → C → L_q` are scalar towers.
  haveI : IsScalarTower (Q.adicCompletionIntegers K) (Q.adicCompletion K) (q.adicCompletion L) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower (Q.adicCompletionIntegers K) (q.adicCompletionIntegers L)
      (q.adicCompletion L) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  -- Algebraic structure of `A = Q.adicCompletionIntegers K`.
  haveI : IsFractionRing (Q.adicCompletionIntegers K) (Q.adicCompletion K) := inferInstance
  haveI : IsDomain (Q.adicCompletionIntegers K) := inferInstance
  haveI : IsPrincipalIdealRing (Q.adicCompletionIntegers K) := inferInstance
  -- `L_q` is a finite-dimensional `K_Q`-vector space.
  haveI : FiniteDimensional (Q.adicCompletion K) (q.adicCompletion L) :=
    Commons.NumberTheory.NumberField.Completion.module_finite_adicCompletion Q q hq
  -- The completed fields have characteristic zero, so the finite extension is separable.
  haveI : CharZero (Q.adicCompletion K) :=
    charZero_of_injective_algebraMap (algebraMap K (Q.adicCompletion K)).injective
  -- `L_q` is torsion-free over `A` (it is a field extension of `K_Q = Frac A`).
  haveI : Module.IsTorsionFree (Q.adicCompletionIntegers K) (q.adicCompletion L) :=
    Module.IsTorsionFree.trans_faithfulSMul (Q.adicCompletionIntegers K) (Q.adicCompletion K)
      (q.adicCompletion L)
  -- `C` is the integral closure of `A` in `L_q`.
  haveI : IsIntegralClosure (q.adicCompletionIntegers L) (Q.adicCompletionIntegers K)
      (q.adicCompletion L) :=
    isIntegralClosure_adicCompletionIntegers_extension Q q hq
  -- The structure theorem for integral closures over a PID.
  exact IsIntegralClosure.module_free (Q.adicCompletionIntegers K) (Q.adicCompletion K)
    (q.adicCompletion L) (q.adicCompletionIntegers L)

end Commons.NumberTheory.NumberField.Completion
