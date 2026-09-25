import Mathlib
import Submission.Commons.RingTheory.Henselian.adicCompletionMap_liesOver
import Submission.Commons.NumberTheory.NumberField.Completion.exists_ringEquiv_adicCompletion_of_residue_ringEquiv
import Submission.Commons.NumberTheory.NumberField.Completion.exists_inertiaSubgroup_adicCompletion_card_eq_ramificationIdx

/-!
# The local field of a number field at a place

This file fixes the conventions of the `NK.LocalReciprocity` area.

For a number field `K` and a finite place `Q` of `K`, the local field is the completion
`K_Q = Q.adicCompletion K`; the residue field of its ring of integers is
`k_Q = IsLocalRing.ResidueField (Q.adicCompletionIntegers K)`, of cardinality
`residueCard Q = #k_Q`.

For a finite Galois extension `L / K` of number fields and a place `q` of `L` above `Q`, the local
field `L_q = q.adicCompletion L` is an algebra over `K_Q` through the canonical map
`Commons.RingTheory.Henselian.adicCompletionMap Q q hq`; this algebra structure is registered
as an *instance* (`NK.LocalReciprocity.instAlgebraAdicCompletion`) so that
`Gal(L_q / K_Q) = L_q ≃ₐ[K_Q] L_q` can be written without explicit `letI`s.  (It agrees
definitionally with the `letI` used throughout
`Submission/Commons/NumberTheory/NumberField/Completion/`.)

The main definition of this file is the predicate `IsFrobeniusLocal σ` describing the *canonical
Frobenius* of an unramified local extension: `σ x ≡ x ^ residueCard Q (mod 𝔪)` for all integral
`x`.  It is characterised by this congruence because the residue action is faithful precisely when
the extension is unramified (`ramificationIdx = 1`).
-/

open scoped NumberField
open IsDedekindDomain.HeightOneSpectrum

namespace NK.LocalReciprocity

/-- The `Algebra` structure of the `q`-adic completion of `L` over the `Q`-adic completion of
`K`, induced by the canonical map `Commons.RingTheory.Henselian.adicCompletionMap`. -/
noncomputable instance instAlgebraAdicCompletion (K : Type*) [Field K] [NumberField K]
    (Q : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (L : Type*) [Field L] [NumberField L]
    [Algebra K L] (q : IsDedekindDomain.HeightOneSpectrum (𝓞 L))
    [hq : q.asIdeal.LiesOver Q.asIdeal] :
    Algebra (Q.adicCompletion K) (q.adicCompletion L) :=
  (Commons.RingTheory.Henselian.adicCompletionMap Q q hq).toAlgebra

/-- The cardinality of the residue field `k_Q` of the local field `K_Q`.  For an unramified
extension `L_q / K_Q` the Frobenius acts on the residue field by `x ↦ x ^ residueCard Q`. -/
noncomputable def residueCard (K : Type*) [Field K] [NumberField K]
    (Q : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) : ℕ :=
  Nat.card (IsLocalRing.ResidueField (Q.adicCompletionIntegers K))

section Frobenius

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

/-- **The canonical Frobenius condition** for a `K_Q`-automorphism `σ` of `L_q`: `σ` acts on the
ring of integers of `L_q` as the `q`-th power map modulo the maximal ideal, where
`q = residueCard Q = #k_Q`.

For an *unramified* extension this determines `σ` uniquely (the residue action is faithful), and
existence is `NK.LocalReciprocity.exists_isFrobeniusLocal`; this is the Frobenius element of the
unramified local extension `L_q / K_Q`, normalised so that the value on the residue field is the
`#k_Q`-power map.  Making this element canonical is what turns the *weak* ("there exists a
surjection with kernel the norm group") form of local reciprocity available in the commons into
the canonical Artin map needed for Neukirch–Uchida. -/
def IsFrobeniusLocal (Q : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (q : IsDedekindDomain.HeightOneSpectrum (𝓞 L)) [hq : q.asIdeal.LiesOver Q.asIdeal] :
    (q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L) → Prop :=
  fun σ => ∀ x : q.adicCompletionIntegers L,
    Valued.v (σ (x : q.adicCompletion L) - (x : q.adicCompletion L) ^ residueCard K Q) < 1

variable (Q : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (q : IsDedekindDomain.HeightOneSpectrum (𝓞 L)) [hq : q.asIdeal.LiesOver Q.asIdeal]

theorem isFrobeniusLocal_iff (σ : q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L) :
    IsFrobeniusLocal Q q σ ↔ ∀ x : q.adicCompletionIntegers L,
      Valued.v (σ (x : q.adicCompletion L) - (x : q.adicCompletion L) ^ residueCard K Q) < 1 :=
  Iff.rfl

end Frobenius

end NK.LocalReciprocity
