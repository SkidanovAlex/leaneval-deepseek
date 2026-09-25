import Submission.NK.LocalReciprocity.Prelude
import Submission.NK.LocalReciprocity.LocalSetup
import Submission.NK.LocalReciprocity.exists_isFrobeniusLocal
import Submission.NK.LocalReciprocity.isFrobeniusLocal_unique
import Submission.NK.LocalReciprocity.orderOf_eq_inertiaDeg_of_isFrobeniusLocal

/-!
# The canonical Frobenius of an unramified local extension

Let `L / K` be a finite Galois extension of number fields, `Q` a finite place of `K` and `q` a
place of `L` above `Q` with ramification index one.  The local extension `L_q / K_Q` is then
unramified, hence cyclic, and has a canonical generator: the *Frobenius*, characterised by acting
as the `#k_Q`-th power map on the residue field.

This file *defines* that generator (`frobeniusLocal`) and records its characteristic property and
its uniqueness.  Existence and uniqueness are the lemmas `exists_isFrobeniusLocal` and
`isFrobeniusLocal_unique`; the definition here is the `Classical.choose` of existence, and
`eq_frobeniusLocal` shows that in a proof one may work with an arbitrary `σ` satisfying the
Frobenius congruence and be sure it *is* the canonical Frobenius.  This is what makes the Artin
map of an unramified local extension canonical (see `NK.LocalReciprocity.artinUnramified`).
-/

open scoped NumberField
open IsDedekindDomain.HeightOneSpectrum

namespace NK.LocalReciprocity

noncomputable section

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

/-- **The canonical Frobenius** of the unramified local extension `L_q / K_Q`. -/
noncomputable def frobeniusLocal (Q : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (q : IsDedekindDomain.HeightOneSpectrum (𝓞 L)) [hq : q.asIdeal.LiesOver Q.asIdeal]
    (hunr : q.asIdeal.ramificationIdx (𝓞 K) = 1) :
    q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L :=
  Classical.choose (exists_isFrobeniusLocal Q q hunr)

/-- The characteristic property of the canonical Frobenius: it acts as the `#k_Q`-th power map on
the ring of integers of `L_q` modulo the maximal ideal. -/
theorem frobeniusLocal_spec (Q : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (q : IsDedekindDomain.HeightOneSpectrum (𝓞 L)) [hq : q.asIdeal.LiesOver Q.asIdeal]
    (hunr : q.asIdeal.ramificationIdx (𝓞 K) = 1) :
    IsFrobeniusLocal Q q (frobeniusLocal Q q hunr) :=
  Classical.choose_spec (exists_isFrobeniusLocal Q q hunr)

/-- **The canonical characterisation of the Frobenius**: an automorphism of `L_q` over `K_Q` is
the Frobenius if and only if it acts as the `#k_Q`-th power map modulo the maximal ideal. -/
theorem eq_frobeniusLocal_iff (Q : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (q : IsDedekindDomain.HeightOneSpectrum (𝓞 L)) [hq : q.asIdeal.LiesOver Q.asIdeal]
    (hunr : q.asIdeal.ramificationIdx (𝓞 K) = 1)
    (σ : q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L) :
    IsFrobeniusLocal Q q σ ↔ σ = frobeniusLocal Q q hunr :=
  ⟨fun h => isFrobeniusLocal_unique Q q hunr h (frobeniusLocal_spec Q q hunr),
    fun h => h ▸ frobeniusLocal_spec Q q hunr⟩

/-- The canonical Frobenius lies in the `zpowers` of no proper subgroup: it generates
`Gal(L_q / K_Q)` for an unramified extension. -/
theorem frobeniusLocal_generates (Q : IsDedekindDomain.HeightOneSpectrum (𝓞 K))
    (q : IsDedekindDomain.HeightOneSpectrum (𝓞 L)) [hq : q.asIdeal.LiesOver Q.asIdeal]
    (hunr : q.asIdeal.ramificationIdx (𝓞 K) = 1) :
    Subgroup.zpowers (frobeniusLocal Q q hunr) = ⊤ := by
  haveI hfin : FiniteDimensional (Q.adicCompletion K) (q.adicCompletion L) :=
    Commons.NumberTheory.NumberField.Completion.module_finite_adicCompletion Q q hq
  haveI : Finite (q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L) := inferInstance
  rw [← Subgroup.card_eq_iff_eq_top, Nat.card_zpowers,
    orderOf_eq_inertiaDeg_of_isFrobeniusLocal Q q hunr _ (frobeniusLocal_spec Q q hunr),
    Commons.NumberTheory.NumberField.Completion.natCard_algEquiv_adicCompletion_eq_inertiaDeg_of_ramificationIdx_eq_one
      Q q hq hunr]

end

end NK.LocalReciprocity
