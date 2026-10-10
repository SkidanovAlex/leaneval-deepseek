import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Submission.Commons.NumberTheory.NumberField.Completion.natCard_quotient_units_range_norm_eq_finrank_of_abelian_local
import Submission.NK.LocalReciprocity.LocalSetup
import Submission.NK.LocalReciprocity.NormGroup
import Submission.NeukirchUchida.Local.LocalGalois
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The index of the local norm group is the local degree

For a finite Galois extension `L / K` of number fields, a finite place `Q` of `K` and a place
`q` of `L` above `Q`, the local field `L_q = q.adicCompletion L` is a finite Galois extension of
`K_Q = Q.adicCompletion K` (`Submission.NeukirchUchida.Local.isGalois_adicCompletion`).  The
target of this file is the **norm index theorem** of local class field theory in the abelian
case: when the local Galois group `Gal(L_q / K_Q)` is abelian,

  `[K_Qˣ : N_{L_q/K_Q} L_qˣ] = [L_q : K_Q]`,

i.e. the norm group `N L_qˣ ≤ K_Qˣ` of units has index equal to the local degree.

The mathematical content is the local reciprocity law; it is available in the shared commons as
`Commons.NumberTheory.NumberField.Completion.natCard_quotient_units_range_norm_eq_finrank_of_abelian_local`,
which computes the cardinality of the quotient `K_Qˣ ⧸ N L_qˣ`.  (Local reciprocity identifies this
quotient with the local Galois group when the latter is abelian; a purely cohomological proof is
also given there, via the fundamental class `H²(Gal(L_q/K_Q), L_qˣ) = ℤ/[L_q:K_Q]`.)  What has to
be added here is only the bookkeeping: the two `Algebra` structures on `L_q` in play are the same
(instance `NK.LocalReciprocity.instAlgebraAdicCompletion`, definitionally
`RingHom.toAlgebra (adicCompletionMap Q q hq)`), and the index of a subgroup is the cardinality of
the quotient group.
-/

set_option linter.style.haveILetI false

namespace NK.LocalReciprocity

/-- **The local norm index theorem** (abelian case).

For `L / K` a finite Galois extension of number fields, `q | Q` a place of `L` above a place `Q`
of `K`, with `q.adicCompletion L` abelian over `Q.adicCompletion K`, the norm group of the units
has index `[q.adicCompletion L : Q.adicCompletion K]` in the units of the local field
`Q.adicCompletion K`. -/
theorem index_normGroup_eq_finrank {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    [hq : q.asIdeal.LiesOver Q.asIdeal]
    (hcomm : ∀ a b : q.adicCompletion L ≃ₐ[Q.adicCompletion K] q.adicCompletion L,
      a * b = b * a) :
    (NK.LocalReciprocity.normGroup (Q.adicCompletion K) (q.adicCompletion L)).index =
      Module.finrank (Q.adicCompletion K) (q.adicCompletion L) := by
  -- the local extension `L_q / K_Q` is finite and Galois
  haveI hfin : FiniteDimensional (Q.adicCompletion K) (q.adicCompletion L) :=
    Commons.NumberTheory.NumberField.Completion.module_finite_adicCompletion Q q hq
  haveI hgal : IsGalois (Q.adicCompletion K) (q.adicCompletion L) :=
    Submission.NeukirchUchida.Local.isGalois_adicCompletion Q q hq
  -- the index of a subgroup is the cardinality of the quotient group, and the norm group is by
  -- definition the range of the norm map on units
  rw [Subgroup.index_eq_card, normGroup_eq_range]
  -- the abelian local norm index theorem of the shared commons
  exact Commons.NumberTheory.NumberField.Completion.natCard_quotient_units_range_norm_eq_finrank_of_abelian_local
    Q hcomm

end NK.LocalReciprocity
