import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Submission.Work.HilbertSymbolGeneral.canonicalAPI
import Submission.Work.LocalFields.finrank_completion_eq_card_decompositionGroup
import Submission.Work.SSGRoute.ZDataTwo.Mu2InvolutionForm
import Submission.Work.SSGRoute.ZDataTwo.exists_level_localNormSubgroup_eq
import Submission.Work.SSGRoute.ZDataTwo.mem_fixingSubgroup_adjoin_simple
import Submission.Work.SSGRoute.exists_kummerChar_of_additive_locConst
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The norm group of a nontrivial quadratic level of `F^{ab}` is not everything

Let `F = Q.adicCompletion k` be the completion of a number field at a finite prime, `b ∈ F` a
non-square and `y` a square root of `b` in a separable closure.  Then the level `F(√b)` of
`F^{ab}` is a genuine quadratic extension, so its norm group is a *proper* subgroup of `Fˣ`.

The mathematics is the norm index theorem at the completion
(`NK.LocalReciprocityLubinTate.NormIndex.normIndex_adicCompletion`): the norm group of a level has
index `[L : F]`, and `[F(√b) : F] = 2` by
`Work.HilbertSymbolGeneral.quadLevel_finrank_eq_two_of_notMem`.  Equivalently: the norm map on units
of a quadratic extension of a `p`-adic field is not surjective — the statement that the local Tate
pairing at a finite place is non-degenerate.  (The restriction to completions is essential: for
*finite* fields the norm map on units of a quadratic extension *is* surjective, so the general
field-theoretic statement is false.)
-/

namespace Work.SSGRoute.ZDataTwo

theorem normGroup_quadLevel_adicCompletion_ne_top {k : Type} [Field k] [NumberField k]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k))
    (b : Q.adicCompletion k)
    (y : SeparableClosure (Q.adicCompletion k))
    (hy : y * y = algebraMap (Q.adicCompletion k) (SeparableClosure (Q.adicCompletion k)) b)
    (hyn : y ∉ Set.range (algebraMap (Q.adicCompletion k) (SeparableClosure (Q.adicCompletion k)))) :
    NK.LocalReciprocity.normGroup (Q.adicCompletion k)
      ↥(NK.NUV2.LC.quadLevel y b hy) ≠ ⊤ := by
  intro htop
  haveI hfd : FiniteDimensional (Q.adicCompletion k) ↥(NK.NUV2.LC.quadLevel y b hy) :=
    NK.NUV2.LC.quadLevel_finiteDimensional y b hy
  haveI hnor : Normal (Q.adicCompletion k) ↥(NK.NUV2.LC.quadLevel y b hy) :=
    NK.NUV2.LC.quadLevel_normal y b hy
  have hfr : Module.finrank (Q.adicCompletion k) ↥(NK.NUV2.LC.quadLevel y b hy) = 2 :=
    Work.HilbertSymbolGeneral.quadLevel_finrank_eq_two_of_notMem y b hy hyn
  have hidx : (NK.LocalReciprocity.normGroup (Q.adicCompletion k)
      ↥(NK.NUV2.LC.quadLevel y b hy)).index
      = Module.finrank (Q.adicCompletion k) ↥(NK.NUV2.LC.quadLevel y b hy) :=
    (NK.LocalReciprocityLubinTate.NormIndex.normIndex_adicCompletion (K := k) Q)
      (NK.NUV2.LC.quadLevel y b hy)
  rw [htop, Subgroup.index_top] at hidx
  omega

end Work.SSGRoute.ZDataTwo
