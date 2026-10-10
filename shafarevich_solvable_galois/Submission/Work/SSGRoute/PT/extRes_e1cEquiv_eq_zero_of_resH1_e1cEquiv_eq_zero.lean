import Mathlib.FieldTheory.KrullTopology
import Mathlib.RingTheory.Henselian
import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RepresentationTheory.Rep.Res
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Valuation.ValuationSubring
import Mathlib.RingTheory.DedekindDomain.Ideal.Lemmas
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Submission.Work.SSGRoute.E1aClean.finLocalCriterion
import Submission.Work.SSGRoute.ExtChain.homCoindFreeT_H1_subgroup
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.PT

theorem extRes_e1cEquiv_eq_zero_of_resH1_e1cEquiv_eq_zero
    (k Ω : Type) [Field k] [NumberField k] [Field Ω] [Algebra k Ω] [IsAlgClosure k Ω]
    (K : IntermediateField k Ω) [FiniteDimensional k K] [IsGalois k K] [NumberField K]
    (N : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)) [Finite N.V]
    [hfin : Module.Finite ℤ ↑(CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover N)).V]
    (A : ValuationSubring Ω) (hA : SSGRoute.IsFinPlace k A)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hAq : ∀ x : NumberField.RingOfIntegers K,
      x ∈ q.asIdeal ↔ A.valuation (((x : K) : Ω)) < 1)
    (z : CategoryTheory.Abelian.Ext.{0}
        (CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover N))
        (SSGRoute.PTExt.unitsK k K) 1) :
    Work.SSGRoute.PT.H2Fin.resH1 (SSGRoute.decomp k A)
        (Work.SSGRoute.homCoind k Ω K
          (CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover N)))
        (Work.SSGRoute.ExtChain.e1cEquiv
          (CategoryTheory.Limits.kernel (Work.SSGRoute.freeCover N)) z) = 0 →
      (SSGRoute.PTExt.extRes
          (SSGRoute.PTExt.decompK (k := k)
            (NK.GlobalCFT.Place.ofFinite q)).subtype z).comp
        (CategoryTheory.Abelian.Ext.mk₀
          (NK.HassePrinciple.unitsToLocalUnits k K (NK.GlobalCFT.Place.ofFinite q)))
        (add_zero 1) = 0 :=
  Work.SSGRoute.E1aClean.finLocalCriterion k Ω K N A hA q hAq z

end Work.SSGRoute.PT
