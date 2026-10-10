import Mathlib.RepresentationTheory.Rep.Res
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.RamificationInertia.Ramification
import Mathlib.NumberTheory.NumberField.InfinitePlace.Basic
import Submission.Work.SSGRoute.ValuationSES.C1
import Submission.Work.SSGRoute.e7comega_defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open Additive

namespace Work.SSGRoute.ValuationSES.C4.gen

/-- **C4 (general ramification).** For a tower `k ⊆ K ⊆ L` of number fields (`K/k`, `L/k` finite
Galois), a finite place `q'` of `L` lying over the finite place `Q` of `K` with ramification index
`e = e(q'|Q)`, the local units map `localUnitsMap` of the level pair `(Q, q')` scales the additive
valuation `localUnitsValHom` by `e`:

`valHom_{q'} (localUnitsMap (u)) = e • valHom_Q (u)`.

The mathematical content is that the local algebra map `K_Q → L_{q'}` of adic completions scales
valuations by the ramification index `e = e(q'|Q)`
(`Commons.NumberTheory.NumberField.Completion.val_adicCompletionMap_eq_pow`), together with the
computation rule `localUnitsMap_spec` and multiplicativity of `WithZero.log`
(`WithZero.log_pow`). -/
theorem valHom_localUnitsMap (k K L : Type) [Field k] [NumberField k]
    [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    [Field L] [NumberField L] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [FiniteDimensional k L] [IsGalois k L]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (q' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hq' : NK.GlobalCFT.Place.LiesOver (NK.GlobalCFT.Place.ofFinite q')
      (NK.GlobalCFT.Place.ofFinite Q))
    (u : (NK.GlobalCFT.Place.localField K (NK.GlobalCFT.Place.ofFinite Q))ˣ) :
    (NK.HassePrinciple.localUnitsValHom (K := k) (L := L) q').hom
        ((Work.SSGRoute.localUnitsMap k K L (NK.GlobalCFT.Place.ofFinite Q)
          (NK.GlobalCFT.Place.ofFinite q') hq').hom (Additive.ofMul u))
      = (q'.asIdeal.ramificationIdx (NumberField.RingOfIntegers K)) •
        ((NK.HassePrinciple.localUnitsValHom (K := k) (L := K) Q).hom (Additive.ofMul u)) := by
  -- The prime `q'` of `𝓞 L` lies over the prime `Q` of `𝓞 K`.
  have hL : q'.asIdeal.LiesOver Q.asIdeal := by
    rcases hq' with ⟨w', v', hw, -, -⟩ | ⟨q, Q', h1, h2, hLies⟩
    · exact absurd hw (by simp)
    · rw [NK.GlobalCFT.Place.ofFinite_inj] at h1 h2
      subst h1; subst h2
      exact hLies
  -- Computation rule of `localUnitsMap`: it is the completion of the inclusion on units.
  rw [Work.SSGRoute.localUnitsMap_spec k K L _ _ hq' u]
  show NK.HassePrinciple.valUnitsAddHom L q'
      (Additive.ofMul ((NK.GlobalCFT.Place.ofFinite q').localAlgebraMapUnits
        (NK.GlobalCFT.Place.ofFinite Q) hq' u))
    = (q'.asIdeal.ramificationIdx (NumberField.RingOfIntegers K)) •
      (NK.HassePrinciple.valUnitsAddHom K Q (Additive.ofMul u))
  -- Rewrite both valuations as `adicVal` of the underlying units.
  rw [NK.HassePrinciple.valUnitsAddHom_apply, NK.HassePrinciple.valUnitsAddHom_apply]
  -- The local units map is `Units.map` of the map of adic completions.
  have hφ : ((NK.GlobalCFT.Place.ofFinite q').localAlgebraMapUnits
        (NK.GlobalCFT.Place.ofFinite Q) hq') u
      = Units.map (Commons.RingTheory.Henselian.adicCompletionMap Q q' hL).toMonoidHom u := by
    rw [NK.GlobalCFT.Inclusion.globalCFT_localAlgebraMapUnits_ofFinite (q := q') (Q := Q) hq']
  -- The valuation of the image under the completion map is the `e`-th power of the valuation.
  have hV : Valued.v (((((NK.GlobalCFT.Place.ofFinite q').localAlgebraMapUnits
        (NK.GlobalCFT.Place.ofFinite Q) hq') u :
        (NK.GlobalCFT.Place.localField L (NK.GlobalCFT.Place.ofFinite q'))ˣ) :
        NK.GlobalCFT.Place.localField L (NK.GlobalCFT.Place.ofFinite q')))
      = (Valued.v ((u : (NK.GlobalCFT.Place.localField K (NK.GlobalCFT.Place.ofFinite Q))ˣ) :
        NK.GlobalCFT.Place.localField K (NK.GlobalCFT.Place.ofFinite Q)))
        ^ (q'.asIdeal.ramificationIdx (NumberField.RingOfIntegers K)) := by
    rw [hφ, Units.coe_map]
    exact Commons.NumberTheory.NumberField.Completion.val_adicCompletionMap_eq_pow Q q' hL _
  -- `WithZero.log` of the `e`-th power is `e` times the logarithm.
  refine congrArg ULift.up ?_
  show WithZero.log (Valued.v ((((NK.GlobalCFT.Place.ofFinite q').localAlgebraMapUnits
        (NK.GlobalCFT.Place.ofFinite Q) hq') u :
        (NK.GlobalCFT.Place.localField L (NK.GlobalCFT.Place.ofFinite q'))ˣ) :
        NK.GlobalCFT.Place.localField L (NK.GlobalCFT.Place.ofFinite q')))
     = (q'.asIdeal.ramificationIdx (NumberField.RingOfIntegers K)) •
        (WithZero.log (Valued.v ((u : (NK.GlobalCFT.Place.localField K (NK.GlobalCFT.Place.ofFinite Q))ˣ) :
        NK.GlobalCFT.Place.localField K (NK.GlobalCFT.Place.ofFinite Q))))
  rw [hV, WithZero.log_pow]

end Work.SSGRoute.ValuationSES.C4.gen
