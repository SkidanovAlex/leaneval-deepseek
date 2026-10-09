import Mathlib
import Submission.Work.SSGRoute.e7comega_defs
import Submission.Work.SSGRoute.ValuationSES.C1
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Node `C4a` of the E7cΩ route: the valuation is insensitive to an unramified level step

Let `k ⊆ K ⊆ L` be a tower of number fields with `K/k`, `L/k` finite Galois, let `Q` be a finite
place of `K` and `q'` a finite place of `L` lying over `Q` with ramification index `e(q'|Q) = 1`.
Then the `D_{q'}`-equivariant local units map `K_Qˣ → L_{q'}ˣ` (`Work.SSGRoute.localUnitsMap`) of
the level pair `(Q, q')` commutes with the valuation `x ↦ adicVal`:

`valHom_{q'} (localUnitsMap (u)) = valHom_Q (u)`.

The mathematical content is that the local algebra map `K_Q → L_{q'}` of adic completions scales
valuations by the ramification index `e = e(q'|Q)`
(`Commons.NumberTheory.NumberField.Completion.val_adicCompletionMap_eq_pow`), which is `1` here;
together with the computation rule `localUnitsMap_spec` this gives the claim.

This is the valuation-level compatibility of `Work.SSGRoute.localUnitsMap` used (together with
`Work.SSGRoute.ValuationSES.C1`, the criterion "unramified iff killed by the valuation") to
transport unramified `Ext¹`-classes along an unramified extension of `Ω`-levels.
-/

open Additive

namespace Work.SSGRoute.ValuationSES.C4a

/-- **C4a.** For a tower `k ⊆ K ⊆ L` of number fields (`K/k`, `L/k` finite Galois) and a finite
place `q'` of `L` lying over the finite place `Q` of `K` with ramification index one, the local
units map `localUnitsMap` of the level pair `(Q, q')` commutes with the valuations
`localUnitsValHom`. -/
theorem valHom_localUnitsMap_of_ramificationIdx_eq_one (k K L : Type) [Field k] [NumberField k]
    [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    [Field L] [NumberField L] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [FiniteDimensional k L] [IsGalois k L]
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (q' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
    (hq' : NK.GlobalCFT.Place.LiesOver (NK.GlobalCFT.Place.ofFinite q')
      (NK.GlobalCFT.Place.ofFinite Q))
    (he : q'.asIdeal.ramificationIdx (NumberField.RingOfIntegers K) = 1)
    (u : (NK.GlobalCFT.Place.localField K (NK.GlobalCFT.Place.ofFinite Q))ˣ) :
    (NK.HassePrinciple.localUnitsValHom (K := k) (L := L) q').hom
        ((Work.SSGRoute.localUnitsMap k K L (NK.GlobalCFT.Place.ofFinite Q)
          (NK.GlobalCFT.Place.ofFinite q') hq').hom (Additive.ofMul u))
      = (NK.HassePrinciple.localUnitsValHom (K := k) (L := K) Q).hom (Additive.ofMul u) := by
  -- The prime `q'` of `𝓞 L` lies over the prime `Q` of `𝓞 K`.
  have hL : q'.asIdeal.LiesOver Q.asIdeal := by
    rcases hq' with ⟨w', v', hw, -, -⟩ | ⟨q, Q', h1, h2, hLies⟩
    · exact absurd hw (by simp)
    · rw [NK.GlobalCFT.Place.ofFinite_inj] at h1 h2
      subst h1; subst h2
      exact hLies
  -- The extension `L/K` is finite, so the adic-completion map is available.
  have hfin : FiniteDimensional K L := FiniteDimensional.right k K L
  have hlies : q'.asIdeal.LiesOver Q.asIdeal := hL
  -- Computation rule of `localUnitsMap`: it is the completion of the inclusion on units.
  rw [Work.SSGRoute.localUnitsMap_spec k K L _ _ hq' u]
  show NK.HassePrinciple.valUnitsAddHom L q'
      (Additive.ofMul ((NK.GlobalCFT.Place.ofFinite q').localAlgebraMapUnits
        (NK.GlobalCFT.Place.ofFinite Q) hq' u))
    = NK.HassePrinciple.valUnitsAddHom K Q (Additive.ofMul u)
  -- Rewrite both valuations as `adicVal` of the underlying units.
  rw [NK.HassePrinciple.valUnitsAddHom_apply, NK.HassePrinciple.valUnitsAddHom_apply]
  -- The local units map is `Units.map` of the map of adic completions.
  have hφ : ((NK.GlobalCFT.Place.ofFinite q').localAlgebraMapUnits
        (NK.GlobalCFT.Place.ofFinite Q) hq') u
      = Units.map (Commons.RingTheory.Henselian.adicCompletionMap Q q' hL).toMonoidHom u := by
    rw [NK.GlobalCFT.Inclusion.globalCFT_localAlgebraMapUnits_ofFinite (q := q') (Q := Q) hq']
  -- The valuation of the image under the completion map is the `e`-th power of the valuation,
  -- and `e = 1`.
  have hV : Valued.v (((((NK.GlobalCFT.Place.ofFinite q').localAlgebraMapUnits
        (NK.GlobalCFT.Place.ofFinite Q) hq') u :
        (NK.GlobalCFT.Place.localField L (NK.GlobalCFT.Place.ofFinite q'))ˣ) :
        NK.GlobalCFT.Place.localField L (NK.GlobalCFT.Place.ofFinite q')))
      = Valued.v ((u : (NK.GlobalCFT.Place.localField K (NK.GlobalCFT.Place.ofFinite Q))ˣ) :
        NK.GlobalCFT.Place.localField K (NK.GlobalCFT.Place.ofFinite Q)) := by
    rw [hφ, Units.coe_map]
    refine (Commons.NumberTheory.NumberField.Completion.val_adicCompletionMap_eq_pow Q q' hL
      ((u : (NK.GlobalCFT.Place.localField K (NK.GlobalCFT.Place.ofFinite Q))ˣ) :
        NK.GlobalCFT.Place.localField K (NK.GlobalCFT.Place.ofFinite Q))).trans ?_
    rw [he, pow_one]
  refine congrArg ULift.up ?_
  show WithZero.log (Valued.v ((((NK.GlobalCFT.Place.ofFinite q').localAlgebraMapUnits
        (NK.GlobalCFT.Place.ofFinite Q) hq') u :
        (NK.GlobalCFT.Place.localField L (NK.GlobalCFT.Place.ofFinite q'))ˣ) :
        NK.GlobalCFT.Place.localField L (NK.GlobalCFT.Place.ofFinite q')))
      = WithZero.log (Valued.v ((u : (NK.GlobalCFT.Place.localField K
        (NK.GlobalCFT.Place.ofFinite Q))ˣ) :
        NK.GlobalCFT.Place.localField K (NK.GlobalCFT.Place.ofFinite Q)))
  exact congrArg WithZero.log hV

end Work.SSGRoute.ValuationSES.C4a
