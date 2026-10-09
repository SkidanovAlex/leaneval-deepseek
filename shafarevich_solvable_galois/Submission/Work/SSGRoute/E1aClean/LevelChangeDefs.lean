import Mathlib
import Submission.Work.SSGRoute.E1aClean.BaseChangeSquare
import Submission.Work.SSGRoute.E1aClean.BaseChangeExtTransport
import Submission.Work.SSGRoute.PT.e1cDelta_beta_relation_gen
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-! # Shared definitions for the level-change square of the `E1c` dictionary

This module collects the definitions that the level-change square
(`Work.SSGRoute.E1aClean.e1cMap_levelChangeSquareExplicit`) and its auxiliary lemmas share, so
that they can be stated in a *short* form (the elaborator times out when the very large
`PhiE`/`freeCover` terms are written out) and so that further lemmas about them can live in
modules that do not import the main theorem.

The objects are:

* `e1cLC_R1k R`, `e1cLC_R1L L R` — the canonical syzygies of `R` at the two levels;
* `e1cLC_Pk R`, `e1cLC_PL L R` — the coefficients `Hom_ℤ(R₁, Ωˣ)` at the two levels;
* `e1cLC_coverCompat L R` — the (canonically chosen) comparison of the two canonical covers along
  `galKIncl L`, together with its specification (`e1cLC_coverCompat_τ₂`, `_τ₃`, `_gen`);
* `e1cLC_π L R`, `e1cLC_κ L R` — the dualised comparison maps on the coefficient and on the middle
  term of the dualised canonical resolution. -/

set_option maxHeartbeats 4000000
set_option linter.unusedSectionVars false

namespace Work.SSGRoute.E1aClean

open CategoryTheory SSGRoute.PTExt

noncomputable section

variable {k : Type} [Field k] {Ω : Type} [Field Ω] [Algebra k Ω]
  {K : IntermediateField k Ω}

/-- The level-`k` syzygy of `R`: the kernel of the canonical cover of `R` over `Gal(K/k)`. -/
abbrev e1cLC_R1k (R : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)) :
    Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K) :=
  Work.SSGRoute.ExtChain.E1cGeneric.E1cR1 R

/-- The level-`L` syzygy: the kernel of the canonical cover of `Rep.res (galKIncl L) R` over
`Gal(K/L)`. -/
abbrev e1cLC_R1L (L : IntermediateField k K) (R : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)) :
    Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[↥L] K) :=
  Work.SSGRoute.ExtChain.E1cGeneric.E1cR1 (k := ↥L) (Ω := Ω) (K := Kover L)
    (Rep.res (galKIncl L) R : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[↥L] K))

/-- The coefficient `Hom_ℤ(R₁, Ωˣ)` at level `k`. -/
abbrev e1cLC_Pk (R : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)) : Type :=
  Work.SSGRoute.homCoind k Ω K (e1cLC_R1k R)

/-- The coefficient `Hom_ℤ(R₁', Ωˣ)` at level `L`. -/
abbrev e1cLC_PL (L : IntermediateField k K) (R : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)) :
    Type :=
  Work.SSGRoute.homCoind ↥L Ω (Kover L) (e1cLC_R1L L R)

variable [FiniteDimensional k K] [IsGalois k K]

/-- **The comparison of the two canonical covers along `galKIncl L`**, chosen canonically once and
for all (`PT.PhiEgen_res_compat`) so that all the lemmas about it refer to the *same* comparison. -/
noncomputable def e1cLC_coverCompat (L : IntermediateField k K)
    [FiniteDimensional ↥L (Kover L)] [IsGalois ↥L (Kover L)] [NumberField (Kover L)]
    (R : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)) :
    CategoryTheory.ShortComplex.Hom (Work.SSGRoute.freeCoverSES
        (Rep.res (galKIncl L) R : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[↥L] K)))
      ((Work.SSGRoute.freeCoverSES R).map
        (Rep.resFunctor (k := SSGRoute.PTExt.Coeff) (galKIncl L))) :=
  Classical.choose (Work.SSGRoute.PT.PhiEgen_res_compat
    (galKIncl L) R (SSGRoute.PTExt.unitsK k K))

/-- The second component of the cover comparison is `freeCoverCompat`. -/
theorem e1cLC_coverCompat_τ₂ (L : IntermediateField k K)
    [FiniteDimensional ↥L (Kover L)] [IsGalois ↥L (Kover L)] [NumberField (Kover L)]
    (R : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)) :
    (e1cLC_coverCompat L R).τ₂ = Work.SSGRoute.PT.freeCoverCompat (galKIncl L) R :=
  (Classical.choose_spec (Work.SSGRoute.PT.PhiEgen_res_compat
    (galKIncl L) R (SSGRoute.PTExt.unitsK k K))).1

/-- The third component of the cover comparison is the identity. -/
theorem e1cLC_coverCompat_τ₃ (L : IntermediateField k K)
    [FiniteDimensional ↥L (Kover L)] [IsGalois ↥L (Kover L)] [NumberField (Kover L)]
    (R : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)) :
    (e1cLC_coverCompat L R).τ₃ = CategoryTheory.CategoryStruct.id
        (Rep.res (galKIncl L) R : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[↥L] K)) :=
  (Classical.choose_spec (Work.SSGRoute.PT.PhiEgen_res_compat
    (galKIncl L) R (SSGRoute.PTExt.unitsK k K))).2.1

/-- **The generator rule of the cover comparison**: the restriction of a `PhiE`-generator is the
`PhiEgen`-generator of the transported element. -/
theorem e1cLC_coverCompat_gen (L : IntermediateField k K)
    [FiniteDimensional ↥L (Kover L)] [IsGalois ↥L (Kover L)] [NumberField (Kover L)]
    (R : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K))
    (w : Abelian.Ext.{0} (e1cLC_R1k R) (SSGRoute.PTExt.unitsK k K) 0) :
    (Rep.resFunctor (k := SSGRoute.PTExt.Coeff) (galKIncl L)).mapExtAddHom
        R (SSGRoute.PTExt.unitsK k K) 1
        (Work.SSGRoute.ExtChain.E1cGeneric.PhiE (k := k) (Ω := Ω) (K := K) R w)
      = Work.SSGRoute.PT.PhiEgen (Rep.res (galKIncl L) R)
          (Rep.res (galKIncl L) (SSGRoute.PTExt.unitsK k K))
          (Abelian.Ext.comp (Abelian.Ext.mk₀ (e1cLC_coverCompat L R).τ₁)
            ((Rep.resFunctor (k := SSGRoute.PTExt.Coeff) (galKIncl L)).mapExtAddHom
              (e1cLC_R1k R) (SSGRoute.PTExt.unitsK k K) 0 w) (zero_add 0)) :=
  (Classical.choose_spec (Work.SSGRoute.PT.PhiEgen_res_compat
    (galKIncl L) R (SSGRoute.PTExt.unitsK k K))).2.2 w

/-- The dualised comparison on the coefficient: `Hom_ℤ(R₁,Ωˣ) → Hom_ℤ(R₁',Ωˣ)`. -/
abbrev e1cLC_π (L : IntermediateField k K)
    [FiniteDimensional ↥L (Kover L)] [IsGalois ↥L (Kover L)] [NumberField (Kover L)]
    (R : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)) : e1cLC_Pk R →+ e1cLC_PL L R :=
  Work.SSGRoute.precompAddHom
    (Rep.Hom.hom (e1cLC_coverCompat L R).τ₁).toAddMonoidHom

/-- The dualised comparison on the middle term of the dualised canonical resolution. -/
abbrev e1cLC_κ (L : IntermediateField k K) [CharZero k] [IsAlgClosure k Ω]
    [FiniteDimensional ↥L (Kover L)] [IsGalois ↥L (Kover L)] [NumberField (Kover L)]
    (R : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K)) :
    Work.SSGRoute.ExtChain.homCoindFreeT k Ω K R.V →+
      Work.SSGRoute.ExtChain.homCoindFreeT ↥L Ω (Kover L)
        (Rep.res (galKIncl L) R).V :=
  Work.SSGRoute.precompAddHom
    (Rep.Hom.hom (e1cLC_coverCompat L R).τ₂).toAddMonoidHom

end

end Work.SSGRoute.E1aClean
