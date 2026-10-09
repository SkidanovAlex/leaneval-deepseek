import Mathlib
import Submission.Work.SSGRoute.Sha2Lib.detectorInterface
import Submission.Work.SSGRoute.Sha2Lib.detector_of_submodule
import Submission.Work.SSGRoute.Sha2Lib.detectsAt_of_hom
import Submission.Work.SSGRoute.Sha2Lib.ext_comp_mk0_ne_zero_of_section
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.Sha2Lib

open CategoryTheory SSGRoute.PTExt

/-!
# The induced reduction of the unramified detector (node `C6`)

`isUnramifiedDetector_of_induced` says that the detector `IsUnramifiedDetector` for the induced
module `Ind_{D_w}^{G}(res_{D_w} M)` implies the detector for `M` itself.  Consequently a prover of
node `C6` may assume that the coefficient module is induced from the decomposition group
`D_w ≤ Gal(K/k)`, which is the shape in which Shapiro's lemma applies.

The mathematical content is the following.  Let `D = D_w ≤ G = Gal(K/k)`, `A = res_D M` and
`N = Ind_D^G A = detectorInd k K w M`.  The counit of the adjunction `Ind_D^G ⊣ res_D`,

  `ε : N = Ind_D^G (res_D M) ⟶ M`   (`(Rep.indResAdjunction Coeff D.subtype).counit.app M`),

is *split surjective as a `D`-module*: the unit `η : res_D M ⟶ res_D N` of the adjunction is a
section of `resMap D.subtype ε`, by the right triangle identity `Adjunction.right_triangle_components`
(`η ≫ resMap D.subtype ε = 𝟙 (res_D M)`).  Hence for `φ ∈ Ext¹_D(res_D M, ℤ)` the pushforward

  `φN = (mk₀ (resMap D.subtype ε)).comp φ : Ext¹_D(res_D N, ℤ)`

is nonzero whenever `φ` is (`ext_comp_mk0_ne_zero_of_section`, the contravariant functoriality of
`Ext` in the first variable).  The detector hypothesis for `N`, applied to `φN`, produces a finite
Galois level `L ⊇ K`, a place `q' | q` with `e(q'|q)` prime to `p`, and a class
`hN ∈ H¹(Gal(L/k), res N)`, unramified at `q'`, whose level pairing with `φN` is nonzero.  Pushing
`hN` forward along `res(ε)` yields a class `h ∈ H¹(Gal(L/k), res M)` which is again unramified at
`q'` (`extHRestrict_pushforward`) and which pairs with `φ` to the *same* value, by naturality of the
level pairing in the coefficient module (`levelPair_pushforward_coeff`).  That final bookkeeping
step is the lemma `detectsAt_of_hom`.
-/

theorem isUnramifiedDetector_of_induced (p : ℕ) [Fact p.Prime] (k K : Type) [Field k] [NumberField k]
    [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω]
    (w : NK.GlobalCFT.Place K)
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (hwq : w = NK.GlobalCFT.Place.ofFinite q)
    (M : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K))
    (h : Work.SSGRoute.Sha2Lib.IsUnramifiedDetector p k K Ω w q hwq
      (Work.SSGRoute.Sha2Lib.detectorInd k K w M)) :
    Work.SSGRoute.Sha2Lib.IsUnramifiedDetector p k K Ω w q hwq M := by
  intro φ hφ
  -- `D_w = decompK w ≤ Gal(K/k)`, and the adjunction `Ind_{D_w}^{G} ⊣ res_{D_w}`.
  let D : Subgroup (K ≃ₐ[k] K) := SSGRoute.PTExt.decompK (k := k) (K := K) w
  let adj : Rep.indFunctor SSGRoute.PTExt.Coeff D.subtype ⊣ Rep.resFunctor D.subtype :=
    Rep.indResAdjunction SSGRoute.PTExt.Coeff D.subtype
  -- The counit `ε : Ind_{D_w}^{G} (res_{D_w} M) ⟶ M`: a map out of `detectorInd k K w M`.
  let ε : detectorInd k K w M ⟶ M := adj.counit.app M
  -- The unit `η : res_{D_w} M ⟶ res_{D_w} (Ind_{D_w}^{G} (res_{D_w} M))` is a section of
  -- `res_{D_w} ε`, by the right triangle identity of the adjunction.
  let η : Rep.res D.subtype M ⟶ Rep.res D.subtype (detectorInd k K w M) :=
    adj.unit.app (Rep.res D.subtype M)
  have hs : η ≫ Rep.resMap D.subtype ε = 𝟙 (Rep.res D.subtype M) :=
    Adjunction.right_triangle_components adj M
  -- Pushing `φ` forward along `res_{D_w} ε` gives a nonzero class on the induced module; the
  -- detector for the induced module then detects `φ` itself, since `ε` is a split epimorphism
  -- of `D_w`-modules.
  refine detectsAt_of_hom p k K Ω w q hwq (detectorInd k K w M) M h ε φ ?_
  exact ext_comp_mk0_ne_zero_of_section (Rep.resMap D.subtype ε) η hs hφ

end Work.SSGRoute.Sha2Lib
