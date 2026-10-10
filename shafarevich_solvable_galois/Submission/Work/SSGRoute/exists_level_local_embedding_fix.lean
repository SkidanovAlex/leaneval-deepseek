import Mathlib.RingTheory.Henselian
import Mathlib.Algebra.Algebra.IsSimpleRing
import Mathlib.Algebra.Lie.OfAssociative
import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Submission.NK.CFTLib.IdeleHasse.Crux.localNormRep
import Submission.NK.GlobalCFT.Inclusion.globalCFT_localFixed_all
import Submission.NK.GlobalCFTdeep.NormIndex.localNormAt

namespace Work.SSGRoute

open IsDedekindDomain.HeightOneSpectrum
open scoped NumberField

noncomputable section

set_option linter.style.haveILetI false

set_option maxHeartbeats 4000000

/-- **Realisation of a finite Galois local extension as a global level containing a prescribed
number field (standalone `_fix` copy).**

Let `k` be a number field, `K/K` finite Galois, `q` a non-archimedean place of `K` over the
non-archimedean place `Q` of `k`, and `F` a finite Galois extension of `k_Q = Q.adicCompletion k`.
Then there is a number field `L` with `k ⊆ K ⊆ L`, `L/k` finite Galois, and a place `q'` of `L` over
`q` together with a `k_Q`-algebra embedding of `F` into `L_{q'}`.

Route: `Commons.NumberTheory.NumberField.Completion.exists_galois_realization` (Krasner) applied to
`F` over `k` at `Q` yields `L₀/k` finite Galois and a place `q₀ | Q` with `F ≃ₐ[k_Q] (L₀)_{q₀}`.
View `K` and `L₀` as intermediate fields of `Ω = AlgebraicClosure k` (via `IsAlgClosed.lift`) and
take `L := K' ⊔ L₀'`.  Pick any place `q'` of `L` over `q` (`NK.GlobalCFTdeep.NormIndex.exists_place_liesOver`),
let `P := q'|_{L₀'}`; then `(L₀)_{P} ↪ L_{q'}` by `Commons.RingTheory.Henselian.adicCompletionMap`
(injective, `adicCompletionMap_injective`), and `(L₀)_{P} ≅ (L₀)_{q₀} ≅ F` because `L₀/k` is Galois
so `Gal(L₀/k)` is transitive on the places over `Q` (`globalCFT_exists_smul_eq_of_liesOver` together
with `Place.localRingEquiv`). -/
theorem exists_level_local_embedding_fix
    (k K : Type) [Field k] [NumberField k] [Field K] [NumberField K]
    [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K))
    (Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers k))
    (hQ : q.asIdeal.LiesOver Q.asIdeal)
    (F : Type) [Field F] [Algebra (Q.adicCompletion k) F]
    [FiniteDimensional (Q.adicCompletion k) F] [IsGalois (Q.adicCompletion k) F] :
    ∃ (L : Type) (_ : Field L) (_ : NumberField L) (_ : Algebra k L) (_ : Algebra K L)
      (_ : IsScalarTower k K L) (_ : FiniteDimensional k L) (_ : IsGalois k L)
      (q' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers L))
      (hq' : q'.asIdeal.LiesOver q.asIdeal)
      (hqQ' : q'.asIdeal.LiesOver Q.asIdeal),
      (letI : Algebra (Q.adicCompletion k) (q'.adicCompletion L) :=
         RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q' hqQ')
       Nonempty (F →ₐ[Q.adicCompletion k] q'.adicCompletion L)) := by
  classical
  -- ## Step 1: realise the local Galois extension `F / k_Q` over `k` at `Q`.
  obtain ⟨L₀, hL₀f, hL₀nf, hL₀a, q₀, hq₀, hgal₀, hne⟩ :=
    Commons.NumberTheory.NumberField.Completion.exists_galois_realization (K := k) Q (E := F)
  letI : Algebra k L₀ := hL₀a
  haveI : IsGalois k L₀ := hgal₀
  haveI hfdL₀k : FiniteDimensional k L₀ := Module.Finite.right ℚ k L₀
  letI : Algebra (Q.adicCompletion k) (q₀.adicCompletion L₀) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q₀ hq₀)
  obtain ⟨e⟩ := hne
  -- ## Step 2: put `K` and `L₀` inside `Ω = AlgebraicClosure k` and form the compositum.
  let Ω := AlgebraicClosure k
  haveI hAlgAlg : Algebra.IsAlgebraic k K := Algebra.IsAlgebraic.of_finite k K
  let ιK : K →ₐ[k] Ω := IsAlgClosed.lift
  let ιL : L₀ →ₐ[k] Ω := IsAlgClosed.lift
  let K' : IntermediateField k Ω := ιK.fieldRange
  let L₀' : IntermediateField k Ω := ιL.fieldRange
  let M : IntermediateField k Ω := K' ⊔ L₀'
  haveI hfdK' : FiniteDimensional k ↥K' :=
    LinearEquiv.finiteDimensional (AlgHom.equivFieldRange ιK).toLinearEquiv
  haveI hfdL₀' : FiniteDimensional k ↥L₀' :=
    LinearEquiv.finiteDimensional (AlgHom.equivFieldRange ιL).toLinearEquiv
  haveI hgalK' : IsGalois k ↥K' := IsGalois.of_algEquiv (AlgHom.equivFieldRange ιK)
  haveI hgalL₀' : IsGalois k ↥L₀' := IsGalois.of_algEquiv (AlgHom.equivFieldRange ιL)
  haveI hsepK' : Algebra.IsSeparable k ↥K' :=
    (isGalois_iff.mp (inferInstance : IsGalois k ↥K')).1
  haveI hnormK' : Normal k ↥K' :=
    (isGalois_iff.mp (inferInstance : IsGalois k ↥K')).2
  haveI hsepL₀' : Algebra.IsSeparable k ↥L₀' :=
    (isGalois_iff.mp (inferInstance : IsGalois k ↥L₀')).1
  haveI hnormL₀' : Normal k ↥L₀' :=
    (isGalois_iff.mp (inferInstance : IsGalois k ↥L₀')).2
  haveI hsepM : Algebra.IsSeparable k ↥M := IntermediateField.isSeparable_sup k Ω K' L₀'
  haveI hnormM : Normal k ↥M := IntermediateField.normal_sup k Ω K' L₀'
  haveI hfdM : FiniteDimensional k ↥M := IntermediateField.finiteDimensional_sup K' L₀'
  haveI hgalM : IsGalois k ↥M := isGalois_iff.mpr ⟨hsepM, hnormM⟩
  haveI hnfM : NumberField ↥M :=
    Commons.NumberTheory.NumberField.numberField_of_intermediateField (K := k) (K' := Ω) M
  -- ## Step 3: the `k`-algebra structures making `K ⊆ L` and `L₀ ⊆ L`.
  let fK : K →ₐ[k] ↥M := (IntermediateField.inclusion (show K' ≤ M from le_sup_left)).comp
    (AlgHom.equivFieldRange ιK)
  letI : Algebra K ↥M := RingHom.toAlgebra fK.toRingHom
  haveI hSTK : IsScalarTower k K ↥M := IsScalarTower.of_algebraMap_eq (fun a => by
    rw [RingHom.algebraMap_toAlgebra]
    exact (fK.commutes a).symm)
  haveI hfdKM : FiniteDimensional K ↥M := Module.Finite.right k K ↥M
  let fL : L₀ →ₐ[k] ↥M := (IntermediateField.inclusion (show L₀' ≤ M from le_sup_right)).comp
    (AlgHom.equivFieldRange ιL)
  letI : Algebra L₀ ↥M := RingHom.toAlgebra fL.toRingHom
  haveI hSTL : IsScalarTower k L₀ ↥M := IsScalarTower.of_algebraMap_eq (fun a => by
    rw [RingHom.algebraMap_toAlgebra]
    exact (fL.commutes a).symm)
  -- ## Step 4: a place `q'` of `L` over `q`, and the place `P` of `L₀` below it.
  obtain ⟨q', hq'⟩ := Commons.NumberTheory.NumberField.exists_heightOneSpectrum_liesOver
    (K := K) (L := ↥M) q
  have hqQ' : q'.asIdeal.LiesOver Q.asIdeal := Ideal.LiesOver.trans q'.asIdeal q.asIdeal Q.asIdeal
  let P : IsDedekindDomain.HeightOneSpectrum (𝓞 L₀) :=
    ⟨q'.asIdeal.under (𝓞 L₀), inferInstance, Ideal.under_ne_bot (𝓞 L₀) q'.ne_bot⟩
  have hPdef : P.asIdeal = q'.asIdeal.under (𝓞 L₀) := rfl
  have hq'P : q'.asIdeal.LiesOver P.asIdeal := Ideal.over_under q'.asIdeal
  have hP : P.asIdeal.LiesOver Q.asIdeal :=
    Ideal.LiesOver.mk (by
      rw [hPdef, Ideal.under_under (A := 𝓞 k) q'.asIdeal]
      exact hqQ'.over)
  -- ## Step 5: the local `k_Q`-algebra embedding `(L₀)_{q₀} → L_{q'}`.
  have hq₀place : NK.GlobalCFT.Place.LiesOver
      (NK.GlobalCFT.Place.ofFinite q₀) (NK.GlobalCFT.Place.ofFinite Q) :=
    NK.GlobalCFT.Place.liesOver_ofFinite hq₀
  have hPplace : NK.GlobalCFT.Place.LiesOver
      (NK.GlobalCFT.Place.ofFinite P) (NK.GlobalCFT.Place.ofFinite Q) :=
    NK.GlobalCFT.Place.liesOver_ofFinite hP
  obtain ⟨σ, hσ⟩ := NK.GlobalCFT.Inclusion.globalCFT_exists_smul_eq_of_liesOver hq₀place hPplace
  have hσ' : NK.GlobalCFT.Place.smulHeightOneSpectrum σ q₀ = P := by
    have h := hσ
    rw [NK.GlobalCFT.Place.smul_ofFinite] at h
    exact NK.GlobalCFT.Place.ofFinite_inj.mp h
  have hP' : (NK.GlobalCFT.Place.smulHeightOneSpectrum σ q₀).asIdeal.LiesOver Q.asIdeal := by
    rw [hσ']; exact hP
  have hq'P' : q'.asIdeal.LiesOver (NK.GlobalCFT.Place.smulHeightOneSpectrum σ q₀).asIdeal := by
    rw [hσ']; exact hq'P
  letI hAlgS : Algebra (Q.adicCompletion k)
      ((NK.GlobalCFT.Place.smulHeightOneSpectrum σ q₀).adicCompletion L₀) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q
      (NK.GlobalCFT.Place.smulHeightOneSpectrum σ q₀) hP')
  letI hAlgT : Algebra (Q.adicCompletion k) (q'.adicCompletion ↥M) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap Q q' hqQ')
  let eσ : (q₀.adicCompletion L₀) ≃ₐ[Q.adicCompletion k]
      ((NK.GlobalCFT.Place.smulHeightOneSpectrum σ q₀).adicCompletion L₀) :=
    AlgEquiv.ofRingEquiv (f := NK.GlobalCFT.Galois.globalCFT_adicCongrEquiv σ q₀) (by
      intro x
      rw [RingHom.algebraMap_toAlgebra, RingHom.algebraMap_toAlgebra]
      exact NK.GlobalCFT.Galois.globalCFT_adicCongrEquiv_adicCompletionMap σ q₀ Q hq₀ hP' x)
  have hcomp : (Commons.RingTheory.Henselian.adicCompletionMap
        (NK.GlobalCFT.Place.smulHeightOneSpectrum σ q₀) q' hq'P').comp
      (Commons.RingTheory.Henselian.adicCompletionMap Q
        (NK.GlobalCFT.Place.smulHeightOneSpectrum σ q₀) hP')
      = Commons.RingTheory.Henselian.adicCompletionMap Q q' hqQ' :=
    Commons.NumberTheory.NumberField.Completion.adicCompletionMap_comp Q
      (NK.GlobalCFT.Place.smulHeightOneSpectrum σ q₀) q' hP' hq'P' hqQ'
  let ψ : ((NK.GlobalCFT.Place.smulHeightOneSpectrum σ q₀).adicCompletion L₀) →ₐ[Q.adicCompletion k]
      (q'.adicCompletion ↥M) :=
    { toRingHom := Commons.RingTheory.Henselian.adicCompletionMap
        (NK.GlobalCFT.Place.smulHeightOneSpectrum σ q₀) q' hq'P'
      commutes' := fun x => by
        rw [RingHom.algebraMap_toAlgebra, RingHom.algebraMap_toAlgebra]
        exact congrFun (congrArg DFunLike.coe hcomp) x }
  -- ## Step 6: assemble.
  refine ⟨↥M, inferInstance, hnfM, inferInstance, RingHom.toAlgebra fK.toRingHom, hSTK,
    hfdM, hgalM, q', hq', hqQ', ?_⟩
  exact ⟨(ψ.comp (eσ : (q₀.adicCompletion L₀) →ₐ[Q.adicCompletion k] _)).comp
    (e : F →ₐ[Q.adicCompletion k] _)⟩

end

end Work.SSGRoute
