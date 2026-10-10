import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.NumberTheory.NumberField.Completion.InfinitePlace
import Submission.NK.CFTLib.HR.isCyclotomic_onePlace_unramified
import Submission.NK.CFTLib.IdeleHasse.localGlobalArtinMap_exists
import Submission.NK.NUV2.ARL.localImage_mem_localNormSubgroup_of_isCyclotomic_of_real
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The cyclotomic crux at a place coprime to the level (the `hM` provider of the descent)

This file supplies the hypothesis `hM` of the one-place Brauer descent
(`NK.HR2.transferStepOnePlace`): the "one place omitted" form of Hilbert reciprocity at the
*cyclotomic* level `M = K(ζ_m)`, at a place `v₀` which is either archimedean or finite and coprime
to the level.

The proof is a case split on `v₀`, using only PROVED inputs:

* `v₀ = ofFinite Q` with `(m : 𝓞 K) ∉ Q.asIdeal`:
  `NK.CFTLib.HR.localImage_mem_localNormSubgroup_of_isCyclotomic_of_unramified_neZero`
  (general `m`), whose global input is the cyclotomic reciprocity law
  `NK.CFTLib.ARL.artinReciprocity_cyclotomic` and the modulus-`m` idèlic Artin map;
* `v₀ = ofInfinite w` with `w` real, `m` an odd prime:
  `NK.NUV2.ARL.localImage_mem_localNormSubgroup_of_isCyclotomic_of_real`;
* `v₀ = ofInfinite w` with `w` complex: the local norm is surjective (`K_w = ℂ`), so the local
  norm subgroup is `⊤` (`localNormSubgroup_eq_top_of_range_top` +
  `NK.NUV2.ArtinBridge.localNormInfinite_range_eq_top_of_complex_complex`).

This is the missing `hM`-assembly for the route
`local condition (L6) + transferStepOnePlace + hM ⟹ HilbertReciprocityOnePlace`; see
`Submission/Work/CFTLib/NOTES_hilbertReciprocity_cyclic_STATE.md`.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

namespace NK.CFTLib

open NumberField IsDedekindDomain
open NK.GlobalCFT

/-- **The cyclotomic crux at a place coprime to the level.**  For `M = K(ζ_m)` with `m` an odd
prime, an element of `Kˣ` which is a local norm from `M` at every place `v ≠ v₀` is a local norm at
`v₀`, provided that `v₀` — if finite — does not divide `(m)`. -/
theorem cyclotomicCruxAt_of_coprime {K M : Type} [Field K] [NumberField K] [Field M]
    [NumberField M] [Algebra K M] [FiniteDimensional K M] [IsGalois K M]
    (m : ℕ) (hm : m.Prime) (hm2 : 2 < m) [IsCyclotomicExtension {m} K M]
    (v₀ : Place K)
    (hcop : ∀ Q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K),
      v₀ = Place.ofFinite Q → (m : NumberField.RingOfIntegers K) ∉ Q.asIdeal)
    (y : Kˣ)
    (h : ∀ v : Place K, v ≠ v₀ →
      localImageHom (K := K) v y ∈
        NK.CFTLib.IdeleHasse.localNormSubgroup (K := K) (L := M) v) :
    localImageHom (K := K) v₀ y ∈
      NK.CFTLib.IdeleHasse.localNormSubgroup (K := K) (L := M) v₀ := by
  classical
  haveI : NeZero m := ⟨hm.ne_zero⟩
  haveI hfact : Fact m.Prime := ⟨hm⟩
  cases v₀ with
  | inl w =>
      by_cases hwR : w.IsReal
      · exact NK.NUV2.ARL.localImage_mem_localNormSubgroup_of_isCyclotomic_of_real
          (K := K) (L := M) m hm2 w hwR y h
      · have hwC : w.IsComplex := InfinitePlace.not_isReal_iff_isComplex.mp hwR
        obtain ⟨u, hu⟩ := NK.CFTLib.IdeleHasse.exists_liesOver_infinite (K := K) (L := M) w
        haveI : u.LiesOver w := hu
        have huc : u.IsComplex := InfinitePlace.LiesOver.isComplex_of_isComplex_under u hwC
        have hrange : MonoidHom.range (Place.localNormInfinite u w) = ⊤ :=
          NK.NUV2.ArtinBridge.localNormInfinite_range_eq_top_of_complex_complex hwC huc
        rw [NK.CFTLib.IdeleHasse.localNormSubgroup_eq_top_of_range_top (K := K) (L := M) hrange]
        exact Subgroup.mem_top _
  | inr Q =>
      exact NK.CFTLib.HR.localImage_mem_localNormSubgroup_of_isCyclotomic_of_unramified_neZero
        (K := K) (L := M) m Q (hcop Q rfl) y h

end NK.CFTLib
