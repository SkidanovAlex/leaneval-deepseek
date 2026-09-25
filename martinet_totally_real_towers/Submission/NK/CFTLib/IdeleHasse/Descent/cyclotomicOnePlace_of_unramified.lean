import Mathlib
import Submission.NK.CFTLib.hilbertReciprocityCyclicAux
import Submission.NK.CFTLib.HR.isCyclotomic_onePlace_unramified
import Submission.NK.CFTLib.HR.isCyclotomic_onePlace_real
import Submission.NK.CFTLib.HR.isTotallyComplex_cyclotomic
import Submission.NK.CFTLib.IdeleHasse.localNormSubgroup

/-!
# The cyclotomic crux at a single place

Feeds the hypothesis `hM` of the one-place Brauer transfer
(`NK.CFTLib.IdeleHasse.Descent.transferOnePlace`): for a cyclotomic level `M = K(ζ_m)` (`m > 2`)
which is **unramified at a finite place `v₀`** (i.e. `(m : 𝓞 K) ∉ Q` where `v₀ = ofFinite Q`), a
global element `y ∈ Kˣ` which is a local norm from `M` at every other place is a local norm at `v₀`.

The content is assembled from three proved inputs, one per place type of `v₀`:

* finite `v₀` with `(m) ∉ Q`: `NK.CFTLib.HR.localImage_mem_localNormSubgroup_of_isCyclotomic_of_unramified_neZero`;
* real `v₀`: `NK.CFTLib.HR.isCyclotomic_onePlace_real` (needs `2 < m`);
* complex `v₀`: the local norm subgroup is `⊤`, since `M` is totally complex
  (`NK.CFTLib.HR.isTotallyComplex_of_isCyclotomicExtension`) so every place of `M` over `v₀` is
  complex and the local norm `ℂˣ → ℂˣ` is surjective.

The hypothesis `2 < m` is the "the auxiliary modulus is an odd prime" condition of the design
(`M = K(ζ_q)` with `q` an odd prime, `NK.CFTLib.HR.exists_prime_orderOf_dvd`).
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped NumberField RestrictedProduct
open NumberField IsDedekindDomain

noncomputable section

namespace NK.CFTLib.IdeleHasse.Descent

open NK.GlobalCFT

variable {K M : Type} [Field K] [NumberField K] [Field M] [NumberField M] [Algebra K M]
  [FiniteDimensional K M] [IsGalois K M]

/-- **The cyclotomic crux at a place `v₀` unramified in `M = K(ζ_m)`** (`m > 2`). -/
theorem cyclotomicOnePlace_of_unramified
    (m : ℕ) (hm : 2 < m) [IsCyclotomicExtension {m} K M]
    (v₀ : Place K)
    (hunr : ∀ Q : HeightOneSpectrum (𝓞 K), v₀ = Place.ofFinite Q → (m : 𝓞 K) ∉ Q.asIdeal)
    (y : Kˣ)
    (h : ∀ v : Place K, v ≠ v₀ →
      NK.CFTLib.localImageHom v y ∈ localNormSubgroup (K := K) (L := M) v) :
    NK.CFTLib.localImageHom v₀ y ∈ localNormSubgroup (K := K) (L := M) v₀ := by
  classical
  haveI : NeZero m := ⟨by omega⟩
  cases v₀ with
  | inl w =>
      by_cases hwr : w.IsReal
      · exact NK.CFTLib.HR.isCyclotomic_onePlace_real (K := K) (L := M) m hm w hwr y h
      · -- a complex place: the local norm subgroup is everything
        have hwC : w.IsComplex := NumberField.InfinitePlace.not_isReal_iff_isComplex.mp hwr
        rw [show localNormSubgroup (K := K) (L := M) (Place.ofInfinite w) = ⊤ from ?_]
        exact Subgroup.mem_top _
        obtain ⟨w', hw'⟩ := NK.CFTLib.IdeleHasse.exists_liesOver_infinite (K := K) (L := M) w
        haveI : w'.LiesOver w := hw'
        exact NK.CFTLib.IdeleHasse.localNormSubgroup_eq_top_of_range_top (K := K) (L := M)
          (v := w) (w₀ := w')
          (NK.NUV2.ArtinBridge.localNormInfinite_range_eq_top_of_complex_complex
            (K := K) (L := M) (v := w) (w := w') hwC
            (NumberField.InfinitePlace.LiesOver.isComplex_of_isComplex_under w' hwC))
  | inr Q =>
      exact NK.CFTLib.HR.localImage_mem_localNormSubgroup_of_isCyclotomic_of_unramified_neZero
        (K := K) (L := M) m Q (hunr Q rfl) y h

end NK.CFTLib.IdeleHasse.Descent
