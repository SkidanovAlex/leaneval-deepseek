import Mathlib
import Submission.NK.HeckeL.Dictionary
import Submission.NK.HeckeL.artinLSeries_tendsto_of_hecke
import Submission.NK.HeckeL.Nonvanishing.artinLSeries_value_ne_zero

open Filter

namespace NK.HeckeL.Consequences

/-- **Non-vanishing of the Hecke `L`-series at `s = 1` for a non-trivial ray class character.**

The Hecke regularity input `hH` (Hecke's theorem, asserting the convergence of the Hecke
`L`-series at `s = 1`) plus Artin reciprocity gives the classical non-vanishing `L(1, χ) ≠ 0` for
every non-trivial character of the ray class group.

The argument transfers the Hecke input to the Galois side: the dictionary
`NK.HeckeL.rayCharEquivGalois` identifies the ray class characters of the modulus with the
characters of `Gal(L/K)`, and for `s > 1` the Hecke `L`-series of `χ` agrees with the Artin
`L`-series of the corresponding Galois character
(`NK.HeckeL.artinLSeries_eq_heckeLSeries`), so the Hecke limit `(hH χ hχ).value` is also the
limit of the Artin `L`-series (`NK.HeckeL.artinLSeries_tendsto_of_hecke`).  Applying
`NK.HeckeL.Nonvanishing.artinLSeries_value_ne_zero` to the transferred family of Artin
regularity data gives the non-vanishing of the value. -/
theorem heckeLRegular_value_ne_zero {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    {U : Subgroup (NK.GlobalCFT.Idele K)}
    [Finite (NK.GlobalCFT.IdeleClassGroup.rayClassGroup K U)]
    (h : NK.GlobalCFT.ArtinReciprocity K L)
    (e : NK.GlobalCFT.IdeleClassGroup.rayClassGroup K U ≃*
      (NK.GlobalCFT.IdeleClassGroup K ⧸ NK.GlobalCFT.Idele.normClassSubgroup K L))
    (S : Finset (NK.HeckeL.PrimeIdeal K)) (hcomm : ∀ a b : Gal(L/K), a * b = b * a)
    (hS : ∀ 𝔭 : NK.HeckeL.PrimeIdeal K, ¬ NK.HeckeL.IsUnramifiedIn (K := K) (L := L) 𝔭 → 𝔭 ∈ S)
    (hFrob : NK.HeckeL.FrobeniusCompatibility K L U h e S)
    (hH : ∀ χ : NK.HeckeL.RayChar K U, χ ≠ 1 → NK.HeckeL.HeckeLRegularAtOne K U S χ)
    (χ : NK.HeckeL.RayChar K U) (hχ : χ ≠ 1) :
    (hH χ hχ).value ≠ 0 := by
  classical
  -- the image of `χ` under the dictionary is non-trivial
  have hχF : NK.HeckeL.rayCharEquivGalois h e χ ≠ 1 :=
    fun h1 => hχ ((NK.HeckeL.rayCharEquivGalois_eq_one_iff h e).mp h1)
  -- transfer the Hecke regularity data to the Artin side along the dictionary
  let h' : ∀ ψ : Gal(L/K) →* ℂˣ, ψ ≠ 1 → NK.HeckeL.ArtinLRegularAtOne K L S ψ :=
    fun ψ hψ => by
      have hne : (NK.HeckeL.rayCharEquivGalois h e).symm ψ ≠ 1 := by
        intro h0
        exact hψ (by
          rw [← MulEquiv.apply_symm_apply (NK.HeckeL.rayCharEquivGalois h e) ψ, h0,
            NK.HeckeL.rayCharEquivGalois_one])
      refine { value := (hH ((NK.HeckeL.rayCharEquivGalois h e).symm ψ) hne).value, tendsto := ?_ }
      have ht := NK.HeckeL.artinLSeries_tendsto_of_hecke (K := K) (L := L) h e S hFrob
        ((NK.HeckeL.rayCharEquivGalois h e).symm ψ)
        (hH ((NK.HeckeL.rayCharEquivGalois h e).symm ψ) hne)
      simpa using ht
  -- the classical non-vanishing on the Artin side
  have key := NK.HeckeL.Nonvanishing.artinLSeries_value_ne_zero (K := K) (L := L)
    S hcomm hS h' (NK.HeckeL.rayCharEquivGalois h e χ) hχF
  -- the transferred value is the limit of the same Artin `L`-series, hence equals the Hecke value
  have hEq : (h' (NK.HeckeL.rayCharEquivGalois h e χ) hχF).value = (hH χ hχ).value :=
    tendsto_nhds_unique (h' (NK.HeckeL.rayCharEquivGalois h e χ) hχF).tendsto
      (NK.HeckeL.artinLSeries_tendsto_of_hecke (K := K) (L := L) h e S hFrob χ (hH χ hχ))
  rwa [hEq] at key

end NK.HeckeL.Consequences
