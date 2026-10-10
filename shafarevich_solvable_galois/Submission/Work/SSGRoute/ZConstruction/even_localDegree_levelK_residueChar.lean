import Mathlib.RingTheory.Henselian
import Mathlib.NumberTheory.Padics.HeightOneSpectrum
import Mathlib.RingTheory.RegularLocalRing.Defs
import Mathlib.RingTheory.SimpleRing.Principal
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Submission.NK.NUV2.LC.cylArtinValues
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.ZConstruction

open Polynomial IsDedekindDomain.HeightOneSpectrum

set_option linter.style.haveILetI false

/-- **The degree of `F(ζ)` divides the degree of any field extension containing `ζ`.**

Let `F` be a field of characteristic zero and `E / F` a field extension containing a primitive
`p`-th root of unity `ζ` (`p` a prime).  If `cyclotomic p F` is irreducible over `F` — so that
`[F(ζ) : F] = p - 1` — then `p - 1` divides `[E : F]`.

Indeed `cyclotomic p F = minpoly F ζ`
(`IsPrimitiveRoot.minpoly_eq_cyclotomic_of_irreducible`), so
`[F(ζ) : F] = (minpoly F ζ).natDegree = p.totient = p - 1`
(`IntermediateField.adjoin.finrank`, `Polynomial.natDegree_cyclotomic`, `Nat.totient_prime`), and
the tower law `Module.finrank_mul_finrank` for `F ⊆ F(ζ) ⊆ E` gives the divisibility. -/
theorem dvd_finrank_of_isPrimitiveRoot_of_irreducible {F E : Type*} [Field F] [Field E]
    [Algebra F E] [CharZero F] {p : ℕ} (hp : p.Prime)
    (hirr : Irreducible (cyclotomic p F)) (ζ : E) (hζ : IsPrimitiveRoot ζ p) :
    p - 1 ∣ Module.finrank F E := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  haveI : NeZero (p : F) := ⟨by exact_mod_cast hp.ne_zero⟩
  have hint : IsIntegral F ζ := by
    have h : IsIntegral F (ζ ^ p) := by rw [hζ.pow_eq_one]; exact isIntegral_one
    exact IsIntegral.of_pow hp.pos h
  have hmin : cyclotomic p F = minpoly F ζ :=
    hζ.minpoly_eq_cyclotomic_of_irreducible hirr
  set S : IntermediateField F E := IntermediateField.adjoin F {ζ} with hS
  have hfr : Module.finrank F ↥S = p - 1 := by
    rw [hS, IntermediateField.adjoin.finrank hint]
    rw [← hmin, natDegree_cyclotomic, Nat.totient_prime hp]
  have htow : Module.finrank F ↥S * Module.finrank ↥S E = Module.finrank F E :=
    Module.finrank_mul_finrank F ↥S E
  exact ⟨Module.finrank ↥S E, by rw [← htow, hfr]⟩

/-- **The absolute local degree at a place of residue characteristic `p` is even.**

For a number field `K`, a prime `𝔭` above the rational prime `p` (`(p : 𝒪_K) ∈ 𝔭`, so the residue
characteristic of `𝔭` is `p`) and an odd prime `p`, if the completion `κ = K_𝔭` contains a
primitive `p`-th root of unity then `[κ : ℚ_p] = localDegree K 𝔭` is even.

Indeed `ℚ_p(ζ_p) ⊆ κ` and `ℚ_p(ζ_p)/ℚ_p` has degree `p - 1` (`Φ_p(X + 1)` is Eisenstein at `p`, so
`Φ_p` is irreducible over `ℚ_p` — see `NK.NUV2.LC.cylArtinValues`,
`irreducible_cyclotomic_prime_pow_of_isLocalRing`), so `p - 1 ∣ [κ : ℚ_p]` by the tower law; as
`p` is odd, `p - 1` is even. -/
theorem even_localDegree_levelK_residueChar {K : Type*} [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) {p : ℕ}
    (hp : p.Prime) (hodd : p ≠ 2)
    (hres : (p : NumberField.RingOfIntegers K) ∈ 𝔭.asIdeal)
    (hζ : ∃ ζ : 𝔭.adicCompletion K, IsPrimitiveRoot ζ p) :
    Even (NK.LocalInputs.localDegree K 𝔭) := by
  obtain ⟨ζ, hζ⟩ := hζ
  -- the `p`-adic base field `ℚ_p = (primeBelow K 𝔭).adicCompletion ℚ`
  let Kp := (NK.LocalInputs.primeBelow K 𝔭).adicCompletion ℚ
  -- the `ℚ_p`-algebra structure on `κ = 𝔭.adicCompletion K` used by `localDegree`
  letI : Algebra Kp (𝔭.adicCompletion K) :=
    RingHom.toAlgebra (Commons.RingTheory.Henselian.adicCompletionMap
      (NK.LocalInputs.primeBelow K 𝔭) 𝔭 (NK.LocalInputs.primeBelow_liesOver K 𝔭))
  haveI hcz : CharZero Kp :=
    charZero_of_injective_algebraMap (RingHom.injective (algebraMap ℚ Kp))
  -- `p` is the rational prime below `𝔭`
  have hnatgen : Rat.HeightOneSpectrum.natGenerator (NK.LocalInputs.primeBelow K 𝔭) = p := by
    have hdiv := NK.LocalInputs.ResidueChar.natGenerator_primeBelow_dvd 𝔭 hres
    have hne : Rat.HeightOneSpectrum.natGenerator (NK.LocalInputs.primeBelow K 𝔭) ≠ 1 :=
      (Rat.HeightOneSpectrum.prime_natGenerator _).ne_one
    exact ((Nat.Prime.dvd_iff_eq hp hne).mp hdiv).symm
  have hrescard : NK.LocalReciprocityLubinTate.residueCard Kp = p := by
    have h : NK.LocalReciprocityLubinTate.residueCard
        ((NK.LocalInputs.primeBelow K 𝔭).adicCompletion ℚ) =
        (Rat.HeightOneSpectrum.primesEquiv (NK.LocalInputs.primeBelow K 𝔭) : ℕ) :=
      NK.NUV2.LC.residueCard_adicCompletion_rat (NK.LocalInputs.primeBelow K 𝔭)
    rw [h]
    exact hnatgen
  -- `Φ_p` is irreducible over `ℚ_p`
  have hcyclo : Irreducible (cyclotomic p Kp) := by
    have h := NK.NUV2.LC.irreducible_cyclotomic_residueCard_pow
      (NK.LocalInputs.primeBelow K 𝔭) 1 (le_refl 1)
    rw [pow_one, hrescard] at h
    exact h
  -- the tower law in `ℚ_p ⊆ ℚ_p(ζ) ⊆ κ`
  have hdvd : p - 1 ∣ Module.finrank Kp (𝔭.adicCompletion K) :=
    dvd_finrank_of_isPrimitiveRoot_of_irreducible hp hcyclo ζ hζ
  rw [show NK.LocalInputs.localDegree K 𝔭 = Module.finrank Kp (𝔭.adicCompletion K) from rfl,
    even_iff_two_dvd]
  obtain ⟨k, hk⟩ := hp.odd_of_ne_two hodd
  exact dvd_trans ⟨k, by omega⟩ hdvd

end Work.SSGRoute.ZConstruction
