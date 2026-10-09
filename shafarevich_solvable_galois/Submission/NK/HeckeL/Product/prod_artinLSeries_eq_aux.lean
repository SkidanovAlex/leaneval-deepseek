/-
The factorisation `∏_χ L(s, χ) = ζ_L^S(s)` of the Dedekind zeta function of an abelian extension
`L / K` as the product of the Artin `L`-series over all complex characters of `Gal(L/K)`.

The proof is the classical local computation, done prime by prime:

* the products over the primes and over the (finite) character group commute;
* at an unramified prime `𝔭` the character product `∏_χ (1 - χ(Frob_𝔭) N𝔭^{-s})⁻¹` equals
  `∏_{𝔮 | 𝔭} (1 - N𝔮^{-s})⁻¹`; this is the orthogonality identity
  `∏_χ (1 - χ(σ) x) = (1 - x ^ orderOf σ) ^ (|G| / orderOf σ)` together with the fundamental
  identity `#(𝔮 | 𝔭) · f(𝔮 | 𝔭) = [L : K]` of ramification theory;
* the primes of `L` not lying over the modulus `S` are exactly the disjoint union over the primes
  `𝔭 ∉ S` of the primes above `𝔭`, which is the fibre decomposition
  `NK.HeckeL.Product.zetaUnramified_eq_tprod_fiber` of the Dedekind Euler product.
-/
import Mathlib
import Submission.NK.HeckeL.Zeta
import Submission.NK.HeckeL.Product.prod_monoidHom_one_sub_mul
import Submission.NK.HeckeL.Product.artinLSeries_one
import Submission.NK.HeckeL.Series.hasProd_artinEulerFactor
import Submission.NK.Chebotarev.IsFrobAtOrderOfEqInertiaDeg
import Submission.NK.HeckeL.Product.zetaUnramified_eq_tprod_fiber
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped Classical BigOperators
open NumberField IsDedekindDomain
open NK.Chebotarev

set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

namespace NK.HeckeL.Product

open NK.HeckeL

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]
  [FiniteDimensional K L] [IsGalois K L]

/-! ## The finite abelian group character product -/

/-- **The product of `(1 - χ(σ) x)⁻¹` over the characters of a finite abelian group.**  It follows
from `∏_χ (1 - χ(σ) x) = (1 - x ^ orderOf σ) ^ (card G / orderOf σ)`
(`NK.HeckeL.Product.prod_monoidHom_one_sub_mul`) by inverting both sides. -/
theorem prod_monoidHom_inv_one_sub_mul (G : Type*) [CommGroup G] [Fintype G] (σ : G) (x : ℂ) :
    ∏ χ : G →* ℂˣ, (1 - (χ σ : ℂ) * x)⁻¹ =
      ((1 - x ^ orderOf σ)⁻¹) ^ (Nat.card G / orderOf σ) := by
  have h1 : (∏ χ : G →* ℂˣ, (1 - (χ σ : ℂ) * x)⁻¹)
      = (∏ χ : G →* ℂˣ, (1 - (χ σ : ℂ) * x))⁻¹ := by
    simpa using (Finset.prod_inv_distrib (s := Finset.univ)
      (f := fun χ : G →* ℂˣ => (1 - (χ σ : ℂ) * x)))
  rw [h1, prod_monoidHom_one_sub_mul, ← inv_pow]

/-! ## The order of the Frobenius at a prime -/

/-- The chosen Frobenius element at an unramified prime of an abelian extension has order equal to
the inertia degree. -/
theorem orderOf_frobAtPrime_eq_inertiaDeg (hcomm : ∀ a b : Gal(L/K), a * b = b * a)
    (𝔭 : PrimeIdeal K) (P : PrimeIdeal L) (hP : P.asIdeal.LiesOver 𝔭.asIdeal)
    (h𝔭 : IsUnramifiedIn (K := K) (L := L) 𝔭) :
    orderOf (frobAtPrime (K := K) (L := L) 𝔭) = P.asIdeal.inertiaDeg (𝓞 K) := by
  obtain ⟨σ, hσ⟩ := exists_isFrobAt (K := K) (L := L) 𝔭 P hP
  have hfp : frobAtPrime (K := K) (L := L) 𝔭 = σ :=
    (isFrobAtPrime_iff_frobAtPrime_eq hcomm 𝔭 h𝔭 σ).mp ⟨P, hP, hσ⟩
  rw [hfp]
  exact IsFrobAtOrderOfEqInertiaDeg hP (h𝔭 P hP) hσ

/-! ## The fundamental identity at an unramified prime -/

/-- The number of primes of `L` above an unramified prime `𝔭` of `K`, times the inertia degree, is
the degree `#Gal(L/K)`.  This is the fundamental identity `∑_{𝔮 | 𝔭} e(𝔮) f(𝔮) = [L : K]` of
ramification theory, specialised to `e = 1`. -/
theorem ncard_primesOver_mul_inertiaDeg_eq_card (𝔭 : PrimeIdeal K) (P : PrimeIdeal L)
    (hP : P.asIdeal.LiesOver 𝔭.asIdeal) (h𝔭 : IsUnramifiedIn (K := K) (L := L) 𝔭) :
    (𝔭.asIdeal.primesOver (𝓞 L)).ncard * P.asIdeal.inertiaDeg (𝓞 K) = Nat.card Gal(L/K) := by
  haveI : 𝔭.asIdeal.IsPrime := 𝔭.isPrime
  haveI : P.asIdeal.IsPrime := P.isPrime
  haveI : P.asIdeal.LiesOver 𝔭.asIdeal := hP
  have h := Ideal.ncard_primesOver_mul_ramificationIdxIn_mul_inertiaDegIn 𝔭.asIdeal (𝓞 L) Gal(L/K)
  rw [Ideal.ramificationIdxIn_eq_ramificationIdx 𝔭.asIdeal P.asIdeal Gal(L/K),
      Ideal.inertiaDegIn_eq_inertiaDeg 𝔭.asIdeal P.asIdeal Gal(L/K), h𝔭 P hP, one_mul] at h
  simpa using h

/-! ## An identity for `rpow` -/

/-- `(N ^ f) ^ (-s) = (N ^ (-s)) ^ f` for a natural number `N`, transferred to `ℂ`. -/
theorem absNorm_pow_rpow_neg (𝔭 : PrimeIdeal K) (f : ℕ) (s : ℝ) :
    ((((Ideal.absNorm 𝔭.asIdeal ^ f : ℕ) : ℝ) ^ (-s) : ℝ) : ℂ)
      = ((((Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s) : ℝ) : ℂ)) ^ f := by
  have key : (((Ideal.absNorm 𝔭.asIdeal : ℝ)) ^ f) ^ (-s)
      = (((Ideal.absNorm 𝔭.asIdeal : ℝ)) ^ (-s)) ^ f := by
    rw [← Real.rpow_natCast (x := (Ideal.absNorm 𝔭.asIdeal : ℝ)) f,
        ← Real.rpow_mul (Nat.cast_nonneg (Ideal.absNorm 𝔭.asIdeal)),
        mul_comm (f : ℝ) (-s),
        Real.rpow_mul (Nat.cast_nonneg (Ideal.absNorm 𝔭.asIdeal)),
        Real.rpow_natCast]
  rw [Nat.cast_pow, key, Complex.ofReal_pow]

/-! ## Convergence of the Dedekind Euler factors -/

/-- For `s > 1` the family of Dedekind Euler factors `(1 - N𝔮^{-s})⁻¹` over the primes of a number
field is multipliable. -/
theorem multipliable_dedekindEulerFactor (L : Type*) [Field L] [NumberField L] {s : ℝ} (hs : 1 < s) :
    Multipliable (fun 𝔮 : PrimeIdeal L =>
      (1 - (((Ideal.absNorm 𝔮.asIdeal : ℝ) ^ (-s) : ℝ) : ℂ))⁻¹) := by
  have hspos : (0 : ℝ) < s := lt_trans zero_lt_one hs
  set z : PrimeIdeal L → ℂ := fun 𝔮 => (((Ideal.absNorm 𝔮.asIdeal : ℝ) ^ (-s) : ℝ) : ℂ) with hz
  have hznorm : ∀ 𝔮 : PrimeIdeal L, ‖z 𝔮‖ = (Ideal.absNorm 𝔮.asIdeal : ℝ) ^ (-s) := by
    intro 𝔮
    simp only [hz, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg (Ideal.absNorm 𝔮.asIdeal)) _)]
  have hsumN : Summable (fun 𝔮 : PrimeIdeal L => (Ideal.absNorm 𝔮.asIdeal : ℝ) ^ (-s)) :=
    Commons.NumberTheory.NumberField.Set.summable_primeIdealZetaSum (K := L) hs
  have hsumz : Summable (fun 𝔮 : PrimeIdeal L => ‖z 𝔮‖) := hsumN.congr fun 𝔮 => (hznorm 𝔮).symm
  have hsum_neg : Summable (fun 𝔮 : PrimeIdeal L => ‖-(z 𝔮)‖) := by simpa using hsumz
  have hmult : Multipliable (fun 𝔮 : PrimeIdeal L => 1 + (-(z 𝔮))) :=
    multipliable_one_add_of_summable hsum_neg
  have hne : ∀ 𝔮 : PrimeIdeal L, 1 + (-(z 𝔮)) ≠ 0 := by
    intro 𝔮 hzero
    have hz1 : z 𝔮 = 1 := by
      have h1 : -(z 𝔮) = -1 := eq_neg_of_add_eq_zero_right hzero
      simpa using (neg_inj.mp h1)
    have hnorm := hznorm 𝔮
    rw [hz1, norm_one] at hnorm
    have hlt := Commons.NumberTheory.NumberField.DedekindZeta.rpow_neg_absNorm_primeIdeal_lt_one
      (K := L) hspos 𝔮
    linarith
  have hprodne : (∏' 𝔮 : PrimeIdeal L, (1 + (-(z 𝔮)))) ≠ 0 :=
    tprod_one_add_ne_zero_of_summable hne hsum_neg
  have hmain := (hmult.hasProd.inv₀ hprodne).multipliable
  refine hmain.congr fun 𝔮 => ?_
  simp only [z, sub_eq_add_neg]

/-! ## The local Euler factor identity -/

/-- **The local factorisation at an unramified prime.**  For an unramified prime `𝔭` of `K`, the
product over all characters of `Gal(L/K)` of the Artin Euler factors is the product over the primes
of `L` above `𝔭` of the Dedekind Euler factors. -/
theorem local_artinEulerFactor_prod (hcomm : ∀ a b : Gal(L/K), a * b = b * a)
    (𝔭 : PrimeIdeal K) (h𝔭 : IsUnramifiedIn (K := K) (L := L) 𝔭) (s : ℝ) :
    ∏ χ : Gal(L/K) →* ℂˣ, artinEulerFactor (K := K) (L := L) χ s 𝔭 =
      ∏ P : ↥(𝔭.asIdeal.primesOver (𝓞 L)),
        (1 - (((Ideal.absNorm (P : Ideal (𝓞 L)) : ℝ) ^ (-s) : ℝ) : ℂ))⁻¹ := by
  classical
  letI : CommGroup Gal(L/K) := { (inferInstance : Group Gal(L/K)) with mul_comm := hcomm }
  obtain ⟨P₀, hP₀⟩ := exists_primeIdeal_liesOver (K := K) (L := L) 𝔭
  set f : ℕ := P₀.asIdeal.inertiaDeg (𝓞 K) with hf
  have hfpos : 0 < f := Ideal.inertiaDeg_pos P₀.asIdeal (𝓞 K)
  have horder : orderOf (frobAtPrime (K := K) (L := L) 𝔭) = f := by
    rw [hf]; exact orderOf_frobAtPrime_eq_inertiaDeg hcomm 𝔭 P₀ hP₀ h𝔭
  set x : ℂ := (((Ideal.absNorm 𝔭.asIdeal : ℝ) ^ (-s) : ℝ) : ℂ) with hx
  haveI : IsGaloisGroup Gal(L/K) (𝓞 K) (𝓞 L) :=
    IsGaloisGroup.of_isFractionRing Gal(L/K) (𝓞 K) (𝓞 L) K L
  have hfac : ∀ P : ↥(𝔭.asIdeal.primesOver (𝓞 L)),
      (1 - (((Ideal.absNorm (P : Ideal (𝓞 L)) : ℝ) ^ (-s) : ℝ) : ℂ))⁻¹ = (1 - x ^ f)⁻¹ := by
    intro P
    haveI hPs : (P : Ideal (𝓞 L)).IsPrime := P.2.1
    haveI hPl : (P : Ideal (𝓞 L)).LiesOver 𝔭.asIdeal := P.2.2
    have hdegP : (P : Ideal (𝓞 L)).inertiaDeg (𝓞 K) = f := by
      rw [hf]
      exact Ideal.inertiaDeg_eq_of_isGaloisGroup 𝔭.asIdeal (P : Ideal (𝓞 L)) P₀.asIdeal Gal(L/K)
    have hnorm : Ideal.absNorm (P : Ideal (𝓞 L)) = Ideal.absNorm 𝔭.asIdeal ^ f := by
      rw [← Ideal.absNorm_pow_inertiaDeg 𝔭.asIdeal (P : Ideal (𝓞 L)), hdegP]
    rw [hnorm, absNorm_pow_rpow_neg 𝔭 f s, hx]
  have hLHS : (∏ χ : Gal(L/K) →* ℂˣ, artinEulerFactor (K := K) (L := L) χ s 𝔭)
      = ((1 - x ^ f)⁻¹) ^ (Nat.card Gal(L/K) / f) := by
    show (∏ χ : Gal(L/K) →* ℂˣ, (1 - (χ (frobAtPrime (K := K) (L := L) 𝔭) : ℂ) * x)⁻¹)
      = ((1 - x ^ f)⁻¹) ^ (Nat.card Gal(L/K) / f)
    rw [prod_monoidHom_inv_one_sub_mul, horder]
  have hRHS : (∏ P : ↥(𝔭.asIdeal.primesOver (𝓞 L)),
        (1 - (((Ideal.absNorm (P : Ideal (𝓞 L)) : ℝ) ^ (-s) : ℝ) : ℂ))⁻¹)
      = ((1 - x ^ f)⁻¹) ^ (𝔭.asIdeal.primesOver (𝓞 L)).ncard := by
    rw [Finset.prod_congr rfl (fun P _ => hfac P), Finset.prod_const, Finset.card_univ]
    rw [Set.fintypeCard_eq_ncard]
  have hN : Nat.card Gal(L/K) = (𝔭.asIdeal.primesOver (𝓞 L)).ncard * f := by
    rw [hf]
    exact (ncard_primesOver_mul_inertiaDeg_eq_card 𝔭 P₀ hP₀ h𝔭).symm
  have hdiv : Nat.card Gal(L/K) / f = (𝔭.asIdeal.primesOver (𝓞 L)).ncard := by
    rw [hN]
    exact Nat.mul_div_left _ hfpos
  rw [hLHS, hRHS, hdiv]

/-! ## Commuting the two products -/

/-- The product over the characters of the Artin `L`-series is the product over the primes outside
`S` of the product over the characters of the local Euler factors. -/
theorem prod_char_artinLSeries_eq_tprod (S : Finset (PrimeIdeal K)) {s : ℝ} (hs : 1 < s) :
    (∏' χ : Gal(L/K) →* ℂˣ, artinLSeries K L S χ s)
      = ∏' 𝔭 : {𝔭 : PrimeIdeal K // 𝔭 ∉ S},
          ∏ χ : Gal(L/K) →* ℂˣ, artinEulerFactor (K := K) (L := L) χ s 𝔭.1 := by
  have hh : HasProd (fun 𝔭 : {𝔭 : PrimeIdeal K // 𝔭 ∉ S} =>
        ∏ χ : Gal(L/K) →* ℂˣ, artinEulerFactor (K := K) (L := L) χ s 𝔭.1)
      (∏ χ : Gal(L/K) →* ℂˣ, artinLSeries K L S χ s) := by
    have h := hasProd_prod (s := (Finset.univ : Finset (Gal(L/K) →* ℂˣ)))
      (f := fun (χ : Gal(L/K) →* ℂˣ) (𝔭 : {𝔭 : PrimeIdeal K // 𝔭 ∉ S}) =>
        artinEulerFactor (K := K) (L := L) χ s 𝔭.1)
      (a := fun χ => artinLSeries K L S χ s)
      (fun χ _ => NK.HeckeL.Series.hasProd_artinEulerFactor S χ hs)
    simpa using h
  have h2 : (∏' 𝔭 : {𝔭 : PrimeIdeal K // 𝔭 ∉ S},
        ∏ χ : Gal(L/K) →* ℂˣ, artinEulerFactor (K := K) (L := L) χ s 𝔭.1)
      = ∏ χ : Gal(L/K) →* ℂˣ, artinLSeries K L S χ s := hh.tprod_eq
  have h3 : (∏' χ : Gal(L/K) →* ℂˣ, artinLSeries K L S χ s)
      = ∏ χ : Gal(L/K) →* ℂˣ, artinLSeries K L S χ s := (hasProd_fintype _).tprod_eq
  rw [h3, ← h2]

/-! ## The main theorem -/

theorem prod_artinLSeries_eq_aux {K L : Type*} [Field K] [NumberField K] [Field L]
    [NumberField L] [Algebra K L] [FiniteDimensional K L] [IsGalois K L]
    (S : Finset (NK.HeckeL.PrimeIdeal K)) (hcomm : ∀ a b : Gal(L/K), a * b = b * a)
    (hS : ∀ 𝔭 : NK.HeckeL.PrimeIdeal K, ¬ NK.HeckeL.IsUnramifiedIn (K := K) (L := L) 𝔭 → 𝔭 ∈ S)
    {s : ℝ} (hs : 1 < s) :
    ∏' χ : Gal(L/K) →* ℂˣ, NK.HeckeL.artinLSeries K L S χ s =
      NK.HeckeL.zetaUnramified K L S s := by
  classical
  have hJ : ∀ 𝔭 : {𝔭 : NK.HeckeL.PrimeIdeal K // 𝔭 ∉ S},
      NK.HeckeL.IsUnramifiedIn (K := K) (L := L) 𝔭.1 := by
    intro 𝔭
    by_contra h
    exact 𝔭.2 (hS 𝔭.1 h)
  have hz := zetaUnramified_eq_tprod_fiber (K := K) (L := L) S hs
  calc ∏' χ : Gal(L/K) →* ℂˣ, NK.HeckeL.artinLSeries K L S χ s
      = ∏' 𝔭 : {𝔭 : NK.HeckeL.PrimeIdeal K // 𝔭 ∉ S},
          ∏ χ : Gal(L/K) →* ℂˣ, NK.HeckeL.artinEulerFactor (K := K) (L := L) χ s 𝔭.1 :=
        prod_char_artinLSeries_eq_tprod S hs
    _ = ∏' 𝔭 : {𝔭 : NK.HeckeL.PrimeIdeal K // 𝔭 ∉ S},
          ∏ P : ↥(𝔭.1.asIdeal.primesOver (𝓞 L)),
            (1 - (((Ideal.absNorm (P : Ideal (𝓞 L)) : ℝ) ^ (-s) : ℝ) : ℂ))⁻¹ :=
        tprod_congr (fun 𝔭 => local_artinEulerFactor_prod hcomm 𝔭.1 (hJ 𝔭) s)
    _ = NK.HeckeL.zetaUnramified K L S s := hz.symm

end NK.HeckeL.Product
