import Mathlib
import Submission.Work.BW.RB.poly_max_ideal_height


/-!
# The height of a maximal ideal of a finitely generated domain over `ℂ`

For a finitely generated domain `D` over `ℂ` and a maximal ideal `M` of `D`, the height of `M`
equals the Krull dimension of `D`.  This is the equidimensionality of affine varieties: an affine
domain is equidimensional, so every maximal ideal has height equal to `dim D`.

## Proof

By Noether normalization (`exists_finite_inj_algHom_of_fg`) there is `s` and an injective,
finite (= integral) `ℂ`-algebra homomorphism `g : ℂ[X₁,…,X_s] → D`.  We view `D` as an algebra over
`A = ℂ[X₁,…,X_s]` via `g` (an instance is added by `algebraize`-style rewriting of the ring hom
into an `Algebra` structure).

Because `A` is a unique factorization domain, it is integrally closed, so the integral extension
`A ⊆ D` satisfies the going-down property (`Algebra.HasGoingDown`).  Hence for the prime `p = M ∩ A`
lying under `M`, Matsumura's height formula for going-down extensions gives

`ht M = ht p + ht (M ⧸ pD) ≥ ht p`.

Now `M` maximal in `D` and `A ⊆ D` integral imply `p` is maximal in `A`, whence
`ht p = s` by `poly_max_ideal_height`; so `s ≤ ht M`.

Conversely, contracting primes along the integral extension is strictly monotone
(`Ideal.IsIntegral.under_lt_under`), so `ringKrullDim D ≤ ringKrullDim A` via
`Order.krullDim_le_of_strictMono`, and `ringKrullDim A = s`.

Finally `ht M ≤ ringKrullDim D` for the prime (maximal) ideal `M`, and combining the bounds
`s ≤ ht M ≤ ringKrullDim D ≤ s` yields `ht M = ringKrullDim D`.
-/

set_option linter.style.haveILetI false

namespace Work.BW.RB

theorem maximal_height_eq_ringKrullDim (D : Type*) [CommRing D] [IsDomain D] [Algebra ℂ D]
    [Algebra.FiniteType ℂ D] (M : Ideal D) [M.IsMaximal] :
    ((M.height : ℕ∞) : WithBot ℕ∞) = ringKrullDim D := by
  -- Noether normalization: `D` is a finite (= integral) extension of a polynomial ring `A`.
  obtain ⟨s, g, hinj, hfin⟩ := exists_finite_inj_algHom_of_fg ℂ D
  let A := MvPolynomial (Fin s) ℂ
  letI : Algebra A D := g.toRingHom.toAlgebra
  haveI : Module.Finite A D := hfin
  haveI : FaithfulSMul A D := (faithfulSMul_iff_algebraMap_injective A D).mpr hinj
  -- `A` is a UFD, hence integrally closed, so the integral extension has going-down.
  haveI : Algebra.HasGoingDown A D := inferInstance
  haveI : IsNoetherianRing D := Algebra.FiniteType.isNoetherianRing ℂ D
  -- `p = M ∩ A` is maximal, since `A ⊆ D` is integral and `M` is maximal.
  let p := M.under A
  have hpmax : p.IsMaximal := Ideal.isMaximal_under_of_isIntegral_of_isMaximal M
  haveI : p.IsPrime := hpmax.isPrime
  haveI : M.LiesOver p := inferInstance
  -- Matsumura's height formula for going-down extensions.
  have hformula := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown (R := A) (S := D) p M
  -- `ht p = s` by the polynomial-ring case.
  have hpht : p.height = (s : ℕ∞) := poly_max_ideal_height s p
  -- Hence `s ≤ ht M`.
  have key : (s : ℕ∞) ≤ M.height := by
    rw [← hpht, hformula]
    exact le_add_right le_rfl
  -- Contracting primes along the integral extension is strictly monotone.
  have hsm : StrictMono (PrimeSpectrum.comap (algebraMap A D)) := by
    intro P Q hPQ
    exact Ideal.IsIntegral.under_lt_under hPQ
  have hdimle : ringKrullDim D ≤ ringKrullDim A := by
    rw [ringKrullDim, ringKrullDim]
    exact Order.krullDim_le_of_strictMono _ hsm
  -- `ringKrullDim A = s`.
  have hdimA : ringKrullDim A = ((s : ℕ∞) : WithBot ℕ∞) := by
    rw [MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite, ringKrullDim_eq_zero_of_field ℂ,
      Nat.card_eq_fintype_card, Fintype.card_fin, zero_add]
    norm_cast
  have hdimle2 : ringKrullDim D ≤ ((s : ℕ∞) : WithBot ℕ∞) := by rw [← hdimA]; exact hdimle
  -- `ht M ≤ ringKrullDim D`, and `s ≤ ht M ≤ ringKrullDim D ≤ s`.
  have hle : ((M.height : ℕ∞) : WithBot ℕ∞) ≤ ringKrullDim D := Ideal.height_le_ringKrullDim_of_isPrime
  refine le_antisymm hle ?_
  calc ringKrullDim D ≤ ((s : ℕ∞) : WithBot ℕ∞) := hdimle2
    _ ≤ ((M.height : ℕ∞) : WithBot ℕ∞) := WithBot.coe_le_coe.mpr key

end Work.BW.RB
