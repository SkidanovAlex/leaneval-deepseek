import Mathlib
import Submission.Work.BW.RB.height_add_ringKrullDim_quotient_eq
import Submission.Work.BW.RB.maximal_height_eq_ringKrullDim

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The dimension formula for the polynomial ring `ℂ[σ]`

For a finite `σ` and a prime ideal `p` of `R = MvPolynomial σ ℂ` (the polynomial ring in
`|σ|` variables over `ℂ`),

  `ht p + dim (R ⧸ p) = dim R`.

This is the "equidimensional"/catenary dimension formula for affine space: `R` is a regular
local ring at every maximal ideal (in particular Cohen–Macaulay), so the local dimension formula
`ht (p R_𝔪) + dim (R_𝔪 ⧸ p R_𝔪) = dim R_𝔪` holds, and every quantity is unchanged by localizing
at a maximal ideal `𝔪 ⊇ p`.

## Proof

* Choose a maximal ideal `𝔪 ⊇ p`.
* `Work.BW.RB.height_add_ringKrullDim_quotient_eq` gives the formula
  `ht (p R_𝔪) + dim (R_𝔪 ⧸ p R_𝔪) = dim R_𝔪` for the local ring `R_𝔪`.
* Localization preserves the height of `p` (`IsLocalization.height_map_of_disjoint`).
* `dim R_𝔪 = ht 𝔪 = dim R` because `R` is equidimensional
  (`Work.BW.RB.maximal_height_eq_ringKrullDim`), using
  `IsLocalization.AtPrime.ringKrullDim_eq_height`.
* `dim (R_𝔪 ⧸ p R_𝔪) = ht (𝔪 ⧸ p) = dim (R ⧸ p)`, where the first equality is
  `ringKrullDim_localization_atPrime_quotient` below and the second again uses
  equidimensionality of `R ⧸ p`.
-/

set_option linter.style.haveILetI false

open MvPolynomial

namespace Work.BW.RB

/-- The Krull dimension of the localization of `A ⧸ P` at the prime `Q ⧸ P`, i.e. of
`A_Q ⧸ P·A_Q`, equals the height of the image of `Q` in `A ⧸ P`.

Indeed `A_Q ⧸ P·A_Q` is a localization of `A ⧸ P` at the complement of `Q ⧸ P`, so it is a
localization at a prime ideal, whose Krull dimension is the height of that prime
(`IsLocalization.AtPrime.ringKrullDim_eq_height`). -/
theorem ringKrullDim_localization_atPrime_quotient {A : Type*} [CommRing A]
    {P Q : Ideal A} [P.IsPrime] [Q.IsPrime] (hPQ : P ≤ Q) :
    ringKrullDim (Localization.AtPrime Q ⧸ P.map (algebraMap A (Localization.AtPrime Q)))
      = ((Q.map (Ideal.Quotient.mk P)).height : WithBot ℕ∞) := by
  haveI hprime : (Q.map (Ideal.Quotient.mk P)).IsPrime :=
    Ideal.isPrime_map_quotientMk_of_isPrime hPQ
  -- `(Q ⧸ P).comap mk = Q`, since `P ≤ Q`.
  have hcomap : (Q.map (Ideal.Quotient.mk P)).comap (Ideal.Quotient.mk P) = Q := by
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective,
      show Ideal.comap (Ideal.Quotient.mk P) ⊥ = P from by
        rw [← RingHom.ker_eq_comap_bot]; exact Ideal.mk_ker,
      sup_eq_left.mpr hPQ]
  -- The complement of `Q` in `A` maps onto the complement of `Q ⧸ P` in `A ⧸ P`.
  have hN : Algebra.algebraMapSubmonoid (A ⧸ P) Q.primeCompl
      = (Q.map (Ideal.Quotient.mk P)).primeCompl := by
    ext x
    simp only [Algebra.algebraMapSubmonoid, Submonoid.mem_map, Ideal.mem_primeCompl_iff,
      Ideal.Quotient.algebraMap_eq]
    constructor
    · rintro ⟨y, hy, rfl⟩ h
      exact hy (hcomap ▸ (Ideal.mem_comap.mpr h))
    · intro hx
      obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective x
      exact ⟨y, fun hy => hx (Ideal.mem_map_of_mem _ hy), rfl⟩
  -- `A_Q ⧸ P·A_Q` is a localization of `A ⧸ P` at the complement of `Q ⧸ P`.
  haveI : IsLocalization ((Q.map (Ideal.Quotient.mk P)).primeCompl)
      (Localization.AtPrime Q ⧸ P.map (algebraMap A (Localization.AtPrime Q))) :=
    hN ▸ (inferInstance : IsLocalization (Algebra.algebraMapSubmonoid (A ⧸ P) Q.primeCompl) _)
  exact IsLocalization.AtPrime.ringKrullDim_eq_height (Q.map (Ideal.Quotient.mk P)) _

theorem mvpoly_dim_formula {σ : Type*} [Fintype σ] (p : Ideal (MvPolynomial σ ℂ)) [p.IsPrime] :
    ((p.height : ℕ∞) : WithBot ℕ∞) + ringKrullDim (MvPolynomial σ ℂ ⧸ p) =
      ringKrullDim (MvPolynomial σ ℂ) := by
  classical
  -- a maximal ideal containing `p`
  obtain ⟨𝔪, h𝔪max, hp𝔪⟩ := p.exists_le_maximal (Ideal.IsPrime.ne_top' (I := p))
  haveI := h𝔪max.isPrime
  -- `p` is disjoint from the complement of `𝔪`, so `p·R_𝔪` is prime.
  have hdisj : Disjoint (𝔪.primeCompl : Set (MvPolynomial σ ℂ))
      (p : Set (MvPolynomial σ ℂ)) := by
    rw [Set.disjoint_left]
    intro x hx hpx
    exact (Ideal.mem_primeCompl_iff.mp hx) (hp𝔪 hpx)
  haveI hPp : (p.map (algebraMap (MvPolynomial σ ℂ) (Localization.AtPrime 𝔪))).IsPrime :=
    IsLocalization.isPrime_of_isPrime_disjoint 𝔪.primeCompl _ p ‹p.IsPrime› hdisj
  -- The dimension formula in the local ring `R_𝔪`.
  have hlocal := height_add_ringKrullDim_quotient_eq 𝔪
    (p.map (algebraMap (MvPolynomial σ ℂ) (Localization.AtPrime 𝔪)))
  -- Localization does not change the height of `p`.
  have hP : (p.map (algebraMap (MvPolynomial σ ℂ) (Localization.AtPrime 𝔪))).height = p.height :=
    IsLocalization.height_map_of_disjoint 𝔪.primeCompl p hdisj
  -- `dim R_𝔪 = ht 𝔪 = dim R`.
  have hdimS : ringKrullDim (Localization.AtPrime 𝔪) = ringKrullDim (MvPolynomial σ ℂ) := by
    rw [IsLocalization.AtPrime.ringKrullDim_eq_height 𝔪 (Localization.AtPrime 𝔪)]
    exact maximal_height_eq_ringKrullDim (MvPolynomial σ ℂ) 𝔪
  -- `𝔪 ⧸ p` is a maximal ideal of `R ⧸ p`.
  haveI hmax : (𝔪.map (Ideal.Quotient.mk p)).IsMaximal :=
    Ideal.IsMaximal.map_of_surjective_of_ker_le Ideal.Quotient.mk_surjective (by
      rw [RingHom.ker_eq_comap_bot, show Ideal.comap (Ideal.Quotient.mk p) ⊥ = p from by
        rw [← RingHom.ker_eq_comap_bot]; exact Ideal.mk_ker]
      exact hp𝔪)
  -- `dim (R_𝔪 ⧸ p R_𝔪) = ht (𝔪 ⧸ p) = dim (R ⧸ p)`.
  have hquot : ringKrullDim (Localization.AtPrime 𝔪
        ⧸ p.map (algebraMap (MvPolynomial σ ℂ) (Localization.AtPrime 𝔪)))
      = ringKrullDim (MvPolynomial σ ℂ ⧸ p) := by
    rw [ringKrullDim_localization_atPrime_quotient hp𝔪]
    exact maximal_height_eq_ringKrullDim (MvPolynomial σ ℂ ⧸ p) (𝔪.map (Ideal.Quotient.mk p))
  rw [hP, hquot, hdimS] at hlocal
  exact hlocal

end Work.BW.RB
