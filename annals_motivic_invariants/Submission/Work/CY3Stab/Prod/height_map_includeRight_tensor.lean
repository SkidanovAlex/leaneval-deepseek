import Mathlib
import Submission.Work.CY3Stab.Prod.height_map_mvPolynomial
import Submission.Work.CY3Stab.Prod.height_le_height_of_flat
import Submission.Work.CY3Stab.Prod.height_map_includeRight_tensor_transfer
import Submission.Work.CY3Stab.Prod.exists_ltSeries_restrict_mvPolynomial

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

set_option linter.style.haveILetI false

namespace Work.CY3Stab.Prod

/-- **Matsumura's height formula for finitely many variables.**  If `A` is Noetherian and `𝔭 ≤ A`
is prime, then for a *finite* set of variables `s` the extension `𝔭 · A[X_s]` has the same height
as `𝔭`: the fibre `(A ⧸ 𝔭)[X_s]` has height `0`, and `MvPolynomial s A` is Noetherian, so
`Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown` applies. -/
theorem height_map_algebraMap_mvPolynomial_finite {A : Type} [CommRing A] [IsNoetherianRing A]
    (𝔭 : Ideal A) [𝔭.IsPrime] (s : Type) [Finite s] :
    (𝔭.map (algebraMap A (MvPolynomial s A))).height = 𝔭.height := by
  haveI : IsNoetherianRing (MvPolynomial s A) := inferInstance
  have hP : (𝔭.map (algebraMap A (MvPolynomial s A))).IsPrime :=
    isPrime_map_algebraMap ‹𝔭.IsPrime› s
  haveI := hP
  haveI : (𝔭.map (algebraMap A (MvPolynomial s A))).LiesOver 𝔭 :=
    ⟨(comap_map_algebraMap_eq 𝔭 s).symm⟩
  have h := Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown 𝔭
    (𝔭.map (algebraMap A (MvPolynomial s A)))
  rw [Ideal.map_quotient_self, Ideal.height_bot, add_zero] at h
  exact h

/-- **Height is preserved by polynomial extensions.**  For a Noetherian commutative ring `A`, a
prime ideal `𝔭 ≤ A` and any type `σ` of variables, the height of the extension `𝔭 · A[X_σ]` equals
the height of `𝔭`.

The inequality `ht (𝔭 · A[X_σ]) ≥ ht 𝔭` holds for any flat algebra
(`Work.CY3Stab.Prod.height_le_height_of_flat`).  For the converse, any chain of primes below
`𝔭 · A[X_σ]` only involves finitely many variables
(`Work.CY3Stab.Prod.exists_ltSeries_restrict_mvPolynomial`), where the finite case above applies. -/
theorem height_map_algebraMap_mvPolynomial {A : Type} [CommRing A] [IsNoetherianRing A]
    (𝔭 : Ideal A) [𝔭.IsPrime] (σ : Type) :
    (𝔭.map (algebraMap A (MvPolynomial σ A))).height = 𝔭.height := by
  refine le_antisymm ?_ ?_
  · have hP : (𝔭.map (algebraMap A (MvPolynomial σ A))).IsPrime :=
      isPrime_map_algebraMap ‹𝔭.IsPrime› σ
    have key : Order.height (⟨𝔭.map (algebraMap A (MvPolynomial σ A)), hP⟩ : PrimeSpectrum _)
        ≤ 𝔭.height := by
      refine Order.height_le_iff.mpr ?_
      intro L hL
      obtain ⟨s, hsf, L', hlen, hle⟩ := exists_ltSeries_restrict_mvPolynomial σ 𝔭 L hL
      haveI : Finite s := hsf
      rw [← hlen]
      calc (L'.length : ℕ∞) ≤ Order.height L'.last := Order.length_le_height_last
        _ = (L'.last).asIdeal.height := (PrimeSpectrum.height_eq_orderHeight L'.last).symm
        _ ≤ (𝔭.map (algebraMap A (MvPolynomial s A))).height := Ideal.height_mono hle
        _ = 𝔭.height := height_map_algebraMap_mvPolynomial_finite 𝔭 s
    rwa [← PrimeSpectrum.height_eq_orderHeight
      (⟨𝔭.map (algebraMap A (MvPolynomial σ A)), hP⟩ : PrimeSpectrum _)] at key
  · haveI : (𝔭.map (algebraMap A (MvPolynomial σ A))).IsPrime :=
      isPrime_map_algebraMap ‹𝔭.IsPrime› σ
    exact height_le_height_of_flat 𝔭 (𝔭.map (algebraMap A (MvPolynomial σ A)))
      ⟨(comap_map_algebraMap_eq 𝔭 σ).symm⟩

open TensorProduct

/-- **The height of an extended prime in a polynomial algebra over the base.**
For a Noetherian ring `A`, a prime `𝔭 ≤ A` and any type `σ` of variables, the extension of `𝔭`
to `MvPolynomial σ 𝕜 ⊗[𝕜] A` has the same height as `𝔭`: `ht (𝔭 · A[X_σ]) = ht 𝔭`.

Proof: `MvPolynomial σ 𝕜 ⊗[𝕜] A ≅ MvPolynomial σ A` as `𝕜`-algebras, carrying `includeRight` to
`algebraMap A (MvPolynomial σ A)`, so the height is that of `𝔭 · A[X_σ]`
(`Work.CY3Stab.Prod.height_map_includeRight_tensor_transfer`), and polynomial extension of a prime
preserves the height (`Work.CY3Stab.Prod.height_map_algebraMap_mvPolynomial`). -/
theorem height_map_includeRight_tensor (𝕜 : Type) [Field 𝕜] (σ : Type) (A : Type) [CommRing A]
    [Algebra 𝕜 A] [IsNoetherianRing A] (𝔭 : Ideal A) [𝔭.IsPrime] :
    (Ideal.map (Algebra.TensorProduct.includeRight (R := 𝕜) (A := MvPolynomial σ 𝕜) (B := A)).toRingHom
      𝔭).height = 𝔭.height := by
  rw [height_map_includeRight_tensor_transfer 𝕜 σ A 𝔭]
  exact height_map_algebraMap_mvPolynomial 𝔭 σ

end Work.CY3Stab.Prod
