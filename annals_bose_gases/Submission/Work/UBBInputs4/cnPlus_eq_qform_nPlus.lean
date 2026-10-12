import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.UBBInputs4.ExtClass
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.UBBInputs4

open MeasureTheory
open scoped Topology Real BigOperators
open Submission.BoseGases

set_option autoImplicit false

/-- The self-pairing of the excited part: `∫ (QᵢΦ)·Φ = ∫ (QᵢΦ)²`.

This is the orthogonality `⟨PᵢΦ, QᵢΦ⟩ = 0` (`aQ_ortho_box`) combined with the
pointwise decomposition `QᵢΦ = Φ − PᵢΦ`:
`(QᵢΦ)·Φ = (QᵢΦ)² + (PᵢΦ)·(QᵢΦ)`, and the second term integrates to `0`. -/
lemma aQ_int_mul_self_eq_sq {N : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) (i : Fin N) {Φ : X N → ℝ}
    (hΦc : Continuous Φ) :
    (∫ x in abox N ℓ, aQ ℓ i Φ x * Φ x) = ∫ x in abox N ℓ, (aQ ℓ i Φ x) ^ 2 := by
  have hIntQ2 : IntegrableOn (fun x : X N => (aQ ℓ i Φ x) ^ 2) (abox N ℓ) volume :=
    integrableOn_sq_aQ hℓ i hΦc
  have hIntPQ : IntegrableOn (fun x : X N => aP ℓ i Φ x * aQ ℓ i Φ x) (abox N ℓ) volume := by
    have h1 : IntegrableOn (fun x : X N => aP ℓ i Φ x * Φ x) (abox N ℓ) volume := by
      have h := integrableOn_mul_aP hℓ i hΦc hΦc
      rw [show (fun x : X N => aP ℓ i Φ x * Φ x) = (fun x : X N => Φ x * aP ℓ i Φ x) from by
            funext x; rw [mul_comm]]
      exact h
    have h2 : IntegrableOn (fun x : X N => (aP ℓ i Φ x) ^ 2) (abox N ℓ) volume :=
      integrableOn_sq_aP hℓ i hΦc
    rw [show (fun x : X N => aP ℓ i Φ x * aQ ℓ i Φ x)
          = (fun x : X N => aP ℓ i Φ x * Φ x) - (fun x : X N => (aP ℓ i Φ x) ^ 2) from by
          funext x; simp only [Pi.sub_apply]; unfold aQ; ring]
    exact h1.sub h2
  have key : (∫ x in abox N ℓ, aQ ℓ i Φ x * Φ x)
      = ∫ x in abox N ℓ, ((aQ ℓ i Φ x) ^ 2 + aP ℓ i Φ x * aQ ℓ i Φ x) := by
    apply integral_congr_ae
    filter_upwards with x
    unfold aQ
    ring
  rw [key, integral_add hIntQ2 hIntPQ, aQ_ortho_box hℓ i hΦc, add_zero]

/-- **`n₊` as a quadratic form.**  The excited-particle count `cnPlus = Σᵢ∫(QᵢΦ)²`
equals the quadratic form `∫ (Σᵢ QᵢΦ)·Φ` of the operator `Σᵢ Qᵢ`, because each
`Qᵢ` is the orthogonal projection onto the complement of the constants, so
`∫ (QᵢΦ)² = ∫ (QᵢΦ)·Φ`, and the finite sum exchanges with the integral. -/
theorem cnPlus_eq_qform_nPlus {N : ℕ} {L : ℝ}
    {Φ : (Fin N → EuclideanSpace ℝ (Fin 3)) → ℝ} (hL : 0 < L) (hΦ : Continuous Φ) :
    Submission.BoseGases.cnPlus L Φ
      = ∫ x in Submission.BoseGases.abox N L,
          (∑ i : Fin N, Submission.BoseGases.aQ L i Φ x) * Φ x := by
  have hIntQ : ∀ i : Fin N, IntegrableOn (fun x : X N => aQ L i Φ x * Φ x) (abox N L) volume := by
    intro i
    have h1 : IntegrableOn (fun x : X N => (Φ x) ^ 2) (abox N L) volume :=
      integrableOn_abox_of_continuous hL (hΦ.pow 2)
    have h2 : IntegrableOn (fun x : X N => aP L i Φ x * Φ x) (abox N L) volume := by
      have h := integrableOn_mul_aP hL i hΦ hΦ
      rw [show (fun x : X N => aP L i Φ x * Φ x) = (fun x : X N => Φ x * aP L i Φ x) from by
            funext x; rw [mul_comm]]
      exact h
    rw [show (fun x : X N => aQ L i Φ x * Φ x)
          = (fun x : X N => (Φ x) ^ 2) - (fun x : X N => aP L i Φ x * Φ x) from by
          funext x; simp only [Pi.sub_apply]; unfold aQ; ring]
    exact h1.sub h2
  unfold Submission.BoseGases.cnPlus
  rw [show (∫ x in abox N L, (∑ i : Fin N, aQ L i Φ x) * Φ x)
        = ∑ i : Fin N, ∫ x in abox N L, aQ L i Φ x * Φ x from by
        rw [show (∫ x in abox N L, (∑ i : Fin N, aQ L i Φ x) * Φ x)
              = ∫ x in abox N L, (∑ i : Fin N, aQ L i Φ x * Φ x) from by
              apply integral_congr_ae
              filter_upwards with x
              rw [Finset.sum_mul]]
        exact integral_finsetSum Finset.univ (fun i _ => hIntQ i)]
  exact Finset.sum_congr rfl (fun i _ => (aQ_int_mul_self_eq_sq hL i hΦ).symm)

end Work.UBBInputs4
