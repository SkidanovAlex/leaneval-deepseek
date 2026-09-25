import Mathlib
import Submission.Work.Tower.CMAdjoin.Basic

open Polynomial NumberField

namespace Work.Tower.CMAdjoin

/-- `4` lies in the conductor of the order `𝓞 L[i]` in `𝓞 (L(i))`.

Equivalently, `4 · 𝓞 (L(i)) ⊆ 𝓞 L[i]`: the order `𝓞 L[i]` has index at most `2` in the
maximal order `𝓞 (L(i))`.

The proof uses the classical identity `𝔣 · 𝔇 = (f'(θ))` for the conductor `𝔣` of `𝓞 L[θ]`,
the different `𝔇` and `f = minpoly (𝓞 L) θ` (`conductor_mul_differentIdeal`).  Here
`θ = iotaInt L` has `f = X ^ 2 + 1`, so `f'(θ) = 2 * θ ∈ 𝔣`; since `𝔣` is an ideal,
also `(2 * θ) ^ 2 = -4 ∈ 𝔣`, hence `4 ∈ 𝔣`. -/
theorem four_mem_conductor (L : Type*) [Field L] [NumberField L] [NumberField.IsTotallyReal L] :
    (4 : NumberField.RingOfIntegers (Work.Tower.CMAdjoin.cmAdjoin L)) ∈
      conductor (NumberField.RingOfIntegers L) (Work.Tower.CMAdjoin.iotaInt L) := by
  have hint : IsIntegral (𝓞 L) (iotaInt L) := Algebra.IsIntegral.isIntegral _
  -- `minpoly L iota = X ^ 2 + 1`
  have hminpolyL : minpoly L (iota L) = sqAddOne L :=
    (minpoly.eq_of_irreducible_of_monic (sqAddOne_irreducible L) (by
      show aeval (iota L) (X ^ 2 + 1 : L[X]) = 0
      simp [iota_sq_add_one]) (sqAddOne_monic L)).symm
  -- `minpoly (𝓞 L) iotaInt = X ^ 2 + 1`, by integral closedness of `𝓞 L` and the field case
  have hmp : minpoly (𝓞 L) (iotaInt L) = sqAddOne (𝓞 L) := by
    apply Polynomial.map_injective (algebraMap (𝓞 L) L) (RingOfIntegers.coe_injective (K := L))
    rw [← minpoly.isIntegrallyClosed_eq_field_fractions L (cmAdjoin L) hint]
    rw [show algebraMap (𝓞 (cmAdjoin L)) (cmAdjoin L) (iotaInt L) = iota L from rfl,
      hminpolyL]
    simp [sqAddOne]
  -- `iota` generates `L(i)` over `L`
  have hx : Algebra.adjoin L {algebraMap (𝓞 (cmAdjoin L)) (cmAdjoin L) (iotaInt L)} = ⊤ := by
    rw [show algebraMap (𝓞 (cmAdjoin L)) (cmAdjoin L) (iotaInt L) = iota L from rfl]
    exact adjoin_iota_eq_top L
  -- the conductor–different identity: `𝔣 * 𝔇 = (f'(θ))`
  have h := conductor_mul_differentIdeal (𝓞 L) L (cmAdjoin L) (iotaInt L) hx
  -- hence `f'(θ) = 2 * θ ∈ 𝔣`
  have hmem : aeval (iotaInt L) (derivative (minpoly (𝓞 L) (iotaInt L))) ∈
      conductor (𝓞 L) (iotaInt L) := by
    have hmem' : aeval (iotaInt L) (derivative (minpoly (𝓞 L) (iotaInt L))) ∈
        conductor (𝓞 L) (iotaInt L) * differentIdeal (𝓞 L) (𝓞 (cmAdjoin L)) := by
      rw [h]
      exact Ideal.mem_span_singleton_self _
    exact Ideal.mul_le_left hmem'
  have h2 : (2 : 𝓞 (cmAdjoin L)) * iotaInt L ∈ conductor (𝓞 L) (iotaInt L) := by
    rw [hmp] at hmem
    simp only [sqAddOne_derivative, map_mul, aeval_X, map_ofNat] at hmem
    exact hmem
  -- `(2 * θ) ^ 2 = -4 ∈ 𝔣`, so also `4 ∈ 𝔣`
  have h4 : ((2 : 𝓞 (cmAdjoin L)) * iotaInt L) * ((2 : 𝓞 (cmAdjoin L)) * iotaInt L) ∈
      conductor (𝓞 L) (iotaInt L) := Ideal.mul_mem_left _ _ h2
  have hneg : (-4 : 𝓞 (cmAdjoin L)) ∈ conductor (𝓞 L) (iotaInt L) := by
    convert h4 using 1
    rw [mul_mul_mul_comm, show iotaInt L * iotaInt L = (-1 : 𝓞 (cmAdjoin L)) from by
      rw [← sq, iotaInt_sq]]
    norm_num
  simpa using neg_mem hneg

end Work.Tower.CMAdjoin
