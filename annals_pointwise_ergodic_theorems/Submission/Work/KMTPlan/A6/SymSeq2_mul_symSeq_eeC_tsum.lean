import Mathlib
import Submission.Work.KMTPlan.A6.SymSeq_coeff1

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.KMTPlan.A6

open MeasureTheory intervalIntegral
open scoped BigOperators ENNReal

noncomputable section

/-- The two-variable kernel `(p,q) ↦ K p q * e(p x + q y)` is summable when `K` is absolutely
summable: the character has unit modulus, so the moduli agree. -/
lemma summable_symSeq2_mul_eeC {K : ℤ → ℤ → ℂ}
    (hK : Summable fun p : ℤ × ℤ => ‖K p.1 p.2‖) (x y : ℝ) :
    Summable fun p : ℤ × ℤ => K p.1 p.2 * eeC (p.1 * x + p.2 * y) := by
  refine Summable.of_norm ?_
  simpa [norm_mul, norm_eeC] using hK

/-- The symbol `symSeq2 K x y`, defined as the iterated series over `ℤ` in each variable, is the
single series over the product index `ℤ × ℤ` (Fubini for absolutely convergent series). -/
lemma symSeq2_eq_tsum_pair {K : ℤ → ℤ → ℂ}
    (hK : Summable fun p : ℤ × ℤ => ‖K p.1 p.2‖) (x y : ℝ) :
    symSeq2 K x y = ∑' p : ℤ × ℤ, K p.1 p.2 * eeC (p.1 * x + p.2 * y) := by
  unfold symSeq2
  exact (summable_symSeq2_mul_eeC hK x y).tsum_prod.symm

/-- **The product of the two symbols is the symbol of the composition, at the level of `tsum`s.**
This is the identity used in the "concrete multiplier" dictionary of §6 of Krause--Mirek--Tao: for
absolutely summable `K`, `κ`, `κ'` the quadruple series defining
`symSeq2 K x y * symSeq κ x * symSeq κ' y` is exactly the product of the three absolutely
convergent series (with the modulation `e(-p₁ x - p₂ y)` kept as a scalar factor). -/
theorem SymSeq2_mul_symSeq_eeC_tsum (K : ℤ → ℤ → ℂ) (κ κ' : ℤ → ℂ)
    (hK : Summable fun p : ℤ × ℤ => ‖K p.1 p.2‖) (hκ : Summable κ) (hκ' : Summable κ')
    (p₁ p₂ : ℤ) (x y : ℝ) :
    Work.KMTPlan.A6.symSeq2 K x y * Work.KMTPlan.A6.symSeq κ x * Work.KMTPlan.A6.symSeq κ' y
        * Work.KMTPlan.A6.eeC (-(p₁ : ℝ) * x - (p₂ : ℝ) * y)
      = ∑' w : (ℤ × ℤ) × (ℤ × ℤ),
          ((K w.1.1 w.1.2 * Work.KMTPlan.A6.eeC (w.1.1 * x + w.1.2 * y))
            * (κ w.2.1 * Work.KMTPlan.A6.eeC (w.2.1 * x)
                * (κ' w.2.2 * Work.KMTPlan.A6.eeC (w.2.2 * y))))
            * Work.KMTPlan.A6.eeC (-(p₁ : ℝ) * x - (p₂ : ℝ) * y) := by
  -- Summability of the three absolutely convergent series.
  have hKnorm : Summable fun p : ℤ × ℤ => ‖K p.1 p.2 * eeC (p.1 * x + p.2 * y)‖ := by
    simpa [norm_mul, norm_eeC] using hK
  have hκnorm : Summable fun c : ℤ => ‖κ c * eeC (c * x)‖ := by
    simpa [norm_mul, norm_eeC] using hκ.norm
  have hκ'norm : Summable fun d : ℤ => ‖κ' d * eeC (d * y)‖ := by
    simpa [norm_mul, norm_eeC] using hκ'.norm
  -- The two-variable series of the `κ, κ'` factors is the product of the two series.
  have hprodB : (∑' b : ℤ × ℤ, (κ b.1 * eeC (b.1 * x)) * (κ' b.2 * eeC (b.2 * y)))
      = (∑' c : ℤ, κ c * eeC (c * x)) * (∑' d : ℤ, κ' d * eeC (d * y)) :=
    (tsum_mul_tsum_of_summable_norm (f := fun c : ℤ => κ c * eeC (c * x))
      (g := fun d : ℤ => κ' d * eeC (d * y)) hκnorm hκ'norm).symm
  have hBnorm : Summable fun b : ℤ × ℤ =>
      ‖(κ b.1 * eeC (b.1 * x)) * (κ' b.2 * eeC (b.2 * y))‖ :=
    hκnorm.mul_norm (f := fun c : ℤ => κ c * eeC (c * x))
      (g := fun d : ℤ => κ' d * eeC (d * y)) hκ'norm
  -- The quadruple series is the product of the `K`-series and the `κ, κ'`-series.
  have hprodA : (∑' w : (ℤ × ℤ) × (ℤ × ℤ),
        (K w.1.1 w.1.2 * eeC (w.1.1 * x + w.1.2 * y))
          * ((κ w.2.1 * eeC (w.2.1 * x)) * (κ' w.2.2 * eeC (w.2.2 * y))))
      = (∑' a : ℤ × ℤ, K a.1 a.2 * eeC (a.1 * x + a.2 * y))
        * (∑' b : ℤ × ℤ, (κ b.1 * eeC (b.1 * x)) * (κ' b.2 * eeC (b.2 * y))) :=
    (tsum_mul_tsum_of_summable_norm
      (f := fun a : ℤ × ℤ => K a.1 a.2 * eeC (a.1 * x + a.2 * y))
      (g := fun b : ℤ × ℤ => (κ b.1 * eeC (b.1 * x)) * (κ' b.2 * eeC (b.2 * y)))
      hKnorm hBnorm).symm
  -- Rewrite the three symbols and squeeze out the scalar modulation.
  rw [symSeq2_eq_tsum_pair hK x y]
  rw [show symSeq κ x = ∑' c : ℤ, κ c * eeC (c * x) from rfl]
  rw [show symSeq κ' y = ∑' d : ℤ, κ' d * eeC (d * y) from rfl]
  rw [tsum_mul_right]
  rw [hprodA, hprodB]
  ring

end

end Work.KMTPlan.A6
