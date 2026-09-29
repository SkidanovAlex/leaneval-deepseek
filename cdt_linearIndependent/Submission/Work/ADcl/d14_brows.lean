import Mathlib
import Submission.Work.ADcl.yode14_defs

/-!
# `Work.ADcl.d14_brows`: the `B`-rows of the 14-tuple's `D`-closure

Given the `D`-closure data `(q₀, A₀)` of the seven pure functions
`Submission.CDTPlan.pureB = ![B₁,…,B₇]`,

  `q₀ · (pureB k)' = Σ_m A₀ k m · pureB m`   for all `k : Fin 7`,

the rows of the coefficient matrix `A14` of `Work.ADcl.yode14_defs` indexed by the `B`-slots
`eIdx14 k` of `Submission.CDTPlan.fourteen a b c` produce the corresponding `D`-closure relation
with the common denominator `QF q0 q = X⁴ · q₀ · q`.

The only work is the reindexing of the 14-term sum onto the seven `B`-slots via `eIdx14`
(the remaining seven slots carry `G, G', G'', G'''` and the three integrals, where every entry of
the row `q · rowB14 q0 A0 k` vanishes).
-/

namespace Work.ADcl

open PowerSeries Polynomial

noncomputable section

/-- The sum of the row `q · rowB14 q0 A0 a` against the fourteen functions is the `B`-row of
`pureB`, rescaled by `q · X⁴`. -/
lemma rowB14_sum (q0 q : Polynomial ℚ) (A0 : Fin 7 → Fin 7 → Polynomial ℚ) (a : Fin 7)
    (p r s : ℤ) :
    (∑ j : Fin 14, ((q * rowB14 q0 A0 a j : Polynomial ℚ) : PowerSeries ℚ)
        * Submission.CDTPlan.fourteen p r s j)
    = (q : PowerSeries ℚ) * ((Polynomial.X ^ 4 : Polynomial ℚ) : PowerSeries ℚ)
        * ∑ k : Fin 7, (A0 a k : PowerSeries ℚ) * Submission.CDTPlan.pureB k := by
  rw [sum_eIdx14 (fun j => ((q * rowB14 q0 A0 a j : Polynomial ℚ) : PowerSeries ℚ)
        * Submission.CDTPlan.fourteen p r s j)
      (fun j hj => by rw [rowB14_zero q0 A0 a hj, mul_zero, Polynomial.coe_zero, zero_mul])]
  have hb : ∀ b' : Fin 7,
      ((q * rowB14 q0 A0 a (eIdx14 b') : Polynomial ℚ) : PowerSeries ℚ)
        * Submission.CDTPlan.fourteen p r s (eIdx14 b')
      = (q : PowerSeries ℚ) * (((Polynomial.X ^ 4 : Polynomial ℚ) : PowerSeries ℚ)
        * ((A0 a b' : PowerSeries ℚ) * Submission.CDTPlan.pureB b')) := by
    intro b'
    rw [rowB14_eIdx14, fourteen_eIdx14, Polynomial.coe_mul, Polynomial.coe_mul]
    ring
  rw [Finset.sum_congr rfl (fun b' _ => hb b')]
  rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i _ => by ring)

theorem d14_brows (q0 q : Polynomial ℚ) (A0 : Fin 7 → Fin 7 → Polynomial ℚ)
    (A : Fin 4 → Polynomial ℚ) (cc : Polynomial ℚ) (a b c : ℤ)
    (hA0 : ∀ k : Fin 7, (q0 : PowerSeries ℚ) *
        PowerSeries.derivative (R := ℚ) (Submission.CDTPlan.pureB k)
        = ∑ m, (A0 k m : PowerSeries ℚ) * Submission.CDTPlan.pureB m)
    (i : Fin 7) :
    (Work.ADcl.QF q0 q : PowerSeries ℚ) *
        PowerSeries.derivative (R := ℚ) (Submission.CDTPlan.fourteen a b c (Work.ADcl.eIdx14 i))
      = ∑ j, (Work.ADcl.A14 q0 q A0 A cc (Submission.CDTPlan.GZ a b c) (Work.ADcl.eIdx14 i) j :
            PowerSeries ℚ) * Submission.CDTPlan.fourteen a b c j := by
  rw [fourteen_eIdx14]
  rw [show (∑ j : Fin 14, (A14 q0 q A0 A cc (Submission.CDTPlan.GZ a b c) (eIdx14 i) j :
          PowerSeries ℚ) * Submission.CDTPlan.fourteen a b c j)
      = ∑ j : Fin 14, ((q * rowB14 q0 A0 i j : Polynomial ℚ) : PowerSeries ℚ)
          * Submission.CDTPlan.fourteen a b c j from
      Finset.sum_congr rfl (fun j _ => by rw [A14_Brow])]
  rw [rowB14_sum q0 q A0 i a b c, ← hA0 i]
  rw [QF, Polynomial.coe_mul, Polynomial.coe_mul]
  ring

end

end Work.ADcl
