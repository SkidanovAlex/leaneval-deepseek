import Mathlib
import Submission.Work.C7.seven_setup
import Submission.Work.C7.caseA_setup
import Submission.Work.C7.caseA_rel
import Submission.Work.C7.caseA_rat

namespace Work.C7

/-- **Case A of the `seven`-independence argument.**  A relation `d·(g 6) + Σⱼ Cⱼ·f5ⱼ = 0` with
`d ≠ 0` between the primitive `g 6 = B₇∘y` and the five `ℚ[x]`-independent functions
`1, L, L², Li₂(x), J(x)` is impossible.

Applying `∂ = x(x-1)²·d/dx` to the relation, multiplying by `d` and replacing `d·(g 6)` by
`-Σⱼ Cⱼ·f5ⱼ` (`Work.C7.caseA_rel`) produces a polynomial-coefficient relation `Σⱼ (Bv d C)ⱼ f5ⱼ = 0`;
`PolyIndependent f5` (`hind`) then kills the `Li₂`-coefficient `(Bv d C) 3`, which by
`Work.C7.Bv_three_factored` reads `x·((x-1)²·(d·(C 3)' - d'·(C 3)) + 2d²(x-2)²) = 0`, i.e.
`(C 3/d)' = -2(x-2)²/(x-1)²`, contradicting `hN1` (`Work.C7.rat_ode2`) via `Work.C7.caseA_rat`. -/
theorem caseA_end
    (hd6 : Work.C7.dsh (Work.C7.g 6) = PowerSeries.X * (PowerSeries.X - 2) ^ 2 *
      (2 * Work.C7.Li2ps + PowerSeries.C (1 / 2 : ℚ) * Work.C7.Lps ^ 2))
    (hdJ : Work.C7.dsh Work.C7.Jps
      = PowerSeries.C (1 / 2 : ℚ) * (PowerSeries.X * (PowerSeries.X - 1)) * Work.C7.Jps
        - (PowerSeries.X - 1) ^ 2 * Work.C7.Lps)
    (hind : Submission.CDTPlan.PolyIndependent Work.C7.f5)
    (hN1 : ∀ δ : RatFunc ℚ, Submission.CDT.dRat δ
      ≠ 2 * (RatFunc.X - 2) ^ 2 * ((RatFunc.X - 1) ^ 2)⁻¹)
    (d : Polynomial ℚ) (hd : d ≠ 0) (C : Fin 5 → Polynomial ℚ)
    (h : (d : PowerSeries ℚ) * Work.C7.g 6
      + ∑ j, (C j : PowerSeries ℚ) * Work.C7.f5 j = 0) : False := by
  -- the derived polynomial-coefficient relation among the `f5ⱼ`
  have hB := Work.C7.caseA_rel hd6 hdJ d C h
  -- `PolyIndependent f5` kills the `Li₂`-coefficient
  have h3 : Work.C7.Bv d C 3 = 0 := hind (Work.C7.Bv d C) hB 3
  rw [Work.C7.Bv_three_factored] at h3
  have hinner : (Polynomial.X - 1) ^ 2 * ((C 3).derivative * d - (C 3) * d.derivative)
      + 2 * d ^ 2 * (Polynomial.X - 2) ^ 2 = 0 := by
    rcases mul_eq_zero.mp h3 with hX | hx
    · exact absurd hX Polynomial.X_ne_zero
    · exact hx
  exact Work.C7.caseA_rat d (C 3) hd hN1 hinner

end Work.C7
