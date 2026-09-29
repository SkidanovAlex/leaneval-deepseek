import Mathlib
import Submission.Work.C7.caseA_setup

/-!
# Area C7 — the elimination step of the "case A" endgame

Given the relation `d·(g 6) + Σⱼ Cⱼ·f5ⱼ = 0` between the primitive `g 6` of the seven-function
system and the five genuine `L`-functions `f5 0 = 1`, `f5 1 = L`, `f5 2 = L²`, `f5 3 = Li₂(x)`,
`f5 4 = J(x)`, we must produce a *polynomial-coefficient* relation among the `f5ⱼ` alone.

The derivation `∂ = x(x-1)²·d/dx` (`Work.C7.dsh`) preserves the `ℚ[x]`-span of
`1, L, L², Li₂(x), J(x), g 6` (`dsh_f5_*`, `hd6`, `hdJ`); applying it to the relation, multiplying
by `d` and replacing `d·(g 6) = -Σⱼ Cⱼ·f5ⱼ` (using the relation itself again) eliminates `g 6` and
leaves exactly the power series `Σⱼ (Bv d C)ⱼ·f5ⱼ` of `Work.C7.Bv`.

Concretely, writing `R = d·(g 6) + Σⱼ Cⱼ·f5ⱼ`, we prove the identity
`Σⱼ (Bv d C)ⱼ·f5ⱼ = d·∂R - (∂d)·R` (`elim_identity`), whence the conclusion is immediate because
`R = 0` kills both terms.
-/

noncomputable section

namespace Work.C7

open PowerSeries
open scoped BigOperators

/-- `(1/2 : ℚ[x])`, viewed in `ℚ⟦x⟧`, is the constant series `PowerSeries.C (1/2)`.  (On `ℚ[x]` the
meaning of `1/2` is Euclidean division, which gives the constant polynomial `C (1/2)`.) -/
lemma coe_half : ((1 / 2 : Polynomial ℚ) : PowerSeries ℚ) = PowerSeries.C (1 / 2 : ℚ) := by
  have h : (1 / 2 : Polynomial ℚ) = Polynomial.C (1 / 2 : ℚ) := by
    rw [show (2 : Polynomial ℚ) = Polynomial.C (2 : ℚ) from
      (Polynomial.C_eq_natCast 2).symm, Polynomial.div_C]
    norm_num
  rw [h, Polynomial.coe_C]

/-- The numeral `2 : ℚ[x]`, viewed in `ℚ⟦x⟧`, is the constant `2`. -/
lemma coe_two : ((2 : Polynomial ℚ) : PowerSeries ℚ) = (2 : PowerSeries ℚ) := by
  rw [show (2 : Polynomial ℚ) = Polynomial.C (2 : ℚ) from (Polynomial.C_eq_natCast 2).symm,
    Polynomial.coe_C]
  exact map_natCast PowerSeries.C 2

/-- **The elimination identity of the `A`-side endgame.**  For `R = d·(g 6) + Σⱼ Cⱼ·f5ⱼ`,

  `Σⱼ (Bv d C)ⱼ·f5ⱼ = d·∂R - (∂d)·R`,

where `∂(g 6)` is substituted using `hd6` and `∂J` using `hdJ`.  (The `g 6`-terms cancel between
`d·∂R` and `(∂d)·R` precisely because `R` contains `d·(g 6)`.) -/
lemma elim_identity
    (hd6 : Work.C7.dsh (Work.C7.g 6) = PowerSeries.X * (PowerSeries.X - 2) ^ 2 *
      (2 * Work.C7.Li2ps + PowerSeries.C (1 / 2 : ℚ) * Work.C7.Lps ^ 2))
    (hdJ : Work.C7.dsh Work.C7.Jps
      = PowerSeries.C (1 / 2 : ℚ) * (PowerSeries.X * (PowerSeries.X - 1)) * Work.C7.Jps
        - (PowerSeries.X - 1) ^ 2 * Work.C7.Lps)
    (d : Polynomial ℚ) (C : Fin 5 → Polynomial ℚ) :
    ∑ j, (Bv d C j : PowerSeries ℚ) * f5 j
      = (d : PowerSeries ℚ) * dsh ((d : PowerSeries ℚ) * g 6
          + ∑ j, (C j : PowerSeries ℚ) * f5 j)
        - ((dshP d : Polynomial ℚ) : PowerSeries ℚ) * ((d : PowerSeries ℚ) * g 6
          + ∑ j, (C j : PowerSeries ℚ) * f5 j) := by
  -- expand `∂R`
  have h_dshR : dsh ((d : PowerSeries ℚ) * g 6 + ∑ j, (C j : PowerSeries ℚ) * f5 j)
      = ((dshP d : Polynomial ℚ) : PowerSeries ℚ) * g 6
        + (d : PowerSeries ℚ) * (PowerSeries.X * (PowerSeries.X - 2) ^ 2
            * (2 * Li2ps + PowerSeries.C (1 / 2 : ℚ) * Lps ^ 2))
        + ∑ j, (((dshP (C j) : Polynomial ℚ) : PowerSeries ℚ) * f5 j
            + (C j : PowerSeries ℚ) * dsh (f5 j)) := by
    rw [dsh_add, dsh_mul, dsh_coe, hd6, dsh_sum]
    congr 1
    exact Finset.sum_congr rfl (fun j _ => by rw [dsh_mul, dsh_coe])
  rw [h_dshR]
  -- expand the finitely many sums and substitute `∂` of the five basis functions
  simp only [Fin.sum_univ_five, Bv_zero, Bv_one, Bv_two, Bv_three, Bv_four,
    f5_zero, f5_one, f5_two, f5_three, f5_four,
    dsh_one, dsh_Lps, dsh_Lps_sq, dsh_Li2ps, hdJ]
  push_cast
  -- move the two numerical coercions into `ℚ⟦x⟧` and finish by commutativity of `ℚ⟦x⟧`
  rw [coe_two, coe_half]
  ring

theorem caseA_rel
    (hd6 : Work.C7.dsh (Work.C7.g 6) = PowerSeries.X * (PowerSeries.X - 2) ^ 2 *
      (2 * Work.C7.Li2ps + PowerSeries.C (1 / 2 : ℚ) * Work.C7.Lps ^ 2))
    (hdJ : Work.C7.dsh Work.C7.Jps
      = PowerSeries.C (1 / 2 : ℚ) * (PowerSeries.X * (PowerSeries.X - 1)) * Work.C7.Jps
        - (PowerSeries.X - 1) ^ 2 * Work.C7.Lps)
    (d : Polynomial ℚ) (C : Fin 5 → Polynomial ℚ)
    (h : (d : PowerSeries ℚ) * Work.C7.g 6
      + ∑ j, (C j : PowerSeries ℚ) * Work.C7.f5 j = 0) :
    ∑ j, (Work.C7.Bv d C j : PowerSeries ℚ) * Work.C7.f5 j = 0 := by
  rw [elim_identity hd6 hdJ d C, h]
  simp

end Work.C7
