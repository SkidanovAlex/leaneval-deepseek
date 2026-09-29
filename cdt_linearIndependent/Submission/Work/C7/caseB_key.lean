import Mathlib
import Submission.Work.C7.seven_setup

/-!
# Area C7 — the "case B" key identity (`Work.C7.caseB_key`)

We are given a `ℚ[x]`-relation

  `d·(g 5 + λ·g 6) + Σⱼ Cⱼ·f5ⱼ = 0`

among the five `ℚ(x)`-independent functions `f5 = (1, L, L², Li₂, J)` (`hind`) and the two
"integral" functions `g 5`, `g 6` whose `∂`-derivatives (`∂ = x(x-1)²·d/dx`, `Work.C7.dsh`)
are known (`hd5`, `hd6`; `hdJ` for `J`).

Applying `∂` to the relation, multiplying by `d` and using `d·(g 5 + λ g 6) = -Σⱼ Cⱼ f5ⱼ` produces
a new `ℚ[x]`-relation `Σⱼ (Bcoef λ d C)ⱼ·f5ⱼ = 0` (`bcoef_rel`).  `PolyIndependent f5` then forces
every `Bcoef` coefficient to vanish; the coefficient of `L² = f5 2` is

  `-(d·(C 2)'·x(x-1)² - d'·(C 2)·x(x-1)²) + d²·(C(-1/2)(x-1)(x-2) + λ·(1/2)·x(x-2)²)`,

and its vanishing is exactly the desired identity `caseB_key`.
-/

noncomputable section

set_option linter.unusedVariables false

namespace Work.C7

open PowerSeries
open scoped BigOperators

/-- The coefficient vector of the `∂`-elimination of the relation
`d·(g 5 + λ g 6) + Σⱼ Cⱼ f5ⱼ = 0` (see `Work.C7.bcoef_rel`). -/
def Bcoef (lam : ℚ) (d : Polynomial ℚ) (C : Fin 5 → Polynomial ℚ) : Fin 5 → Polynomial ℚ :=
  ![ -(dshP d) * (C 0) + d * dshP (C 0) + d * (C 1) * (Polynomial.X * (Polynomial.X - 1)),
     -(dshP d) * (C 1) + d * dshP (C 1) + d * (C 2) * (2 * Polynomial.X * (Polynomial.X - 1))
       - d * (C 3) * ((Polynomial.X - 1) ^ 2) - d * (C 4) * ((Polynomial.X - 1) ^ 2),
     -(dshP d) * (C 2) + d * dshP (C 2)
       + d ^ 2 * (Polynomial.C (-(1/2)) * (Polynomial.X - 1) * (Polynomial.X - 2)
           + Polynomial.C lam * Polynomial.C (1/2) * Polynomial.X * (Polynomial.X - 2) ^ 2),
     -(dshP d) * (C 3) + d * dshP (C 3)
       + d ^ 2 * (2 * Polynomial.C lam * Polynomial.X * (Polynomial.X - 2) ^ 2),
     -(dshP d) * (C 4) + d * dshP (C 4)
       + d * (C 4) * (Polynomial.C (1/2) * Polynomial.X * (Polynomial.X - 1)) ]

/-- `((2 : ℚ[X]) : ℚ⟦X⟧) = 2` for the specific coercion (used to align the numeral coercions
in the coefficient computation). -/
lemma coe_two_ps : ((2 : Polynomial ℚ) : PowerSeries ℚ) = 2 :=
  map_ofNat Polynomial.coeToPowerSeries.ringHom 2

/-- The coefficient of `L²` in the derived relation, read off from `Bcoef`. -/
lemma bcoef_two (lam : ℚ) (d : Polynomial ℚ) (C : Fin 5 → Polynomial ℚ) :
    Bcoef lam d C 2 = -(dshP d * C 2 - d * dshP (C 2))
      + d ^ 2 * (Polynomial.C (-(1 / 2)) * (Polynomial.X - 1) * (Polynomial.X - 2)
          + Polynomial.C lam * Polynomial.C (1 / 2) * Polynomial.X * (Polynomial.X - 2) ^ 2) := by
  simp [Bcoef]
  ring

/-- **The derivation step.**  Multiplying `∂` of the relation by `d` and clearing `g 5`, `g 6`
gives a `ℚ[x]`-coefficient relation whose coefficient vector is `Bcoef`. -/
lemma bcoef_key
    (hd5 : Work.C7.dsh (Work.C7.g 5)
      = PowerSeries.C (-(1 / 2) : ℚ) * (PowerSeries.X - 1) * (PowerSeries.X - 2)
        * Work.C7.Lps ^ 2)
    (hd6 : Work.C7.dsh (Work.C7.g 6) = PowerSeries.X * (PowerSeries.X - 2) ^ 2 *
      (2 * Work.C7.Li2ps + PowerSeries.C (1 / 2 : ℚ) * Work.C7.Lps ^ 2))
    (hdJ : Work.C7.dsh Work.C7.Jps
      = PowerSeries.C (1 / 2 : ℚ) * (PowerSeries.X * (PowerSeries.X - 1)) * Work.C7.Jps
        - (PowerSeries.X - 1) ^ 2 * Work.C7.Lps)
    (lam : ℚ) (d : Polynomial ℚ) (C : Fin 5 → Polynomial ℚ)
    (h : (d : PowerSeries ℚ) * (Work.C7.g 5 + PowerSeries.C lam * Work.C7.g 6)
      + ∑ j, (C j : PowerSeries ℚ) * Work.C7.f5 j = 0) :
    (d : PowerSeries ℚ) * dsh ((d : PowerSeries ℚ)
        * (Work.C7.g 5 + PowerSeries.C lam * Work.C7.g 6)
      + ∑ j, (C j : PowerSeries ℚ) * Work.C7.f5 j)
      = ∑ j, (Bcoef lam d C j : PowerSeries ℚ) * Work.C7.f5 j := by
  have hG : dsh (g 5 + PowerSeries.C lam * g 6)
      = PowerSeries.C (-(1/2) : ℚ) * (PowerSeries.X - 1) * (PowerSeries.X - 2) * Lps ^ 2
        + PowerSeries.C lam * (PowerSeries.X * (PowerSeries.X - 2) ^ 2 *
          (2 * Li2ps + PowerSeries.C (1/2 : ℚ) * Lps ^ 2)) := by
    rw [dsh_add, dsh_smul_C, hd5, hd6]
  have hS : dsh (∑ j : Fin 5, (C j : PowerSeries ℚ) * f5 j)
      = ∑ j : Fin 5, ((dshP (C j) : PowerSeries ℚ) * f5 j
          + (C j : PowerSeries ℚ) * dsh (f5 j)) := by
    rw [dsh_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [dsh_mul, dsh_coe]
  have hDG' : (d : PowerSeries ℚ) * (g 5 + PowerSeries.C lam * g 6)
      = -((C 0 : PowerSeries ℚ) + (C 1 : PowerSeries ℚ) * Lps
          + (C 2 : PowerSeries ℚ) * Lps ^ 2 + (C 3 : PowerSeries ℚ) * Li2ps
          + (C 4 : PowerSeries ℚ) * Jps) := by
    have hh : (d : PowerSeries ℚ) * (g 5 + PowerSeries.C lam * g 6)
        = -(∑ j, (C j : PowerSeries ℚ) * f5 j) := by linear_combination h
    rw [hh, Fin.sum_univ_five]
    simp only [f5_zero, f5_one, f5_two, f5_three, f5_four]
    ring
  rw [dsh_add, dsh_mul, dsh_coe, hG, hS]
  rw [Fin.sum_univ_five, Fin.sum_univ_five]
  simp only [f5_zero, f5_one, f5_two, f5_three, f5_four, dsh_one, dsh_Lps, dsh_Lps_sq,
    dsh_Li2ps, hdJ]
  simp only [Bcoef]
  push_cast
  rw [coe_two_ps]
  linear_combination ((dshP d : Polynomial ℚ) : PowerSeries ℚ) * hDG'

/-- The derived relation among the five basis functions. -/
lemma bcoef_rel
    (hd5 : Work.C7.dsh (Work.C7.g 5)
      = PowerSeries.C (-(1 / 2) : ℚ) * (PowerSeries.X - 1) * (PowerSeries.X - 2)
        * Work.C7.Lps ^ 2)
    (hd6 : Work.C7.dsh (Work.C7.g 6) = PowerSeries.X * (PowerSeries.X - 2) ^ 2 *
      (2 * Work.C7.Li2ps + PowerSeries.C (1 / 2 : ℚ) * Work.C7.Lps ^ 2))
    (hdJ : Work.C7.dsh Work.C7.Jps
      = PowerSeries.C (1 / 2 : ℚ) * (PowerSeries.X * (PowerSeries.X - 1)) * Work.C7.Jps
        - (PowerSeries.X - 1) ^ 2 * Work.C7.Lps)
    (lam : ℚ) (d : Polynomial ℚ) (C : Fin 5 → Polynomial ℚ)
    (h : (d : PowerSeries ℚ) * (Work.C7.g 5 + PowerSeries.C lam * Work.C7.g 6)
      + ∑ j, (C j : PowerSeries ℚ) * Work.C7.f5 j = 0) :
    ∑ j, (Bcoef lam d C j : PowerSeries ℚ) * Work.C7.f5 j = 0 := by
  have key := bcoef_key hd5 hd6 hdJ lam d C h
  rw [h, dsh_zero, mul_zero] at key
  exact key.symm

theorem caseB_key
    (hd5 : Work.C7.dsh (Work.C7.g 5)
      = PowerSeries.C (-(1 / 2) : ℚ) * (PowerSeries.X - 1) * (PowerSeries.X - 2)
        * Work.C7.Lps ^ 2)
    (hd6 : Work.C7.dsh (Work.C7.g 6) = PowerSeries.X * (PowerSeries.X - 2) ^ 2 *
      (2 * Work.C7.Li2ps + PowerSeries.C (1 / 2 : ℚ) * Work.C7.Lps ^ 2))
    (hdJ : Work.C7.dsh Work.C7.Jps
      = PowerSeries.C (1 / 2 : ℚ) * (PowerSeries.X * (PowerSeries.X - 1)) * Work.C7.Jps
        - (PowerSeries.X - 1) ^ 2 * Work.C7.Lps)
    (hind : Submission.CDTPlan.PolyIndependent Work.C7.f5)
    (lam : ℚ) (d : Polynomial ℚ) (hd : d ≠ 0) (C : Fin 5 → Polynomial ℚ)
    (h : (d : PowerSeries ℚ) * (Work.C7.g 5 + PowerSeries.C lam * Work.C7.g 6)
      + ∑ j, (C j : PowerSeries ℚ) * Work.C7.f5 j = 0) :
    Work.C7.dshP d * C 2 - d * Work.C7.dshP (C 2)
      = d ^ 2 * (Polynomial.C (-(1 / 2)) * (Polynomial.X - 1) * (Polynomial.X - 2)
          + Polynomial.C lam * Polynomial.C (1 / 2) * Polynomial.X * (Polynomial.X - 2) ^ 2) := by
  have hrel : ∑ j, (Bcoef lam d C j : PowerSeries ℚ) * Work.C7.f5 j = 0 :=
    bcoef_rel hd5 hd6 hdJ lam d C h
  have h2 : Bcoef lam d C 2 = 0 := hind (Bcoef lam d C) hrel 2
  have hbt := bcoef_two lam d C
  rw [hbt] at h2
  linear_combination -h2

end Work.C7
