import Mathlib
import Submission.Work.C7.seven_setup

/-!
# Area C7 — closure of the `ℚ[x]`-span of `f5 0,…,f5 4, g 5, g 6` under `∂`

With `∂ = x(x-1)²·d/dx` (`Work.C7.dsh`) the derivations of the "integral" functions `g 5`, `g 6`
and of the fifth basis function `J = f5 4` land in the `ℚ[x]`-span of the five basis functions
`1, L, L², Li₂, J` (`hd5`, `hd6`, `hdJ`), and `∂(f5 j)` likewise.  Hence applying `∂` to a
`ℚ[x]`-relation

`c5·g 5 + c6·g 6 + Σⱼ Aⱼ·f5ⱼ = 0`

produces a new relation *of the same shape* whose `g 5`- and `g 6`-coefficients are **exactly**
`∂c5` and `∂c6` (`dshP`): `∂(g 5)` and `∂(g 6)` contribute only `f5`-terms, and so do the
`∂(f5 j)`.  This is `Work.C7.dsh_rel`, the "differentiate the relation" step of the elimination
argument of the paper's Lemma `seven` (`Work.C7.indep_seven`, `Work.C7.reduce_pair`).

The explicit coefficient vector of the `f5`-terms is `Work.C7.AtilF`, identified in
`Work.C7.dsh_comb`.
-/

namespace Work.C7

open PowerSeries
open scoped BigOperators

noncomputable section

/-! ## The transformed coefficient vector -/

/-- The vector of `ℚ[x]`-coefficients of the `f5`-part of `∂` applied to the relation
`c5·g 5 + c6·g 6 + Σⱼ Aⱼ·f5ⱼ = 0` (see `Work.C7.dsh_comb`).  Its `j`-th entry consists of `∂Aⱼ`
together with the `f5ⱼ`-coefficients of `∂` of the other functions. -/
def AtilF (c5 c6 : Polynomial ℚ) (A : Fin 5 → Polynomial ℚ) : Fin 5 → Polynomial ℚ :=
  ![ dshP (A 0) + A 1 * (Polynomial.X * (Polynomial.X - 1)),
     dshP (A 1) + A 2 * (2 * Polynomial.X * (Polynomial.X - 1))
       - A 3 * (Polynomial.X - 1) ^ 2 - A 4 * (Polynomial.X - 1) ^ 2,
     dshP (A 2) - (1 / 2 : Polynomial ℚ) * (Polynomial.X - 1) * (Polynomial.X - 2) * c5
       + (1 / 2 : Polynomial ℚ) * Polynomial.X * (Polynomial.X - 2) ^ 2 * c6,
     dshP (A 3) + 2 * Polynomial.X * (Polynomial.X - 2) ^ 2 * c6,
     dshP (A 4) + A 4 * ((1 / 2 : Polynomial ℚ) * Polynomial.X * (Polynomial.X - 1)) ]

@[simp] lemma AtilF_zero (c5 c6 : Polynomial ℚ) (A : Fin 5 → Polynomial ℚ) :
    AtilF c5 c6 A 0
      = dshP (A 0) + A 1 * (Polynomial.X * (Polynomial.X - 1)) := rfl

@[simp] lemma AtilF_one (c5 c6 : Polynomial ℚ) (A : Fin 5 → Polynomial ℚ) :
    AtilF c5 c6 A 1 = dshP (A 1) + A 2 * (2 * Polynomial.X * (Polynomial.X - 1))
       - A 3 * (Polynomial.X - 1) ^ 2 - A 4 * (Polynomial.X - 1) ^ 2 := rfl

@[simp] lemma AtilF_two (c5 c6 : Polynomial ℚ) (A : Fin 5 → Polynomial ℚ) :
    AtilF c5 c6 A 2
      = dshP (A 2) - (1 / 2 : Polynomial ℚ) * (Polynomial.X - 1) * (Polynomial.X - 2) * c5
       + (1 / 2 : Polynomial ℚ) * Polynomial.X * (Polynomial.X - 2) ^ 2 * c6 := rfl

@[simp] lemma AtilF_three (c5 c6 : Polynomial ℚ) (A : Fin 5 → Polynomial ℚ) :
    AtilF c5 c6 A 3 = dshP (A 3) + 2 * Polynomial.X * (Polynomial.X - 2) ^ 2 * c6 := rfl

@[simp] lemma AtilF_four (c5 c6 : Polynomial ℚ) (A : Fin 5 → Polynomial ℚ) :
    AtilF c5 c6 A 4
      = dshP (A 4) + A 4 * ((1 / 2 : Polynomial ℚ) * Polynomial.X * (Polynomial.X - 1)) := rfl

/-! ## Normalising casts of rational polynomials

The `ℚ[x]`-coefficients are pushed into `ℚ⟦x⟧` by `push_cast`; the two constants that `push_cast`
cannot see through (the numeral `2`, whose cast is not reducibly the `PowerSeries` numeral, and
`1/2`, Euclidean division in `ℚ[x]`) are normalised by hand so that the final `ring` sees a
single normal form. -/

lemma coe_two_ps_dsh_rel : (((2 : Polynomial ℚ) : PowerSeries ℚ)) = (2 : PowerSeries ℚ) := by
  rw [← Polynomial.coeToPowerSeries.ringHom_apply, map_ofNat]

lemma coe_half_ps : (((1 / 2 : Polynomial ℚ) : PowerSeries ℚ)) = PowerSeries.C (1 / 2 : ℚ) := by
  have h : (1 / 2 : Polynomial ℚ) = Polynomial.C (1 / 2 : ℚ) := by
    rw [show (2 : Polynomial ℚ) = Polynomial.C (2 : ℚ) from
      (Polynomial.C_eq_natCast 2).symm, Polynomial.div_C]
    norm_num
  rw [h, Polynomial.coe_C]

lemma neg_C_half : (PowerSeries.C (-(1 / 2) : ℚ) : PowerSeries ℚ)
    = -(PowerSeries.C (1 / 2 : ℚ)) := by
  simp

/-! ## The closure identity -/

/-- **The closure identity.**  Applying the derivation `∂ = x(x-1)²·d/dx` to the `ℚ[x]`-combination
`c5·g 5 + c6·g 6 + Σⱼ Aⱼ·f5ⱼ` and collecting the result in the basis
`g 5, g 6, f5 0, f5 1, f5 2, f5 3, f5 4` gives the combination with coefficients `dshP c5`,
`dshP c6` on `g 5`, `g 6` and `AtilF c5 c6 A` on `f5`.

The point is that `∂(g 5)` (`hd5`), `∂(g 6)` (`hd6`) and `∂(f5 j)` (`dsh_Lps`, `dsh_Lps_sq`,
`dsh_Li2ps`, `hdJ`) have **no** `g 5`- or `g 6`-components, so the `g 5`- and `g 6`-coefficients are
just the `∂` of the corresponding coefficients. -/
lemma dsh_comb
    (hd5 : dsh (g 5) = PowerSeries.C (-(1 / 2) : ℚ) * (PowerSeries.X - 1) * (PowerSeries.X - 2)
      * Lps ^ 2)
    (hd6 : dsh (g 6) = PowerSeries.X * (PowerSeries.X - 2) ^ 2 *
      (2 * Li2ps + PowerSeries.C (1 / 2 : ℚ) * Lps ^ 2))
    (hdJ : dsh Jps = PowerSeries.C (1 / 2 : ℚ) * (PowerSeries.X * (PowerSeries.X - 1)) * Jps
      - (PowerSeries.X - 1) ^ 2 * Lps)
    (c5 c6 : Polynomial ℚ) (A : Fin 5 → Polynomial ℚ) :
    dsh ((c5 : PowerSeries ℚ) * g 5 + (c6 : PowerSeries ℚ) * g 6
        + ∑ j, (A j : PowerSeries ℚ) * f5 j)
      = ((dshP c5 : Polynomial ℚ) : PowerSeries ℚ) * g 5
        + ((dshP c6 : Polynomial ℚ) : PowerSeries ℚ) * g 6
        + ∑ j, ((AtilF c5 c6 A j : Polynomial ℚ) : PowerSeries ℚ) * f5 j := by
  simp only [Fin.sum_univ_five, dsh_add, dsh_mul, dsh_coe, hd5, hd6, hdJ,
    dsh_one, dsh_Lps, dsh_Lps_sq, dsh_Li2ps,
    f5_zero, f5_one, f5_two, f5_three, f5_four,
    AtilF_zero, AtilF_one, AtilF_two, AtilF_three, AtilF_four]
  push_cast
  rw [coe_two_ps_dsh_rel, coe_half_ps, neg_C_half]
  ring

end

theorem dsh_rel
    (hd5 : Work.C7.dsh (Work.C7.g 5)
      = PowerSeries.C (-(1 / 2) : ℚ) * (PowerSeries.X - 1) * (PowerSeries.X - 2)
        * Work.C7.Lps ^ 2)
    (hd6 : Work.C7.dsh (Work.C7.g 6) = PowerSeries.X * (PowerSeries.X - 2) ^ 2 *
      (2 * Work.C7.Li2ps + PowerSeries.C (1 / 2 : ℚ) * Work.C7.Lps ^ 2))
    (hdJ : Work.C7.dsh Work.C7.Jps
      = PowerSeries.C (1 / 2 : ℚ) * (PowerSeries.X * (PowerSeries.X - 1)) * Work.C7.Jps
        - (PowerSeries.X - 1) ^ 2 * Work.C7.Lps)
    (c5 c6 : Polynomial ℚ) (A : Fin 5 → Polynomial ℚ)
    (hR1 : (c5 : PowerSeries ℚ) * Work.C7.g 5 + (c6 : PowerSeries ℚ) * Work.C7.g 6
      + ∑ j, (A j : PowerSeries ℚ) * Work.C7.f5 j = 0) :
    ∃ Atil : Fin 5 → Polynomial ℚ,
      ((Work.C7.dshP c5 : Polynomial ℚ) : PowerSeries ℚ) * Work.C7.g 5
        + ((Work.C7.dshP c6 : Polynomial ℚ) : PowerSeries ℚ) * Work.C7.g 6
        + ∑ j, (Atil j : PowerSeries ℚ) * Work.C7.f5 j = 0 := by
  refine ⟨AtilF c5 c6 A, ?_⟩
  have h := dsh_comb hd5 hd6 hdJ c5 c6 A
  rw [hR1, dsh_zero] at h
  exact h.symm

end Work.C7
