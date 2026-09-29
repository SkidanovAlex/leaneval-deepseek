import Mathlib
import Submission.Work.C7.xdefs
import Submission.Work.C7.seven_setup
import Submission.Work.C7.dsh_pull
import Submission.Work.C7.dsh_rel
import Submission.Work.C7.g_five_part
import Submission.Work.C7.caseA_end
import Submission.Work.C7.caseB_end

/-!
# Area C7 — Lemma `seven` on the `x`-side: `B₁,…,B₇` are `ℚ(x)`-independent

The seven pullbacks `g i = Bᵢ ∘ y` (`y = x²/(x-1)`) of the seven pure functions `B₁,…,B₇` of
Calegari–Dimitrov–Tang (arXiv:2408.15403, Lemma `seven`) are `ℚ(x)`-linearly independent.

The proof is the elimination argument of the paper, run with the derivation `∂ = x(x-1)²·d/dx` of
`ℚ⟦x⟧` (which keeps the `ℚ[x]`-span of the seven functions closed with *polynomial* coefficients):

* `g 0,…,g 4` are a `ℚ(x)`-invertible (triangular) combination of the five `ℚ(x)`-independent
  functions `f5 = (1, L, L², Li₂, J)` (`hind`), while `∂g 5`, `∂g 6 ∈ span f5`;
* if a non-trivial relation existed, then (dividing by the coefficient of `g 5`, differentiating and
  crossing) one produces a `ℚ[x]`-relation of one of the two shapes
  `d·g 6 ∈ span f5` (case A) or `d·(g 5 + λ·g 6) ∈ span f5` with `λ ∈ ℚ` (case B), `d ≠ 0`;
* applying `∂` to such a relation and comparing coefficients (using `hind`) forces in each case a
  rational function `β` with `dRat β = (x-2)/(x(x-1))` or `dRat β = 2(x-2)²/(x-1)²`, impossible
  because these have a non-zero residue at their pole.

The coefficient clearing (`rel_cleared`), the closure of the span under `∂` (`dsh_rel`), the
derivative identities (`dsh_pull`), the `P 5 = P 6 = 0` case (`g_five_part`) and the two endgames
(`caseA_end`, `caseB_end`) are separate modules; the reduction (case analysis) and the assembly are
in this file.
-/

namespace Work.C7

open PowerSeries
open scoped BigOperators

noncomputable section

/-! ## Packaged `ℚ[x]`-combinations of the seven pullbacks -/

/-- The `ℚ[x]`-combination `c5·g 5 + c6·g 6 + Σ_j A_j·f5_j` of the pullbacks. -/
def comb (c5 c6 : Polynomial ℚ) (A : Fin 5 → Polynomial ℚ) : PowerSeries ℚ :=
  (c5 : PowerSeries ℚ) * g 5 + (c6 : PowerSeries ℚ) * g 6
    + ∑ j, (A j : PowerSeries ℚ) * f5 j

/-- `comb` is additive in the coefficient tuples. -/
lemma comb_add (c5 c6 : Polynomial ℚ) (A : Fin 5 → Polynomial ℚ)
    (c5' c6' : Polynomial ℚ) (A' : Fin 5 → Polynomial ℚ) :
    comb c5 c6 A + comb c5' c6' A' = comb (c5 + c5') (c6 + c6') (A + A') := by
  rw [comb, comb, comb]
  rw [show (∑ j : Fin 5, (((A + A') j : Polynomial ℚ) : PowerSeries ℚ) * f5 j)
      = ∑ j : Fin 5, ((A j : PowerSeries ℚ) * f5 j + (A' j : PowerSeries ℚ) * f5 j) from
    Finset.sum_congr rfl (fun j _ => by
      rw [show ((A + A') j : Polynomial ℚ) = A j + A' j from rfl]
      push_cast
      ring)]
  rw [Finset.sum_add_distrib]
  push_cast
  ring

/-- `comb` is `ℚ[x]`-linear in the coefficient tuples. -/
lemma comb_smul (p c5 c6 : Polynomial ℚ) (A : Fin 5 → Polynomial ℚ) :
    (p : PowerSeries ℚ) * comb c5 c6 A = comb (p * c5) (p * c6) (fun j => p * A j) := by
  rw [comb, comb, mul_add, mul_add, Finset.mul_sum]
  rw [show (∑ j : Fin 5, (((fun j => p * A j) j : Polynomial ℚ) : PowerSeries ℚ) * f5 j)
      = ∑ j : Fin 5, (p : PowerSeries ℚ) * ((A j : PowerSeries ℚ) * f5 j) from
    Finset.sum_congr rfl (fun j _ => by push_cast; ring)]
  push_cast
  ring

lemma comb_neg (c5 c6 : Polynomial ℚ) (A : Fin 5 → Polynomial ℚ) :
    comb (-c5) (-c6) (fun j => -A j) = -comb c5 c6 A := by
  rw [comb, comb]
  rw [show (∑ j : Fin 5, (((fun j => -A j) j : Polynomial ℚ) : PowerSeries ℚ) * f5 j)
      = ∑ j : Fin 5, -((A j : PowerSeries ℚ) * f5 j) from
    Finset.sum_congr rfl (fun j _ => by push_cast; ring)]
  rw [Finset.sum_neg_distrib]
  push_cast
  ring

lemma comb_sub (c5 c6 : Polynomial ℚ) (A : Fin 5 → Polynomial ℚ)
    (c5' c6' : Polynomial ℚ) (A' : Fin 5 → Polynomial ℚ) :
    comb c5 c6 A - comb c5' c6' A' = comb (c5 - c5') (c6 - c6') (A - A') := by
  rw [comb, comb, comb]
  rw [show (∑ j : Fin 5, (((A - A') j : Polynomial ℚ) : PowerSeries ℚ) * f5 j)
      = ∑ j : Fin 5, ((A j : PowerSeries ℚ) * f5 j - (A' j : PowerSeries ℚ) * f5 j) from
    Finset.sum_congr rfl (fun j _ => by
      rw [show ((A - A') j : Polynomial ℚ) = A j - A' j from rfl]
      push_cast
      ring)]
  rw [Finset.sum_sub_distrib]
  push_cast
  ring


/-! ## Clearing the coefficients of the first five pullbacks -/

/-- Splitting a sum over `Fin 7` into its seven terms. -/
lemma sum7_split (u : Fin 7 → PowerSeries ℚ) :
    ∑ i, u i = u 0 + u 1 + u 2 + u 3 + u 4 + u 5 + u 6 :=
  Fin.sum_univ_seven u

lemma sub_one_mul_cfun :
    ((PowerSeries.X : PowerSeries ℚ) - 1) * cfun
      = (PowerSeries.X : PowerSeries ℚ) * ((PowerSeries.X : PowerSeries ℚ) - 2) := by
  rw [cfun_eq']
  have h := mul_gU
  linear_combination ((PowerSeries.X : PowerSeries ℚ) * ((PowerSeries.X : PowerSeries ℚ) - 2)) * h

lemma mul_yps_sub_one :
    ((PowerSeries.X : PowerSeries ℚ) - 1) * yps = (PowerSeries.X : PowerSeries ℚ) ^ 2 := by
  rw [mul_comm]; exact yps_mul_sub_one_seven_setup

lemma C_neg_half : (PowerSeries.C (-(1 / 2) : ℚ)) = -(PowerSeries.C (1 / 2 : ℚ)) := by
  rw [map_neg]

/-- `(x-1)·g 0 = (x-1)·1`. -/
lemma mul_sub_one_g0 (h0 : g 0 = 1) :
    ((PowerSeries.X : PowerSeries ℚ) - 1) * g 0
      = (((PowerSeries.X : PowerSeries ℚ) - 1)) * f5 0 := by
  rw [h0, f5_zero, mul_one]

/-- `(x-1)·g 1 = 2x² - x(x-2)L`. -/
lemma mul_sub_one_g1 (h1 : g 1 = 2 * yps - cfun * Lps) :
    ((PowerSeries.X : PowerSeries ℚ) - 1) * g 1
      = (2 * (PowerSeries.X : PowerSeries ℚ) ^ 2) * f5 0
        - ((PowerSeries.X : PowerSeries ℚ) * ((PowerSeries.X : PowerSeries ℚ) - 2)) * f5 1 := by
  have expand : ((PowerSeries.X : PowerSeries ℚ) - 1) * (2 * yps - cfun * Lps)
      = 2 * (((PowerSeries.X : PowerSeries ℚ) - 1) * yps)
        - (((PowerSeries.X : PowerSeries ℚ) - 1) * cfun) * Lps := by ring
  rw [h1, expand, mul_yps_sub_one, sub_one_mul_cfun, f5_zero, f5_one]
  ring

/-- `(x-1)·g 2 = -(1/2)(x-1)L²`. -/
lemma mul_sub_one_g2 (h2 : g 2 = -(PowerSeries.C (1 / 2 : ℚ)) * Lps ^ 2) :
    ((PowerSeries.X : PowerSeries ℚ) - 1) * g 2
      = (PowerSeries.C (-(1 / 2) : ℚ) * ((PowerSeries.X : PowerSeries ℚ) - 1)) * f5 2 := by
  rw [h2, f5_two, C_neg_half]
  ring

/-- `(x-1)·g 3 = x(x-2)(2Li₂ + (1/2)L²)`. -/
lemma mul_sub_one_g3
    (h3 : g 3 = (PowerSeries.X - Submission.CDT.sympPhi) * (2 * Li2ps
      + PowerSeries.C (1 / 2 : ℚ) * Lps ^ 2)) :
    ((PowerSeries.X : PowerSeries ℚ) - 1) * g 3
      = (PowerSeries.C (1 / 2 : ℚ)
            * ((PowerSeries.X : PowerSeries ℚ) * ((PowerSeries.X : PowerSeries ℚ) - 2))) * f5 2
        + (2 * ((PowerSeries.X : PowerSeries ℚ) * ((PowerSeries.X : PowerSeries ℚ) - 2))) * f5 3 := by
  have expand : ((PowerSeries.X : PowerSeries ℚ) - 1)
        * ((PowerSeries.X - Submission.CDT.sympPhi)
            * (2 * Li2ps + PowerSeries.C (1 / 2 : ℚ) * Lps ^ 2))
      = (((PowerSeries.X : PowerSeries ℚ) - 1) * cfun)
          * (2 * Li2ps + PowerSeries.C (1 / 2 : ℚ) * Lps ^ 2) := by
    rw [cfun_sub_phi]
    ring
  rw [h3, expand, sub_one_mul_cfun, f5_two, f5_three]
  ring

/-- `(x-1)·g 4 = x·J`. -/
lemma mul_sub_one_g4 (h4 : g 4 = (PowerSeries.X * (PowerSeries.X - 1)⁻¹) * Jps) :
    ((PowerSeries.X : PowerSeries ℚ) - 1) * g 4
      = (PowerSeries.X : PowerSeries ℚ) * f5 4 := by
  rw [h4, f5_four]
  have h := mul_gU
  linear_combination ((PowerSeries.X : PowerSeries ℚ) * Jps) * h

/-- The `f5`-coefficients of the `(x-1)`-cleared first five pullbacks (times the coefficients of
the relation). -/
def Ared (P : Fin 7 → Polynomial ℚ) : Fin 5 → Polynomial ℚ :=
  ![(Polynomial.X - 1) * P 0 + 2 * Polynomial.X ^ 2 * P 1,
    -(Polynomial.X * (Polynomial.X - 2)) * P 1,
    Polynomial.C (-(1 / 2)) * (Polynomial.X - 1) * P 2
      + Polynomial.C (1 / 2) * (Polynomial.X * (Polynomial.X - 2)) * P 3,
    2 * (Polynomial.X * (Polynomial.X - 2)) * P 3,
    Polynomial.X * P 4]

/-- **Clearing the relation.**  From a `ℚ[x]`-relation `Σᵢ Pᵢ·(g i) = 0` among the seven pullbacks,
multiplying by `(x-1)` and replacing the first five pullbacks by their `f5`-expansions produces a
`ℚ[x]`-relation of the shape `comb ((x-1)P 5) ((x-1)P 6) A = 0`. -/
theorem rel_cleared_local (h0 : g 0 = 1) (h1 : g 1 = 2 * yps - cfun * Lps)
    (h2 : g 2 = -(PowerSeries.C (1 / 2 : ℚ)) * Lps ^ 2)
    (h3 : g 3 = (PowerSeries.X - Submission.CDT.sympPhi) * (2 * Li2ps
      + PowerSeries.C (1 / 2 : ℚ) * Lps ^ 2))
    (h4 : g 4 = (PowerSeries.X * (PowerSeries.X - 1)⁻¹) * Jps)
    (P : Fin 7 → Polynomial ℚ)
    (hP : ∑ i, (P i : PowerSeries ℚ) * g i = 0) :
    ∃ A : Fin 5 → Polynomial ℚ, comb ((Polynomial.X - 1) * P 5) ((Polynomial.X - 1) * P 6) A = 0 := by
  refine ⟨Ared P, ?_⟩
  have hmul : ∑ i : Fin 7,
      (((Polynomial.X - 1) * P i : Polynomial ℚ) : PowerSeries ℚ) * g i = 0 := by
    have h := congrArg (fun z : PowerSeries ℚ =>
      ((Polynomial.X - 1 : Polynomial ℚ) : PowerSeries ℚ) * z) hP
    rw [mul_zero, Finset.mul_sum] at h
    rw [← h]
    refine Finset.sum_congr rfl fun i _ => ?_
    push_cast
    ring
  rw [sum7_split] at hmul
  rw [show (((Polynomial.X - 1) * P 0 : Polynomial ℚ) : PowerSeries ℚ) * g 0
        = (P 0 : PowerSeries ℚ) * (((PowerSeries.X : PowerSeries ℚ) - 1) * g 0) from by
      push_cast; ring,
    show (((Polynomial.X - 1) * P 1 : Polynomial ℚ) : PowerSeries ℚ) * g 1
        = (P 1 : PowerSeries ℚ) * (((PowerSeries.X : PowerSeries ℚ) - 1) * g 1) from by
      push_cast; ring,
    show (((Polynomial.X - 1) * P 2 : Polynomial ℚ) : PowerSeries ℚ) * g 2
        = (P 2 : PowerSeries ℚ) * (((PowerSeries.X : PowerSeries ℚ) - 1) * g 2) from by
      push_cast; ring,
    show (((Polynomial.X - 1) * P 3 : Polynomial ℚ) : PowerSeries ℚ) * g 3
        = (P 3 : PowerSeries ℚ) * (((PowerSeries.X : PowerSeries ℚ) - 1) * g 3) from by
      push_cast; ring,
    show (((Polynomial.X - 1) * P 4 : Polynomial ℚ) : PowerSeries ℚ) * g 4
        = (P 4 : PowerSeries ℚ) * (((PowerSeries.X : PowerSeries ℚ) - 1) * g 4) from by
      push_cast; ring,
    show (((Polynomial.X - 1) * P 5 : Polynomial ℚ) : PowerSeries ℚ) * g 5
        = (P 5 : PowerSeries ℚ) * (((PowerSeries.X : PowerSeries ℚ) - 1) * g 5) from by
      push_cast; ring,
    show (((Polynomial.X - 1) * P 6 : Polynomial ℚ) : PowerSeries ℚ) * g 6
        = (P 6 : PowerSeries ℚ) * (((PowerSeries.X : PowerSeries ℚ) - 1) * g 6) from by
      push_cast; ring] at hmul
  have hfive : (P 0 : PowerSeries ℚ) * (((PowerSeries.X : PowerSeries ℚ) - 1) * g 0)
        + (P 1 : PowerSeries ℚ) * (((PowerSeries.X : PowerSeries ℚ) - 1) * g 1)
        + (P 2 : PowerSeries ℚ) * (((PowerSeries.X : PowerSeries ℚ) - 1) * g 2)
        + (P 3 : PowerSeries ℚ) * (((PowerSeries.X : PowerSeries ℚ) - 1) * g 3)
        + (P 4 : PowerSeries ℚ) * (((PowerSeries.X : PowerSeries ℚ) - 1) * g 4)
      = ∑ k : Fin 5, ((Ared P k : Polynomial ℚ) : PowerSeries ℚ) * f5 k := by
    rw [mul_sub_one_g0 h0, mul_sub_one_g1 h1, mul_sub_one_g2 h2, mul_sub_one_g3 h3,
      mul_sub_one_g4 h4]
    simp only [Ared, Fin.sum_univ_five]
    push_cast
    have htwo : (((2 : Polynomial ℚ)) : PowerSeries ℚ) = (2 : PowerSeries ℚ) :=
      map_ofNat (algebraMap (Polynomial ℚ) (PowerSeries ℚ)) 2
    rw [htwo]
    ring
  rw [comb]
  rw [show (((Polynomial.X - 1) * P 5 : Polynomial ℚ) : PowerSeries ℚ) * g 5
        = (P 5 : PowerSeries ℚ) * (((PowerSeries.X : PowerSeries ℚ) - 1) * g 5) from by
      push_cast; ring,
    show (((Polynomial.X - 1) * P 6 : Polynomial ℚ) : PowerSeries ℚ) * g 6
        = (P 6 : PowerSeries ℚ) * (((PowerSeries.X : PowerSeries ℚ) - 1) * g 6) from by
      push_cast; ring]
  rw [hfive] at hmul
  linear_combination hmul

/-! ## Extracting a constant coefficient from a vanishing Wronskian -/

/-- If `c5·c6' = c5'·c6` with `c5 ≠ 0` then `c6/c5` is a constant of `ℚ(x)`, i.e. `c6 = C λ·c5`
for some `λ ∈ ℚ`.  (The constant field of `ℚ(x)` is `ℚ`: `Submission.CDT.exists_const_of_dRat_eq_zero`.) -/
lemma const_of_wronskian (c5 c6 : Polynomial ℚ) (hc5 : c5 ≠ 0)
    (h : c5 * Polynomial.derivative c6 - Polynomial.derivative c5 * c6 = 0) :
    ∃ lam : ℚ, c6 = Polynomial.C lam * c5 := by
  have hden : ((c5 : Polynomial ℚ) : RatFunc ℚ) ≠ 0 := RatFunc.algebraMap_ne_zero hc5
  have hd : Submission.CDT.dRat (((c6 : Polynomial ℚ) : RatFunc ℚ)
      / ((c5 : Polynomial ℚ) : RatFunc ℚ)) = 0 := by
    rw [show ((c6 : Polynomial ℚ) : RatFunc ℚ) / ((c5 : Polynomial ℚ) : RatFunc ℚ)
        = (algebraMap (Polynomial ℚ) (RatFunc ℚ) c6)
          / (algebraMap (Polynomial ℚ) (RatFunc ℚ) c5) from rfl]
    rw [Submission.CDT.dRat_div]
    rw [show (Polynomial.derivative c6 * c5 - c6 * Polynomial.derivative c5 : Polynomial ℚ) = 0 from by
      linear_combination h]
    rw [map_zero, zero_div]
  obtain ⟨lam, hlam⟩ := Submission.CDT.exists_const_of_dRat_eq_zero hd
  have h5 := congrArg (fun z : RatFunc ℚ => z * ((c5 : Polynomial ℚ) : RatFunc ℚ)) hlam
  rw [div_mul_cancel₀ _ hden] at h5
  refine ⟨lam, ?_⟩
  apply RatFunc.algebraMap_injective ℚ
  rw [map_mul]
  rw [Submission.CDT.am_C' lam]
  exact h5

/-! ## The reduction: a non-trivial relation produces case A or case B -/

/-- **Reduction.**  Given a `ℚ[x]`-relation `c5·g 5 + c6·g 6 + Σ A_j·f5_j = 0` with `(c5,c6) ≠ 0`,
either `g 6` lies in the `ℚ(x)`-span of `f5` with a non-zero polynomial coefficient (case A), or
`g 5 + λ·g 6` does, for some constant `λ ∈ ℚ` (case B).

This is the Wronskian step of the paper's Lemma `seven`: apply `∂` to the relation (`dsh_rel`),
multiply the differentiated relation by `c5` and subtract `dshP c5` times the original one; the
`g 5`-terms cancel and one is left with `Y·g 6 + (…) = 0` for `Y = c5·(dshP c6) - (dshP c5)·c6`.
If `Y ≠ 0` this is case A; if `Y = 0` then `(c6/c5)' = 0`, so `c6 = λ·c5` for a constant `λ ∈ ℚ`
and the original relation is case B. -/
theorem reduce_pair
    (hd5 : dsh (g 5) = PowerSeries.C (-(1 / 2) : ℚ) * (PowerSeries.X - 1) * (PowerSeries.X - 2)
      * Lps ^ 2)
    (hd6 : dsh (g 6) = PowerSeries.X * (PowerSeries.X - 2) ^ 2 *
      (2 * Li2ps + PowerSeries.C (1 / 2 : ℚ) * Lps ^ 2))
    (hdJ : dsh Jps = PowerSeries.C (1 / 2 : ℚ) * (PowerSeries.X * (PowerSeries.X - 1)) * Jps
      - (PowerSeries.X - 1) ^ 2 * Lps)
    (c5 c6 : Polynomial ℚ) (A : Fin 5 → Polynomial ℚ)
    (hR1 : comb c5 c6 A = 0)
    (hne : c5 ≠ 0 ∨ c6 ≠ 0) :
    (∃ d : Polynomial ℚ, d ≠ 0 ∧ ∃ C : Fin 5 → Polynomial ℚ,
        (d : PowerSeries ℚ) * g 6 + ∑ j, (C j : PowerSeries ℚ) * f5 j = 0)
    ∨ (∃ lam : ℚ, ∃ d : Polynomial ℚ, d ≠ 0 ∧ ∃ C : Fin 5 → Polynomial ℚ,
        (d : PowerSeries ℚ) * (g 5 + PowerSeries.C lam * g 6)
          + ∑ j, (C j : PowerSeries ℚ) * f5 j = 0) := by
  by_cases hc5 : c5 = 0
  · -- `c5 = 0`: the relation already has the shape of case A
    refine Or.inl ⟨c6, ?_, A, ?_⟩
    · rcases hne with h | h
      · exact absurd hc5 h
      · exact h
    · rw [comb] at hR1
      simpa [hc5] using hR1
  · obtain ⟨Atil, hR2⟩ := dsh_rel hd5 hd6 hdJ c5 c6 A hR1
    by_cases hY : (c5 * dshP c6 - dshP c5 * c6 : Polynomial ℚ) = 0
    · -- `Y = 0`: `c6/c5` is constant, so we are in case B
      right
      have hY' : (Polynomial.X * (Polynomial.X - 1) ^ 2 : Polynomial ℚ)
          * (c5 * Polynomial.derivative c6 - Polynomial.derivative c5 * c6) = 0 := by
        rw [← hY]
        simp only [dshP]
        ring
      have hfac : (Polynomial.X * (Polynomial.X - 1) ^ 2 : Polynomial ℚ) ≠ 0 :=
        mul_ne_zero Polynomial.X_ne_zero (pow_ne_zero 2 (Polynomial.X_sub_C_ne_zero 1))
      have hW : c5 * Polynomial.derivative c6 - Polynomial.derivative c5 * c6 = 0 :=
        (mul_eq_zero.mp hY').resolve_left hfac
      obtain ⟨lam, hc6⟩ := const_of_wronskian c5 c6 hc5 hW
      refine ⟨lam, c5, hc5, A, ?_⟩
      have hnew : (c5 : PowerSeries ℚ) * (g 5 + PowerSeries.C lam * g 6)
            + ∑ j, (A j : PowerSeries ℚ) * f5 j
          = comb c5 (Polynomial.C lam * c5) A := by
        rw [comb]
        push_cast
        ring
      rw [hnew, ← hc6]
      exact hR1
    · -- `Y ≠ 0`: case A
      refine Or.inl ⟨c5 * dshP c6 - dshP c5 * c6, hY, fun j => c5 * Atil j - dshP c5 * A j, ?_⟩
      have hzero : (c5 : PowerSeries ℚ) * comb (dshP c5) (dshP c6) Atil
          - ((dshP c5 : Polynomial ℚ) : PowerSeries ℚ) * comb c5 c6 A = 0 := by
        rw [hR1]
        rw [comb]
        rw [hR2]
        ring
      have hYrel : ((c5 * dshP c6 - dshP c5 * c6 : Polynomial ℚ) : PowerSeries ℚ) * g 6
            + ∑ j, ((c5 * Atil j - dshP c5 * A j : Polynomial ℚ) : PowerSeries ℚ) * f5 j
          = (c5 : PowerSeries ℚ) * comb (dshP c5) (dshP c6) Atil
            - ((dshP c5 : Polynomial ℚ) : PowerSeries ℚ) * comb c5 c6 A := by
        rw [comb_smul c5 (dshP c5) (dshP c6) Atil, comb_smul (dshP c5) c5 c6 A, comb_sub]
        rw [comb]
        simp only [Pi.sub_apply]
        push_cast
        ring
      show ((c5 * dshP c6 - dshP c5 * c6 : Polynomial ℚ) : PowerSeries ℚ) * g 6
        + ∑ j, ((c5 * Atil j - dshP c5 * A j : Polynomial ℚ) : PowerSeries ℚ) * f5 j = 0
      rw [hYrel, hzero]


/-! ## Assembly -/

/-- **Lemma `seven` on the `x`-side**: the seven pullbacks `B₁∘y,…,B₇∘y` of the pure functions are
`ℚ(x)`-linearly independent.

Given a `ℚ[x]`-relation `Σ Pᵢ·(g i) = 0`:

* if `P 5 = P 6 = 0` then `g_five_part` (the first five pullbacks are a triangular `ℚ(x)`-combination
  of the five independent functions `1, L, L², Li₂, J`) forces `P = 0`;
* otherwise `rel_cleared` rewrites the relation as `c5·g 5 + c6·g 6 + Σ A_j·f5_j = 0` with
  `(c5,c6) ≠ 0`, `reduce_pair` turns it into case A or case B, and the endgames `caseA_end`
  (`dRat β = 2(x-2)²/(x-1)²` impossible) and `caseB_end` (same, or `dRat β = (x-2)/(x(x-1))`
  impossible) give the contradiction. -/
theorem indep_seven
    (h0 : Work.C7.g 0 = 1)
    (h1 : Work.C7.g 1 = 2 * Work.C7.yps - Work.C7.cfun * Work.C7.Lps)
    (h2 : Work.C7.g 2 = -(PowerSeries.C (1/2 : ℚ)) * Work.C7.Lps ^ 2)
    (h3 : Work.C7.g 3 = (PowerSeries.X - Submission.CDT.sympPhi) * (2 * Work.C7.Li2ps + (PowerSeries.C (1/2 : ℚ)) * Work.C7.Lps ^ 2))
    (h4 : Work.C7.g 4 = (PowerSeries.X * (PowerSeries.X - 1)⁻¹) * Work.C7.Jps)
    (h6 : Work.C7.yps * PowerSeries.derivative (R := ℚ) (Work.C7.g 5) = (Work.C7.g 2) * PowerSeries.derivative (R := ℚ) Work.C7.yps)
    (h7 : Work.C7.yps * PowerSeries.derivative (R := ℚ) (Work.C7.g 6) = (Work.C7.g 3) * PowerSeries.derivative (R := ℚ) Work.C7.yps)
    (hind : Submission.CDTPlan.PolyIndependent (fun i : Fin 5 => ![1, Work.C7.Lps, Work.C7.Lps ^ 2, Work.C7.Li2ps, Work.C7.Jps] i))
    (hJ : 2 * PowerSeries.X * (PowerSeries.X - 1) * PowerSeries.derivative (R := ℚ) Work.C7.Jps - PowerSeries.X * Work.C7.Jps = 2 * (1 - PowerSeries.X) * Work.C7.Lps)
    (hN1 : ∀ δ : RatFunc ℚ, Submission.CDT.dRat δ ≠ 2 * (RatFunc.X - 2) ^ 2 * ((RatFunc.X - 1) ^ 2)⁻¹)
    (hN2 : ∀ δ : RatFunc ℚ, Submission.CDT.dRat δ ≠ (RatFunc.X - 2) * (RatFunc.X * (RatFunc.X - 1))⁻¹)
    (hsq : ∀ ε : RatFunc ℚ, Submission.CDT.dRat ε = ε / (2 * (RatFunc.X - 1)) → ε = 0)
    (hsq' : ∀ ε : RatFunc ℚ, Submission.CDT.dRat ε = -ε / (2 * (RatFunc.X - 1)) → ε = 0) :
    Submission.CDTPlan.PolyIndependent (fun i : Fin 7 => Work.C7.g i) := by
  obtain ⟨hd5, hd6, hdJ⟩ := dsh_pull h2 h3 h6 h7 hJ
  intro P hP
  by_contra hcon
  by_cases h56 : P 5 ≠ 0 ∨ P 6 ≠ 0
  · obtain ⟨A, hA⟩ := rel_cleared_local h0 h1 h2 h3 h4 P hP
    have hx1 : (Polynomial.X - 1 : Polynomial ℚ) ≠ 0 := by
      simpa using Polynomial.X_sub_C_ne_zero (1 : ℚ)
    have hne : (Polynomial.X - 1) * P 5 ≠ 0 ∨ (Polynomial.X - 1) * P 6 ≠ 0 := by
      rcases h56 with h | h
      · exact Or.inl (mul_ne_zero hx1 h)
      · exact Or.inr (mul_ne_zero hx1 h)
    rcases reduce_pair hd5 hd6 hdJ ((Polynomial.X - 1) * P 5) ((Polynomial.X - 1) * P 6) A hA hne with
      ⟨d, hd, C, hC⟩ | ⟨lam, d, hd, C, hC⟩
    · exact caseA_end hd6 hdJ hind hN1 d hd C hC
    · exact caseB_end hd5 hd6 hdJ hind hN1 hN2 lam d hd C hC
  · push Not at h56
    exact hcon (g_five_part h0 h1 h2 h3 h4 hind P hP h56.1 h56.2)

end

end Work.C7
