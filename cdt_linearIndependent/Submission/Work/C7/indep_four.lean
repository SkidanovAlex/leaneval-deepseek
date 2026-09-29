import Mathlib
import Submission.Work.C7.xdefs
import Submission.Work.C7.indep_small
import Submission.Work.C7b.four_elim

/-!
# Area C7 — `1, log(1-x), log²(1-x), Li₂(x)` are `ℚ[x]`-independent

The target `Work.C7.indep_four` (consumed as `h4` by `Work.C7.indep_five`) states that the four
power series `1, Lps = log(1-x), Lps², Li2ps = Li₂(x)` are linearly independent over `ℚ[x]`.

Route (purely algebraic, no analysis; `Lps`, `Li2ps` are the power series of `x07/../`):

* `1, Lps, Lps²` independent is `Work.C7.indep_three` (second conjunct of `Work.C7.indep_small`);
* differentiating a hypothetical relation and multiplying by `X (1 - X)` — so that
  `(1-X)·Lps' = -1` and `X·Li2ps' = -Lps` become polynomial identities — eliminates `Li2ps`
  between the relation and its derivative (`Work.C7b.four_elim`), producing a `ℚ[x]`-relation
  among `1, Lps, Lps²`;
* `Work.C7b.indep_three` kills the three coefficients `D0, D1, D2`;
* `D2 = 0` forces `p2 = c·p3`, and `D1 = 0` then reads, in `ℚ(x)`,
  `X(1-X)·(p1/p3)' = 2cX + (1-X)`, i.e. `(p1/p3)' = 1/X + 2c/(1-X)`: impossible, since a derivative
  of a rational function has no simple pole (`Submission.CDT.ordAt_dRat_ne_neg_one`) whereas the
  right-hand side has a simple pole of residue `1` at `0`.

The endgame (last two bullets) is proved here.
-/

noncomputable section

namespace Work.C7

open Polynomial PowerSeries
open scoped BigOperators

/-- The constant `c : ℚ`, as an element of `ℚ(x)` (spelled with the polynomial algebra map so that
it is the same term as the coercions of constant polynomials). -/
private abbrev cf (c : ℚ) : RatFunc ℚ := algebraMap (Polynomial ℚ) (RatFunc ℚ) (Polynomial.C c)

section Endgame

private lemma ordAt_zero_one_sub_X : Submission.CDT.ordAt (0 : ℚ) (1 - RatFunc.X) = 0 := by
  have h : (1 - (RatFunc.X : RatFunc ℚ))
      = algebraMap (Polynomial ℚ) (RatFunc ℚ) (1 - Polynomial.X) := by
    rw [map_sub, map_one, RatFunc.algebraMap_X]
  rw [h, Submission.CDT.ordAt_algebraMap, Polynomial.rootMultiplicity_eq_zero]
  · norm_num
  · rw [Polynomial.IsRoot.def]; simp

private lemma ordAt_zero_X_inv : Submission.CDT.ordAt (0 : ℚ) ((RatFunc.X : RatFunc ℚ)⁻¹) = -1 := by
  have hX0 : (RatFunc.X : RatFunc ℚ) ≠ 0 := by
    rw [← RatFunc.algebraMap_X]
    exact RatFunc.algebraMap_ne_zero Polynomial.X_ne_zero
  rw [Submission.CDT.ordAt_inv (0 : ℚ) hX0]
  rw [show (RatFunc.X : RatFunc ℚ) = algebraMap (Polynomial ℚ) (RatFunc ℚ) Polynomial.X from
      RatFunc.algebraMap_X,
    Submission.CDT.ordAt_algebraMap,
    show (Polynomial.X : Polynomial ℚ) = Polynomial.X - Polynomial.C 0 from by simp,
    Polynomial.rootMultiplicity_X_sub_C_self]
  norm_num

/-- `cf (2c) = 2 · cf c`. -/
private lemma cf_two_mul (c : ℚ) : cf (2 * c) = cf c * 2 := by
  have hC : (algebraMap (Polynomial ℚ) (RatFunc ℚ) (Polynomial.C (2 : ℚ))) = 2 := by
    rw [show (Polynomial.C (2 : ℚ) : Polynomial ℚ) = (2 : Polynomial ℚ) from map_ofNat _ 2,
      map_ofNat]
  rw [show cf (2 * c)
      = algebraMap (Polynomial ℚ) (RatFunc ℚ) (Polynomial.C (2 * c)) from rfl,
    show cf c = algebraMap (Polynomial ℚ) (RatFunc ℚ) (Polynomial.C c) from rfl,
    show (Polynomial.C (2 * c) : Polynomial ℚ) = Polynomial.C c * Polynomial.C 2 from by
      rw [mul_comm (2 : ℚ) c, map_mul],
    map_mul, hC]

/-- The shape in which the endgame meets the constant term. -/
private lemma two_cf_div (c : ℚ) :
    (2 * cf c / (1 - RatFunc.X)) = cf (2 * c) * (1 - RatFunc.X)⁻¹ := by
  rw [cf_two_mul]
  field_simp

private lemma ordAt_zero_cf (c : ℚ) : Submission.CDT.ordAt (0 : ℚ) (cf c) = 0 := by
  rw [show cf c = algebraMap (Polynomial ℚ) (RatFunc ℚ) (Polynomial.C c) from rfl,
    Submission.CDT.ordAt_algebraMap, Polynomial.rootMultiplicity_C]
  norm_num

private lemma cf_ne_zero {c : ℚ} (hc : c ≠ 0) : cf c ≠ 0 := by
  rw [show cf c = algebraMap (Polynomial ℚ) (RatFunc ℚ) (Polynomial.C c) from rfl]
  exact RatFunc.algebraMap_ne_zero (Polynomial.C_ne_zero.mpr hc)

/-- The quotient rule in the form used by the endgame: `(p/q)' · q² = p'q - pq'`. -/
private lemma dRat_div_mul (u v : Polynomial ℚ) (hv : v ≠ 0) :
    Submission.CDT.dRat ((u : RatFunc ℚ) / (v : RatFunc ℚ)) * (v : RatFunc ℚ) ^ 2
      = (u.derivative : RatFunc ℚ) * (v : RatFunc ℚ)
        - (u : RatFunc ℚ) * (v.derivative : RatFunc ℚ) := by
  rw [show ((u : RatFunc ℚ) / (v : RatFunc ℚ))
      = (algebraMap (Polynomial ℚ) (RatFunc ℚ) u / algebraMap (Polynomial ℚ) (RatFunc ℚ) v)
      from rfl]
  rw [Submission.CDT.dRat_div]
  have hvR : (v : RatFunc ℚ) ≠ 0 := RatFunc.algebraMap_ne_zero hv
  rw [show (algebraMap (Polynomial ℚ) (RatFunc ℚ) v) ^ 2 = (v : RatFunc ℚ) ^ 2 from rfl]
  rw [div_mul_cancel₀ _ (pow_ne_zero 2 hvR)]
  simp [map_sub, map_mul]

/-- A vanishing Wronskian for polynomials: `u'v = uv'` with `v ≠ 0` makes `u/v` a constant. -/
private lemma exists_const_of_wronskian_eq_zero (u v : Polynomial ℚ) (hv : v ≠ 0)
    (h : u.derivative * v - u * v.derivative = 0) :
    ∃ c : ℚ, (u : RatFunc ℚ) = cf c * (v : RatFunc ℚ) := by
  have hvR : (v : RatFunc ℚ) ≠ 0 := RatFunc.algebraMap_ne_zero hv
  have hd : Submission.CDT.dRat ((u : RatFunc ℚ) / (v : RatFunc ℚ)) = 0 := by
    have hm := dRat_div_mul u v hv
    have hzu : (u.derivative : RatFunc ℚ) * (v : RatFunc ℚ)
        - (u : RatFunc ℚ) * (v.derivative : RatFunc ℚ) = 0 := by
      have h' := congrArg (algebraMap (Polynomial ℚ) (RatFunc ℚ)) h
      rw [map_sub, map_mul, map_mul, map_zero] at h'
      exact h'
    rw [hzu] at hm
    exact (mul_eq_zero.mp hm).resolve_right (pow_ne_zero 2 hvR)
  obtain ⟨c, hc⟩ := Submission.CDT.exists_const_of_dRat_eq_zero hd
  refine ⟨c, ?_⟩
  have h2 := congrArg (fun x => x * (v : RatFunc ℚ)) hc
  rw [div_mul_cancel₀ _ hvR] at h2
  exact h2.trans (congrArg (fun x => x * (v : RatFunc ℚ)) (Submission.CDT.am_C' c).symm)

/-- **The endgame.**  The two polynomial relations produced by `Work.C7b.four_elim` (after
`Work.C7b.indep_three` has killed its coefficients) are inconsistent when `p3 ≠ 0`. -/
private lemma endgame_contradiction (p1 p2 p3 : Polynomial ℚ) (hp3 : p3 ≠ 0)
    (hD2 : Polynomial.X * (1 - Polynomial.X) * (p3 * p2.derivative - p3.derivative * p2) = 0)
    (hD1 : Polynomial.X * (1 - Polynomial.X) * (p3 * p1.derivative - p3.derivative * p1)
        - 2 * Polynomial.X * p2 * p3 - (1 - Polynomial.X) * p3 ^ 2 = 0) : False := by
  have hX : (Polynomial.X : Polynomial ℚ) ≠ 0 := Polynomial.X_ne_zero
  have h1X : (1 - Polynomial.X : Polynomial ℚ) ≠ 0 := by
    intro h
    have := congrArg (fun p : Polynomial ℚ => p.coeff 0) h
    simp at this
  have hfac : p2.derivative * p3 - p2 * p3.derivative = 0 := by
    have h : p3 * p2.derivative - p3.derivative * p2 = 0 := by
      rcases mul_eq_zero.mp hD2 with h | h
      · rcases mul_eq_zero.mp h with h | h
        · exact absurd h hX
        · exact absurd h h1X
      · exact h
    linear_combination h
  obtain ⟨c, hp2⟩ := exists_const_of_wronskian_eq_zero p2 p3 hp3 hfac
  have hX0 : (RatFunc.X : RatFunc ℚ) ≠ 0 := by
    rw [← RatFunc.algebraMap_X]
    exact RatFunc.algebraMap_ne_zero Polynomial.X_ne_zero
  have h1X0 : (1 - RatFunc.X : RatFunc ℚ) ≠ 0 := by
    rw [show (1 - RatFunc.X : RatFunc ℚ)
        = algebraMap (Polynomial ℚ) (RatFunc ℚ) (1 - Polynomial.X) from by
      rw [map_sub, map_one, RatFunc.algebraMap_X]]
    exact RatFunc.algebraMap_ne_zero h1X
  have hA : (RatFunc.X : RatFunc ℚ) * (1 - RatFunc.X) ≠ 0 := mul_ne_zero hX0 h1X0
  -- transfer the `D1`-relation to `ℚ(x)`, in the orientation of `dRat_div_mul`
  have hD1'' : Polynomial.X * (1 - Polynomial.X)
      * (p1.derivative * p3 - p1 * p3.derivative)
      - 2 * Polynomial.X * p2 * p3 - (1 - Polynomial.X) * p3 ^ 2 = 0 := by
    rw [show p3 * p1.derivative - p3.derivative * p1
        = p1.derivative * p3 - p1 * p3.derivative from by ring] at hD1
    exact hD1
  have hD1R : (RatFunc.X : RatFunc ℚ) * (1 - RatFunc.X)
        * ((p1.derivative : RatFunc ℚ) * (p3 : RatFunc ℚ)
            - (p1 : RatFunc ℚ) * (p3.derivative : RatFunc ℚ))
      - 2 * (RatFunc.X : RatFunc ℚ) * (p2 : RatFunc ℚ) * (p3 : RatFunc ℚ)
      - (1 - RatFunc.X) * (p3 : RatFunc ℚ) ^ 2 = 0 := by
    have h := congrArg (algebraMap (Polynomial ℚ) (RatFunc ℚ)) hD1''
    simp only [map_sub, map_mul, map_pow, map_one, map_zero, map_ofNat,
      RatFunc.algebraMap_X] at h
    simpa using h
  have hmul := dRat_div_mul p1 p3 hp3
  have hkey : (RatFunc.X : RatFunc ℚ) * (1 - RatFunc.X)
        * (Submission.CDT.dRat ((p1 : RatFunc ℚ) / (p3 : RatFunc ℚ)) * (p3 : RatFunc ℚ) ^ 2)
      = (2 * cf c * (RatFunc.X : RatFunc ℚ) + (1 - RatFunc.X)) * (p3 : RatFunc ℚ) ^ 2 := by
    rw [hmul]
    have h := hD1R
    rw [hp2] at h
    linear_combination h
  have hβ : (RatFunc.X : RatFunc ℚ) * (1 - RatFunc.X)
        * Submission.CDT.dRat ((p1 : RatFunc ℚ) / (p3 : RatFunc ℚ))
      = 2 * cf c * (RatFunc.X : RatFunc ℚ) + (1 - RatFunc.X) := by
    have hv : (p3 : RatFunc ℚ) ^ 2 ≠ 0 := pow_ne_zero 2 (RatFunc.algebraMap_ne_zero hp3)
    have h2 : ((RatFunc.X : RatFunc ℚ) * (1 - RatFunc.X)
          * Submission.CDT.dRat ((p1 : RatFunc ℚ) / (p3 : RatFunc ℚ))) * (p3 : RatFunc ℚ) ^ 2
        = (2 * cf c * (RatFunc.X : RatFunc ℚ) + (1 - RatFunc.X)) * (p3 : RatFunc ℚ) ^ 2 := by
      rw [← hkey]; ring
    exact mul_right_cancel₀ hv h2
  have hβ' : Submission.CDT.dRat ((p1 : RatFunc ℚ) / (p3 : RatFunc ℚ))
      = (RatFunc.X : RatFunc ℚ)⁻¹ + 2 * cf c / (1 - RatFunc.X) := by
    have h3 : Submission.CDT.dRat ((p1 : RatFunc ℚ) / (p3 : RatFunc ℚ))
        = (2 * cf c * (RatFunc.X : RatFunc ℚ) + (1 - RatFunc.X))
          / ((RatFunc.X : RatFunc ℚ) * (1 - RatFunc.X)) := by
      rw [eq_div_iff hA]
      linear_combination hβ
    rw [h3]
    field_simp
    ring
  -- `2c/(1-X)` has no pole at `0` (`ordAt 0 = 0`), while `X⁻¹` has a simple pole there
  have hy : Submission.CDT.ordAt (0 : ℚ) (2 * cf c / (1 - RatFunc.X)) = 0 := by
    rcases eq_or_ne c 0 with hc | hc
    · subst hc
      have h0 : (2 * cf 0 / (1 - RatFunc.X)) = 0 := by
        rw [show cf 0 = 0 from by
          rw [show cf 0 = algebraMap (Polynomial ℚ) (RatFunc ℚ) (Polynomial.C 0) from rfl]; simp]
        simp
      rw [h0]
      exact Submission.CDT.ordAt_zero (0 : ℚ)
    · rw [two_cf_div]
      rw [Submission.CDT.ordAt_mul (0 : ℚ) (cf_ne_zero (by positivity)) (inv_ne_zero h1X0),
        Submission.CDT.ordAt_inv (0 : ℚ) h1X0, ordAt_zero_one_sub_X,
        ordAt_zero_cf]
      ring
  rcases eq_or_ne c 0 with hc0 | hc0
  · subst hc0
    have h := Submission.CDT.ordAt_dRat_ne_neg_one (0 : ℚ) ((p1 : RatFunc ℚ) / (p3 : RatFunc ℚ))
    rw [hβ'] at h
    refine h ?_
    rw [show cf 0 = 0 from by
      rw [show cf 0 = algebraMap (Polynomial ℚ) (RatFunc ℚ) (Polynomial.C 0) from rfl]; simp]
    simp only [mul_zero, zero_div, add_zero]
    exact ordAt_zero_X_inv
  · have hyne : (2 * cf c / (1 - RatFunc.X)) ≠ 0 := by
      intro hh
      rw [two_cf_div] at hh
      rcases mul_eq_zero.mp hh with h1 | h1
      · exact cf_ne_zero (by positivity) h1
      · exact inv_ne_zero h1X0 h1
    have h := Submission.CDT.ordAt_dRat_ne_neg_one (0 : ℚ) ((p1 : RatFunc ℚ) / (p3 : RatFunc ℚ))
    rw [hβ'] at h
    rw [Submission.CDT.ordAt_add_of_lt (0 : ℚ) (inv_ne_zero hX0) hyne (by
      rw [ordAt_zero_X_inv, hy]; norm_num), ordAt_zero_X_inv] at h
    exact h rfl

end Endgame

theorem indep_four :
    Submission.CDTPlan.PolyIndependent (fun i : Fin 4 => ![1, Work.C7.Lps, Work.C7.Lps ^ 2, Work.C7.Li2ps] i) := by
  intro P hP
  -- the relation in explicit form
  have hrel : (P 0 : PowerSeries ℚ) + (P 1 : PowerSeries ℚ) * Lps
      + (P 2 : PowerSeries ℚ) * Lps ^ 2 + (P 3 : PowerSeries ℚ) * Li2ps = 0 := by
    simpa [Fin.sum_univ_four] using hP
  intro i
  by_cases h3 : P 3 = 0
  · -- `P₃ = 0`: only `1, L, L²` occur
    have hrel' : (P 0 : PowerSeries ℚ) + (P 1 : PowerSeries ℚ) * Lps
        + (P 2 : PowerSeries ℚ) * Lps ^ 2 = 0 := by
      rw [h3] at hrel
      simpa using hrel
    have hH : ∀ j : Fin 3, ![P 0, P 1, P 2] j = 0 :=
      Work.C7.indep_small.2 (fun j : Fin 3 => ![P 0, P 1, P 2] j) (by
        rw [Fin.sum_univ_three]
        simpa using hrel')
    fin_cases i
    · exact hH 0
    · exact hH 1
    · exact hH 2
    · exact h3
  · -- `P₃ ≠ 0`: eliminate `Li₂` between the relation and its derivative
    have helim := Work.C7b.four_elim (P 0) (P 1) (P 2) (P 3) hrel
    have hH : ∀ j : Fin 3,
        ![(Polynomial.X * (1 - Polynomial.X) * (P 3 * (P 0).derivative - (P 3).derivative * (P 0))
              - Polynomial.X * (P 1) * (P 3)),
          (Polynomial.X * (1 - Polynomial.X) * (P 3 * (P 1).derivative - (P 3).derivative * (P 1))
              - 2 * Polynomial.X * (P 2) * (P 3) - (1 - Polynomial.X) * (P 3) ^ 2),
          (Polynomial.X * (1 - Polynomial.X) * (P 3 * (P 2).derivative - (P 3).derivative * (P 2)))] j
        = 0 :=
      Work.C7.indep_small.2 _
        (by rw [Fin.sum_univ_three]; simpa using helim)
    exact (endgame_contradiction (P 1) (P 2) (P 3) h3 (hH 2) (hH 1)).elim

end Work.C7
