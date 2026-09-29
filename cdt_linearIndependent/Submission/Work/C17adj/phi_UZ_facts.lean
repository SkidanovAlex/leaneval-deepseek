import Mathlib
import Submission.Work.C17adj.phi_defs

/-!
# Top-degree data for the coefficient polynomials `PhiU, PhiV, PhiZ`

`Work.C17adj.PhiU, PhiV, PhiZ` are the `W`-, `W'`-, `W''`-coefficients of the cleared adjoint
numerator `PhiNum` (see `Submission.Work.C17adj.phi_defs`):

* `PhiU = P₂·(2·D'² − D·D'') − A·D'·D + C·D²`,
* `PhiV = −2·P₂·D·D' + A·D²`,
* `PhiZ = P₂·D²`,

with `D = DadjL`, `A = AadjL a b`, `C = CadjL a b`, `P₂ = P2Cm a b`.

From the top-degree data of `P₂, A, C, D, D', D''` (`P2Cm` has degree `7` and top coefficient `1`,
`AadjL` `6`/`11`, `CadjL` `5`/`25`, `DadjL` `10`/`1`, `D'` `9`/`10`, `D''` `8`/`90`) the top-degree
data of the three coefficient polynomials follows by collecting the leading contributions:

* `PhiU`: `25`/`25`  —  `P₂·(2D'² − D D'')` contributes `1·(2·10·10 − 1·90) = 110` at degree `25`,
  `−A·D'·D` contributes `−11·10·1 = −110`, `C·D²` contributes `25·1 = 25`;
* `PhiV`: `26`/`−9` —  `−2·P₂·D·D'` contributes `−2·1·1·10 = −20`, `A·D²` contributes `11·1 = 11`;
* `PhiZ`: `27`/`1`  —  `1·1·1 = 1`.

The bookkeeping is packaged in the predicate `IsTopCoeff p n c` ("`natDegree p ≤ n` and
`coeff n = c`"), which is closed under products (`IsTopCoeff.mul`, using the lemma
`Work.C17adj.coeff_mul_natDegree_le` of `phi_defs`), sums (`IsTopCoeff.add`), differences
(`IsTopCoeff.sub`), negation (`IsTopCoeff.neg`) and the constants (`IsTopCoeff.C`,
`IsTopCoeff.natCast`).
-/

open Polynomial

namespace Work.C17adj

/-- Top-degree data of a polynomial over `ℂ`: degree at most `n`, with `n`-th coefficient `c`. -/
def IsTopCoeff (p : Polynomial ℂ) (n : ℕ) (c : ℂ) : Prop := p.natDegree ≤ n ∧ p.coeff n = c

namespace IsTopCoeff

/-- The top-degree data of a product: degrees add, top coefficients multiply. -/
lemma mul {p q : Polynomial ℂ} {m t n : ℕ} {c d e : ℂ}
    (hp : IsTopCoeff p m c) (hq : IsTopCoeff q t d) (hn : m + t = n) (he : c * d = e) :
    IsTopCoeff (p * q) n e := by
  obtain ⟨h1, h2⟩ := hp
  obtain ⟨h3, h4⟩ := hq
  have hcoe : (p * q).coeff (m + t) = c * d := by
    rw [coeff_mul_natDegree_le p q m t h1 h3, h2, h4]
  refine ⟨?_, ?_⟩
  · rw [← hn]
    exact le_trans Polynomial.natDegree_mul_le (add_le_add h1 h3)
  · rw [← hn, hcoe, he]

/-- The top-degree data of a sum of two polynomials of degree at most `n`. -/
lemma add {p q : Polynomial ℂ} {n : ℕ} {c d e : ℂ}
    (hp : IsTopCoeff p n c) (hq : IsTopCoeff q n d) (he : c + d = e) :
    IsTopCoeff (p + q) n e := by
  obtain ⟨h1, h2⟩ := hp
  obtain ⟨h3, h4⟩ := hq
  refine ⟨le_trans (Polynomial.natDegree_add_le p q) (max_le h1 h3), ?_⟩
  rw [Polynomial.coeff_add, h2, h4, he]

/-- The top-degree data of a difference of two polynomials of degree at most `n`. -/
lemma sub {p q : Polynomial ℂ} {n : ℕ} {c d e : ℂ}
    (hp : IsTopCoeff p n c) (hq : IsTopCoeff q n d) (he : c - d = e) :
    IsTopCoeff (p - q) n e := by
  obtain ⟨h1, h2⟩ := hp
  obtain ⟨h3, h4⟩ := hq
  refine ⟨le_trans (Polynomial.natDegree_sub_le p q) (max_le h1 h3), ?_⟩
  rw [Polynomial.coeff_sub, h2, h4, he]

/-- The top-degree data of a negation. -/
lemma neg {p : Polynomial ℂ} {n : ℕ} {c d : ℂ} (hp : IsTopCoeff p n c) (hd : -c = d) :
    IsTopCoeff (-p) n d := by
  obtain ⟨h1, h2⟩ := hp
  refine ⟨by rw [Polynomial.natDegree_neg]; exact h1, ?_⟩
  rw [Polynomial.coeff_neg, h2, hd]

/-- The top-degree data of a constant polynomial. -/
lemma C (k : ℂ) : IsTopCoeff (Polynomial.C k) 0 k := by
  refine ⟨?_, ?_⟩
  · simp
  · simp [Polynomial.coeff_C]

/-- The top-degree data of a natural number, viewed as a constant polynomial. -/
lemma natCast (n : ℕ) : IsTopCoeff (n : Polynomial ℂ) 0 (n : ℂ) := by
  obtain ⟨h1, h2⟩ := C (n : ℂ)
  rw [Polynomial.C_eq_natCast] at h1 h2
  exact ⟨h1, h2⟩

end IsTopCoeff

theorem phi_UZ_facts (a b : ℚ)
    (hP2 : (Work.C17adj.P2Cm a b).natDegree ≤ 7 ∧ (Work.C17adj.P2Cm a b).coeff 7 = 1)
    (hA : (Work.C17adj.AadjL a b).natDegree ≤ 6 ∧ (Work.C17adj.AadjL a b).coeff 6 = 11)
    (hC : (Work.C17adj.CadjL a b).natDegree ≤ 5 ∧ (Work.C17adj.CadjL a b).coeff 5 = 25)
    (hD : Work.C17adj.DadjL.natDegree ≤ 10 ∧ Work.C17adj.DadjL.coeff 10 = 1)
    (hD1 : Work.C17adj.DadjL.derivative.natDegree ≤ 9 ∧ Work.C17adj.DadjL.derivative.coeff 9 = 10)
    (hD2 : Work.C17adj.DadjL.derivative.derivative.natDegree ≤ 8 ∧
      Work.C17adj.DadjL.derivative.derivative.coeff 8 = 90) :
    (Work.C17adj.PhiU a b).natDegree ≤ 25 ∧ (Work.C17adj.PhiU a b).coeff 25 = 25 ∧
    (Work.C17adj.PhiV a b).natDegree ≤ 26 ∧ (Work.C17adj.PhiV a b).coeff 26 = -9 ∧
    (Work.C17adj.PhiZ a b).natDegree ≤ 27 ∧ (Work.C17adj.PhiZ a b).coeff 27 = 1 := by
  have hP2t : IsTopCoeff (P2Cm a b) 7 1 := hP2
  have hAt : IsTopCoeff (AadjL a b) 6 11 := hA
  have hCt : IsTopCoeff (CadjL a b) 5 25 := hC
  have hDt : IsTopCoeff DadjL 10 1 := hD
  have hD1t : IsTopCoeff DadjL.derivative 9 10 := hD1
  have hD2t : IsTopCoeff DadjL.derivative.derivative 8 90 := hD2
  -- the common building blocks
  have hDsq : IsTopCoeff (DadjL ^ 2) 20 1 := by
    rw [pow_two]
    exact IsTopCoeff.mul hDt hDt (by norm_num) (by norm_num)
  have hD1sq : IsTopCoeff (DadjL.derivative ^ 2) 18 100 := by
    rw [pow_two]
    exact IsTopCoeff.mul hD1t hD1t (by norm_num) (by norm_num)
  have hDD2 : IsTopCoeff (DadjL * DadjL.derivative.derivative) 18 90 :=
    IsTopCoeff.mul hDt hD2t (by norm_num) (by norm_num)
  -- `PhiU`
  have ht1 : IsTopCoeff (2 * DadjL.derivative ^ 2) 18 200 :=
    IsTopCoeff.mul (IsTopCoeff.natCast 2) hD1sq (by norm_num) (by norm_num)
  have hBr : IsTopCoeff (2 * DadjL.derivative ^ 2 - DadjL * DadjL.derivative.derivative) 18 110 :=
    IsTopCoeff.sub ht1 hDD2 (by norm_num)
  have hP2Br : IsTopCoeff
      (P2Cm a b * (2 * DadjL.derivative ^ 2 - DadjL * DadjL.derivative.derivative)) 25 110 :=
    IsTopCoeff.mul hP2t hBr (by norm_num) (by norm_num)
  have hAD'D : IsTopCoeff (AadjL a b * DadjL.derivative * DadjL) 25 110 := by
    have h1 : IsTopCoeff (AadjL a b * DadjL.derivative) 15 110 :=
      IsTopCoeff.mul hAt hD1t (by norm_num) (by norm_num)
    exact IsTopCoeff.mul h1 hDt (by norm_num) (by norm_num)
  have hCDsq : IsTopCoeff (CadjL a b * DadjL ^ 2) 25 25 :=
    IsTopCoeff.mul hCt hDsq (by norm_num) (by norm_num)
  have hdiff : IsTopCoeff
      (P2Cm a b * (2 * DadjL.derivative ^ 2 - DadjL * DadjL.derivative.derivative)
        - AadjL a b * DadjL.derivative * DadjL) 25 0 :=
    IsTopCoeff.sub hP2Br hAD'D (by norm_num)
  have hU : IsTopCoeff (PhiU a b) 25 25 := by
    rw [PhiU]
    exact IsTopCoeff.add hdiff hCDsq (by norm_num)
  -- `PhiV`
  have hVt1 : IsTopCoeff (2 * P2Cm a b * DadjL * DadjL.derivative) 26 20 := by
    have h1 : IsTopCoeff (2 * P2Cm a b) 7 2 :=
      IsTopCoeff.mul (IsTopCoeff.natCast 2) hP2t (by norm_num) (by norm_num)
    have h2 : IsTopCoeff (2 * P2Cm a b * DadjL) 17 2 :=
      IsTopCoeff.mul h1 hDt (by norm_num) (by norm_num)
    exact IsTopCoeff.mul h2 hD1t (by norm_num) (by norm_num)
  have hVterm : IsTopCoeff (-2 * P2Cm a b * DadjL * DadjL.derivative) 26 (-20) := by
    have hform : (-2 * P2Cm a b * DadjL * DadjL.derivative : Polynomial ℂ)
        = -(2 * P2Cm a b * DadjL * DadjL.derivative) := by ring
    rw [hform]
    exact IsTopCoeff.neg hVt1 (by norm_num)
  have hV2 : IsTopCoeff (AadjL a b * DadjL ^ 2) 26 11 :=
    IsTopCoeff.mul hAt hDsq (by norm_num) (by norm_num)
  have hV : IsTopCoeff (PhiV a b) 26 (-9) := by
    rw [PhiV]
    exact IsTopCoeff.add hVterm hV2 (by norm_num)
  -- `PhiZ`
  have hZ : IsTopCoeff (PhiZ a b) 27 1 := by
    rw [PhiZ]
    exact IsTopCoeff.mul hP2t hDsq (by norm_num) (by norm_num)
  exact ⟨hU.1, hU.2, hV.1, hV.2, hZ.1, hZ.2⟩

end Work.C17adj
