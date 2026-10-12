import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.BoseBox.Nodes
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.FRK.zeroCellArith` — the zero-cell row's diluteness arithmetic

The `k = 0` (zero-momentum cell) part of FS's cubic term is bounded, in
`Submission/Work/BoseBoxFock/FRK/potCubicZeroCell_exists.lean`, by the product of
the two Cauchy–Schwarz rows `zeroCellRow_le` and `zeroCellSX_le` (both proved in
this directory), the χ/θ-frame constants, and the *diluteness factor*

    a·ℓ⁻¹·√(𝓜(d+2))      (ℓ = sideAt μ a,  𝓜 = bigM (paramsAt μ a) a μ),

where `n ≤ 2μℓ³` for the low-band state turns it into the factor
`a·ℓ⁻¹·√(2 μ ℓ³ 𝓜)` treated here.  The lemma proved in this file is exactly the
arithmetic that converts that factor into `√2·(μa³)^{1/9}`, which the consumer
then pays against the low-band gap `γℓ⁻²n₊`:

    a·ℓ⁻¹·√(2 μ ℓ³ 𝓜)  ≤  √2·(μ a³)^{1/9} .

## The computation

At the diluteness `t = μ a³` FS's parameter choice gives (see `Basic.lean`)

    K_ℓ = t^{-3/646} ,   ℓ = K_ℓ(μa)^{-1/2} = a·t^{-163/323} ,
    μ ℓ³ = t^{-166/323} ,   𝓜 = K_M t^{-1/4} = t^{-327/1292} ,

so the left-hand side is an explicit monomial in `t`:

    a ℓ⁻¹ = t^{163/323} ,   2 μ ℓ³ 𝓜 = 2 t^{-991/1292} ,
    √(2 μ ℓ³ 𝓜) = √2·t^{-991/2584} ,
    LHS = √2·t^{163/323 - 991/2584} = √2·t^{313/2584} .

Since `313/2584 ≥ 1/9` (`2817 ≥ 2584`) and `0 < t ≤ 1`, the exponent comparison
`t^{313/2584} ≤ t^{1/9}` (`Real.rpow_le_rpow_of_exponent_ge`) closes the goal.
The inequality is therefore *sharp* at the extreme diluteness `μa³ = 1`; the
margin `t^{313/2584 - 1/9} = t^{(2817-2584)/23256} = t^{233/23256}` is what the
diluteness hypothesis buys.

The two closed forms `sideAt`/`bigM` are proved here as `private` lemmas rather
than imported from `Submission.Work.BoseBox.sideAt_large`
(`Work.BoseBox.sideAt_eq_rpow` — the same statement, same proof) so that this
module's import cone stays inside `BoseBox.Word`/`BoseBox.Nodes`.
-/

namespace Work.BoseBoxFock.FRK

/-- Closed form of the box side at FS's parameters: `ℓ = a·(μa³)^{-163/323}`.
This is `Work.BoseBox.sideAt_eq_rpow` (`Submission/Work/BoseBox/sideAt_large.lean`),
reproved locally to keep the import cone minimal. -/
private lemma sideAt_rpow {μ a : ℝ} (hμ : 0 < μ) (ha : 0 < a) :
    Work.BoseBox.sideAt μ a = a * (μ * a ^ 3) ^ (-(163 / 323 : ℝ)) := by
  have hμa3 : 0 < μ * a ^ 3 := by positivity
  -- `(μa)^{-1/2} = a (μa³)^{-1/2}`
  have hsec : (μ * a) ^ (-(1 / 2 : ℝ)) = a * (μ * a ^ 3) ^ (-(1 / 2 : ℝ)) := by
    have h : μ * a = (μ * a ^ 3) / a ^ 2 := by field_simp
    rw [h, Real.div_rpow hμa3.le (by positivity : (0 : ℝ) ≤ a ^ 2)]
    rw [show (a ^ 2 : ℝ) ^ (-(1 / 2 : ℝ)) = a⁻¹ by
      rw [show (a ^ 2 : ℝ) = a ^ (2 : ℕ) by ring, ← Real.rpow_natCast a 2,
        ← Real.rpow_mul ha.le]
      norm_num
      rw [Real.rpow_neg_one]]
    rw [div_eq_mul_inv, inv_inv]
    ring
  -- unfold `sideAt` at the parameters `fsParams (μa³)`
  rw [show Work.BoseBox.sideAt μ a
      = (μ * a ^ 3) ^ (-(3 / 646 : ℝ)) * (μ * a) ^ (-(1 / 2 : ℝ)) by
    simp only [Work.BoseBox.sideAt, Work.BoseBox.boxSide, Work.BoseBox.paramsAt,
      Work.BoseBox.fsParams, Work.BoseBox.fsXp]
    norm_num]
  rw [hsec,
    show (μ * a ^ 3) ^ (-(3 / 646 : ℝ)) * (a * (μ * a ^ 3) ^ (-(1 / 2 : ℝ)))
      = a * ((μ * a ^ 3) ^ (-(3 / 646 : ℝ)) * (μ * a ^ 3) ^ (-(1 / 2 : ℝ))) by ring,
    ← Real.rpow_add hμa3]
  congr 1
  norm_num

/-- The matrix window at FS's parameters: `𝓜 = K_M(μa³)^{-1/4} = (μa³)^{-327/1292}`. -/
private lemma bigM_paramsAt {μ a : ℝ} (hμ : 0 < μ) (ha : 0 < a) :
    Work.BoseBox.bigM (Work.BoseBox.paramsAt μ a) a μ
      = (μ * a ^ 3) ^ (-(327 / 1292 : ℝ)) := by
  have ht : 0 < μ * a ^ 3 := by positivity
  simp only [Work.BoseBox.bigM, Work.BoseBox.paramsAt, Work.BoseBox.fsParams,
    Work.BoseBox.fsXp]
  rw [← Real.rpow_add ht]
  congr 1
  norm_num

/-- `√(2·t^r) = √2·t^{r/2}` for `t > 0`. -/
private lemma sqrt_two_mul_rpow {t r : ℝ} (ht : 0 < t) :
    Real.sqrt (2 * t ^ r) = Real.sqrt 2 * t ^ (r / 2) := by
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
  simp only [Real.sqrt_eq_rpow]
  rw [← Real.rpow_mul ht.le]
  congr 1
  ring_nf

/-- **The zero-cell arithmetic.**  At FS's parameters the box side `ℓ = sideAt μ a`
and the matrix window `𝓜 = bigM (paramsAt μ a) a μ` are monomials in the
diluteness `t = μa³` (`sideAt_rpow`, `bigM_paramsAt`); the whole left-hand side
collapses to `√2·t^{313/2584}`, and `313/2584 ≥ 1/9`. -/
theorem zeroCellArith {μ a : ℝ} (hμ : 0 < μ) (ha : 0 < a) (ht : μ * a ^ 3 ≤ 1) :
    a * (Work.BoseBox.sideAt μ a)⁻¹
      * Real.sqrt (2 * μ * (Work.BoseBox.sideAt μ a) ^ 3
          * Work.BoseBox.bigM (Work.BoseBox.paramsAt μ a) a μ)
    ≤ Real.sqrt 2 * (μ * a ^ 3) ^ (1 / 9 : ℝ) := by
  have htpos : 0 < μ * a ^ 3 := by positivity
  -- ## the three closed forms of the factors
  have hside : Work.BoseBox.sideAt μ a = a * (μ * a ^ 3) ^ (-(163 / 323 : ℝ)) :=
    sideAt_rpow hμ ha
  have hell : μ * (Work.BoseBox.sideAt μ a) ^ 3 = (μ * a ^ 3) ^ (-(166 / 323 : ℝ)) := by
    simpa only [Work.BoseBox.sideAt, Work.BoseBox.paramsAt] using
      Work.BoseBox.mu_ell_cube_fsParams (μ := μ) (a := a) hμ ha
  have hM := bigM_paramsAt (μ := μ) (a := a) hμ ha
  -- ## `a ℓ⁻¹ = t^{163/323}`
  have haell : a * (Work.BoseBox.sideAt μ a)⁻¹ = (μ * a ^ 3) ^ (163 / 323 : ℝ) := by
    rw [hside, mul_inv_rev, Real.rpow_neg htpos.le (163 / 323), inv_inv]
    rw [show a * ((μ * a ^ 3) ^ (163 / 323 : ℝ) * a⁻¹)
        = a * a⁻¹ * (μ * a ^ 3) ^ (163 / 323 : ℝ) by ring,
      mul_inv_cancel₀ (ne_of_gt ha), one_mul]
  -- ## `2 μ ℓ³ 𝓜 = 2 t^{-991/1292}`
  have hinner : 2 * μ * (Work.BoseBox.sideAt μ a) ^ 3
        * Work.BoseBox.bigM (Work.BoseBox.paramsAt μ a) a μ
      = 2 * (μ * a ^ 3) ^ (-(991 / 1292 : ℝ)) := by
    rw [show 2 * μ * (Work.BoseBox.sideAt μ a) ^ 3
          * Work.BoseBox.bigM (Work.BoseBox.paramsAt μ a) a μ
        = 2 * (μ * (Work.BoseBox.sideAt μ a) ^ 3
          * Work.BoseBox.bigM (Work.BoseBox.paramsAt μ a) a μ) by ring]
    rw [hell, hM, ← Real.rpow_add htpos]
    congr 1
    norm_num
  -- ## the square root
  have hsqrt : Real.sqrt (2 * μ * (Work.BoseBox.sideAt μ a) ^ 3
        * Work.BoseBox.bigM (Work.BoseBox.paramsAt μ a) a μ)
      = Real.sqrt 2 * (μ * a ^ 3) ^ (-(991 / 2584 : ℝ)) := by
    rw [hinner, sqrt_two_mul_rpow htpos]
    congr 1
    norm_num
  -- ## the assembly: LHS `= √2 t^{313/2584} ≤ √2 t^{1/9}`
  calc a * (Work.BoseBox.sideAt μ a)⁻¹
        * Real.sqrt (2 * μ * (Work.BoseBox.sideAt μ a) ^ 3
            * Work.BoseBox.bigM (Work.BoseBox.paramsAt μ a) a μ)
      = (μ * a ^ 3) ^ (163 / 323 : ℝ)
          * (Real.sqrt 2 * (μ * a ^ 3) ^ (-(991 / 2584 : ℝ))) := by rw [haell, hsqrt]
    _ = Real.sqrt 2 * ((μ * a ^ 3) ^ (163 / 323 : ℝ)
          * (μ * a ^ 3) ^ (-(991 / 2584 : ℝ))) := by ring
    _ = Real.sqrt 2 * (μ * a ^ 3) ^ (313 / 2584 : ℝ) := by
        rw [← Real.rpow_add htpos]
        congr 1
        norm_num
    _ ≤ Real.sqrt 2 * (μ * a ^ 3) ^ (1 / 9 : ℝ) :=
        mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow_of_exponent_ge htpos ht (by norm_num))
          (Real.sqrt_nonneg 2)

end Work.BoseBoxFock.FRK
