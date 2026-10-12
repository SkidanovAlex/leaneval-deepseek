import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.BoseFixR.Arith
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission/Work/BoseFixR/AbsorbCloseFix.lean` — the §11 *close* absorption, corrected

## Why this file exists

The requested lemma `Work.BoseFixR.AbsorbClose` (`Submission/Work/BoseFixR/AbsorbClose.lean`)
is **false as stated**: the §11 close comparison needs the LHY term at the condensate
density `ρ`, namely `4π·lhyC·ρ²aℓ³√(ρa³)`, to dominate the LHY term of the target
`ℓ³Λ = −4πμ²aℓ³ + 4π·lhyC·μ²aℓ³√t − 4πμ²aℓ³K t^{1/2+η₀}` at `t`.  Comparing the two
requires `√(μa³) ≥ √t` — the diluteness identity of the corpus (`Work.BoseFixR.dil`,
`t = μ·a³`) — and `AbsorbClose` has no hypothesis relating the free variable `t` to `μa³`.

Concretely, with `a = ℓ = 1`, `t = 2^{-6460}`, `μ = t²` (so `μa³ = t² ≪ t`), `R = 0`,
`C₄ = C₆ = 0`, `η₀ = 1/1615`, `K = bigK 1 0 0 0` and `ρ = μ(1 − t^{3/323})` all the
hypotheses of `AbsorbClose` hold, while the two sides differ by
`4πμ²√t·(lhyC − K·t^{η₀} − lhyC·√t·(1−t^{3/323})^{5/2}) > 0`
(at these values `t^{η₀} = 1/16`, so `lhyC − K/16 = (5/8)lhyC − 1/(64π) > 3`, while the
remaining term is `≤ lhyC·2^{-3230}`; here `lhyC = 128/(15√π)`, `4 < lhyC < 5`).

This module proves the corrected statement: the same inequality with the single extra
hypothesis `hμa : t ≤ μ * a ^ 3` (the corpus always instantiates `t := dil v μ = μ·(a v)³`,
for which `hμa` is `le_refl`).  Nothing else changes; `AbsorbFar` needs no such hypothesis
because its comparison is homogeneous in the target's own `√t`.

## The arithmetic (with `F = 4πμ²aℓ³ > 0`, `r = ρ/μ`)

* LHY at `ρ`: `4π·lhyC·ρ²aℓ³√(ρa³) = lhyC·F·r²√r·√(μa³)` (`ρ² = μ²r²`,
  `√(ρa³) = √r·√(μa³)`).  Since `r ≥ 1 − t^{3/323}` (`hρlo`) and `√(μa³) ≥ √t` (`hμa`),
  `lhyC·F·r²√r√(μa³) ≥ lhyC·F·√t·(1 − 3t^{3/323}) ≥ lhyC·F·√t − 3·lhyC·F·√t·t^{η₀}`,
  using `r²√r ≥ (1−δ)²√(1−δ) ≥ (1−δ)³ ≥ 1−3δ` and `t^{3/323} ≤ t^{η₀`
  (`η₀ ≤ 3/323`, from `hη₃`).
* errors: `errAbs ≤ C₄(3+(R/a)²)·μ²aℓ³·√t·t^{η₀}` and
  `C₆μ²aℓ³√t·Y ≤ C₆(2+(R/a)²)·μ²aℓ³·√t·t^{η₀}`, because every monomial of the two brackets
  is `≤ t^{η₀}` (`η₀` below `9/646`, `2/323`, `1/2`, `1/1615`).
* constant: `C₄(3+(R/a)²) + C₆(2+(R/a)²) + 12π·lhyC ≤ 4πK`, which is `bigK ≤ K`
  multiplied by `4π` (the discarded `12π·lhyC ≤ 24π·lhyC + 1` is slack).
-/

noncomputable section

open scoped Real Topology BigOperators

namespace Work.BoseFixR

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 4000000

/-- `(1-δ)³ ≥ 1 - 3δ` for `δ ≤ 1` (the elementary polynomial bound `δ²(3-δ) ≥ 0`, used in
place of the Bernoulli-type bound `(1-δ)^{5/2} ≥ 1 - (5/2)δ`). -/
lemma one_sub_three_mul_le_cube (δ : ℝ) (h1 : δ ≤ 1) : 1 - 3 * δ ≤ (1 - δ) ^ 3 := by
  have h : (1 - δ) ^ 3 - (1 - 3 * δ) = δ ^ 2 * (3 - δ) := by ring
  nlinarith [sq_nonneg δ, h1]

/-- **FS §11, close case, with the diluteness relation.**  The target `ℓ³Λ(a,K,η₀,μ)` plus
the §8 error is at most the §10 close bound `CloseBoundR`, whenever `K ≥ bigK a R C₄ C₆`,
`t ≤ 1`, `t ≤ μa³` (the corpus's `t = μa³`) and `ρ ≥ μ(1 − t^{3/323})`.

This is the statement of `Work.BoseFixR.AbsorbClose` with the one missing hypothesis `hμa`
added; see the module docstring for the counterexample showing that `hμa` is needed. -/
theorem AbsorbCloseFix {a ℓ t μ R C₄ C₆ K η₀ ρ : ℝ}
    (ha : 0 < a) (hℓ : 0 < ℓ) (hμ : 0 < μ) (hR : 0 ≤ R) (hC₄ : 0 ≤ C₄)
    (hC₆ : 0 ≤ C₆) (hη₀ : 0 ≤ η₀) (hη₂ : η₀ < 2 / 323) (hη₃ : η₀ ≤ 1 / 1615)
    (ht : 0 < t) (ht1 : t ≤ 1) (hK : bigK a R C₄ C₆ ≤ K) (hρ : 0 ≤ ρ)
    (hμa : t ≤ μ * a ^ 3) (hρlo : μ * (1 - t ^ (3 / 323 : ℝ)) ≤ ρ) :
    (-4 * Real.pi * μ ^ 2 * a * ℓ ^ 3
        + 4 * Real.pi * Work.UBB.lhyC * μ ^ 2 * a * ℓ ^ 3 * Real.sqrt t
        - 4 * Real.pi * μ ^ 2 * a * ℓ ^ 3 * K * t ^ (1 / 2 + η₀))
      + errAbs a ℓ t μ R C₄
    ≤ -4 * Real.pi * μ ^ 2 * a * ℓ ^ 3
        + 4 * Real.pi * Work.UBB.lhyC * ρ ^ 2 * a * ℓ ^ 3 * Real.sqrt (ρ * a ^ 3)
        - C₆ * μ ^ 2 * a * ℓ ^ 3 * Real.sqrt t
            * (t ^ (2 / 323 : ℝ) + (R / a) ^ 2 * Real.sqrt t + t ^ (1 / 1615 : ℝ)) := by
  have hπ : 0 < Real.pi := Real.pi_pos
  have hlhyC : 0 < Work.UBB.lhyC := Work.UBB.lhyC_pos
  -- ## exponents: `η₀` lies below all the error exponents
  have he3 : η₀ ≤ 3 / 323 := by
    have h : (1 : ℝ) / 1615 ≤ 3 / 323 := by norm_num
    linarith
  have he_646 : η₀ ≤ 9 / 646 := by
    have h : (2 : ℝ) / 323 ≤ 9 / 646 := by norm_num
    linarith
  have he_half : η₀ ≤ 1 / 2 := by
    have h : (1 : ℝ) / 1615 ≤ 1 / 2 := by norm_num
    linarith
  have hδ1 : t ^ (3 / 323 : ℝ) ≤ 1 := Real.rpow_le_one ht.le ht1 (by norm_num)
  have hδ : t ^ (3 / 323 : ℝ) ≤ t ^ η₀ := rpow_le_rpow_of_le ht ht1 he3
  have h9 : t ^ (9 / 646 : ℝ) ≤ t ^ η₀ := rpow_le_rpow_of_le ht ht1 he_646
  have h2 : t ^ (2 / 323 : ℝ) ≤ t ^ η₀ := rpow_le_rpow_of_le ht ht1 hη₂.le
  have h1615 : t ^ (1 / 1615 : ℝ) ≤ t ^ η₀ := rpow_le_rpow_of_le ht ht1 hη₃
  have hsqrt : Real.sqrt t ≤ t ^ η₀ := by
    rw [Real.sqrt_eq_rpow]
    exact rpow_le_rpow_of_le ht ht1 he_half
  have hR2 : (0 : ℝ) ≤ (R / a) ^ 2 := sq_nonneg _
  -- ## the two error brackets are at most `(3 + (R/a)²)t^{η₀}`, `(2 + (R/a)²)t^{η₀}`
  have hX : t ^ (9 / 646 : ℝ) + t ^ (2 / 323 : ℝ) + (R / a) ^ 2 * Real.sqrt t
      + t ^ (1 / 1615 : ℝ) ≤ (3 + (R / a) ^ 2) * t ^ η₀ := by
    have hr : (R / a) ^ 2 * Real.sqrt t ≤ (R / a) ^ 2 * t ^ η₀ :=
      mul_le_mul_of_nonneg_left hsqrt hR2
    nlinarith [h9, h2, h1615, hr]
  have hY : t ^ (2 / 323 : ℝ) + (R / a) ^ 2 * Real.sqrt t + t ^ (1 / 1615 : ℝ)
      ≤ (2 + (R / a) ^ 2) * t ^ η₀ := by
    have hr : (R / a) ^ 2 * Real.sqrt t ≤ (R / a) ^ 2 * t ^ η₀ :=
      mul_le_mul_of_nonneg_left hsqrt hR2
    nlinarith [h2, h1615, hr]
  -- ## the LHY term at `ρ`: `r²√r ≥ 1 - 3δ` with `r = ρ/μ`, `δ = t^{3/323}`
  have hsub : 1 - t ^ (3 / 323 : ℝ) ≤ ρ / μ := by
    rw [le_div_iff₀ hμ]
    linarith [hρlo]
  have hy0 : 0 ≤ 1 - t ^ (3 / 323 : ℝ) := by linarith [hδ1]
  have hyn : 0 ≤ t ^ (3 / 323 : ℝ) := Real.rpow_nonneg ht.le _
  have hr0 : 0 ≤ ρ / μ := div_nonneg hρ hμ.le
  have hsq : (1 - t ^ (3 / 323 : ℝ)) ^ 2 ≤ 1 - t ^ (3 / 323 : ℝ) := by
    have hmul : 0 ≤ (1 - t ^ (3 / 323 : ℝ)) * (1 - (1 - t ^ (3 / 323 : ℝ))) :=
      mul_nonneg hy0 (by linarith [hyn])
    nlinarith [hmul]
  have hsqrtge : (1 - t ^ (3 / 323 : ℝ)) ≤ Real.sqrt (1 - t ^ (3 / 323 : ℝ)) :=
    Real.le_sqrt_of_sq_le hsq
  have hkey : 1 - 3 * t ^ (3 / 323 : ℝ) ≤ (ρ / μ) ^ 2 * Real.sqrt (ρ / μ) := by
    have hcube : 1 - 3 * t ^ (3 / 323 : ℝ) ≤ (1 - t ^ (3 / 323 : ℝ)) ^ 3 :=
      one_sub_three_mul_le_cube _ hδ1
    have hstep1 : (1 - t ^ (3 / 323 : ℝ)) ^ 3
        ≤ (1 - t ^ (3 / 323 : ℝ)) ^ 2 * Real.sqrt (1 - t ^ (3 / 323 : ℝ)) := by
      have h : (1 - t ^ (3 / 323 : ℝ)) ^ 3
          = (1 - t ^ (3 / 323 : ℝ)) ^ 2 * (1 - t ^ (3 / 323 : ℝ)) := by ring
      rw [h]
      exact mul_le_mul_of_nonneg_left hsqrtge (sq_nonneg _)
    have hstep2 : (1 - t ^ (3 / 323 : ℝ)) ^ 2 * Real.sqrt (1 - t ^ (3 / 323 : ℝ))
        ≤ (ρ / μ) ^ 2 * Real.sqrt (ρ / μ) := by
      have h1 : (1 - t ^ (3 / 323 : ℝ)) ^ 2 ≤ (ρ / μ) ^ 2 := by nlinarith [hsub, hy0]
      have h2' : Real.sqrt (1 - t ^ (3 / 323 : ℝ)) ≤ Real.sqrt (ρ / μ) :=
        Real.sqrt_le_sqrt hsub
      exact mul_le_mul h1 h2' (Real.sqrt_nonneg _) (sq_nonneg _)
    linarith [hcube, hstep1, hstep2]
  -- ## the LHY bound at `ρ`, in the shape of the goal's two LHY terms
  have hsqrtρ : Real.sqrt (ρ * a ^ 3) = Real.sqrt (ρ / μ) * Real.sqrt (μ * a ^ 3) := by
    have h : ρ * a ^ 3 = (ρ / μ) * (μ * a ^ 3) := by
      field_simp
    rw [h, Real.sqrt_mul hr0]
  have hsu : Real.sqrt t ≤ Real.sqrt (μ * a ^ 3) := Real.sqrt_le_sqrt hμa
  have hcore : (1 - 3 * t ^ η₀) * Real.sqrt t
      ≤ (ρ / μ) ^ 2 * Real.sqrt (ρ / μ) * Real.sqrt (μ * a ^ 3) := by
    have h1 : 1 - 3 * t ^ η₀ ≤ (ρ / μ) ^ 2 * Real.sqrt (ρ / μ) := by linarith [hkey, hδ]
    have h2' : (1 - 3 * t ^ η₀) * Real.sqrt t
        ≤ (ρ / μ) ^ 2 * Real.sqrt (ρ / μ) * Real.sqrt t :=
      mul_le_mul_of_nonneg_right h1 (Real.sqrt_nonneg t)
    have h3 : (0 : ℝ) ≤ (ρ / μ) ^ 2 * Real.sqrt (ρ / μ) :=
      mul_nonneg (sq_nonneg _) (Real.sqrt_nonneg _)
    have h4 : (ρ / μ) ^ 2 * Real.sqrt (ρ / μ) * Real.sqrt t
        ≤ (ρ / μ) ^ 2 * Real.sqrt (ρ / μ) * Real.sqrt (μ * a ^ 3) :=
      mul_le_mul_of_nonneg_left hsu h3
    linarith [h2', h4]
  have hρ2 : ρ ^ 2 = μ ^ 2 * (ρ / μ) ^ 2 := by
    field_simp
  have hLHY : Work.UBB.lhyC * (4 * Real.pi * μ ^ 2 * a * ℓ ^ 3 * Real.sqrt t)
      - 3 * Work.UBB.lhyC * (4 * Real.pi * μ ^ 2 * a * ℓ ^ 3 * Real.sqrt t) * t ^ η₀
      ≤ Work.UBB.lhyC * (4 * Real.pi * ρ ^ 2 * a * ℓ ^ 3 * Real.sqrt (ρ * a ^ 3)) := by
    have hfac : (0 : ℝ) ≤ Work.UBB.lhyC * (4 * Real.pi * μ ^ 2 * a * ℓ ^ 3) := by positivity
    have h2' := mul_le_mul_of_nonneg_left hcore hfac
    have he1 : Work.UBB.lhyC * (4 * Real.pi * μ ^ 2 * a * ℓ ^ 3 * Real.sqrt t)
        - 3 * Work.UBB.lhyC * (4 * Real.pi * μ ^ 2 * a * ℓ ^ 3 * Real.sqrt t) * t ^ η₀
        = (Work.UBB.lhyC * (4 * Real.pi * μ ^ 2 * a * ℓ ^ 3)) * ((1 - 3 * t ^ η₀) * Real.sqrt t) := by
      ring
    have he2 : (Work.UBB.lhyC * (4 * Real.pi * μ ^ 2 * a * ℓ ^ 3))
          * ((ρ / μ) ^ 2 * Real.sqrt (ρ / μ) * Real.sqrt (μ * a ^ 3))
        = Work.UBB.lhyC * (4 * Real.pi * ρ ^ 2 * a * ℓ ^ 3 * Real.sqrt (ρ * a ^ 3)) := by
      rw [hsqrtρ, hρ2]
      ring
    rw [he1, ← he2]
    exact h2'
  -- ## the two error terms
  have herr : errAbs a ℓ t μ R C₄
      ≤ C₄ * (3 + (R / a) ^ 2) * (μ ^ 2 * a * ℓ ^ 3 * (Real.sqrt t * t ^ η₀)) := by
    rw [errAbs]
    have h1 : 0 ≤ C₄ * μ ^ 2 * a * ℓ ^ 3 * Real.sqrt t := by positivity
    have h2' := mul_le_mul_of_nonneg_left hX h1
    have he : C₄ * (3 + (R / a) ^ 2) * (μ ^ 2 * a * ℓ ^ 3 * (Real.sqrt t * t ^ η₀))
        = C₄ * μ ^ 2 * a * ℓ ^ 3 * Real.sqrt t * ((3 + (R / a) ^ 2) * t ^ η₀) := by
      ring
    rw [he]
    exact h2'
  have hc6 : C₆ * μ ^ 2 * a * ℓ ^ 3 * Real.sqrt t
        * (t ^ (2 / 323 : ℝ) + (R / a) ^ 2 * Real.sqrt t + t ^ (1 / 1615 : ℝ))
      ≤ C₆ * (2 + (R / a) ^ 2) * (μ ^ 2 * a * ℓ ^ 3 * (Real.sqrt t * t ^ η₀)) := by
    have h1 : 0 ≤ C₆ * μ ^ 2 * a * ℓ ^ 3 * Real.sqrt t := by positivity
    have h2' := mul_le_mul_of_nonneg_left hY h1
    have he : C₆ * (2 + (R / a) ^ 2) * (μ ^ 2 * a * ℓ ^ 3 * (Real.sqrt t * t ^ η₀))
        = C₆ * μ ^ 2 * a * ℓ ^ 3 * Real.sqrt t * ((2 + (R / a) ^ 2) * t ^ η₀) := by
      ring
    rw [he]
    exact h2'
  -- ## the constant, and the product inequality that absorbs the `K t^{1/2+η₀}` term
  have hexpand : C₄ * (3 + (R / a) ^ 2) + C₆ * (2 + (R / a) ^ 2)
      + 12 * Real.pi * Work.UBB.lhyC ≤ 4 * Real.pi * K := by
    have h1 : C₄ * (3 + (R / a) ^ 2) + C₆ * (2 + (R / a) ^ 2)
        + 12 * Real.pi * Work.UBB.lhyC ≤ 4 * Real.pi * bigK a R C₄ C₆ := by
      have hπ4 : (0 : ℝ) < 4 * Real.pi := by positivity
      rw [bigK, mul_comm (4 * Real.pi), div_mul_cancel₀ _ (ne_of_gt hπ4)]
      nlinarith [hlhyC, hπ]
    have h2' : 4 * Real.pi * bigK a R C₄ C₆ ≤ 4 * Real.pi * K :=
      mul_le_mul_of_nonneg_left hK (by positivity)
    linarith [h1, h2']
  have hstar : (C₄ * (3 + (R / a) ^ 2) + C₆ * (2 + (R / a) ^ 2)
        + 12 * Real.pi * Work.UBB.lhyC) * (μ ^ 2 * a * ℓ ^ 3 * (Real.sqrt t * t ^ η₀))
      ≤ K * (4 * Real.pi * μ ^ 2 * a * ℓ ^ 3 * (Real.sqrt t * t ^ η₀)) := by
    calc (C₄ * (3 + (R / a) ^ 2) + C₆ * (2 + (R / a) ^ 2)
            + 12 * Real.pi * Work.UBB.lhyC) * (μ ^ 2 * a * ℓ ^ 3 * (Real.sqrt t * t ^ η₀))
        ≤ (4 * Real.pi * K) * (μ ^ 2 * a * ℓ ^ 3 * (Real.sqrt t * t ^ η₀)) :=
          mul_le_mul_of_nonneg_right hexpand (by positivity)
      _ = K * (4 * Real.pi * μ ^ 2 * a * ℓ ^ 3 * (Real.sqrt t * t ^ η₀)) := by ring
  have hdistrib : C₄ * (3 + (R / a) ^ 2) * (μ ^ 2 * a * ℓ ^ 3 * (Real.sqrt t * t ^ η₀))
        + C₆ * (2 + (R / a) ^ 2) * (μ ^ 2 * a * ℓ ^ 3 * (Real.sqrt t * t ^ η₀))
        + 12 * Real.pi * Work.UBB.lhyC * (μ ^ 2 * a * ℓ ^ 3 * (Real.sqrt t * t ^ η₀))
      ≤ K * (4 * Real.pi * μ ^ 2 * a * ℓ ^ 3 * (Real.sqrt t * t ^ η₀)) := by
    have he : C₄ * (3 + (R / a) ^ 2) * (μ ^ 2 * a * ℓ ^ 3 * (Real.sqrt t * t ^ η₀))
          + C₆ * (2 + (R / a) ^ 2) * (μ ^ 2 * a * ℓ ^ 3 * (Real.sqrt t * t ^ η₀))
          + 12 * Real.pi * Work.UBB.lhyC * (μ ^ 2 * a * ℓ ^ 3 * (Real.sqrt t * t ^ η₀))
        = (C₄ * (3 + (R / a) ^ 2) + C₆ * (2 + (R / a) ^ 2)
            + 12 * Real.pi * Work.UBB.lhyC) * (μ ^ 2 * a * ℓ ^ 3 * (Real.sqrt t * t ^ η₀)) := by
      ring
    rw [he]
    exact hstar
  -- ## assemble
  have hstep : errAbs a ℓ t μ R C₄ + C₆ * μ ^ 2 * a * ℓ ^ 3 * Real.sqrt t
        * (t ^ (2 / 323 : ℝ) + (R / a) ^ 2 * Real.sqrt t + t ^ (1 / 1615 : ℝ))
        + 3 * Work.UBB.lhyC * (4 * Real.pi * μ ^ 2 * a * ℓ ^ 3 * Real.sqrt t) * t ^ η₀
      ≤ K * (4 * Real.pi * μ ^ 2 * a * ℓ ^ 3 * (Real.sqrt t * t ^ η₀)) := by
    have he : 3 * Work.UBB.lhyC * (4 * Real.pi * μ ^ 2 * a * ℓ ^ 3 * Real.sqrt t) * t ^ η₀
        = 12 * Real.pi * Work.UBB.lhyC * (μ ^ 2 * a * ℓ ^ 3 * (Real.sqrt t * t ^ η₀)) := by
      ring
    linarith [herr, hc6, hdistrib, he]
  have hpow : t ^ (1 / 2 + η₀) = Real.sqrt t * t ^ η₀ := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add ht]
  -- the LHY comparison, in the shapes of the goal
  have h_i : -4 * Real.pi * μ ^ 2 * a * ℓ ^ 3
        + 4 * Real.pi * Work.UBB.lhyC * μ ^ 2 * a * ℓ ^ 3 * Real.sqrt t
        - 3 * Work.UBB.lhyC * (4 * Real.pi * μ ^ 2 * a * ℓ ^ 3 * Real.sqrt t) * t ^ η₀
      ≤ -4 * Real.pi * μ ^ 2 * a * ℓ ^ 3
        + 4 * Real.pi * Work.UBB.lhyC * ρ ^ 2 * a * ℓ ^ 3 * Real.sqrt (ρ * a ^ 3) := by
    nlinarith [hLHY]
  -- the `K t^{1/2+η₀}` term and the errors, with `errAbs` expanded
  have h_ii : C₄ * μ ^ 2 * a * ℓ ^ 3 * Real.sqrt t
          * (t ^ (9 / 646 : ℝ) + t ^ (2 / 323 : ℝ) + (R / a) ^ 2 * Real.sqrt t
            + t ^ (1 / 1615 : ℝ))
        + C₆ * μ ^ 2 * a * ℓ ^ 3 * Real.sqrt t
          * (t ^ (2 / 323 : ℝ) + (R / a) ^ 2 * Real.sqrt t + t ^ (1 / 1615 : ℝ))
        + 3 * Work.UBB.lhyC * (4 * Real.pi * μ ^ 2 * a * ℓ ^ 3 * Real.sqrt t) * t ^ η₀
      ≤ 4 * Real.pi * μ ^ 2 * a * ℓ ^ 3 * K * (Real.sqrt t * t ^ η₀) := by
    rw [errAbs] at hstep
    nlinarith [hstep]
  rw [errAbs, hpow]
  nlinarith [h_i, h_ii]

end Work.BoseFixR
