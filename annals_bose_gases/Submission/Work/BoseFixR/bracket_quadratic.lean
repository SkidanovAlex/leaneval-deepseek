import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixR.Defs
import Submission.Work.BoseFixR.FamForm.sideAt_d_powers
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixR.bracket_quadratic` — the completion-of-the-square at the core of the bracket

The §11 bracket of FS's `eq:Combined2` has the shape

`16π μ²aℓ³√(μa³)(X² + (R/a)²√(μa³) + (μa³)^{1/1615}) + 4π x² aℓ³ ≥ x|W₀|𝓜`,

with `x` the (nonnegative) deviation variable, `W₀ = Ŵ₁(0) − Ŵ₁ω(0)` the potential
constant bounded by `16πa` (`KzKernels.W1omega0_le` etc.), and `𝓜 = X^{-327/4}` the
matrix window.  It is a quadratic in `x` whose linear coefficient is beaten by the
quadratic term once the constant `A := 16π μ²aℓ³√(μa³)X²` (only the `X²` part of
the bracket — the other two summands are nonnegative) satisfies `A ≥ (16πa𝓜)²/(16πaℓ³)`.

That last inequality is a strict monomial comparison in the diluteness `t = μa³`:
with `μℓ³ = t^{-166/323}` (`Work.BoseBox.mu_ell_cube_fsParams`), `√t = t^{1/2}` and
`X² = t^{2/323}`,

`μ²ℓ⁶√t X² = (μℓ³)²√t X² = t^{-337/646}`   and   `𝓜² = t^{-327/646}`,

and `t^{-337/646} ≥ t^{-327/646}` because `0 < t ≤ 1` (the margin is `t^{-5/323}`).
All constants here are free except the exponent bookkeeping, so nothing of the
sharp LHY layer is involved.
-/

namespace Work.BoseFixR

set_option linter.unusedVariables false

open scoped Real Topology BigOperators

open _root_.BoseGases

/-- **AM–GM for the bracket.**  If `c > 0` and `w² ≤ 4cA` then `wx ≤ A + cx²` for
every `x`: multiplying `A + cx² - wx = c(x - w/(2c))² + (A - w²/(4c))` by `4c > 0`
gives `4c(A + cx²) - 4cwx = (w - 2cx)² + (4cA - w²) ≥ 0`. -/
private lemma bracketAMGM {A c w x : ℝ} (hc : 0 < c) (h : w ^ 2 ≤ 4 * c * A) :
    w * x ≤ A + c * x ^ 2 := by
  have h4 : (0 : ℝ) < 4 * c := by linarith
  have hkey : 4 * c * (w * x) ≤ 4 * c * (A + c * x ^ 2) := by
    nlinarith [sq_nonneg (w - 2 * c * x)]
  exact (mul_le_mul_iff_of_pos_left h4).mp hkey

theorem bracket_quadratic {v : EuclideanSpace ℝ (Fin 3) → ℝ} {μ R W0 bM x : ℝ}
    (hμ : 0 < μ) (hav : 0 < BoseGases.a v) (hR : 0 ≤ R) (ht1 : Work.BoseFixR.dil v μ ≤ 1)
    (hW : |W0| ≤ 16 * Real.pi * BoseGases.a v)
    (hM : bM = Work.BoseBox.fsXp (Work.BoseFixR.dil v μ) (-(327 / 4))) (hx : 0 ≤ x) :
    16 * Real.pi * (μ ^ 2 * BoseGases.a v * Work.BoseFixR.ell3 v μ * Real.sqrt (Work.BoseFixR.dil v μ)
        * (Work.BoseFixR.fsX v μ ^ 2 + (R / BoseGases.a v) ^ 2 * Real.sqrt (Work.BoseFixR.dil v μ)
            + Work.BoseFixR.errExp v μ))
      + 4 * Real.pi * x ^ 2 * BoseGases.a v * Work.BoseFixR.ell3 v μ ≥ x * |W0| * bM := by
  set a : ℝ := BoseGases.a v with ha_def
  set t : ℝ := Work.BoseFixR.dil v μ with ht_def
  set X : ℝ := Work.BoseFixR.fsX v μ with hX_def
  have ha : 0 < a := hav
  have ht0 : 0 < t := by
    rw [ht_def, Work.BoseFixR.dil]
    exact mul_pos hμ (pow_pos hav 3)
  have ht1' : t ≤ 1 := ht1
  -- FS's healing-length identity `μℓ³ = t^{-166/323}` at the box parameters.
  have hmuL : μ * ell3 v μ = t ^ (-(166 / 323 : ℝ)) := by
    rw [ht_def]
    have h := Work.BoseBox.mu_ell_cube_fsParams (μ := μ) (a := a) hμ ha
    simpa [ell3, ell, Work.BoseBox.sideAt, Work.BoseBox.paramsAt, Work.BoseFixR.dil] using h
  have hLpos : 0 < ell3 v μ := by
    have h1 : 0 < μ * ell3 v μ := by rw [hmuL]; exact Real.rpow_pos_of_pos ht0 _
    exact pos_of_mul_pos_right h1 hμ.le
  have hbMpos : 0 < bM := by rw [hM]; exact Work.BoseBox.fsXp_pos ht0
  -- the matrix window `𝓜² = t^{-327/646}`
  have hbM2 : bM ^ 2 = t ^ (-(327 / 646 : ℝ)) := by
    rw [hM, Work.BoseBox.fsXp_pow (le_of_lt ht0), Work.BoseBox.fsXp]
    congr 1
    norm_num
  -- **the key monomial comparison**: `𝓜² ≤ μ²ℓ⁶√t X²`
  have hcore : bM ^ 2 ≤ μ ^ 2 * (ell3 v μ) ^ 2 * Real.sqrt t * X ^ 2 := by
    have hmuLsq : μ ^ 2 * (ell3 v μ) ^ 2 = t ^ (-(332 / 323 : ℝ)) := by
      have h1 : (μ * ell3 v μ) ^ 2 = t ^ (-(332 / 323 : ℝ)) := by
        rw [hmuL, ← Real.rpow_natCast (t ^ (-(166 / 323 : ℝ))) 2,
          ← Real.rpow_mul (le_of_lt ht0)]
        congr 1
        norm_num
      rw [← h1]; ring
    have hXeq : X = Work.BoseBox.fsXp t 1 := by rw [hX_def, Work.BoseFixR.fsX, ht_def]
    have hXsq : X ^ 2 = t ^ (2 / 323 : ℝ) := by
      rw [hXeq, Work.BoseBox.fsXp_pow (le_of_lt ht0), Work.BoseBox.fsXp]
      congr 1
      norm_num
    have hLHS : μ ^ 2 * (ell3 v μ) ^ 2 * Real.sqrt t * X ^ 2 = t ^ (-(337 / 646 : ℝ)) := by
      rw [hmuLsq, Real.sqrt_eq_rpow t, hXsq]
      rw [← Real.rpow_add ht0, ← Real.rpow_add ht0]
      congr 1
      norm_num
    rw [hbM2, hLHS]
    exact Real.rpow_le_rpow_of_exponent_ge ht0 ht1' (by norm_num)
  -- the bracket dominates its `X²` part (the other two summands are nonnegative)
  have hbr : X ^ 2 ≤ X ^ 2 + (R / a) ^ 2 * Real.sqrt t + errExp v μ := by
    have h1 : 0 ≤ (R / a) ^ 2 * Real.sqrt t := mul_nonneg (sq_nonneg _) (Real.sqrt_nonneg t)
    have h2 : 0 ≤ errExp v μ := by
      rw [errExp, ← ht_def]
      exact Real.rpow_nonneg (le_of_lt ht0) _
    linarith
  have hfac : 0 ≤ μ ^ 2 * a * ell3 v μ * Real.sqrt t :=
    mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg μ) ha.le) hLpos.le) (Real.sqrt_nonneg t)
  have hA0 : 16 * Real.pi * (μ ^ 2 * a * ell3 v μ * Real.sqrt t * X ^ 2)
      ≤ 16 * Real.pi * (μ ^ 2 * a * ell3 v μ * Real.sqrt t
          * (X ^ 2 + (R / a) ^ 2 * Real.sqrt t + errExp v μ)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hbr hfac) (by positivity)
  -- the quadratic-form input `(16πa𝓜)² ≤ 4·(4πaℓ³)·A`
  have hkey : (16 * Real.pi * a * bM) ^ 2
      ≤ 4 * (4 * Real.pi * a * ell3 v μ)
          * (16 * Real.pi * (μ ^ 2 * a * ell3 v μ * Real.sqrt t * X ^ 2)) := by
    have h1 : (16 * Real.pi * a * bM) ^ 2 = 256 * Real.pi ^ 2 * a ^ 2 * bM ^ 2 := by ring
    have h2 : 4 * (4 * Real.pi * a * ell3 v μ)
          * (16 * Real.pi * (μ ^ 2 * a * ell3 v μ * Real.sqrt t * X ^ 2))
        = 256 * Real.pi ^ 2 * a ^ 2 * (μ ^ 2 * (ell3 v μ) ^ 2 * Real.sqrt t * X ^ 2) := by ring
    rw [h1, h2]
    exact mul_le_mul_of_nonneg_left hcore (by positivity)
  -- the linear term `x|W₀|𝓜` is at most `x·16πa𝓜`
  have hw : x * |W0| * bM ≤ (16 * Real.pi * a * bM) * x := by
    have h1 : |W0| * bM ≤ 16 * Real.pi * a * bM :=
      mul_le_mul_of_nonneg_right hW hbMpos.le
    have h2 : x * (|W0| * bM) ≤ x * (16 * Real.pi * a * bM) :=
      mul_le_mul_of_nonneg_left h1 hx
    calc x * |W0| * bM = x * (|W0| * bM) := by ring
      _ ≤ x * (16 * Real.pi * a * bM) := h2
      _ = (16 * Real.pi * a * bM) * x := by ring
  have hmain : (16 * Real.pi * a * bM) * x
      ≤ 16 * Real.pi * (μ ^ 2 * a * ell3 v μ * Real.sqrt t
            * (X ^ 2 + (R / a) ^ 2 * Real.sqrt t + errExp v μ))
        + 4 * Real.pi * x ^ 2 * a * ell3 v μ := by
    have hc : 0 < 4 * Real.pi * a * ell3 v μ := by positivity
    have hstep := bracketAMGM (A := 16 * Real.pi * (μ ^ 2 * a * ell3 v μ * Real.sqrt t * X ^ 2))
      (c := 4 * Real.pi * a * ell3 v μ) (w := 16 * Real.pi * a * bM) (x := x) hc hkey
    have hceq : (4 * Real.pi * a * ell3 v μ) * x ^ 2 = 4 * Real.pi * x ^ 2 * a * ell3 v μ := by ring
    linarith [hstep, hA0, hceq]
  linarith [hw, hmain]

end Work.BoseFixR
