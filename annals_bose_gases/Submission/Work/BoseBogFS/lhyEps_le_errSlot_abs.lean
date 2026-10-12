import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseBogFS.lhyEps_le_errSlot
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBogFS

noncomputable section

open scoped Real Topology BigOperators

open MeasureTheory Filter Metric

open _root_.BoseGases Submission.BoseGases Work.UBB Work.BoseBox Work.BoseBoxFix Work.BoseFixR

set_option autoImplicit false
set_option linter.unusedVariables false

/-!
# `Work.BoseBogFS.lhyEps_le_errSlot_abs` — `lhyEps` inside the §11 bracket, *unrestricted* `R`

The sibling `Work.BoseBogFS.lhyEps_le_errSlot` bounds FS's Lebesgue error `ε(μ,R)` by the
bracket's second slot

  `errSlot v R μ = X² + (R/a)² √(μa³) + (μa³)^{1/1615}`

but only under the *geometric* restriction `R ≤ cc·a` (the short-range regime `R ≲ a`).  Here the
restriction is removed: only `0 < R`, `0 < a v`, `0 < μ` and the diluteness `μ (a v)³ ≤ 1` are
assumed.

The mechanism is the same power gap as in the sibling for the three summands that carry the
parameters (`t^{23/1292}`, `t^{1/646}(1 + c log)`, `t^{1/1292}(1 + c log)`, all `≤ C·t^{1/1615}` up
to one logarithm, `t = μa³`), *plus* a genuinely new ingredient for the Lebesgue summand
`(μa)^{1/4}√R`: with `t = μa³` and `s = R/a > 0` that summand is

  `(μa)^{1/4}√R = t^{1/4} √s = (s²√t)^{1/4} · (t^{1/6})^{3/4}`,

so the weighted AM–GM inequality with weights `(1/4, 3/4)` gives

  `(μa)^{1/4}√R ≤ (1/4)·(R/a)²√(μa³) + (3/4)·(μa³)^{1/6} ≤ (1/4)(R/a)²√(μa³) + (3/4)·X²`,

the last step because `1/6 > 2/323` and `t ≤ 1`.  Both right-hand terms are summands of
`errSlot`, so no restriction on `R` is needed: the quadratic slot pays for `R ≫ a` and the
`X²`-slot (i.e. `t^{2/323}`) pays for `R ≲ a`.  The two regimes meet exactly at
`s²√t ~ t^{1/6}`, i.e. `R/a ~ t^{-1/6}`, and `t^{1/6} ≤ t^{2/323}` for `t ≤ 1` is the (very
comfortable) power gap that makes the *small*-`R` side work.
-/

/-- **The Lebesgue summand `(μa)^{1/4}√R` of `lhyEps`, with no restriction on `R`.**

With `t := μa³ ∈ (0,1]` and `s := R/a > 0` the summand is `t^{1/4}√s = (s²√t)^{1/4}(t^{1/6})^{3/4}`,
so weighted AM–GM gives `t^{1/4}√s ≤ (1/4)s²√t + (3/4)t^{1/6} ≤ (1/4)s²√t + (3/4)t^{2/323}`. -/
lemma term1_le {A R μ : ℝ} (hA : 0 < A) (hR : 0 < R) (hμ : 0 < μ)
    (hm : μ * A ^ 3 ≤ 1) :
    (μ * A) ^ (1 / 4 : ℝ) * Real.sqrt R
      ≤ (1 / 4) * ((R / A) ^ 2 * Real.sqrt (μ * A ^ 3))
        + (3 / 4) * (μ * A ^ 3) ^ (2 / 323 : ℝ) := by
  have hT0 : 0 < μ * A ^ 3 := by positivity
  -- `√R = √A·√(R/A)`
  have hsplit : Real.sqrt R = Real.sqrt A * Real.sqrt (R / A) := by
    rw [← Real.sqrt_mul hA.le]
    congr 1
    field_simp
  -- `(μA)^{1/4}√A = (μA³)^{1/4}`
  have hq : (μ * A) ^ (1 / 4 : ℝ) * Real.sqrt A = (μ * A ^ 3) ^ (1 / 4 : ℝ) := by
    have hμ1 : (μ * A) ^ (1 / 4 : ℝ) = μ ^ (1 / 4 : ℝ) * A ^ (1 / 4 : ℝ) :=
      Real.mul_rpow hμ.le hA.le
    have hμ2 : (μ * A ^ 3) ^ (1 / 4 : ℝ) = μ ^ (1 / 4 : ℝ) * (A ^ 3) ^ (1 / 4 : ℝ) :=
      Real.mul_rpow hμ.le (by positivity)
    rw [hμ1, hμ2, Real.sqrt_eq_rpow, mul_assoc, ← Real.rpow_add hA (1 / 4) (1 / 2),
      ← Real.rpow_natCast A 3, ← Real.rpow_mul hA.le]
    norm_num
  -- the substitution `t^{1/4}√s = (s²√t)^{1/4}t^{1/8}`
  have he : (μ * A ^ 3) ^ (1 / 4 : ℝ) * Real.sqrt (R / A)
      = ((R / A) ^ 2 * Real.sqrt (μ * A ^ 3)) ^ (1 / 4 : ℝ) * (μ * A ^ 3) ^ (1 / 8 : ℝ) := by
    have hs : 0 ≤ R / A := by positivity
    rw [Real.sqrt_eq_rpow (R / A), Real.sqrt_eq_rpow (μ * A ^ 3),
      Real.mul_rpow (by positivity : (0 : ℝ) ≤ (R / A) ^ 2)
        (Real.rpow_nonneg hT0.le _),
      ← Real.rpow_natCast (R / A) 2, ← Real.rpow_mul hs, ← Real.rpow_mul hT0.le]
    norm_num
    rw [mul_assoc, ← Real.rpow_add hT0 (1 / 8) (1 / 8)]
    norm_num
    ring
  -- weighted AM–GM with weights `(1/4, 3/4)`
  have hamgm : ((R / A) ^ 2 * Real.sqrt (μ * A ^ 3)) ^ (1 / 4 : ℝ)
        * (μ * A ^ 3) ^ (1 / 8 : ℝ)
      ≤ (1 / 4) * ((R / A) ^ 2 * Real.sqrt (μ * A ^ 3))
        + (3 / 4) * (μ * A ^ 3) ^ (1 / 6 : ℝ) := by
    have hS : 0 ≤ (R / A) ^ 2 * Real.sqrt (μ * A ^ 3) := by positivity
    have h : (μ * A ^ 3) ^ (1 / 8 : ℝ) = ((μ * A ^ 3) ^ (1 / 6 : ℝ)) ^ (3 / 4 : ℝ) := by
      rw [← Real.rpow_mul hT0.le]
      congr 1
      norm_num
    rw [h]
    have hg := Real.geom_mean_le_arith_mean2_weighted (w₁ := (1 / 4 : ℝ)) (w₂ := (3 / 4 : ℝ))
      (p₁ := (R / A) ^ 2 * Real.sqrt (μ * A ^ 3)) (p₂ := (μ * A ^ 3) ^ (1 / 6 : ℝ))
      (by norm_num) (by norm_num) hS (Real.rpow_nonneg hT0.le _) (by norm_num)
    linarith
  have hmono : (μ * A ^ 3) ^ (1 / 6 : ℝ) ≤ (μ * A ^ 3) ^ (2 / 323 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_ge hT0 hm (by norm_num)
  calc (μ * A) ^ (1 / 4 : ℝ) * Real.sqrt R
      = (μ * A ^ 3) ^ (1 / 4 : ℝ) * Real.sqrt (R / A) := by
        rw [hsplit, ← mul_assoc, hq]
    _ = ((R / A) ^ 2 * Real.sqrt (μ * A ^ 3)) ^ (1 / 4 : ℝ)
          * (μ * A ^ 3) ^ (1 / 8 : ℝ) := he
    _ ≤ (1 / 4) * ((R / A) ^ 2 * Real.sqrt (μ * A ^ 3))
          + (3 / 4) * (μ * A ^ 3) ^ (1 / 6 : ℝ) := hamgm
    _ ≤ (1 / 4) * ((R / A) ^ 2 * Real.sqrt (μ * A ^ 3))
          + (3 / 4) * (μ * A ^ 3) ^ (2 / 323 : ℝ) := by linarith

/-- **`lhyEps` is inside the §11 bracket slot with no geometric restriction on `R`.**

`Work.BoseBogFS.lhyEps_le_errSlot` gives `lhyEps ≤ 10⁸(1+cc)·errSlot` for `R ≤ cc·a`; here the
`R ≤ cc·a` hypothesis is dropped (the constant `10⁴` above is enough because the only summand that
needed it is the first one, and `term1_le` pays it by the bracket's own two slots). -/
theorem lhyEps_le_errSlot_abs :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R μ : ℝ},
      0 < R → 0 < _root_.BoseGases.a v → 0 < μ → μ * (_root_.BoseGases.a v) ^ 3 ≤ 1 →
      Work.BoseB6.lhyEps (_root_.BoseGases.a v) R
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).Kl
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ
        ≤ C * Work.BoseBogFS.errSlot v R μ := by
  refine ⟨10 ^ 4, by norm_num, ?_⟩
  intro v R μ hR hav hμ hm
  have hT0 : 0 < Work.BoseFixR.dil v μ := by
    rw [Work.BoseFixR.dil]; positivity
  have hT1 : Work.BoseFixR.dil v μ ≤ 1 := by
    rw [Work.BoseFixR.dil]; exact hm
  -- nonnegativity of the slot
  have herr0 : 0 ≤ Work.BoseBogFS.errSlot v R μ := by
    rw [Work.BoseBogFS.errSlot, Work.BoseFixR.errExp_eq]
    have h1 : (0 : ℝ) ≤ Work.BoseFixR.fsX v μ ^ 2 := sq_nonneg _
    have h2 : (0 : ℝ) ≤ (R / _root_.BoseGases.a v) ^ 2
        * Real.sqrt (Work.BoseFixR.dil v μ) := by positivity
    have h3 : (0 : ℝ) ≤ (Work.BoseFixR.dil v μ) ^ (1 / 1615 : ℝ) :=
      Real.rpow_nonneg hT0.le _
    linarith
  -- the Lebesgue summand
  have hterm1 : (μ * _root_.BoseGases.a v) ^ (1 / 4 : ℝ) * Real.sqrt R
      ≤ Work.BoseBogFS.errSlot v R μ := by
    refine le_trans (term1_le hav hR hμ hm) ?_
    rw [Work.BoseBogFS.errSlot, Work.BoseFixR.fsX_sq v hμ hav, Work.BoseFixR.errExp_eq,
      Work.BoseFixR.dil]
    have h2 : (0 : ℝ) ≤ (R / _root_.BoseGases.a v) ^ 2 * Real.sqrt (μ * _root_.BoseGases.a v ^ 3)
        := by positivity
    have h3 : (0 : ℝ) ≤ (μ * _root_.BoseGases.a v ^ 3) ^ (1 / 1615 : ℝ) :=
      Real.rpow_nonneg (by positivity) _
    have h4 : (0 : ℝ) ≤ (μ * _root_.BoseGases.a v ^ 3) ^ (2 / 323 : ℝ) :=
      Real.rpow_nonneg (by positivity) _
    linarith
  -- the `ε_T` summand
  have hterm2 : (Work.BoseFixR.dil v μ) ^ ((23 : ℝ) / 1292) ≤ Work.BoseBogFS.errSlot v R μ := by
    rw [Work.BoseBogFS.errSlot, Work.BoseFixR.fsX_sq v hμ hav, Work.BoseFixR.errExp_eq]
    have h2 : (0 : ℝ) ≤ (R / _root_.BoseGases.a v) ^ 2
        * Real.sqrt (Work.BoseFixR.dil v μ) := by positivity
    have h3 : (0 : ℝ) ≤ (Work.BoseFixR.dil v μ) ^ (1 / 1615 : ℝ) :=
      Real.rpow_nonneg hT0.le _
    have hkey : (Work.BoseFixR.dil v μ) ^ ((23 : ℝ) / 1292)
        ≤ (Work.BoseFixR.dil v μ) ^ (2 / 323 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_ge hT0 hT1 (by norm_num)
    linarith
  -- the `(K_ℓ s)⁻¹(1+log)` summand
  have hterm3 : (Work.BoseFixR.dil v μ) ^ ((1 : ℝ) / 646)
        * (1 + ((162 : ℝ) / 323) * Real.log (1 / Work.BoseFixR.dil v μ))
      ≤ 1081 * Work.BoseBogFS.errSlot v R μ := by
    have hb : (Work.BoseFixR.dil v μ) ^ ((1 : ℝ) / 646)
          * (1 + ((162 : ℝ) / 323) * Real.log (1 / Work.BoseFixR.dil v μ))
        ≤ 1081 * Work.BoseFixR.errExp v μ := by
      rw [Work.BoseFixR.errExp_eq]
      refine le_trans (rpow_mul_one_add_log_inv_le (t := Work.BoseFixR.dil v μ)
        (p := (1 : ℝ) / 646) (q := (1 : ℝ) / 1615) (c := (162 : ℝ) / 323)
        hT0 hT1 (by norm_num) (by norm_num)) ?_
      exact mul_le_mul_of_nonneg_right (by norm_num) (Real.rpow_nonneg hT0.le _)
    refine le_trans hb ?_
    rw [Work.BoseBogFS.errSlot, Work.BoseFixR.errExp_eq]
    have h1 : (0 : ℝ) ≤ Work.BoseFixR.fsX v μ ^ 2 := sq_nonneg _
    have h2 : (0 : ℝ) ≤ (R / _root_.BoseGases.a v) ^ 2
        * Real.sqrt (Work.BoseFixR.dil v μ) := by positivity
    nlinarith [h1, h2]
  -- the `ε_T(K_ℓ d s)⁻¹(1+log)` summand
  have hterm4 : (Work.BoseFixR.dil v μ) ^ ((1 : ℝ) / 1292)
        * (1 + ((156 : ℝ) / 323) * Real.log (1 / Work.BoseFixR.dil v μ))
      ≤ 6241 * Work.BoseBogFS.errSlot v R μ := by
    have hb : (Work.BoseFixR.dil v μ) ^ ((1 : ℝ) / 1292)
          * (1 + ((156 : ℝ) / 323) * Real.log (1 / Work.BoseFixR.dil v μ))
        ≤ 6241 * Work.BoseFixR.errExp v μ := by
      rw [Work.BoseFixR.errExp_eq]
      refine le_trans (rpow_mul_one_add_log_inv_le (t := Work.BoseFixR.dil v μ)
        (p := (1 : ℝ) / 1292) (q := (1 : ℝ) / 1615) (c := (156 : ℝ) / 323)
        hT0 hT1 (by norm_num) (by norm_num)) ?_
      exact mul_le_mul_of_nonneg_right (by norm_num) (Real.rpow_nonneg hT0.le _)
    refine le_trans hb ?_
    rw [Work.BoseBogFS.errSlot, Work.BoseFixR.errExp_eq]
    have h1 : (0 : ℝ) ≤ Work.BoseFixR.fsX v μ ^ 2 := sq_nonneg _
    have h2 : (0 : ℝ) ≤ (R / _root_.BoseGases.a v) ^ 2
        * Real.sqrt (Work.BoseFixR.dil v μ) := by positivity
    nlinarith [h1, h2]
  rw [lhyEps_explicit v R μ hμ hav]
  nlinarith [hterm1, hterm2, hterm3, hterm4, herr0]

end

end Work.BoseBogFS
