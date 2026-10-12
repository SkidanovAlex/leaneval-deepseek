import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseBogFS.ZpError
import Submission.Work.BoseBogFS.lhyEps_explicit
import Submission.Work.BoseBogFS.rpow_mul_log_inv_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseBogFS.lhyEps_le_errSlot` — FS's `lhyEps` inside the §11 bracket

The `hEzero` slot of `Work.BoseBogFS.bogOpBoundFS_of_fsData` compares the zero-point
error, whose scalar part is `zpScalar = (1/2)(2π)⁻³(latticeMeshErr + zpRiemErr)
+ (1/2)10¹⁰·lhyEps`, against the §11 bracket `errBracket = μ²aℓ³√(dil)·errSlot`.  The
only term of `lhyEps` that is not visibly a power of the diluteness with a *small*
exponent is the Lebesgue error `(μa)^{1/4}√R`; this module proves that the whole of
FS's `eq:LebesgueError-Total` error `ε(μ,ρ_z)` is absorbed by the bracket

  `errSlot v R μ = X² + (R/a)²√(μa³) + (μa³)^{1/1615}`,  `X = (μa³)^{1/323}`,

at the free constant `10⁸(1+cc)`, under the two structural hypotheses `μa³ ≤ 1` and
`R ≤ cc·a`.

The mechanism is the power gap of FS `eq:Xchoice`: at `t := μa³ = X^{323}` the four
summands of `ε` and their coefficients are (via `lhyEps_explicit`)

  `(μa)^{1/4}√R`, `t^{23/1292}`, `t^{1/646}(1 + (162/323)log(1/t))`,
  `t^{1/1292}(1 + (156/323)log(1/t))`,

the exponents `23/1292, 1/646, 1/1292` all being strictly larger than `1/1615`, so the
first two are dominated by `t^{1/1615}` and the last two by `t^{1/1615}` *up to one
logarithm*, which the positive gap in the exponent converts into a constant
(`Work.BoseBogFS.rpow_mul_log_inv_le`) — this is the same `log vs power` slack that
underlies the a-priori bounds.  Everything is then a multiple of `t^{1/1615}` and the
constants are free.
-/

noncomputable section

open scoped Real Topology BigOperators

open MeasureTheory Filter Metric

open _root_.BoseGases

namespace Work.BoseBogFS

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

/-- **The `(μa)^{1/4}√R` summand of `lhyEps`.**  With `R ≤ cc·a` and `μa³ ≤ 1`:

  `(μa)^{1/4}√R ≤ √cc·(μa)^{1/4}a^{1/2} = √cc·(μa³)^{1/4} ≤ (1+cc)(μa³)^{1/1615}`.

The middle identity `(μa)^{1/4}a^{1/2} = (μa³)^{1/4}` is the one place where the
positive fourth root matters; `√cc ≤ 1 + cc` and `(μa³)^{1/4} ≤ (μa³)^{1/1615}` are the
two monotonicities the free constant pays for. -/
lemma term_first_le {μ a R cc : ℝ} (hμ : 0 < μ) (ha : 0 < a) (hcc : 0 ≤ cc)
    (hR : R ≤ cc * a) (hm : μ * a ^ 3 ≤ 1) :
    (μ * a) ^ (1/4 : ℝ) * Real.sqrt R ≤ (1 + cc) * (μ * a ^ 3) ^ (1/1615 : ℝ) := by
  have hsq : Real.sqrt R ≤ Real.sqrt (cc * a) := Real.sqrt_le_sqrt hR
  have hsqrt : Real.sqrt (cc * a) = Real.sqrt cc * Real.sqrt a := Real.sqrt_mul hcc a
  have hm0 : 0 < μ * a ^ 3 := mul_pos hμ (pow_pos ha 3)
  have hcore : (μ * a) ^ (1/4 : ℝ) * Real.sqrt a = (μ * a ^ 3) ^ (1/4 : ℝ) := by
    have h1 : (μ * a) ^ (1/4 : ℝ) * Real.sqrt a
        = μ ^ (1/4 : ℝ) * (a ^ (1/4 : ℝ) * a ^ (1/2 : ℝ)) := by
      rw [Real.sqrt_eq_rpow, Real.mul_rpow hμ.le ha.le, mul_assoc]
    rw [h1, ← Real.rpow_add ha (1/4) (1/2),
      Real.mul_rpow hμ.le (pow_nonneg ha.le 3), ← Real.rpow_natCast a 3,
      ← Real.rpow_mul ha.le]
    norm_num
  have hstep1 : (μ * a) ^ (1/4 : ℝ) * Real.sqrt R
      ≤ Real.sqrt cc * ((μ * a) ^ (1/4 : ℝ) * Real.sqrt a) := by
    calc (μ * a) ^ (1/4 : ℝ) * Real.sqrt R
        ≤ (μ * a) ^ (1/4 : ℝ) * Real.sqrt (cc * a) :=
          mul_le_mul_of_nonneg_left hsq (Real.rpow_nonneg (mul_nonneg hμ.le ha.le) _)
      _ = (μ * a) ^ (1/4 : ℝ) * (Real.sqrt cc * Real.sqrt a) := by rw [hsqrt]
      _ = Real.sqrt cc * ((μ * a) ^ (1/4 : ℝ) * Real.sqrt a) := by ring
  rw [hcore] at hstep1
  have hccle : Real.sqrt cc ≤ 1 + cc := by
    nlinarith [Real.sq_sqrt hcc, Real.sqrt_nonneg cc]
  have hpow : (μ * a ^ 3) ^ (1/4 : ℝ) ≤ (μ * a ^ 3) ^ (1/1615 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_ge hm0 hm (by norm_num)
  calc (μ * a) ^ (1/4 : ℝ) * Real.sqrt R
      ≤ Real.sqrt cc * (μ * a ^ 3) ^ (1/4 : ℝ) := hstep1
    _ ≤ (1 + cc) * (μ * a ^ 3) ^ (1/1615 : ℝ) :=
        mul_le_mul hccle hpow (Real.rpow_nonneg hm0.le _) (by linarith)

/-- **The `(1 + c·log)` form of the log bound.**  For `0 < t ≤ 1`, `q < p` and `c ≥ 0`:

  `t^p(1 + c·log(1/t)) ≤ (1 + c·2/(p-q))·t^q`.

This is the shape in which the last two summands of `lhyEps_explicit` appear.  It is
`t^p ≤ t^q` for the `1`, and `Work.BoseBogFS.rpow_mul_log_inv_le` for the logarithm,
with the whole constant `2/(p-q)` paid on the (free) error side. -/
lemma rpow_mul_one_add_log_inv_le {t p q c : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1)
    (h : q < p) (hc : 0 ≤ c) :
    t ^ p * (1 + c * Real.log (1 / t)) ≤ (1 + c * (2 / (p - q))) * t ^ q := by
  have hpq : q ≤ p := le_of_lt h
  have hp_le : t ^ p ≤ t ^ q := Real.rpow_le_rpow_of_exponent_ge ht0 ht1 hpq
  have hlog := rpow_mul_log_inv_le (t := t) (p := p) (q := q) ht0 ht1 h
  have step1 : t ^ p * (1 + c * Real.log (1 / t))
      = t ^ p + c * (t ^ p * Real.log (1 / t)) := by ring
  have step2 : (1 + c * (2 / (p - q))) * t ^ q = t ^ q + c * ((2 / (p - q)) * t ^ q) := by
    ring
  rw [step1, step2]
  nlinarith [hp_le, mul_le_mul_of_nonneg_left hlog hc]

/-- **The `hEzero` slot, scalar form.**  FS's Lebesgue error `ε(μ,ρ_z)`
(`eq:LebesgueError-Total`, `Work.BoseB6.lhyEps`) at the box parameters
`paramsAt μ (a v)` is bounded by the second factor of the §11 bracket, at the free
constant `10⁸(1+cc)`, under `μa³ ≤ 1` (FS's diluteness) and `R ≤ cc·a`.

The four summands are bounded by `(1+cc)·t^{1/1615}`, `t^{1/1615}`, `1081·t^{1/1615}` and
`6241·t^{1/1615}` with `t = μa³`; the total `7324 + cc ≤ 7324(1+cc)` is well inside the
free `10⁸`. -/
theorem lhyEps_le_errSlot (v : EuclideanSpace ℝ (Fin 3) → ℝ) (R μ : ℝ)
    (hav : 0 < _root_.BoseGases.a v) (hμ : 0 < μ)
    (hdil : Work.BoseFixR.dil v μ ≤ 1) {cc : ℝ} (hcc : 0 ≤ cc)
    (hR : R ≤ cc * _root_.BoseGases.a v) :
    Work.BoseB6.lhyEps (_root_.BoseGases.a v) R
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).Kl
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ
      ≤ (10 ^ 8 * (1 + cc)) * Work.BoseBogFS.errSlot v R μ := by
  have ht0 : 0 < Work.BoseFixR.dil v μ := by
    rw [Work.BoseFixR.dil]; exact mul_pos hμ (pow_pos hav 3)
  have ht1 : Work.BoseFixR.dil v μ ≤ 1 := hdil
  have h1cc : 0 ≤ 1 + cc := by linarith
  -- the dominant power of the bracket's third slot
  obtain ⟨X, hX⟩ : ∃ X : ℝ, X = (Work.BoseFixR.dil v μ) ^ ((1:ℝ)/1615) := ⟨_, rfl⟩
  have hX0 : 0 ≤ X := by rw [hX]; exact Real.rpow_nonneg ht0.le _
  have herr : X ≤ Work.BoseBogFS.errSlot v R μ := by
    rw [hX, Work.BoseBogFS.errSlot, Work.BoseFixR.errExp_eq]
    have h1 : 0 ≤ Work.BoseFixR.fsX v μ ^ 2 := sq_nonneg _
    have h2 : 0 ≤ (R / _root_.BoseGases.a v) ^ 2 * Real.sqrt (Work.BoseFixR.dil v μ) :=
      mul_nonneg (sq_nonneg _) (Real.sqrt_nonneg _)
    linarith
  rw [lhyEps_explicit v R μ hμ hav]
  -- the four summands
  have hT1 : (μ * _root_.BoseGases.a v) ^ ((1:ℝ)/4) * Real.sqrt R ≤ (1 + cc) * X := by
    rw [hX]; exact term_first_le hμ hav hcc hR hdil
  have hT2 : (Work.BoseFixR.dil v μ) ^ ((23:ℝ)/1292) ≤ X := by
    rw [hX]
    exact Real.rpow_le_rpow_of_exponent_ge ht0 ht1 (by norm_num)
  have hT3 : (Work.BoseFixR.dil v μ) ^ ((1:ℝ)/646)
      * (1 + ((162:ℝ)/323) * Real.log (1 / Work.BoseFixR.dil v μ)) ≤ 1081 * X := by
    rw [hX]
    refine le_trans (rpow_mul_one_add_log_inv_le (t := Work.BoseFixR.dil v μ)
      (p := (1:ℝ)/646) (q := (1:ℝ)/1615) (c := (162:ℝ)/323) ht0 ht1
      (by norm_num) (by norm_num)) ?_
    exact mul_le_mul_of_nonneg_right (by norm_num) (Real.rpow_nonneg ht0.le _)
  have hT4 : (Work.BoseFixR.dil v μ) ^ ((1:ℝ)/1292)
      * (1 + ((156:ℝ)/323) * Real.log (1 / Work.BoseFixR.dil v μ)) ≤ 6241 * X := by
    rw [hX]
    refine le_trans (rpow_mul_one_add_log_inv_le (t := Work.BoseFixR.dil v μ)
      (p := (1:ℝ)/1292) (q := (1:ℝ)/1615) (c := (156:ℝ)/323) ht0 ht1
      (by norm_num) (by norm_num)) ?_
    exact mul_le_mul_of_nonneg_right (by norm_num) (Real.rpow_nonneg ht0.le _)
  -- sum the four
  have hsum : (μ * _root_.BoseGases.a v) ^ ((1:ℝ)/4) * Real.sqrt R
      + (Work.BoseFixR.dil v μ) ^ ((23:ℝ)/1292)
      + (Work.BoseFixR.dil v μ) ^ ((1:ℝ)/646)
          * (1 + ((162:ℝ)/323) * Real.log (1 / Work.BoseFixR.dil v μ))
      + (Work.BoseFixR.dil v μ) ^ ((1:ℝ)/1292)
          * (1 + ((156:ℝ)/323) * Real.log (1 / Work.BoseFixR.dil v μ))
      ≤ 7324 * (1 + cc) * X := by
    refine le_trans (add_le_add (add_le_add (add_le_add hT1 hT2) hT3) hT4) ?_
    have hA : ((1 + cc) * X + X) + 1081 * X + 6241 * X = (7324 + cc) * X := by ring
    rw [hA]
    have : (7324 + cc : ℝ) ≤ 7324 * (1 + cc) := by nlinarith [hcc]
    exact mul_le_mul_of_nonneg_right this hX0
  calc (μ * _root_.BoseGases.a v) ^ ((1:ℝ)/4) * Real.sqrt R
      + (Work.BoseFixR.dil v μ) ^ ((23:ℝ)/1292)
      + (Work.BoseFixR.dil v μ) ^ ((1:ℝ)/646)
          * (1 + ((162:ℝ)/323) * Real.log (1 / Work.BoseFixR.dil v μ))
      + (Work.BoseFixR.dil v μ) ^ ((1:ℝ)/1292)
          * (1 + ((156:ℝ)/323) * Real.log (1 / Work.BoseFixR.dil v μ))
      ≤ 7324 * (1 + cc) * X := hsum
    _ ≤ 7324 * (1 + cc) * Work.BoseBogFS.errSlot v R μ :=
        mul_le_mul_of_nonneg_left herr (mul_nonneg (by norm_num) h1cc)
    _ ≤ 10 ^ 8 * (1 + cc) * Work.BoseBogFS.errSlot v R μ :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (by norm_num : (7324:ℝ) ≤ 10^8) h1cc)
          (le_trans hX0 herr)

end Work.BoseBogFS
