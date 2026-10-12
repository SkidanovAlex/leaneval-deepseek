import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBogFS.CleanFunAux
import Submission.Work.BoseBogFS.CleanRiem
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBogFS.CellExcessAux` — the elementary cell-excess layer of the clean Riemann row

This module collects the *elementary* (no analysis) layer needed to prove
`Work.BoseBogFS.cleanFun_tsum_le_integral`:

* the exact algebraic decomposition of the clean summand,
  `cleanFun k = (τ+c) − √(τ(τ+2c)) − c²/(2‖k‖²)`, which separates the singular piece
  `c²/(2‖k‖²)` and exposes the *only* non-smooth ingredient `H := √(τ(τ+2c))`;
* the per-cell excess tools: `f (lpt) − ⨍_{cell} f` is dominated by any uniform bound for the
  pointwise excess `f (lpt) − f x` on the cell (`cell_excess_le_of_pointwise`), the trivial
  `abs` version, additivity of the excess, and the ball form of the hypothesis;
* the `√`-Hölder inequality `|√(ab) − √(a'b')| ≤ √(a|b−b'|) + √(b'|a−a'|)` which is what makes
  the square-root cusp of `H` summable.

Everything here is `sorry`-free and independent of the analytic inputs.
-/

noncomputable section

open scoped Real Topology BigOperators

open MeasureTheory

namespace Work.BoseBogFS

open _root_.BoseGases Submission.BoseGases Work.UBB Work.BoseBox Work.BoseBoxFix Work.BoseFixR

set_option autoImplicit false
set_option linter.unusedVariables false

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## 1. The exact decomposition of the clean summand -/

/-- `𝒵(t+c, c) = t + c − √(t(t+2c))`: the square root is that of the *honest* discriminant
`(t+c)² − c² = t² + 2tc = t(t+2c)`. -/
theorem bogZeroPoint_add_eq (t c : ℝ) :
    Work.BoseB6.bogZeroPoint (t + c) c = t + c - Real.sqrt (t * (t + 2 * c)) := by
  rw [Work.BoseB6.bogZeroPoint]
  congr 1
  ring_nf

/-- **The clean summand split into its three elementary pieces:**
`cleanFun = A − H − G` with `A = τ + c`, `H = √(τ(τ+2c))` and `G = c²/(2‖k‖²)`. -/
theorem cleanFun_eq_decomp (v : E3 → ℝ) (h : ScatSol v) (ρ μ : ℝ) (k : E3) :
    cleanFun v h ρ μ k = (tauAt v μ k + cAt v h ρ μ k)
      - Real.sqrt (tauAt v μ k * (tauAt v μ k + 2 * cAt v h ρ μ k))
      - (cAt v h ρ μ k) ^ 2 / (2 * ‖k‖ ^ 2) := by
  rw [cleanFun, bogZeroPoint_add_eq]

/-! ## 2. Per-cell excess tools -/

/-- **The per-cell excess is dominated by a uniform pointwise excess bound.**  If every
`x` of the cell satisfies `f (lpt) − f x ≤ B` then the excess of the cell centre over the cell
average is at most `B`. -/
theorem cell_excess_le_of_pointwise {m : ℝ} (hm : 0 < m) (n : Fin 3 → ℤ) {f : E3 → ℝ} {B : ℝ}
    (hf : IntegrableOn f (cell m n))
    (hpt : ∀ x ∈ cell m n, f (lpt m n) - f x ≤ B) :
    f (lpt m n) - (m ^ 3)⁻¹ * (∫ x in cell m n, f x) ≤ B := by
  have hm3 : 0 < m ^ 3 := by positivity
  have hcell : volume (cell m n) ≠ ⊤ := by
    rw [volume_cell hm n]
    exact ENNReal.ofReal_ne_top
  have hfi : IntegrableOn (fun _ : E3 => f (lpt m n)) (cell m n) volume :=
    MeasureTheory.integrableOn_const hcell (by exact enorm_ne_top)
  have hBi : IntegrableOn (fun _ : E3 => B) (cell m n) volume :=
    MeasureTheory.integrableOn_const hcell (by exact enorm_ne_top)
  have hmono : ∫ x in cell m n, (f (lpt m n) - f x) ≤ ∫ x in cell m n, (fun _ : E3 => B) x := by
    refine MeasureTheory.integral_mono_ae (hfi.sub hf) hBi ?_
    filter_upwards [MeasureTheory.self_mem_ae_restrict (measurableSet_cell m n)] with x hx
    exact hpt x hx
  have hsub : ∫ x in cell m n, (f (lpt m n) - f x)
      = f (lpt m n) * m ^ 3 - ∫ x in cell m n, f x := by
    rw [MeasureTheory.integral_sub hfi hf, setIntegral_cell_const hm n]
    ring
  rw [hsub, setIntegral_cell_const hm n] at hmono
  have hkey : (m ^ 3)⁻¹ * (f (lpt m n) * m ^ 3 - ∫ x in cell m n, f x)
      = f (lpt m n) - (m ^ 3)⁻¹ * (∫ x in cell m n, f x) := by
    field_simp
  rw [← hkey]
  calc (m ^ 3)⁻¹ * (f (lpt m n) * m ^ 3 - ∫ x in cell m n, f x)
      ≤ (m ^ 3)⁻¹ * (m ^ 3 * B) := mul_le_mul_of_nonneg_left hmono (by positivity)
    _ = B := by field_simp

/-- The `abs` form of `cell_excess_le_of_pointwise`. -/
theorem cell_excess_le_of_abs {m : ℝ} (hm : 0 < m) (n : Fin 3 → ℤ) {f : E3 → ℝ} {B : ℝ}
    (hf : IntegrableOn f (cell m n))
    (hpt : ∀ x ∈ cell m n, |f (lpt m n) - f x| ≤ B) :
    f (lpt m n) - (m ^ 3)⁻¹ * (∫ x in cell m n, f x) ≤ B :=
  cell_excess_le_of_pointwise hm n hf fun x hx => le_trans (le_abs_self _) (hpt x hx)

/-- **Additivity of the per-cell excess** in the integrand. -/
theorem cell_excess_add {m : ℝ} (hm : 0 < m) (n : Fin 3 → ℤ) {f g : E3 → ℝ}
    (hf : IntegrableOn f (cell m n)) (hg : IntegrableOn g (cell m n)) :
    (f + g) (lpt m n) - (m ^ 3)⁻¹ * (∫ x in cell m n, (f + g) x)
      = (f (lpt m n) - (m ^ 3)⁻¹ * (∫ x in cell m n, f x))
        + (g (lpt m n) - (m ^ 3)⁻¹ * (∫ x in cell m n, g x)) := by
  have h1 : ∫ x in cell m n, (f + g) x = (∫ x in cell m n, f x) + (∫ x in cell m n, g x) :=
    MeasureTheory.integral_add hf hg
  rw [Pi.add_apply, h1]
  ring

/-! ## 3. The `√`-Hölder inequality -/

/-- `|√b − √b'| ≤ √|b − b'|` for `b, b' ≥ 0`. -/
lemma abs_sqrt_sub_sqrt_le_sqrt_abs {b b' : ℝ} (hb : 0 ≤ b) (hb' : 0 ≤ b') :
    |Real.sqrt b - Real.sqrt b'| ≤ Real.sqrt |b - b'| := by
  have hexp : (Real.sqrt b - Real.sqrt b') ^ 2
      = b + b' - 2 * (Real.sqrt b * Real.sqrt b') := by
    rw [sub_sq, Real.sq_sqrt hb, Real.sq_sqrt hb']
    ring
  have key : ∀ {x y : ℝ}, 0 ≤ y → 0 ≤ x → y ≤ x → y ≤ Real.sqrt x * Real.sqrt y := by
    intro x y hy hx0 hxy
    have h1 : y ^ 2 ≤ x * y := by nlinarith
    calc y = Real.sqrt (y ^ 2) := (Real.sqrt_sq hy).symm
      _ ≤ Real.sqrt (x * y) := Real.sqrt_le_sqrt h1
      _ = Real.sqrt x * Real.sqrt y := Real.sqrt_mul hx0 y
  rw [← Real.sqrt_sq (abs_nonneg _), sq_abs]
  refine Real.sqrt_le_sqrt ?_
  rw [hexp]
  rcases le_total b' b with h | h
  · rw [abs_of_nonneg (by linarith)]
    have hk := key hb' hb h
    nlinarith [hk]
  · rw [abs_of_nonpos (by linarith), neg_sub]
    have hk := key hb hb' h
    nlinarith [hk]

/-- **The `√`-Hölder inequality for a product of two nonnegative quantities.**
`|√(ab) − √(a'b')| ≤ √(a|b−b'|) + √(b'|a−a'|)`.  Both sides vanish at the cusp. -/
theorem abs_sqrt_mul_sub_le {a b a' b' : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (ha' : 0 ≤ a')
    (hb' : 0 ≤ b') :
    |Real.sqrt (a * b) - Real.sqrt (a' * b')|
      ≤ Real.sqrt (a * |b - b'|) + Real.sqrt (b' * |a - a'|) := by
  have h1 : |Real.sqrt (a * b) - Real.sqrt (a * b')| ≤ Real.sqrt (a * |b - b'|) := by
    have hfac : Real.sqrt (a * b) - Real.sqrt (a * b')
        = Real.sqrt a * (Real.sqrt b - Real.sqrt b') := by
      rw [Real.sqrt_mul ha b, Real.sqrt_mul ha b']
      ring
    rw [hfac, abs_mul, abs_of_nonneg (Real.sqrt_nonneg a)]
    calc Real.sqrt a * |Real.sqrt b - Real.sqrt b'|
        ≤ Real.sqrt a * Real.sqrt |b - b'| :=
          mul_le_mul_of_nonneg_left (abs_sqrt_sub_sqrt_le_sqrt_abs hb hb') (Real.sqrt_nonneg a)
      _ = Real.sqrt (a * |b - b'|) := (Real.sqrt_mul ha _).symm
  have h2 : |Real.sqrt (a * b') - Real.sqrt (a' * b')| ≤ Real.sqrt (b' * |a - a'|) := by
    have hfac : Real.sqrt (a * b') - Real.sqrt (a' * b')
        = Real.sqrt b' * (Real.sqrt a - Real.sqrt a') := by
      rw [Real.sqrt_mul ha b', Real.sqrt_mul ha' b']
      ring
    rw [hfac, abs_mul, abs_of_nonneg (Real.sqrt_nonneg b')]
    calc Real.sqrt b' * |Real.sqrt a - Real.sqrt a'|
        ≤ Real.sqrt b' * Real.sqrt |a - a'| :=
          mul_le_mul_of_nonneg_left (abs_sqrt_sub_sqrt_le_sqrt_abs ha ha') (Real.sqrt_nonneg b')
      _ = Real.sqrt (b' * |a - a'|) := (Real.sqrt_mul hb' _).symm
  calc |Real.sqrt (a * b) - Real.sqrt (a' * b')|
      = |(Real.sqrt (a * b) - Real.sqrt (a * b'))
          + (Real.sqrt (a * b') - Real.sqrt (a' * b'))| := by ring_nf
    _ ≤ |Real.sqrt (a * b) - Real.sqrt (a * b')|
          + |Real.sqrt (a * b') - Real.sqrt (a' * b')| := abs_add_le _ _
    _ ≤ _ := add_le_add h1 h2

/-! ## 4. The ball form of the pointwise hypothesis -/

/-- A uniform bound on `f (lpt) − f x` on the *ball* containing the cell dominates the excess. -/
theorem cell_excess_le_of_ball {m : ℝ} (hm : 0 < m) (n : Fin 3 → ℤ) {f : E3 → ℝ} {B : ℝ}
    (hf : IntegrableOn f (cell m n))
    (hpt : ∀ x : E3, ‖x - lpt m n‖ ≤ m * Real.sqrt 3 / 2 → f (lpt m n) - f x ≤ B) :
    f (lpt m n) - (m ^ 3)⁻¹ * (∫ x in cell m n, f x) ≤ B :=
  cell_excess_le_of_pointwise hm n hf fun x hx => hpt x (norm_sub_lpt_le hm hx)

/-- The `abs` form of `cell_excess_le_of_ball`. -/
theorem cell_excess_le_of_ball_abs {m : ℝ} (hm : 0 < m) (n : Fin 3 → ℤ) {f : E3 → ℝ} {B : ℝ}
    (hf : IntegrableOn f (cell m n))
    (hpt : ∀ x : E3, ‖x - lpt m n‖ ≤ m * Real.sqrt 3 / 2 → |f (lpt m n) - f x| ≤ B) :
    f (lpt m n) - (m ^ 3)⁻¹ * (∫ x in cell m n, f x) ≤ B :=
  cell_excess_le_of_ball hm n hf fun x hx => le_trans (le_abs_self _) (hpt x hx)

end Work.BoseBogFS
