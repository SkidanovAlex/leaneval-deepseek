import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Measure.Lebesgue.VolumeOfBalls
import Submission.Work.BoseBogFS.CleanRiem
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The per-cell Riemann excess at the origin cell

This module proves `Work.BoseBogFS.origin_cell_excess_le`: the excess of the clean summand
`cleanFun` at the centre of the *origin* cell over the cell average is bounded by an explicit
amount depending only on the sup-norm `β₀` of the pairing coefficient `cAt`.

The origin cell is the one cell where the second-order Taylor estimate `cell_excess_le` does not
apply: `cleanFun` is unbounded below there (the subtracted mass term `c²/(2‖k‖²)` blows up like
`‖k‖⁻²` as `k → 0`), and only *local integrability in dimension three* saves the estimate.

The proof is a pointwise estimate combined with the exact radial integral

  `∫_{‖x‖ ≤ R} ‖x‖⁻² dx = 4πR`   (in dimension 3),

applied on the closed ball `‖x‖ ≤ m√3/2`, which contains the origin cell of side `m = 2π/ℓ`.

## The pointwise bound

Write `t = tauAt v μ x ≥ 0`, `b = cAt v h ρ μ x`, `|b| ≤ β₀`, so that

  `cleanFun x = 𝒵(t+b, b) - b²/(2‖x‖²)`,   `𝒵(A,B) = A - √(A²-B²)`,   `cleanFun 0 = c(0)`.

Since `√(A²-B²) ≤ |A|` we get `𝒵(A,B) ≥ A - |A| ≥ -2β₀` (as `A = t + b ≥ -β₀`).  Together with
`|b| ≤ β₀` this gives the *global* pointwise bound

  `-cleanFun x ≤ 2β₀ + (β₀²/2)·‖x‖⁻²`   for every `x`,

valid even at `x = 0` (where both sides are honest real numbers).

## The cell estimate

`⨍_{cell} ‖x‖⁻² ≤ (m³)⁻¹·4πR = (m³)⁻¹·4π·(m√3/2) = 2π√3/m²`, hence

  `-⨍_{cell} cleanFun ≤ 2β₀ + (β₀²/2)·2π√3/m²`,

and adding `cleanFun 0 ≤ β₀` gives the stated bound `3β₀ + β₀²·(2π√3)/m²` with a factor two to
spare (`(β₀²/2)·(2π√3/m²) = β₀²·π√3/m² ≤ β₀²·2π√3/m²`).
-/

noncomputable section

open scoped Real Topology BigOperators

open MeasureTheory Filter Metric

namespace Work.BoseBogFS

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## 1. Elementary algebraic helper -/

/-- Rewriting a double quotient as a product: `a/(2‖x‖²) = (a/2)·‖x‖⁻²`.  Needed because the
pointwise bound is most naturally produced by `div_le_div_of_nonneg_right` while the integral is
handled in the `·⁻¹` form. -/
lemma div_two_mul_eq (a : ℝ) (x : E3) : a / (2 * ‖x‖ ^ 2) = (a / 2) * (‖x‖ ^ 2)⁻¹ := by
  rw [div_eq_mul_inv, div_eq_mul_inv, mul_inv]
  ring

/-! ## 2. The radial integral of `‖x‖⁻²` in dimension three -/

/-- **Integrability of `‖x‖⁻²` on a (closed) ball.**  This is `integrableOn_fun_norm_addHaar`
applied to `f y = (y²)⁻¹`: the radial density is `y²·(y²)⁻¹ = 1` on `(0, ∞)`, which is integrable
on a bounded interval. -/
lemma integrableOn_inv_normSq_closedBall {R : ℝ} :
    IntegrableOn (fun x : E3 => (‖x‖ ^ 2)⁻¹) (Metric.closedBall (0 : E3) R) := by
  have hball : IntegrableOn (fun x : E3 => (‖x‖ ^ 2)⁻¹) (Metric.ball (0 : E3) (R + 1)) := by
    refine (MeasureTheory.integrableOn_fun_norm_addHaar (μ := (volume : Measure E3))
      (f := fun y : ℝ => (y ^ 2)⁻¹) (r := R + 1)).mpr ?_
    have hvol : (volume : Measure ℝ) (Set.Ioo (0 : ℝ) (R + 1)) ≠ ⊤ := by
      rw [Real.volume_Ioo]; exact ENNReal.ofReal_ne_top
    have hEq : Set.EqOn (fun _ : ℝ => (1 : ℝ))
        (fun y : ℝ => y ^ (Module.finrank ℝ E3 - 1) • (y ^ 2)⁻¹) (Set.Ioo 0 (R + 1)) := by
      intro y hy
      have hy0 : 0 < y := hy.1
      have hfr : Module.finrank ℝ E3 = 3 := by simp [finrank_euclideanSpace]
      show (1 : ℝ) = y ^ (Module.finrank ℝ E3 - 1) • (y ^ 2)⁻¹
      rw [hfr, show ((3 : ℕ) - 1) = 2 from rfl, smul_eq_mul, eq_comm]
      exact mul_inv_cancel₀ (pow_ne_zero 2 (ne_of_gt hy0))
    exact (MeasureTheory.integrableOn_const (s := Set.Ioo (0 : ℝ) (R + 1))
      (μ := (volume : Measure ℝ)) (C := (1 : ℝ)) hvol enorm_ne_top).congr_fun hEq
        measurableSet_Ioo
  refine hball.mono_set ?_
  intro x hx
  simp only [Metric.mem_ball, Metric.mem_closedBall, dist_eq_norm, sub_zero] at hx ⊢
  linarith

/-- **The exact radial integral in dimension three:** `∫_{‖x‖ ≤ R} ‖x‖⁻² dx = 4πR`. -/
lemma setIntegral_inv_normSq_closedBall {R : ℝ} (hR : 0 ≤ R) :
    ∫ x in Metric.closedBall (0 : E3) R, (‖x‖ ^ 2)⁻¹ = 4 * Real.pi * R := by
  classical
  have hmble : MeasurableSet (Metric.closedBall (0 : E3) R) := measurableSet_closedBall
  rw [← MeasureTheory.integral_indicator hmble (f := fun x : E3 => (‖x‖ ^ 2)⁻¹)]
  have hmem : ∀ x : E3, (x ∈ Metric.closedBall (0 : E3) R) ↔ ‖x‖ ≤ R := by
    intro x; rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
  have hpt : ∀ x : E3,
      (Metric.closedBall (0 : E3) R).indicator (fun x : E3 => (‖x‖ ^ 2)⁻¹) x
        = (fun y : ℝ => if y ≤ R then (y ^ 2)⁻¹ else 0) ‖x‖ := by
    intro x
    rw [Set.indicator_apply, hmem x]
  rw [funext hpt]
  rw [MeasureTheory.integral_fun_norm_addHaar (μ := (volume : Measure E3))
      (f := fun y : ℝ => if y ≤ R then (y ^ 2)⁻¹ else 0)]
  have hfr : Module.finrank ℝ E3 = 3 := by simp [finrank_euclideanSpace]
  rw [hfr]
  have hreal : (volume : Measure E3).real (Metric.ball 0 1) = 4 * Real.pi / 3 := by
    rw [MeasureTheory.Measure.real, EuclideanSpace.volume_ball_fin_three]
    simp only [ENNReal.ofReal_one, one_pow, one_mul]
    rw [ENNReal.toReal_ofReal (by positivity)]
    ring
  have hlen : ∫ y in Set.Ioi (0 : ℝ), y ^ ((3 : ℕ) - 1) • (if y ≤ R then (y ^ 2)⁻¹ else 0)
      = R := by
    have hg : ∀ y ∈ Set.Ioi (0 : ℝ), y ^ ((3 : ℕ) - 1) • (if y ≤ R then (y ^ 2)⁻¹ else 0)
        = (Set.Ioc (0 : ℝ) R).indicator (fun _ => (1 : ℝ)) y := by
      intro y hy
      have hy0 : 0 < y := hy
      have hy2 : y ^ 2 ≠ 0 := pow_ne_zero 2 (ne_of_gt hy0)
      rw [Set.indicator_apply, show ((3 : ℕ) - 1) = 2 from rfl]
      by_cases hyR : y ≤ R
      · rw [if_pos hyR, if_pos ⟨hy0, hyR⟩, smul_eq_mul]
        exact mul_inv_cancel₀ hy2
      · rw [if_neg hyR, if_neg (fun h => hyR h.2), smul_eq_mul, mul_zero]
    rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hg]
    rw [MeasureTheory.setIntegral_indicator measurableSet_Ioc]
    have hinter : Set.Ioi (0 : ℝ) ∩ Set.Ioc (0 : ℝ) R = Set.Ioc (0 : ℝ) R := by
      ext y; simp only [Set.mem_inter_iff, Set.mem_Ioi, Set.mem_Ioc]; tauto
    rw [hinter, MeasureTheory.setIntegral_const]
    rw [MeasureTheory.Measure.real, Real.volume_Ioc]
    rw [ENNReal.toReal_ofReal (by linarith)]
    simp
  rw [hlen, hreal]
  ring

/-! ## 3. The pointwise bound for the clean summand -/

/-- **The clean summand is bounded below by `-2β₀ - (β₀²/2)‖x‖⁻²`.**  The hypotheses on `τ` and
`c` are used only through `τ ≥ 0` and `|c| ≤ β₀`. -/
lemma neg_cleanFun_le {v : E3 → ℝ} {h : Work.UBB.ScatSol v} {ρ μ β₀ : ℝ}
    (hβ0 : 0 ≤ β₀) (hτnn : ∀ k : E3, 0 ≤ Work.BoseBogFS.tauAt v μ k)
    (hβ : ∀ k : E3, |Work.BoseBogFS.cAt v h ρ μ k| ≤ β₀) (x : E3) :
    -(Work.BoseBogFS.cleanFun v h ρ μ x) ≤ 2 * β₀ + (β₀ ^ 2 / 2) * (‖x‖ ^ 2)⁻¹ := by
  set t := Work.BoseBogFS.tauAt v μ x
  set b := Work.BoseBogFS.cAt v h ρ μ x
  have ht : 0 ≤ t := hτnn x
  have hb : |b| ≤ β₀ := hβ x
  have hble : -β₀ ≤ b := (abs_le.mp hb).1
  have hbsq : b ^ 2 ≤ β₀ ^ 2 := by nlinarith [hb, hβ0, abs_nonneg b, sq_abs b]
  have hA : -β₀ ≤ t + b := by linarith
  have hsqrt : Real.sqrt ((t + b) ^ 2 - b ^ 2) ≤ |t + b| := by
    rw [← Real.sqrt_sq_eq_abs]
    apply Real.sqrt_le_sqrt
    nlinarith [sq_nonneg b]
  have hAbsA : |t + b| - (t + b) ≤ 2 * β₀ := by
    rcases le_or_gt 0 (t + b) with hA0 | hA0
    · rw [abs_of_nonneg hA0]; linarith
    · rw [abs_of_neg hA0]; linarith
  have hZ : -(Work.BoseB6.bogZeroPoint (t + b) b) ≤ 2 * β₀ := by
    rw [Work.BoseB6.bogZeroPoint]; linarith [hsqrt, hAbsA]
  have hdiv : b ^ 2 / (2 * ‖x‖ ^ 2) ≤ β₀ ^ 2 / (2 * ‖x‖ ^ 2) :=
    div_le_div_of_nonneg_right hbsq (by positivity)
  rw [div_two_mul_eq (b ^ 2) x, div_two_mul_eq (β₀ ^ 2) x] at hdiv
  have hexp : -(Work.BoseBogFS.cleanFun v h ρ μ x)
      = -(Work.BoseB6.bogZeroPoint (t + b) b) + b ^ 2 / (2 * ‖x‖ ^ 2) := by
    rw [Work.BoseBogFS.cleanFun]; ring
  rw [hexp, div_two_mul_eq (b ^ 2) x]
  linarith [hZ, hdiv]

/-! ## 4. The integral inequality without an integrability hypothesis on the left -/

/-- If `-f ≤ g` pointwise, `g` is integrable on `s` and `∫_s g ≥ 0`, then
`-∫_s g ≤ ∫_s f`.  The point is that the case `f ∉ L¹(s)` is handled by the *junk* value of the
Bochner integral (`∫_s f = 0`), which is the correct value for the final estimate since the right
hand side is nonnegative. -/
lemma neg_setIntegral_le_of_pointwise {f g : E3 → ℝ} {s : Set E3}
    (h : ∀ x, -f x ≤ g x) (hg : IntegrableOn g s) (hg0 : 0 ≤ ∫ x in s, g x) :
    -∫ x in s, g x ≤ ∫ x in s, f x := by
  by_cases hf : IntegrableOn f s
  · have h1 : ∫ x in s, (-f) x ≤ ∫ x in s, g x :=
      MeasureTheory.integral_mono_ae hf.neg hg (Filter.Eventually.of_forall h)
    simp only [Pi.neg_apply] at h1
    rw [MeasureTheory.integral_neg] at h1
    linarith
  · rw [MeasureTheory.integral_undef hf]
    linarith

/-! ## 5. The main theorem -/

theorem origin_cell_excess_le {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v} {ρ μ β₀ : ℝ}
    (hβ0 : 0 ≤ β₀) (hτ : Work.BoseBogFS.tauAt v μ 0 = 0)
    (hτnn : ∀ k : EuclideanSpace ℝ (Fin 3), 0 ≤ Work.BoseBogFS.tauAt v μ k)
    (hβ : ∀ k : EuclideanSpace ℝ (Fin 3), |Work.BoseBogFS.cAt v h ρ μ k| ≤ β₀) :
    Work.BoseBogFS.cleanFun v h ρ μ 0
        - ((2 * Real.pi / Work.BoseFixR.ell v μ) ^ 3)⁻¹
          * (∫ x in Work.BoseBogFS.cell (2 * Real.pi / Work.BoseFixR.ell v μ) 0,
              Work.BoseBogFS.cleanFun v h ρ μ x)
      ≤ 3 * β₀ + β₀ ^ 2 * (2 * Real.pi * Real.sqrt 3)
          / (2 * Real.pi / Work.BoseFixR.ell v μ) ^ 2 := by
  classical
  set m : ℝ := 2 * Real.pi / Work.BoseFixR.ell v μ with hmdef
  -- the value at the centre: at `k = 0` both `‖k‖` and `τ(k)` vanish
  have hfin0 : Work.BoseBogFS.cleanFun v h ρ μ 0 = Work.BoseBogFS.cAt v h ρ μ 0 := by
    simp [Work.BoseBogFS.cleanFun, Work.BoseB6.bogZeroPoint, hτ]
  have hfin0le : Work.BoseBogFS.cleanFun v h ρ μ 0 ≤ β₀ := by
    rw [hfin0]; exact (abs_le.mp (hβ 0)).2
  have hpt : ∀ x : E3, -(Work.BoseBogFS.cleanFun v h ρ μ x)
      ≤ 2 * β₀ + (β₀ ^ 2 / 2) * (‖x‖ ^ 2)⁻¹ := fun x => neg_cleanFun_le hβ0 hτnn hβ x
  by_cases hm : 0 < m
  · -- Nondegenerate case: the cell has side `m > 0` and lies in the ball of radius `m√3/2`.
    set R : ℝ := m * Real.sqrt 3 / 2 with hRdef
    have hRnn : 0 ≤ R := by rw [hRdef]; positivity
    have hballval : ∫ x in Metric.closedBall (0 : E3) R, (‖x‖ ^ 2)⁻¹ = 4 * Real.pi * R :=
      setIntegral_inv_normSq_closedBall hRnn
    have hφcl : IntegrableOn (fun x : E3 => (‖x‖ ^ 2)⁻¹) (Metric.closedBall (0 : E3) R) :=
      integrableOn_inv_normSq_closedBall
    have hcellsub : Work.BoseBogFS.cell m (0 : Fin 3 → ℤ) ⊆ Metric.closedBall (0 : E3) R := by
      intro x hx
      have h := Work.BoseBogFS.norm_sub_lpt_le hm hx
      have hl : Work.BoseBogFS.lpt m (0 : Fin 3 → ℤ) = 0 := by
        ext i; simp [Work.BoseBogFS.lpt]
      rw [hl, sub_zero] at h
      simpa [Metric.mem_closedBall, dist_eq_norm, hRdef] using h
    have hcellφ : IntegrableOn (fun x : E3 => (‖x‖ ^ 2)⁻¹)
        (Work.BoseBogFS.cell m (0 : Fin 3 → ℤ)) := hφcl.mono_set hcellsub
    have hφnn : 0 ≤ ∫ x in Work.BoseBogFS.cell m (0 : Fin 3 → ℤ), (‖x‖ ^ 2)⁻¹ :=
      MeasureTheory.integral_nonneg (f := fun x : E3 => (‖x‖ ^ 2)⁻¹)
        (fun x => inv_nonneg.mpr (sq_nonneg ‖x‖))
    have hcellval : ∫ x in Work.BoseBogFS.cell m (0 : Fin 3 → ℤ), (‖x‖ ^ 2)⁻¹
        ≤ 4 * Real.pi * R := by
      have hmono := MeasureTheory.setIntegral_mono_set hφcl
        (Filter.Eventually.of_forall fun x => inv_nonneg.mpr (sq_nonneg ‖x‖))
        (Filter.Eventually.of_forall fun x hx => hcellsub hx)
      rwa [hballval] at hmono
    have hcint : IntegrableOn (fun _ : E3 => 2 * β₀) (Work.BoseBogFS.cell m (0 : Fin 3 → ℤ)) := by
      refine MeasureTheory.integrableOn_const ?_ ?_
      · rw [Work.BoseBogFS.volume_cell hm 0]; exact ENNReal.ofReal_ne_top
      · exact enorm_ne_top
    have hgint : IntegrableOn (fun x : E3 => 2 * β₀ + (β₀ ^ 2 / 2) * (‖x‖ ^ 2)⁻¹)
        (Work.BoseBogFS.cell m (0 : Fin 3 → ℤ)) :=
      hcint.add (hcellφ.const_mul (β₀ ^ 2 / 2))
    have hgval : ∫ x in Work.BoseBogFS.cell m (0 : Fin 3 → ℤ),
          (2 * β₀ + (β₀ ^ 2 / 2) * (‖x‖ ^ 2)⁻¹)
        = 2 * β₀ * m ^ 3 + (β₀ ^ 2 / 2)
            * (∫ x in Work.BoseBogFS.cell m (0 : Fin 3 → ℤ), (‖x‖ ^ 2)⁻¹) := by
      have hsplit : (fun x : E3 => 2 * β₀ + (β₀ ^ 2 / 2) * (‖x‖ ^ 2)⁻¹)
          = fun x : E3 => (fun _ : E3 => 2 * β₀) x
              + (fun x : E3 => (β₀ ^ 2 / 2) * (‖x‖ ^ 2)⁻¹) x := rfl
      rw [hsplit, MeasureTheory.integral_add hcint (hcellφ.const_mul _),
        Work.BoseBogFS.setIntegral_cell_const hm 0 (2 * β₀), MeasureTheory.integral_const_mul]
      ring
    have hgnn : 0 ≤ ∫ x in Work.BoseBogFS.cell m (0 : Fin 3 → ℤ),
        (2 * β₀ + (β₀ ^ 2 / 2) * (‖x‖ ^ 2)⁻¹) := by
      rw [hgval]
      have h1 : 0 ≤ 2 * β₀ * m ^ 3 := by positivity
      have h2 : 0 ≤ (β₀ ^ 2 / 2)
          * (∫ x in Work.BoseBogFS.cell m (0 : Fin 3 → ℤ), (‖x‖ ^ 2)⁻¹) :=
        mul_nonneg (by positivity) hφnn
      linarith
    have hint := neg_setIntegral_le_of_pointwise hpt hgint hgnn
    have hint' : -∫ x in Work.BoseBogFS.cell m (0 : Fin 3 → ℤ),
          Work.BoseBogFS.cleanFun v h ρ μ x
        ≤ ∫ x in Work.BoseBogFS.cell m (0 : Fin 3 → ℤ),
            (2 * β₀ + (β₀ ^ 2 / 2) * (‖x‖ ^ 2)⁻¹) := by linarith
    have hstep : Work.BoseBogFS.cleanFun v h ρ μ 0
        - (m ^ 3)⁻¹ * (∫ x in Work.BoseBogFS.cell m (0 : Fin 3 → ℤ),
            Work.BoseBogFS.cleanFun v h ρ μ x)
        ≤ β₀ + (m ^ 3)⁻¹ * (∫ x in Work.BoseBogFS.cell m (0 : Fin 3 → ℤ),
            (2 * β₀ + (β₀ ^ 2 / 2) * (‖x‖ ^ 2)⁻¹)) := by
      have h1 : (m ^ 3)⁻¹ * (-∫ x in Work.BoseBogFS.cell m (0 : Fin 3 → ℤ),
            Work.BoseBogFS.cleanFun v h ρ μ x)
          ≤ (m ^ 3)⁻¹ * (∫ x in Work.BoseBogFS.cell m (0 : Fin 3 → ℤ),
            (2 * β₀ + (β₀ ^ 2 / 2) * (‖x‖ ^ 2)⁻¹)) :=
        mul_le_mul_of_nonneg_left hint' (by positivity)
      have h2 : Work.BoseBogFS.cleanFun v h ρ μ 0
          - (m ^ 3)⁻¹ * (∫ x in Work.BoseBogFS.cell m (0 : Fin 3 → ℤ),
              Work.BoseBogFS.cleanFun v h ρ μ x)
          = Work.BoseBogFS.cleanFun v h ρ μ 0 + (m ^ 3)⁻¹
              * (-∫ x in Work.BoseBogFS.cell m (0 : Fin 3 → ℤ),
                  Work.BoseBogFS.cleanFun v h ρ μ x) := by
        ring
      rw [h2]
      linarith [hfin0le]
    have hlast : β₀ + (m ^ 3)⁻¹ * (∫ x in Work.BoseBogFS.cell m (0 : Fin 3 → ℤ),
          (2 * β₀ + (β₀ ^ 2 / 2) * (‖x‖ ^ 2)⁻¹))
        ≤ 3 * β₀ + β₀ ^ 2 * (2 * Real.pi * Real.sqrt 3) / m ^ 2 := by
      rw [hgval]
      have hm3 : m ^ 3 ≠ 0 := pow_ne_zero 3 (ne_of_gt hm)
      set I : ℝ := ∫ x in Work.BoseBogFS.cell m (0 : Fin 3 → ℤ), (‖x‖ ^ 2)⁻¹ with hI
      have hIle : I ≤ 4 * Real.pi * R := hcellval
      have h1 : (m ^ 3)⁻¹ * (2 * β₀ * m ^ 3 + (β₀ ^ 2 / 2) * I)
          = 2 * β₀ + (m ^ 3)⁻¹ * ((β₀ ^ 2 / 2) * I) := by
        have hmul : (m ^ 3)⁻¹ * (2 * β₀ * m ^ 3) = 2 * β₀ := by
          rw [mul_comm (2 * β₀) (m ^ 3), ← mul_assoc, inv_mul_cancel₀ hm3, one_mul]
        rw [mul_add, hmul]
      have h2 : (m ^ 3)⁻¹ * ((β₀ ^ 2 / 2) * I)
          ≤ (m ^ 3)⁻¹ * ((β₀ ^ 2 / 2) * (4 * Real.pi * R)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hIle (by positivity))
          (by positivity)
      have h3 : (m ^ 3)⁻¹ * ((β₀ ^ 2 / 2) * (4 * Real.pi * R))
          = β₀ ^ 2 * (Real.pi * Real.sqrt 3) / m ^ 2 := by
        rw [hRdef]
        field_simp
        try ring
      have h4 : β₀ ^ 2 * (Real.pi * Real.sqrt 3) / m ^ 2
          ≤ β₀ ^ 2 * (2 * Real.pi * Real.sqrt 3) / m ^ 2 := by
        apply div_le_div_of_nonneg_right _ (by positivity)
        have h0 : (0 : ℝ) ≤ β₀ ^ 2 * (Real.pi * Real.sqrt 3) :=
          mul_nonneg (sq_nonneg β₀) (by positivity)
        nlinarith [h0]
      linarith [h1, h2, h3, h4]
    linarith [hstep, hlast]
  · -- Degenerate case `m ≤ 0`: the cell is empty, the integral is `0`, and the bound reduces to
    -- `cleanFun 0 ≤ β₀ ≤ 3β₀ ≤ 3β₀ + β₀²(2π√3)/m²`.
    have hempty : Work.BoseBogFS.cell m (0 : Fin 3 → ℤ) = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro x hx
      obtain ⟨h1, h2⟩ := (Work.BoseBogFS.mem_cell.mp hx) 0
      simp only [Pi.zero_apply, Int.cast_zero, mul_zero, zero_sub, zero_add] at h1 h2
      linarith
    have hzero : ∫ x in Work.BoseBogFS.cell m (0 : Fin 3 → ℤ),
        Work.BoseBogFS.cleanFun v h ρ μ x = 0 := by
      rw [hempty, MeasureTheory.setIntegral_empty]
    rw [hzero, mul_zero, sub_zero]
    have hnn : 0 ≤ β₀ ^ 2 * (2 * Real.pi * Real.sqrt 3) / m ^ 2 := by positivity
    linarith [hfin0le, hnn, hβ0]

end Work.BoseBogFS
