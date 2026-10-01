import Mathlib
import Submission.Work.ZeroFreeTables.OffAxis.G72Base
import Submission.Work.OffAxis.Tf72One.Mtt_bound
import Submission.Work.OffAxis.G72Mom234
import Submission.Work.OffAxis.G72MomentClosed

open scoped Interval
open MeasureTheory

namespace Work.OffAxis.Tf72One

open Work.ZeroFreeTables
open Work.ZeroFreeTables.OffAxis

/-- Transport of `HasDerivAt` across a pointwise equality of the functions (the two `HasDerivAt`
types can differ in the type-class instances chosen for `ℝ`, so this is more robust than `simpa`). -/
lemma hasDerivAt_congr_of_eq {f g : ℝ → ℝ} {f' x : ℝ} (hg : HasDerivAt g f' x)
    (hfg : ∀ y, f y = g y) : HasDerivAt f f' x :=
  (Filter.EventuallyEq.hasDerivAt_iff (Filter.Eventually.of_forall hfg)).mpr hg

/-! ## The unit-interval exponential interpolation bound -/

/-- The unit-interval sharp two-point interpolation bound for `θ ↦ e^{θh}`:
`|e^{θh} - (1-θ+θe^h)| ≤ h²e^h/8` for `h ≥ 0`, `θ ∈ [0,1]`.

The upper half is the convexity of `exp`; the lower half follows from the concavity on `(-∞,1]`
of `θ ↦ θ(1-θ)h²e^h/2 - (1-θ+θe^h-e^{θh})`, which vanishes at `0` and `1`. -/
lemma interp_exp_unit (h θ : ℝ) (hh : 0 ≤ h) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1) :
    |Real.exp (θ * h) - ((1 - θ) + θ * Real.exp h)| ≤ h ^ 2 * Real.exp h / 8 := by
  have hconv : Real.exp (θ * h) ≤ (1 - θ) + θ * Real.exp h := by
    have h2 := convexOn_exp.2 (Set.mem_univ (0:ℝ)) (Set.mem_univ h)
      (show (0:ℝ) ≤ 1 - θ by linarith) (show (0:ℝ) ≤ θ by linarith)
      (show (1 - θ) + θ = 1 by ring)
    simpa using h2
  set F : ℝ → ℝ := fun τ =>
    (h ^ 2 * Real.exp h / 2) * (τ * (1 - τ))
      - ((1 - τ) + τ * Real.exp h - Real.exp (τ * h)) with hF
  have hF0 : F 0 = 0 := by simp [hF]
  have hF1 : F 1 = 0 := by simp [hF]
  have hFderiv : ∀ τ : ℝ, HasDerivAt F
      ((h ^ 2 * Real.exp h / 2) * (1 - 2 * τ) + (1 - Real.exp h) + h * Real.exp (τ * h)) τ := by
    intro τ
    have hraw := (((hasDerivAt_id τ).mul ((hasDerivAt_const τ (1:ℝ)).sub (hasDerivAt_id τ))).const_mul
          (h ^ 2 * Real.exp h / 2)).sub
          ((((hasDerivAt_const τ (1:ℝ)).sub (hasDerivAt_id τ)).add
            ((hasDerivAt_id τ).mul (hasDerivAt_const τ (Real.exp h)))).sub
            (((hasDerivAt_id τ).mul (hasDerivAt_const τ h)).exp))
    refine hasDerivAt_congr_of_eq (hraw.congr_deriv ?_) ?_
    · simp only [Pi.sub_apply, Pi.add_apply, Pi.mul_apply, id_eq, Function.comp_apply]
      ring
    · intro y
      simp only [hF, Pi.sub_apply, Pi.add_apply, Pi.mul_apply, id_eq, Function.comp_apply]
      try ring
  have hFderiv2 : ∀ τ : ℝ, HasDerivAt
      (fun τ : ℝ => (h ^ 2 * Real.exp h / 2) * (1 - 2 * τ) + (1 - Real.exp h)
        + h * Real.exp (τ * h))
      (h ^ 2 * (Real.exp (τ * h) - Real.exp h)) τ := by
    intro τ
    have hraw := ((((hasDerivAt_const τ (1:ℝ)).sub ((hasDerivAt_id τ).const_mul 2)).const_mul
          (h ^ 2 * Real.exp h / 2)).add (hasDerivAt_const τ ((1:ℝ) - Real.exp h))).add
          ((((hasDerivAt_id τ).mul (hasDerivAt_const τ h)).exp).const_mul h)
    refine hasDerivAt_congr_of_eq (hraw.congr_deriv ?_) ?_
    · simp only [Pi.sub_apply, Pi.add_apply, Pi.mul_apply, id_eq, Function.comp_apply]
      try ring
    · intro y
      simp only [Pi.sub_apply, Pi.add_apply, Pi.mul_apply, id_eq, Function.comp_apply]
  have hconc : ConcaveOn ℝ (Set.Iic 1) F := by
    refine concaveOn_of_hasDerivWithinAt2_nonpos (D := Set.Iic 1)
      (f' := fun τ : ℝ =>
        (h ^ 2 * Real.exp h / 2) * (1 - 2 * τ) + (1 - Real.exp h) + h * Real.exp (τ * h))
      (f'' := fun τ : ℝ => h ^ 2 * (Real.exp (τ * h) - Real.exp h))
      (convex_Iic 1) ?_ ?_ ?_ ?_
    · exact ((by fun_prop : Continuous F)).continuousOn
    · intro x hx
      exact (hFderiv x).hasDerivWithinAt
    · intro x hx
      exact (hFderiv2 x).hasDerivWithinAt
    · intro x hx
      have hx1 : x < 1 := by
        rw [interior_Iic] at hx
        exact hx
      have hcx : Real.exp (x * h) ≤ Real.exp h := by
        apply Real.exp_le_exp.mpr
        have h1 : (0:ℝ) ≤ (1 - x) * h := mul_nonneg (by linarith) hh
        nlinarith [h1]
      exact mul_nonpos_of_nonneg_of_nonpos (sq_nonneg h) (sub_nonpos.mpr hcx)
  have hFnn : 0 ≤ F θ := by
    have hch := hconc.2 (show (0:ℝ) ∈ Set.Iic 1 by simp) (show (1:ℝ) ∈ Set.Iic 1 by norm_num)
      (show (0:ℝ) ≤ 1 - θ by linarith) (show (0:ℝ) ≤ θ by linarith)
      (show (1 - θ) + θ = 1 by ring)
    simpa [hF0, hF1] using hch
  have hGval : F θ = θ * (1 - θ) * h ^ 2 * Real.exp h / 2
      - ((1 - θ) + θ * Real.exp h - Real.exp (θ * h)) := by
    simp only [hF]; ring
  have hGle : (1 - θ) + θ * Real.exp h - Real.exp (θ * h) ≤ h ^ 2 * Real.exp h / 8 := by
    have hθw : θ * (1 - θ) ≤ 1/4 := by nlinarith [sq_nonneg (2*θ - 1)]
    have hmul : θ * (1 - θ) * (h ^ 2 * Real.exp h / 2) ≤ (1/4) * (h ^ 2 * Real.exp h / 2) :=
      mul_le_mul_of_nonneg_right hθw (by positivity)
    have hEq : θ * (1 - θ) * h ^ 2 * Real.exp h / 2
        = θ * (1 - θ) * (h ^ 2 * Real.exp h / 2) := by ring
    have hEmul : (1/4) * (h ^ 2 * Real.exp h / 2) = h ^ 2 * Real.exp h / 8 := by ring
    have h1 := hFnn
    rw [hGval] at h1
    linarith [h1, hmul, hEq, hEmul]
  rw [abs_le]
  constructor
  · linarith [hGle]
  · have hpos : (0:ℝ) ≤ h ^ 2 * Real.exp h / 8 := by positivity
    linarith [hconv, hpos]

/-- **Exponential two-point interpolation bound.** For `a < b` and `0 ≤ y`, the linear interpolant of
`σ ↦ e^{σy}` at the endpoints `a`, `b` approximates it to within the sharp bound `(b-a)²/8 · y²e^{by}`:
on `[a,b]` the second derivative in `σ` is `y²e^{σy} ≤ y²e^{by}` (as `y ≥ 0`), so the classical
`(b-a)²/8 · sup|f''|` two-point interpolation error bound applies. -/
theorem InterpExpError (a b σ y : ℝ) (hab : a < b) (hσ : σ ∈ Set.Icc a b) (hy : 0 ≤ y) :
    |Real.exp (σ * y) - ((b - σ) / (b - a) * Real.exp (a * y)
        + (σ - a) / (b - a) * Real.exp (b * y))| ≤ (b - a) ^ 2 / 8 * (y ^ 2 * Real.exp (b * y)) := by
  have hba : (0:ℝ) < b - a := by linarith
  have hne : b - a ≠ 0 := ne_of_gt hba
  have hh : 0 ≤ (b - a) * y := mul_nonneg (le_of_lt hba) hy
  have hθ0 : 0 ≤ (σ - a) / (b - a) := div_nonneg (by linarith [hσ.1]) (le_of_lt hba)
  have hθ1 : (σ - a) / (b - a) ≤ 1 := by
    rw [div_le_iff₀ hba, one_mul]
    linarith [hσ.2]
  have hunit := interp_exp_unit ((b - a) * y) ((σ - a) / (b - a)) hh hθ0 hθ1
  have hmul := mul_le_mul_of_nonneg_left hunit (Real.exp_nonneg (a * y))
  have hαh : ((σ - a) / (b - a)) * ((b - a) * y) = (σ - a) * y := by
    rw [← mul_assoc, div_mul_cancel₀ _ hne]
  have hL : Real.exp (σ * y) - ((b - σ) / (b - a) * Real.exp (a * y)
        + (σ - a) / (b - a) * Real.exp (b * y))
      = Real.exp (a * y) * (Real.exp (((σ - a) / (b - a)) * ((b - a) * y))
          - ((1 - (σ - a) / (b - a)) + (σ - a) / (b - a) * Real.exp ((b - a) * y))) := by
    have e1 : Real.exp (σ * y) = Real.exp (a * y) * Real.exp (((σ - a) / (b - a)) * ((b - a) * y)) := by
      rw [← Real.exp_add]
      congr 1
      rw [hαh]; ring
    have e2 : Real.exp (b * y) = Real.exp (a * y) * Real.exp ((b - a) * y) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have e3 : (b - σ) / (b - a) = 1 - (σ - a) / (b - a) := by
      have h2 : ((b - a) - (σ - a)) / (b - a) = 1 - (σ - a) / (b - a) := by
        rw [sub_div, div_self hne]
      have h3 : (b - a) - (σ - a) = b - σ := by ring
      rw [← h3]; exact h2
    rw [e1, e2, e3]
    ring
  have hR : Real.exp (a * y) * (((b - a) * y) ^ 2 * Real.exp ((b - a) * y) / 8)
      = (b - a) ^ 2 / 8 * (y ^ 2 * Real.exp (b * y)) := by
    have e2 : Real.exp (b * y) = Real.exp (a * y) * Real.exp ((b - a) * y) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [e2]
    ring
  calc |Real.exp (σ * y) - ((b - σ) / (b - a) * Real.exp (a * y)
          + (σ - a) / (b - a) * Real.exp (b * y))|
      = |Real.exp (a * y) * (Real.exp (((σ - a) / (b - a)) * ((b - a) * y))
          - ((1 - (σ - a) / (b - a)) + (σ - a) / (b - a) * Real.exp ((b - a) * y)))| := by
        rw [hL]
    _ = Real.exp (a * y) * |Real.exp (((σ - a) / (b - a)) * ((b - a) * y))
          - ((1 - (σ - a) / (b - a)) + (σ - a) / (b - a) * Real.exp ((b - a) * y))| := by
        rw [abs_mul, abs_of_nonneg (Real.exp_nonneg _)]
    _ ≤ Real.exp (a * y) * (((b - a) * y) ^ 2 * Real.exp ((b - a) * y) / 8) := hmul
    _ = (b - a) ^ 2 / 8 * (y ^ 2 * Real.exp (b * y)) := hR

/-! ## The pointwise integrand bound in `s` -/

/-- Pointwise interpolation in `s` of the integrand: the `s`-dependence of
`(e^{sy}-2)cos(ty)g72 y` is controlled by its values at `s0`, `s1` plus the error term
`(s1-s0)²/8 · y²e^{s1y}g72 y`, using `|cos| ≤ 1` and `g72 ≥ 0`. -/
lemma integrand_interp_le_s (s t s0 s1 y : ℝ) (hs01 : s0 < s1) (hs0 : s0 ≤ s) (hs1 : s ≤ s1)
    (hy : y ∈ Set.Icc (0:ℝ) 2) :
    (Real.exp (s * y) - 2) * Real.cos (t * y) * g72 y ≤
      (s1 - s) / (s1 - s0) * ((Real.exp (s0 * y) - 2) * Real.cos (t * y) * g72 y)
      + (s - s0) / (s1 - s0) * ((Real.exp (s1 * y) - 2) * Real.cos (t * y) * g72 y)
      + (s1 - s0) ^ 2 / 8 * (y ^ 2 * Real.exp (s1 * y) * g72 y) := by
  have hgs : 0 ≤ g72 y := g72_nonneg hy.1 hy.2
  have hne : s1 - s0 ≠ 0 := ne_of_gt (by linarith : (0:ℝ) < s1 - s0)
  have hkey := InterpExpError s0 s1 s y hs01 ⟨hs0, hs1⟩ hy.1
  set w0 : ℝ := (s1 - s) / (s1 - s0) with hw0
  set w1 : ℝ := (s - s0) / (s1 - s0) with hw1
  set C : ℝ := Real.cos (t * y) with hC
  set G : ℝ := g72 y with hG
  set E0 : ℝ := Real.exp (s0 * y) with hE0
  set E1 : ℝ := Real.exp (s1 * y) with hE1
  set Es : ℝ := Real.exp (s * y) with hEs
  have hkey' : |Es - (w0 * E0 + w1 * E1)| ≤ (s1 - s0) ^ 2 / 8 * (y ^ 2 * E1) := hkey
  have hw : w0 + w1 = 1 := by
    rw [hw0, hw1, ← add_div, show (s1 - s) + (s - s0) = s1 - s0 by ring, div_self hne]
  have hGs : 0 ≤ G := by rw [hG]; exact hgs
  have hCs : |C| ≤ 1 := by rw [hC]; exact Real.abs_cos_le_one (t * y)
  have hErr : (Es - (w0 * E0 + w1 * E1)) * C * G ≤ |Es - (w0 * E0 + w1 * E1)| * G := by
    have h1 : (Es - (w0 * E0 + w1 * E1)) * C * G ≤ |(Es - (w0 * E0 + w1 * E1)) * C * G| :=
      le_abs_self _
    have h2 : |(Es - (w0 * E0 + w1 * E1)) * C * G| = |Es - (w0 * E0 + w1 * E1)| * |C| * G := by
      rw [abs_mul, abs_mul, abs_of_nonneg hGs]
    have h3 : |Es - (w0 * E0 + w1 * E1)| * |C| * G ≤ |Es - (w0 * E0 + w1 * E1)| * 1 * G := by
      apply mul_le_mul_of_nonneg_right
      · exact mul_le_mul_of_nonneg_left hCs (abs_nonneg _)
      · exact hGs
    have h4 : |Es - (w0 * E0 + w1 * E1)| * 1 * G = |Es - (w0 * E0 + w1 * E1)| * G := by ring
    have h5 : |Es - (w0 * E0 + w1 * E1)| * G ≤ (s1 - s0) ^ 2 / 8 * (y ^ 2 * E1) * G :=
      mul_le_mul_of_nonneg_right hkey' hGs
    linarith [h1, h2, h3, h4, h5]
  have hL2 : w0 * E0 + w1 * E1 - 2 = w0 * (E0 - 2) + w1 * (E1 - 2) := by
    have h : (w0 * E0 + w1 * E1 - 2) - (w0 * (E0 - 2) + w1 * (E1 - 2)) = 2 * (w0 + w1 - 1) := by
      ring
    rw [hw] at h
    linarith
  have hid : Es - 2 = (w0 * (E0 - 2) + w1 * (E1 - 2)) + (Es - (w0 * E0 + w1 * E1)) := by
    rw [← hL2]; ring
  calc (Es - 2) * C * G
      = (w0 * (E0 - 2) + w1 * (E1 - 2)) * C * G
        + (Es - (w0 * E0 + w1 * E1)) * C * G := by rw [hid]; ring
    _ ≤ (w0 * (E0 - 2) + w1 * (E1 - 2)) * C * G + |Es - (w0 * E0 + w1 * E1)| * G := by
        linarith [hErr]
    _ ≤ (w0 * (E0 - 2) + w1 * (E1 - 2)) * C * G + ((s1 - s0) ^ 2 / 8 * (y ^ 2 * E1)) * G := by
        linarith [mul_le_mul_of_nonneg_right hkey' hGs]
    _ = w0 * ((E0 - 2) * C * G) + w1 * ((E1 - 2) * C * G) + (s1 - s0) ^ 2 / 8 * (y ^ 2 * E1 * G) := by
        ring
    _ = (s1 - s) / (s1 - s0) * ((Real.exp (s0 * y) - 2) * Real.cos (t * y) * g72 y)
        + (s - s0) / (s1 - s0) * ((Real.exp (s1 * y) - 2) * Real.cos (t * y) * g72 y)
        + (s1 - s0) ^ 2 / 8 * (y ^ 2 * Real.exp (s1 * y) * g72 y) := by
        rw [hw0, hw1, hE0, hE1, hC, hG]; try ring

/-! ## The `s`-second-derivative integral bound -/

/-- The `s`-second-derivative bound for the Lemma 7.2 Laplace transform at `λ = 1`:
`∫₀² y² e^{sy} g72 y dy ≤ 13/10` for `0 ≤ s ≤ 17/16`. -/
lemma MssBoundS (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 17/16) :
    ∫ y in (0:ℝ)..2, y ^ 2 * Real.exp (s * y) * g72 y ≤ 13/10 := by
  have hI1 : IntervalIntegrable (fun y : ℝ => y ^ 2 * Real.exp (s * y) * g72 y)
      volume (0:ℝ) 2 := by
    apply Continuous.intervalIntegrable
    simp only [Work.ZeroFreeTables.g72]; fun_prop
  have hI2 : IntervalIntegrable (fun y : ℝ =>
      y ^ 2 * (1 + (17/16) * y + (17/16) ^ 2 * y ^ 2 / 2 + (17/16) ^ 3 * y ^ 3 / 6
        + (4/45) * (17/16) ^ 4 * y ^ 4) * g72 y) volume (0:ℝ) 2 := by
    apply Continuous.intervalIntegrable
    simp only [Work.ZeroFreeTables.g72]; fun_prop
  have hpt : ∀ y ∈ Set.Icc (0:ℝ) 2, y ^ 2 * Real.exp (s * y) * g72 y ≤
      y ^ 2 * (1 + (17/16) * y + (17/16) ^ 2 * y ^ 2 / 2 + (17/16) ^ 3 * y ^ 3 / 6
        + (4/45) * (17/16) ^ 4 * y ^ 4) * g72 y := by
    intro y hy
    have hy0 : 0 ≤ y := hy.1
    have hy2 : y ≤ 2 := hy.2
    have hg : 0 ≤ g72 y := g72_nonneg hy0 hy2
    have hexp : Real.exp (s * y) ≤ 1 + (17/16) * y + (17/16) ^ 2 * y ^ 2 / 2
        + (17/16) ^ 3 * y ^ 3 / 6 + (4/45) * (17/16) ^ 4 * y ^ 4 := by
      have h1 : Real.exp (s * y) ≤ Real.exp (17 * y / 16) :=
        Real.exp_le_exp.mpr (by nlinarith)
      have h2 : Real.exp (17 * y / 16) ≤ 1 + (17 * y / 16) + (17 * y / 16) ^ 2 / 2
          + (17 * y / 16) ^ 3 / 6 + (4/45) * (17 * y / 16) ^ 4 :=
        exp_series_quartic (17 * y / 16) (by positivity) (by nlinarith)
      have h3 : 1 + (17 * y / 16) + (17 * y / 16) ^ 2 / 2 + (17 * y / 16) ^ 3 / 6
          + (4/45) * (17 * y / 16) ^ 4
          = 1 + (17/16) * y + (17/16) ^ 2 * y ^ 2 / 2 + (17/16) ^ 3 * y ^ 3 / 6
            + (4/45) * (17/16) ^ 4 * y ^ 4 := by ring
      linarith [h1, h2, h3]
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hexp (sq_nonneg y)) hg
  have hmono := intervalIntegral.integral_mono_on (show (0:ℝ) ≤ 2 by norm_num) hI1 hI2 hpt
  have hval : (∫ y in (0:ℝ)..2, y ^ 2 * (1 + (17/16) * y + (17/16) ^ 2 * y ^ 2 / 2
      + (17/16) ^ 3 * y ^ 3 / 6 + (4/45) * (17/16) ^ 4 * y ^ 4) * g72 y) ≤ 13/10 := by
    have hI : ∀ k : ℕ, IntervalIntegrable (fun y : ℝ => y ^ k * g72 y) volume (0:ℝ) 2 := by
      intro k
      apply Continuous.intervalIntegrable
      simp only [Work.ZeroFreeTables.g72]; fun_prop
    have hcongr : (∫ y in (0:ℝ)..2, y ^ 2 * (1 + (17/16) * y + (17/16) ^ 2 * y ^ 2 / 2
        + (17/16) ^ 3 * y ^ 3 / 6 + (4/45) * (17/16) ^ 4 * y ^ 4) * g72 y)
        = ∫ y in (0:ℝ)..2, (y ^ 2 * g72 y + (17/16) * (y ^ 3 * g72 y)
            + ((17/16) ^ 2 / 2) * (y ^ 4 * g72 y) + ((17/16) ^ 3 / 6) * (y ^ 5 * g72 y)
            + ((4/45) * (17/16) ^ 4) * (y ^ 6 * g72 y)) := by
      apply intervalIntegral.integral_congr
      intro y _
      ring
    have hsplit : (∫ y in (0:ℝ)..2, (y ^ 2 * g72 y + (17/16) * (y ^ 3 * g72 y)
            + ((17/16) ^ 2 / 2) * (y ^ 4 * g72 y) + ((17/16) ^ 3 / 6) * (y ^ 5 * g72 y)
            + ((4/45) * (17/16) ^ 4) * (y ^ 6 * g72 y)))
        = (∫ y in (0:ℝ)..2, y ^ 2 * g72 y) + (17/16) * (∫ y in (0:ℝ)..2, y ^ 3 * g72 y)
          + ((17/16) ^ 2 / 2) * (∫ y in (0:ℝ)..2, y ^ 4 * g72 y)
          + ((17/16) ^ 3 / 6) * (∫ y in (0:ℝ)..2, y ^ 5 * g72 y)
          + ((4/45) * (17/16) ^ 4) * (∫ y in (0:ℝ)..2, y ^ 6 * g72 y) := by
      rw [intervalIntegral.integral_add, intervalIntegral.integral_add,
        intervalIntegral.integral_add, intervalIntegral.integral_add,
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
      all_goals (first
        | (apply Continuous.intervalIntegrable; simp only [Work.ZeroFreeTables.g72]; fun_prop)
        | rfl | ring)
    rw [hcongr, hsplit, Work.OffAxis.G72Mom234.1, Work.OffAxis.G72Mom234.2.1,
      Work.OffAxis.G72Mom234.2.2, Work.OffAxis.G72MomentClosed 5,
      Work.OffAxis.G72MomentClosed 6]
    norm_num
  linarith [hmono, hval]

/-! ## Assembly -/

theorem isub_le_interp_aux_s (s t s0 s1 : ℝ) (hs01 : s0 < s1) (hs0 : s0 ≤ s) (hs1 : s ≤ s1)
    (hM : ∫ y in (0:ℝ)..2, y ^ 2 * Real.exp (s1 * y) * g72 y ≤ 13/10) :
    Work.ZeroFreeTables.OffAxis.Isub s t ≤
      max (Work.ZeroFreeTables.OffAxis.Isub s0 t) (Work.ZeroFreeTables.OffAxis.Isub s1 t)
        + (s1 - s0) ^ 2 / 8 * (13/10) := by
  have hba : (0:ℝ) < s1 - s0 := by linarith
  have hIt : IntervalIntegrable (fun y : ℝ => (Real.exp (s * y) - 2) * Real.cos (t * y) * g72 y)
      volume (0:ℝ) 2 := by
    apply Continuous.intervalIntegrable
    simp only [Work.ZeroFreeTables.g72]; fun_prop
  have hI0 : IntervalIntegrable (fun y : ℝ => (Real.exp (s0 * y) - 2) * Real.cos (t * y) * g72 y)
      volume (0:ℝ) 2 := by
    apply Continuous.intervalIntegrable
    simp only [Work.ZeroFreeTables.g72]; fun_prop
  have hI1 : IntervalIntegrable (fun y : ℝ => (Real.exp (s1 * y) - 2) * Real.cos (t * y) * g72 y)
      volume (0:ℝ) 2 := by
    apply Continuous.intervalIntegrable
    simp only [Work.ZeroFreeTables.g72]; fun_prop
  have hIe : IntervalIntegrable (fun y : ℝ => y ^ 2 * Real.exp (s1 * y) * g72 y)
      volume (0:ℝ) 2 := by
    apply Continuous.intervalIntegrable
    simp only [Work.ZeroFreeTables.g72]; fun_prop
  have hpt : ∀ y ∈ Set.Icc (0:ℝ) 2,
      (Real.exp (s * y) - 2) * Real.cos (t * y) * g72 y ≤
        (s1 - s) / (s1 - s0) * ((Real.exp (s0 * y) - 2) * Real.cos (t * y) * g72 y)
        + (s - s0) / (s1 - s0) * ((Real.exp (s1 * y) - 2) * Real.cos (t * y) * g72 y)
        + (s1 - s0) ^ 2 / 8 * (y ^ 2 * Real.exp (s1 * y) * g72 y) :=
    fun y hy => integrand_interp_le_s s t s0 s1 y hs01 hs0 hs1 hy
  have hsumI : IntervalIntegrable
      (fun y : ℝ => (s1 - s) / (s1 - s0) * ((Real.exp (s0 * y) - 2) * Real.cos (t * y) * g72 y)
        + (s - s0) / (s1 - s0) * ((Real.exp (s1 * y) - 2) * Real.cos (t * y) * g72 y)
        + (s1 - s0) ^ 2 / 8 * (y ^ 2 * Real.exp (s1 * y) * g72 y)) volume (0:ℝ) 2 :=
    ((hI0.const_mul _).add (hI1.const_mul _)).add (hIe.const_mul _)
  have hmono := intervalIntegral.integral_mono_on (show (0:ℝ) ≤ 2 by norm_num) hIt hsumI hpt
  have hsplit : (∫ y in (0:ℝ)..2,
        (s1 - s) / (s1 - s0) * ((Real.exp (s0 * y) - 2) * Real.cos (t * y) * g72 y)
        + (s - s0) / (s1 - s0) * ((Real.exp (s1 * y) - 2) * Real.cos (t * y) * g72 y)
        + (s1 - s0) ^ 2 / 8 * (y ^ 2 * Real.exp (s1 * y) * g72 y))
      = (s1 - s) / (s1 - s0) * Work.ZeroFreeTables.OffAxis.Isub s0 t
        + (s - s0) / (s1 - s0) * Work.ZeroFreeTables.OffAxis.Isub s1 t
        + (s1 - s0) ^ 2 / 8 * (∫ y in (0:ℝ)..2, y ^ 2 * Real.exp (s1 * y) * g72 y) := by
    rw [intervalIntegral.integral_add ((hI0.const_mul _).add (hI1.const_mul _)) (hIe.const_mul _),
      intervalIntegral.integral_add (hI0.const_mul _) (hI1.const_mul _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const_mul,
      ← Work.ZeroFreeTables.OffAxis.Isub_eq_integral s0 t,
      ← Work.ZeroFreeTables.OffAxis.Isub_eq_integral s1 t]
  rw [hsplit, ← Work.ZeroFreeTables.OffAxis.Isub_eq_integral s t] at hmono
  have h0 : 0 ≤ (s1 - s) / (s1 - s0) := div_nonneg (by linarith) (le_of_lt hba)
  have h1 : 0 ≤ (s - s0) / (s1 - s0) := div_nonneg (by linarith) (le_of_lt hba)
  have hsumw : (s1 - s) / (s1 - s0) + (s - s0) / (s1 - s0) = 1 := by
    rw [← add_div, show s1 - s + (s - s0) = s1 - s0 by ring, div_self (ne_of_gt hba)]
  have hmax : (s1 - s) / (s1 - s0) * Work.ZeroFreeTables.OffAxis.Isub s0 t
      + (s - s0) / (s1 - s0) * Work.ZeroFreeTables.OffAxis.Isub s1 t
      ≤ max (Work.ZeroFreeTables.OffAxis.Isub s0 t) (Work.ZeroFreeTables.OffAxis.Isub s1 t) := by
    have hm := add_le_add
      (mul_le_mul_of_nonneg_left (le_max_left (Work.ZeroFreeTables.OffAxis.Isub s0 t)
        (Work.ZeroFreeTables.OffAxis.Isub s1 t)) h0)
      (mul_le_mul_of_nonneg_left (le_max_right (Work.ZeroFreeTables.OffAxis.Isub s0 t)
        (Work.ZeroFreeTables.OffAxis.Isub s1 t)) h1)
    have he : (s1 - s) / (s1 - s0) * max (Work.ZeroFreeTables.OffAxis.Isub s0 t)
          (Work.ZeroFreeTables.OffAxis.Isub s1 t)
        + (s - s0) / (s1 - s0) * max (Work.ZeroFreeTables.OffAxis.Isub s0 t)
          (Work.ZeroFreeTables.OffAxis.Isub s1 t)
        = max (Work.ZeroFreeTables.OffAxis.Isub s0 t) (Work.ZeroFreeTables.OffAxis.Isub s1 t) := by
      rw [← add_mul, hsumw, one_mul]
    linarith [hm, he]
  have herr : (s1 - s0) ^ 2 / 8 * (∫ y in (0:ℝ)..2, y ^ 2 * Real.exp (s1 * y) * g72 y)
      ≤ (s1 - s0) ^ 2 / 8 * (13/10) := mul_le_mul_of_nonneg_left hM (by positivity)
  linarith [hmono, hmax, herr]

/-- **`s`-interpolation for `Isub`.**  `s ↦ Isub s t = ∫₀² (e^{sy}-2)cos(ty)g72 y dy` is controlled by
its values at the endpoints of `[s0,s1]`: the second `s`-derivative is `∫₀² y²e^{sy}cos(ty)g72 y dy`,
of absolute value at most `∫₀² y²e^{s1y}g72 ≤ 13/10`, so the sharp two-point interpolation bound
applied pointwise in `y` and integrated gives the claim. -/
theorem Isub_le_interp_s (s t s0 s1 : ℝ) (hs0 : s0 ≤ s) (hs1 : s ≤ s1) (h0 : 0 ≤ s0) (h17 : s1 ≤ 17/16) :
    Work.ZeroFreeTables.OffAxis.Isub s t ≤
      max (Work.ZeroFreeTables.OffAxis.Isub s0 t) (Work.ZeroFreeTables.OffAxis.Isub s1 t)
        + (s1 - s0) ^ 2 / 8 * (13/10) := by
  rcases lt_or_ge s0 s1 with h | h
  · exact isub_le_interp_aux_s s t s0 s1 h hs0 hs1 (MssBoundS s1 (le_trans (le_trans h0 hs0) hs1) h17)
  · have hss1 : s0 = s1 := le_antisymm (le_trans hs0 hs1) h
    subst hss1
    have hse : s = s0 := le_antisymm hs1 hs0
    subst hse
    simp

end Work.OffAxis.Tf72One
