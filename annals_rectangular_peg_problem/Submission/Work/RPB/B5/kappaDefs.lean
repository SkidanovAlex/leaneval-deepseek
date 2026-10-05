import Mathlib
import Submission.Work.RPV.Defs
import Submission.Work.RPV.VBasic
import Submission.Work.RPB.Defs

/-!
# B5: the `κ`-parametrised collar — definitions

This file fixes the objects used by `Work.RPB.B5.collar_exists_kappa`.  It is deliberately
self-contained (it does not import `collar_exists_noL`), so that the (much more detailed)
development of the sibling `noL` route can proceed in parallel.

## Design

Given the `ρ = r²`-chart `W` of the chord annulus and its level inverse `ρh` on the level
interval `(-κ, κ)` (`K₀ (W τ t (ρh τ t σ)) + 1 = -σ`), we build the collar `(Γc, Ac)` of the
levels `σ ≥ 0` with the ten properties of `collar_exists_kappa`.

Write `N τ σ t = uproj (W τ t (ρh τ t σ))` (the reduced coordinate of the chart point on the
level `σ`) and `A τ σ t` for its phase.  The key local facts (proved in sibling modules) are

* for `σ < 0` small and `τ = 0` one has `N 0 σ t = √(2+2σ) e^{it}` and `A 0 σ t = t + π/2 + 2πk`
  (`kappa_tau0`), and `N`, `A` are `C¹²` in `σ`, so the differences from these closed forms are
  *flat* at `σ = 0`;
* the flux defect `Def = ω_ℂ(∂_σ N, ∂_t N) - ∂_t A` vanishes for `σ < 0` (the chord chart is
  Lagrangian there), hence, by smoothness, is *flat to order* `8` at `σ = 0` (`kappa_defect`);
* consequently `σ ↦ signedArea (t ↦ N τ σ t)` equals `2π(1+σ)` for `σ ≤ 0` small
  (`kappa_near_area`).

The collar is then

* `kshape` — a *single* smooth formula: the clamped chart family (the level is clamped so that
  `ρh` is only ever evaluated inside `(-κ,κ)`, which makes the formula smooth with no piecewise
  argument), corrected near `τ = 0` so that the `τ = 0` slice is exactly the target circle, and
  blended into the rescaled circle family `kfsh` (which equals `√(2+2σ) e^{i(t-π/2)}` for
  `σ ≥ 2δ`, because `krpf` is `0` and `kphc` is `-π/2 - 2πk` there);
* `kg`, `kgam` — the *real-linear* normalisation `z ↦ kdiagM (g σ) z` with `g σ = 2π(1+σ)/karS σ`.
  Unlike the square-root normalisation of the `noL` route this needs no square root, so it is
  smooth on all of `ℝ` (as soon as `karS` is nonvanishing), it gives the exact area law
  `g · karS = 2π(1+σ)` for *every* `σ` — which is what makes the `+2π` monodromy of `Ac` available
  for all `σ ∈ ℝ` — and its `τ = 0` slice is exact because `g = 1` there;
* `kac` — the phase: the `σ`-jet interpolation `kA0` at `t = 0` plus the flux integral, so that
  the Lagrangian identity `∂_t Ac = ω_ℂ(∂_σ Γc, ∂_t Γc)` holds by the fundamental theorem of
  calculus.
-/

open RectangularPegProblem
open Manifold Complex Real
open scoped ContDiff Topology Interval

set_option autoImplicit false

noncomputable section

namespace Work.RPB.B5

/-! ## Copy of the elementary transition function (kept local to this file) -/

/-- The smooth transition function: `0` on `(-∞,0]`, `1` on `[1,∞)`. -/
def kstp (x : ℝ) : ℝ := Real.smoothTransition x

theorem kstp_contDiff : ContDiff ℝ ∞ kstp := Real.smoothTransition.contDiff

theorem kstp_zero {x : ℝ} (h : x ≤ 0) : kstp x = 0 := Real.smoothTransition.zero_of_nonpos h

theorem kstp_one {x : ℝ} (h : 1 ≤ x) : kstp x = 1 := Real.smoothTransition.one_of_one_le h

theorem kstp_nonneg (x : ℝ) : 0 ≤ kstp x := Real.smoothTransition.nonneg x

theorem kstp_le_one (x : ℝ) : kstp x ≤ 1 := Real.smoothTransition.le_one x

/-! ## The clamps and cutoffs -/

/-- The lower clamp: `= σ` for `σ ≥ -δ/2`, `= -δ/2` for `σ ≤ -δ`. -/
def kcneg (δ σ : ℝ) : ℝ := σ - (σ + δ / 2) * kstp (-(σ + δ / 2) / (δ / 2))

/-- The upper clamp: `= σ` for `σ ≤ δ/2`, `= δ/2` for `σ ≥ δ`. -/
def kcpos (δ σ : ℝ) : ℝ := σ - (σ - δ / 2) * kstp ((σ - δ / 2) / (δ / 2))

/-- A two-sided smooth clamp of the level, taking values in `(-δ, δ)` and equal to `σ` on
`[-δ/2, δ/2]`.  Its purpose is to keep every evaluation of the level inverse `ρh` inside
`(-κ,κ)` (when `δ < κ`), which makes the formulas below smooth with no piecewise argument. -/
def kclamp (δ σ : ℝ) : ℝ := kcpos δ (kcneg δ σ)

/-- The cutoff of the `τ = 0` correction: `0` for `σ ≤ -δ/4`, `1` for `σ ≥ 0`.  It switches the
correction off before the `Real.sqrt` singularity of `krd` at `σ = -1`; this is harmless because
the correction already vanishes identically for `-δ/4 < σ ≤ 0`. -/
def xfade (δ σ : ℝ) : ℝ := kstp (4 * σ / δ + 1)

/-- The phase offset: `0` for `σ ≤ δ`, `-(π/2 + 2πk)` for `σ ≥ 2δ`. -/
def kphc (δ : ℝ) (k : ℤ) (σ : ℝ) : ℝ :=
  (-(Real.pi / 2) - 2 * Real.pi * k) * kstp ((σ - δ) / δ)

/-- The chord parameter of the far family: `1` for `σ ≤ δ`, `0` for `σ ≥ 2δ`. -/
def krpf (δ σ : ℝ) : ℝ := 1 - kstp ((σ - δ) / δ)

/-- The blend cutoff between the chart part and the far circles: `0` for `σ ≤ δ/2`, `1` for
`σ ≥ δ`. -/
def kblf (δ σ : ℝ) : ℝ := kstp ((σ - δ / 2) / (δ / 2))

/-- The bump switching on the `τ = 0` correction: `1` for `τ ≤ 0`, `0` for `τ ≥ δ`. -/
def kbbmp (δ τ : ℝ) : ℝ := 1 - kstp (τ / δ)

/-- The radius of the far circles. -/
def krd (σ : ℝ) : ℝ := Real.sqrt (2 + 2 * σ)

/-- The diagonal real-linear map `(x,y) ↦ (x, g·y)` of `ℂ ≅ ℝ²`; its determinant is `g`, so it
scales the signed area by `g` and reverses orientation when `g < 0`. -/
def kdiagM (g : ℝ) (z : ℂ) : ℂ := (z.re : ℂ) + ((g * z.im : ℝ) : ℂ) * Complex.I

/-- The `τ = 0` target circle of radius `√(2+2σ)`. -/
def ktarg (δ : ℝ) (k : ℤ) (σ t : ℝ) : ℂ :=
  (krd σ : ℂ) * Complex.exp ((t + kphc δ k σ) * Complex.I)

/-- The far family: the rescaled curve family carried by `CI.c`, equal to the target circle for
`σ ≥ 2δ`. -/
def kfsh (CI : Work.RPV.CurveIsotopy) (δ : ℝ) (k : ℤ) (τ σ t : ℝ) : ℂ :=
  (krd σ : ℂ) * CI.c (krpf δ σ * τ) (t + kphc δ k σ)

/-- The `σ`-jets of the phase of the chart point at `t = 0`. -/
def kcj (W : ℝ → ℝ → ℝ → Work.RPV.PS) (ρh : ℝ → ℝ → ℝ → ℝ) (τ : ℝ) (j : ℕ) : ℝ :=
  iteratedDeriv j (fun σ : ℝ => (W τ 0 (ρh τ 0 σ)).1.2) 0

/-- The bump of the jet interpolation. -/
def kjbump (δ σ : ℝ) : ℝ := 1 - kstp (σ / δ)

/-- The constant of integration of the phase: its `σ`-jets at `σ = 0` are those of the chart
phase at `t = 0` (so that the jet condition of the statement holds), it equals
`φ + π/2 + 2πk` on the `τ = 0` slice (so that the `τ = 0` slice lies in the zero section) and it
vanishes for `σ ≥ 2δ`. -/
def kA0 (W : ℝ → ℝ → ℝ → Work.RPV.PS) (ρh : ℝ → ℝ → ℝ → ℝ) (δ : ℝ) (k : ℤ) (τ σ : ℝ) : ℝ :=
  (kphc δ k σ + Real.pi / 2 + 2 * Real.pi * k) +
    ∑ j ∈ Finset.range 9,
      (kcj W ρh τ j - kcj W ρh 0 j) * (σ ^ j / (Nat.factorial j : ℝ)) * kjbump δ σ

/-! ## The glued shape and its normalisation -/

/-- The near shape: the reduced coordinate of the chart point on the clamped level `kclamp δ σ`,
corrected so that the `τ = 0` slice is exactly the target circle `ktarg`.  The correction
vanishes identically for `σ ≤ 0` (where the `τ = 0` chart already is the circle) and is flat to
order `12` at `σ = 0`, so it never disturbs the `σ`-jets. -/
def knear (CI : Work.RPV.CurveIsotopy) (W : ℝ → ℝ → ℝ → Work.RPV.PS) (ρh : ℝ → ℝ → ℝ → ℝ)
    (δ : ℝ) (k : ℤ) (τ σ t : ℝ) : ℂ :=
  Work.RPV.uproj (W τ t (ρh τ t (kclamp δ σ)))
    + kbbmp δ τ * xfade δ σ *
        (ktarg δ k σ t - Work.RPV.uproj (W 0 t (ρh 0 t (kclamp δ σ))))

/-- The glued shape (before the normalisation). -/
def kshape (CI : Work.RPV.CurveIsotopy) (W : ℝ → ℝ → ℝ → Work.RPV.PS) (ρh : ℝ → ℝ → ℝ → ℝ)
    (δ : ℝ) (k : ℤ) (τ σ t : ℝ) : ℂ :=
  (1 - kblf δ σ) * knear CI W ρh δ k τ σ t + kblf δ σ * kfsh CI δ k τ σ t

/-- The signed area of the glued shape. -/
def karS (CI : Work.RPV.CurveIsotopy) (W : ℝ → ℝ → ℝ → Work.RPV.PS) (ρh : ℝ → ℝ → ℝ → ℝ)
    (δ : ℝ) (k : ℤ) (τ σ : ℝ) : ℝ :=
  Work.RPB.signedArea (fun t => kshape CI W ρh δ k τ σ t)

/-- The real-linear normalisation factor; `kg · karS = 2π(1+σ)` exactly. -/
def kg (CI : Work.RPV.CurveIsotopy) (W : ℝ → ℝ → ℝ → Work.RPV.PS) (ρh : ℝ → ℝ → ℝ → ℝ)
    (δ : ℝ) (k : ℤ) (τ σ : ℝ) : ℝ :=
  2 * Real.pi * (1 + σ) / karS CI W ρh δ k τ σ

/-- The collar curve family: the normalised glued shape. -/
def kgam (CI : Work.RPV.CurveIsotopy) (W : ℝ → ℝ → ℝ → Work.RPV.PS) (ρh : ℝ → ℝ → ℝ → ℝ)
    (δ : ℝ) (k : ℤ) (τ σ t : ℝ) : ℂ :=
  kdiagM (kg CI W ρh δ k τ σ) (kshape CI W ρh δ k τ σ t)

/-- The phase of the collar: the jet interpolation `kA0` at `σ = 0` plus the flux integral. -/
def kac (CI : Work.RPV.CurveIsotopy) (W : ℝ → ℝ → ℝ → Work.RPV.PS) (ρh : ℝ → ℝ → ℝ → ℝ)
    (δ : ℝ) (k : ℤ) (τ σ t : ℝ) : ℝ :=
  kA0 W ρh δ k τ σ +
    ∫ u in (0 : ℝ)..t,
      Work.RPV.ωC (deriv (fun s => kgam CI W ρh δ k τ s u) σ)
        (deriv (fun s => kgam CI W ρh δ k τ σ s) u)

/-! ## Elementary properties of the clamps -/

theorem kclamp_contDiff (δ : ℝ) : ContDiff ℝ ∞ (kclamp δ) := by
  unfold kclamp kcpos kcneg kstp
  fun_prop

theorem xfade_contDiff (δ : ℝ) : ContDiff ℝ ∞ (xfade δ) := by
  unfold xfade kstp
  fun_prop

theorem kcneg_le_max {δ σ : ℝ} (hδ : 0 < δ) : kcneg δ σ ≤ max σ (-(δ / 2)) := by
  unfold kcneg
  have h0 : 0 ≤ kstp (-(σ + δ / 2) / (δ / 2)) := kstp_nonneg _
  have h1 : kstp (-(σ + δ / 2) / (δ / 2)) ≤ 1 := kstp_le_one _
  rcases lt_or_ge σ (-(δ / 2)) with h | h
  · rw [max_eq_right h.le]
    have hs : σ + δ / 2 ≤ 0 := by linarith
    nlinarith [mul_le_mul_of_nonpos_left h1 hs]
  · rw [max_eq_left h]
    have hz : kstp (-(σ + δ / 2) / (δ / 2)) = 0 :=
      kstp_zero (div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith))
    rw [hz, mul_zero, sub_zero]

theorem kcneg_ge_min {δ σ : ℝ} (hδ : 0 < δ) : min σ (-(δ / 2)) ≤ kcneg δ σ := by
  unfold kcneg
  have h0 : 0 ≤ kstp (-(σ + δ / 2) / (δ / 2)) := kstp_nonneg _
  rcases lt_or_ge σ (-(δ / 2)) with h | h
  · rw [min_eq_left h.le]
    have hs : σ + δ / 2 ≤ 0 := by linarith
    nlinarith [mul_nonpos_of_nonpos_of_nonneg hs h0]
  · rw [min_eq_right h]
    have hz : kstp (-(σ + δ / 2) / (δ / 2)) = 0 :=
      kstp_zero (div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith))
    rw [hz, mul_zero, sub_zero]
    exact h

theorem kcpos_le_max {δ σ : ℝ} (hδ : 0 < δ) : kcpos δ σ ≤ max σ (δ / 2) := by
  unfold kcpos
  have h0 : 0 ≤ kstp ((σ - δ / 2) / (δ / 2)) := kstp_nonneg _
  rcases lt_or_ge σ (δ / 2) with h | h
  · rw [max_eq_right h.le]
    have hz : kstp ((σ - δ / 2) / (δ / 2)) = 0 :=
      kstp_zero (div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith))
    rw [hz, mul_zero, sub_zero]
    exact h.le
  · rw [max_eq_left h]
    have hs : 0 ≤ σ - δ / 2 := by linarith
    nlinarith [mul_nonneg hs h0]

theorem kcpos_ge_min {δ σ : ℝ} (hδ : 0 < δ) : min σ (δ / 2) ≤ kcpos δ σ := by
  unfold kcpos
  have h1 : kstp ((σ - δ / 2) / (δ / 2)) ≤ 1 := kstp_le_one _
  rcases lt_or_ge σ (δ / 2) with h | h
  · rw [min_eq_left h.le]
    have hz : kstp ((σ - δ / 2) / (δ / 2)) = 0 :=
      kstp_zero (div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith))
    rw [hz, mul_zero, sub_zero]
  · rw [min_eq_right h]
    have hs : 0 ≤ σ - δ / 2 := by linarith
    nlinarith [mul_le_mul_of_nonneg_left h1 hs]

/-- `kcneg δ σ = σ` when `σ ≥ -δ/2`. -/
theorem kcneg_eq_self {δ σ : ℝ} (hδ : 0 < δ) (h : -(δ / 2) ≤ σ) : kcneg δ σ = σ := by
  unfold kcneg
  have hz : kstp (-(σ + δ / 2) / (δ / 2)) = 0 :=
    kstp_zero (div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith))
  rw [hz, mul_zero, sub_zero]

/-- `kcneg δ σ = -δ/2` when `σ ≤ -δ`. -/
theorem kcneg_eq_neg_half {δ σ : ℝ} (hδ : 0 < δ) (h : σ ≤ -(δ)) : kcneg δ σ = -(δ / 2) := by
  unfold kcneg
  have h1 : kstp (-(σ + δ / 2) / (δ / 2)) = 1 := by
    apply kstp_one
    rw [le_div_iff₀ (by linarith : (0 : ℝ) < δ / 2)]
    linarith
  rw [h1, mul_one]
  ring

/-- `kcpos δ σ = σ` when `σ ≤ δ/2`. -/
theorem kcpos_eq_self {δ σ : ℝ} (hδ : 0 < δ) (h : σ ≤ δ / 2) : kcpos δ σ = σ := by
  unfold kcpos
  have hz : kstp ((σ - δ / 2) / (δ / 2)) = 0 :=
    kstp_zero (div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith))
  rw [hz, mul_zero, sub_zero]

/-- `kcpos δ σ = δ/2` when `σ ≥ δ`. -/
theorem kcpos_eq_half {δ σ : ℝ} (hδ : 0 < δ) (h : δ ≤ σ) : kcpos δ σ = δ / 2 := by
  unfold kcpos
  have h1 : kstp ((σ - δ / 2) / (δ / 2)) = 1 := by
    apply kstp_one
    rw [le_div_iff₀ (by linarith : (0 : ℝ) < δ / 2)]
    linarith
  rw [h1, mul_one]
  ring

/-- For `σ ≤ -δ/2` the first clamp lands in `[-δ, -δ/2]`. -/
theorem kcneg_mem_Icc {δ σ : ℝ} (hδ : 0 < δ) (h : σ ≤ -(δ / 2)) :
    kcneg δ σ ∈ Set.Icc (-(δ)) (-(δ / 2)) := by
  constructor
  · rcases lt_or_ge σ (-(δ)) with h2 | h2
    · rw [kcneg_eq_neg_half hδ h2.le]
      linarith
    · have hmin : min σ (-(δ / 2)) = σ := min_eq_left h
      have hge := kcneg_ge_min hδ (δ := δ) (σ := σ)
      rw [hmin] at hge
      linarith
  · have hmax : max σ (-(δ / 2)) = -(δ / 2) := max_eq_right h
    have hle := kcneg_le_max hδ (δ := δ) (σ := σ)
    rw [hmax] at hle
    exact hle

/-- For `δ/2 ≤ σ ≤ δ` the second clamp lands in `[δ/2, δ]`. -/
theorem kcpos_mem_Icc {δ σ : ℝ} (hδ : 0 < δ) (h : δ / 2 ≤ σ) (h2 : σ ≤ δ) :
    kcpos δ σ ∈ Set.Icc (δ / 2) δ := by
  constructor
  · have hmin : min σ (δ / 2) = δ / 2 := min_eq_right h
    have hge := kcpos_ge_min hδ (δ := δ) (σ := σ)
    rw [hmin] at hge
    exact hge
  · rcases lt_or_ge σ δ with h3 | h3
    · have hmax : max σ (δ / 2) = σ := max_eq_left h
      have hle := kcpos_le_max hδ (δ := δ) (σ := σ)
      rw [hmax] at hle
      linarith
    · rw [kcpos_eq_half hδ h3]
      linarith

/-- `kclamp δ σ = σ` for `|σ| ≤ δ/2`. -/
theorem kclamp_of_abs_le {δ σ : ℝ} (hδ : 0 < δ) (h : |σ| ≤ δ / 2) : kclamp δ σ = σ := by
  have h1 : kcneg δ σ = σ := kcneg_eq_self hδ (by linarith [(abs_le.mp h).1])
  have h2 : kcpos δ σ = σ := kcpos_eq_self hδ (by linarith [(abs_le.mp h).2])
  unfold kclamp
  rw [h1, h2]

/-- `kclamp δ σ ≤ 0` when `σ ≤ 0`. -/
theorem kclamp_nonpos {δ σ : ℝ} (hδ : 0 < δ) (h : σ ≤ 0) : kclamp δ σ ≤ 0 := by
  have h1 : kcneg δ σ ≤ 0 := by
    rcases lt_or_ge σ (-(δ / 2)) with h2 | h2
    · have hmem := kcneg_mem_Icc hδ h2.le
      linarith [hmem.2]
    · rw [kcneg_eq_self hδ h2]
      exact h
  unfold kclamp
  rw [kcpos_eq_self hδ (by linarith)]
  exact h1

/-- The clamp takes values in `(-δ, δ)`. -/
theorem abs_kclamp_le {δ σ : ℝ} (hδ : 0 < δ) : |kclamp δ σ| ≤ δ := by
  rcases lt_or_ge σ (-(δ / 2)) with hσ | hσ
  · have hmem := kcneg_mem_Icc hδ hσ.le
    have hkc : kclamp δ σ = kcneg δ σ := by
      unfold kclamp
      exact kcpos_eq_self hδ (by linarith [hmem.2])
    rw [hkc, abs_le]
    exact ⟨by linarith [hmem.1], by linarith [hmem.2]⟩
  · have h1 : kcneg δ σ = σ := kcneg_eq_self hδ hσ
    unfold kclamp
    rw [h1]
    rcases lt_or_ge σ (δ / 2) with h2 | h2
    · have h3 : kcpos δ σ = σ := kcpos_eq_self hδ h2.le
      rw [h3, abs_le]
      constructor <;> linarith
    · rcases lt_or_ge σ δ with h3 | h3
      · have hmem := kcpos_mem_Icc hδ h2 h3.le
        rw [abs_le]
        exact ⟨by linarith [hmem.1], by linarith [hmem.2]⟩
      · have h4 : kcpos δ σ = δ / 2 := kcpos_eq_half hδ h3
        rw [h4, abs_le]
        constructor <;> linarith

theorem xfade_zero {δ σ : ℝ} (hδ : 0 < δ) (h : σ ≤ -(δ / 4)) : xfade δ σ = 0 := by
  unfold xfade
  apply kstp_zero
  have : 4 * σ / δ ≤ -1 := by
    rw [div_le_iff₀ hδ]
    linarith
  linarith

theorem xfade_one {δ σ : ℝ} (hδ : 0 < δ) (h : 0 ≤ σ) : xfade δ σ = 1 := by
  unfold xfade
  apply kstp_one
  have : (0 : ℝ) ≤ 4 * σ / δ := div_nonneg (by linarith) hδ.le
  linarith

end Work.RPB.B5
