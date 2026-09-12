import Submission.EquilibriumHolder
import Submission.Serre
import Submission.SupportConcentration
import Mathlib.MeasureTheory.Measure.MeasureSpace

/-!
# 1/2-Hölder hypothesis for Serre's measure

The Serre combination `μ = γ·ν + (1−γ)·μ_eq` on `[a,b]` is 1/2-Hölder:
for `a ≤ u ≤ v ≤ b`,

    μ (Icc u v) ≤ ENNReal.ofReal (4·(a+b)/(a·√(b−a)) · √(v−u)).

## Route
1. `equilibrium a b (Icc u v) ≤ (4/√(b−a))·√(v−u)` by
   `Submission.EquilibriumHolder.equilibrium_holder`.
2. ν-part: `nu a b (Icc u v) = equilibrium (1/b) (1/a) (invMap ⁻¹' (Icc u v))`
   (pushforward, `Measure.map_apply`) and `invMap ⁻¹' (Icc u v) = Icc (1/v) (1/u)`
   (inversion is antitone on positives), an interval inside `[1/b, 1/a]` of
   length `1/u − 1/v = (v−u)/(u·v) ≤ (v−u)/a²`; applying
   `equilibrium_holder` to `[1/b,1/a]` with interval length `(v−u)/a²` gives
   `ν(Icc u v) ≤ (4/(a·√(1/a − 1/b)))·√(v−u)`, and since
   `1/a − 1/b ≥ (b−a)/b²` (i.e. `ab ≤ b²`) this is
   `≤ (4b/(a·√(b−a)))·√(v−u)`.
3. Combination: `μ(I) = γ·ν(I) + (1−γ)·μ_eq(I)` (`Measure.add_apply`,
   `Measure.smul_apply`, `toReal_ofReal`), and `γ, 1−γ ≤ 1`, so
   `μ(I) ≤ ν(I) + μ_eq(I) ≤ (4/√(b−a) + 4b/(a√(b−a)))·√(v−u)
     = 4·(a+b)/(a·√(b−a))·√(v−u)`.
-/

noncomputable section

open MeasureTheory
open scoped Real ENNReal

namespace Submission.SerreHolder

open Submission.EquilibriumHolder
open Submission.Equilibrium
open Submission.Serre

/-- Inversion maps the reciprocal of the subinterval `[u,v]` (inclusion of
preimages: `{x | x⁻¹ ∈ [u,v]} ⊆ [v⁻¹, u⁻¹]` for `0 < u`). -/
lemma invMap_preimage_Icc_subset {a u v : ℝ} (ha : 0 < a) (hu : a ≤ u) (huv : u ≤ v) :
    invMap ⁻¹' (Set.Icc u v) ⊆ Set.Icc (v⁻¹) (u⁻¹) := by
  have hu0 : 0 < u := lt_of_lt_of_le ha hu
  have hv0 : 0 < v := lt_of_lt_of_le hu0 huv
  intro x hx
  rw [Set.mem_preimage] at hx
  have hxu : u ≤ x⁻¹ := by simpa [invMap] using hx.1
  have hxv : x⁻¹ ≤ v := by simpa [invMap] using hx.2
  have hxinv : 0 < x⁻¹ := lt_of_lt_of_le hu0 hxu
  have hxne : x ≠ 0 := by
    intro hxz
    simp [hxz] at hxinv
  constructor
  · have h1 : v⁻¹ ≤ x⁻¹⁻¹ := (inv_le_inv₀ hv0 hxinv).2 hxv
    simpa using h1
  · have h2 : x⁻¹⁻¹ ≤ u⁻¹ := (inv_le_inv₀ hxinv hu0).2 hxu
    simpa using h2

/-- The ν-part is 1/2-Hölder (via the inversion pullback to the reciprocal
equilibrium measure). -/
lemma nu_holder {a b u v : ℝ} (ha : 0 < a) (hab : a < b) (hu : a ≤ u)
    (huv : u ≤ v) (hv : v ≤ b) :
    nu a b (Set.Icc u v) ≤
      ENNReal.ofReal ((4 * b / (a * Real.sqrt (b - a))) * Real.sqrt (v - u)) := by
  have hb : 0 < b := lt_trans ha hab
  have hu0 : 0 < u := lt_of_lt_of_le ha hu
  have hv0 : 0 < v := lt_of_lt_of_le hu0 huv
  have hba : 0 < b - a := sub_pos.mpr hab
  have hL : 0 ≤ v - u := sub_nonneg.mpr huv
  have hsqb : 0 < Real.sqrt (b - a) := Real.sqrt_pos.mpr hba
  have hmeas : nu a b (Set.Icc u v) =
      equilibrium (b⁻¹) (a⁻¹) (invMap ⁻¹' (Set.Icc u v)) := by
    unfold nu
    rw [Measure.map_apply invMap_measurable isClosed_Icc.measurableSet]
  have hhold : equilibrium (b⁻¹) (a⁻¹) (Set.Icc (v⁻¹) (u⁻¹)) ≤
      ENNReal.ofReal ((4 / Real.sqrt (a⁻¹ - b⁻¹)) * Real.sqrt (u⁻¹ - v⁻¹)) := by
    have hrec_lt : b⁻¹ < a⁻¹ := (inv_lt_inv₀ hb ha).2 hab
    have h1 : b⁻¹ ≤ v⁻¹ := (inv_le_inv₀ hb hv0).2 hv
    have h2 : v⁻¹ ≤ u⁻¹ := (inv_le_inv₀ hv0 hu0).2 huv
    have h3 : u⁻¹ ≤ a⁻¹ := (inv_le_inv₀ hu0 ha).2 hu
    exact equilibrium_holder (a := b⁻¹) (b := a⁻¹) (x := v⁻¹) (y := u⁻¹) hrec_lt h1 h2 h3
  -- real chain: Holder bound on the reciprocal interval is ≤ the claimed ν-bound
  have hreal : (4 / Real.sqrt (a⁻¹ - b⁻¹)) * Real.sqrt (u⁻¹ - v⁻¹) ≤
      (4 * b / (a * Real.sqrt (b - a))) * Real.sqrt (v - u) := by
    have hlen1 : u⁻¹ - v⁻¹ ≤ (v - u) / a ^ 2 := by
      have ha2 : 0 < a ^ 2 := sq_pos_of_pos ha
      have hua2 : a * a ≤ u * v := by
        have h1 : a ≤ v := le_trans hu huv
        exact mul_le_mul hu h1 (le_of_lt ha) (le_of_lt hu0)
      have hrec : (u * v)⁻¹ ≤ (a ^ 2)⁻¹ := by
        exact (inv_le_inv₀ (mul_pos hu0 hv0) ha2).2 (by simpa [pow_two] using hua2)
      calc
        u⁻¹ - v⁻¹ = (v - u) * (u * v)⁻¹ := by
          field_simp [hu0.ne', hv0.ne']
        _ ≤ (v - u) * (a ^ 2)⁻¹ := mul_le_mul_of_nonneg_left hrec hL
        _ = (v - u) / a ^ 2 := by rw [div_eq_mul_inv]
    have hsqrt1 : Real.sqrt (u⁻¹ - v⁻¹) ≤ Real.sqrt (v - u) / a := by
      calc
        Real.sqrt (u⁻¹ - v⁻¹) ≤ Real.sqrt ((v - u) / a ^ 2) := Real.sqrt_le_sqrt hlen1
        _ = Real.sqrt (v - u) / a := by
          rw [Real.sqrt_div hL]
          rw [Real.sqrt_sq (le_of_lt ha)]
    have hlen2 : (b - a) / b ^ 2 ≤ a⁻¹ - b⁻¹ := by
      have hbab0 : 0 ≤ b - a := le_of_lt hba
      have habm : a * b ≤ b * b := by
        exact mul_le_mul (le_of_lt hab) le_rfl (le_of_lt hb) (le_of_lt hb)
      have hrec : (1 : ℝ) / b ^ 2 ≤ 1 / (a * b) := by
        exact one_div_le_one_div_of_le (mul_pos ha hb) (by simpa [pow_two] using habm)
      calc
        (b - a) / b ^ 2 = (b - a) * (1 / b ^ 2) := by simp [div_eq_mul_inv]
        _ ≤ (b - a) * (1 / (a * b)) := mul_le_mul_of_nonneg_left hrec hbab0
        _ = (b - a) / (a * b) := by simp [div_eq_mul_inv]
        _ = a⁻¹ - b⁻¹ := by
          field_simp [ha.ne', hb.ne']
    have hA1 : 0 < (b - a) / b ^ 2 := by positivity
    have hA : 0 < a⁻¹ - b⁻¹ := lt_of_lt_of_le hA1 hlen2
    have hsqrt2 : Real.sqrt (b - a) / b ≤ Real.sqrt (a⁻¹ - b⁻¹) := by
      calc
        Real.sqrt (b - a) / b = Real.sqrt ((b - a) / b ^ 2) := by
          rw [Real.sqrt_div (le_of_lt hba)]
          rw [Real.sqrt_sq (le_of_lt hb)]
        _ ≤ Real.sqrt (a⁻¹ - b⁻¹) := Real.sqrt_le_sqrt hlen2
    have hrec2 : (Real.sqrt (a⁻¹ - b⁻¹))⁻¹ ≤ b / Real.sqrt (b - a) := by
      have hB1 : 0 < Real.sqrt (b - a) / b := div_pos hsqb hb
      have hB2 : 0 < Real.sqrt (a⁻¹ - b⁻¹) := Real.sqrt_pos.mpr hA
      have hB3 : (Real.sqrt (a⁻¹ - b⁻¹))⁻¹ ≤ (Real.sqrt (b - a) / b)⁻¹ :=
        (inv_le_inv₀ hB2 hB1).2 hsqrt2
      simpa [one_div, div_eq_mul_inv] using hB3
    have hfac2 : 4 * (Real.sqrt (a⁻¹ - b⁻¹))⁻¹ ≤ 4 * (b / Real.sqrt (b - a)) := by
      exact mul_le_mul_of_nonneg_left hrec2 (by norm_num)
    calc
      (4 / Real.sqrt (a⁻¹ - b⁻¹)) * Real.sqrt (u⁻¹ - v⁻¹)
          = (4 * (Real.sqrt (a⁻¹ - b⁻¹))⁻¹) * Real.sqrt (u⁻¹ - v⁻¹) := by
            rw [div_eq_mul_inv]
      _ ≤ (4 * (Real.sqrt (a⁻¹ - b⁻¹))⁻¹) * (Real.sqrt (v - u) / a) := by
            exact mul_le_mul_of_nonneg_left hsqrt1 (by positivity : 0 ≤ 4 * (Real.sqrt (a⁻¹ - b⁻¹))⁻¹)
      _ ≤ (4 * (b / Real.sqrt (b - a))) * (Real.sqrt (v - u) / a) := by
            exact mul_le_mul_of_nonneg_right hfac2 (by positivity : 0 ≤ Real.sqrt (v - u) / a)
      _ = (4 * b / (a * Real.sqrt (b - a))) * Real.sqrt (v - u) := by
            field_simp [ha.ne', hsqb.ne', (Real.sqrt_pos.mpr hA).ne']
  calc
    nu a b (Set.Icc u v) = equilibrium (b⁻¹) (a⁻¹) (invMap ⁻¹' (Set.Icc u v)) := hmeas
    _ ≤ equilibrium (b⁻¹) (a⁻¹) (Set.Icc (v⁻¹) (u⁻¹)) := by
      exact MeasureTheory.measure_mono (invMap_preimage_Icc_subset (a := a) ha hu huv)
    _ ≤ ENNReal.ofReal ((4 / Real.sqrt (a⁻¹ - b⁻¹)) * Real.sqrt (u⁻¹ - v⁻¹)) := hhold
    _ ≤ ENNReal.ofReal ((4 * b / (a * Real.sqrt (b - a))) * Real.sqrt (v - u)) :=
      ENNReal.ofReal_le_ofReal hreal

/-- Serre's combination measure is 1/2-Hölder on `[a,b]`. -/
theorem serre_holder {a b γ u v : ℝ} (ha : 0 < a) (hab : a < b)
    (hγ0 : 0 ≤ γ) (hγ1 : γ ≤ 1) (hu : a ≤ u) (huv : u ≤ v) (hv : v ≤ b) :
    serreMeasure γ a b (Set.Icc u v) ≤
      ENNReal.ofReal ((4 * (a + b) / (a * Real.sqrt (b - a))) * Real.sqrt (v - u)) := by
  have hba : 0 < b - a := sub_pos.mpr hab
  have hL : 0 ≤ v - u := sub_nonneg.mpr huv
  have hb : 0 < b := lt_trans ha hab
  have hs : Real.sqrt (b - a) ≠ 0 := (Real.sqrt_pos.mpr hba).ne'
  have hnu : nu a b (Set.Icc u v) ≤
      ENNReal.ofReal ((4 * b / (a * Real.sqrt (b - a))) * Real.sqrt (v - u)) :=
    nu_holder ha hab hu huv hv
  have heq : equilibrium a b (Set.Icc u v) ≤
      ENNReal.ofReal ((4 / Real.sqrt (b - a)) * Real.sqrt (v - u)) :=
    equilibrium_holder hab hu huv hv
  have h1n : 0 ≤ (4 * b / (a * Real.sqrt (b - a))) * Real.sqrt (v - u) := by positivity
  have h2n : 0 ≤ (4 / Real.sqrt (b - a)) * Real.sqrt (v - u) := by positivity
  have hcoeff1 : ENNReal.ofReal γ ≤ (1 : ℝ≥0∞) := by
    simpa using (ENNReal.ofReal_le_ofReal hγ1 : ENNReal.ofReal γ ≤ ENNReal.ofReal (1 : ℝ))
  have hcoeff2 : ENNReal.ofReal (1 - γ) ≤ (1 : ℝ≥0∞) := by
    have hg : 1 - γ ≤ 1 := by linarith
    simpa using (ENNReal.ofReal_le_ofReal hg : ENNReal.ofReal (1 - γ) ≤ ENNReal.ofReal (1 : ℝ))
  have hsum_real : (4 * b / (a * Real.sqrt (b - a)) + 4 / Real.sqrt (b - a)) *
        Real.sqrt (v - u) = (4 * (a + b) / (a * Real.sqrt (b - a))) * Real.sqrt (v - u) := by
    have h1 : 4 * b / (a * Real.sqrt (b - a)) + 4 / Real.sqrt (b - a) =
        4 * (a + b) / (a * Real.sqrt (b - a)) := by
      field_simp [ha.ne', hs]
      ring
    rw [h1]
  have hstep1 : ENNReal.ofReal γ • nu a b (Set.Icc u v) ≤
      ENNReal.ofReal ((4 * b / (a * Real.sqrt (b - a))) * Real.sqrt (v - u)) := by
    calc
      ENNReal.ofReal γ • nu a b (Set.Icc u v)
          = ENNReal.ofReal γ * nu a b (Set.Icc u v) := by simp [smul_eq_mul]
      _ ≤ ENNReal.ofReal γ *
            ENNReal.ofReal ((4 * b / (a * Real.sqrt (b - a))) * Real.sqrt (v - u)) := by
            exact mul_le_mul_of_nonneg_left hnu (by positivity : 0 ≤ ENNReal.ofReal γ)
      _ ≤ (1 : ℝ≥0∞) *
            ENNReal.ofReal ((4 * b / (a * Real.sqrt (b - a))) * Real.sqrt (v - u)) := by
            exact mul_le_mul_of_nonneg_right hcoeff1 (by positivity : 0 ≤
              ENNReal.ofReal ((4 * b / (a * Real.sqrt (b - a))) * Real.sqrt (v - u)))
      _ = ENNReal.ofReal ((4 * b / (a * Real.sqrt (b - a))) * Real.sqrt (v - u)) := by simp
  have hstep2 : ENNReal.ofReal (1 - γ) • equilibrium a b (Set.Icc u v) ≤
      ENNReal.ofReal ((4 / Real.sqrt (b - a)) * Real.sqrt (v - u)) := by
    calc
      ENNReal.ofReal (1 - γ) • equilibrium a b (Set.Icc u v)
          = ENNReal.ofReal (1 - γ) * equilibrium a b (Set.Icc u v) := by simp [smul_eq_mul]
      _ ≤ ENNReal.ofReal (1 - γ) *
            ENNReal.ofReal ((4 / Real.sqrt (b - a)) * Real.sqrt (v - u)) := by
            exact mul_le_mul_of_nonneg_left heq (by positivity : 0 ≤ ENNReal.ofReal (1 - γ))
      _ ≤ (1 : ℝ≥0∞) *
            ENNReal.ofReal ((4 / Real.sqrt (b - a)) * Real.sqrt (v - u)) := by
            exact mul_le_mul_of_nonneg_right hcoeff2 (by positivity : 0 ≤
              ENNReal.ofReal ((4 / Real.sqrt (b - a)) * Real.sqrt (v - u)))
      _ = ENNReal.ofReal ((4 / Real.sqrt (b - a)) * Real.sqrt (v - u)) := by simp
  calc
    serreMeasure γ a b (Set.Icc u v)
        = ENNReal.ofReal γ • nu a b (Set.Icc u v)
            + ENNReal.ofReal (1 - γ) • equilibrium a b (Set.Icc u v) := by
            unfold serreMeasure
            rw [Measure.add_apply, Measure.smul_apply, Measure.smul_apply]
    _ ≤ ENNReal.ofReal ((4 * b / (a * Real.sqrt (b - a))) * Real.sqrt (v - u))
            + ENNReal.ofReal ((4 / Real.sqrt (b - a)) * Real.sqrt (v - u)) := by
            exact add_le_add hstep1 hstep2
    _ = ENNReal.ofReal ((4 * (a + b) / (a * Real.sqrt (b - a))) * Real.sqrt (v - u)) := by
            rw [← ENNReal.ofReal_add h1n h2n]
            congr 1
            calc
              (4 * b / (a * Real.sqrt (b - a))) * Real.sqrt (v - u)
                  + (4 / Real.sqrt (b - a)) * Real.sqrt (v - u)
                  = (4 * b / (a * Real.sqrt (b - a)) + 4 / Real.sqrt (b - a)) *
                      Real.sqrt (v - u) := by ring
              _ = (4 * (a + b) / (a * Real.sqrt (b - a))) * Real.sqrt (v - u) := hsum_real

end Submission.SerreHolder
