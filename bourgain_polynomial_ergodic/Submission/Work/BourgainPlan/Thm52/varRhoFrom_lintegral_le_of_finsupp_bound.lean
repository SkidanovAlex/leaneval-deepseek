import Mathlib
import Submission.Work.BourgainPlan.IonescuWainger.varRhoFrom_two_le_liminf
import Submission.Work.BourgainPlan.Maximal.kmsz_major_defs
import Submission.Work.BourgainPlan.IonescuWainger.sampling_principle_variation

namespace Work.BourgainPlan.Thm52

open MeasureTheory

-- Route: for each `k : ℤ`, `varRhoFrom_two_le_liminf κ (fun n => T n h k) (fun j n => T₀ n (f j) k)`
-- (with `hconv k`) gives `V²_{n≥κ}(T n h k) ≤ liminf_j V²_{n≥κ}(T₀ n (f j) k)`; then
-- `liminf_rpow_le_liminf_rpow` (`Submission/Work/BourgainPlan/IonescuWainger/sampling_principle_variation.lean`)
-- and Fatou's lemma `lintegral_liminf_le` give
-- `∫⁻_k (V²(T h))^p ≤ liminf_j ∫⁻_k (V²(T₀ (f j)))^p`, and `hbound` + `happ` close the estimate.
-- This is the *density/extension* step that upgrades a bound proved on finitely supported inputs to
-- one on all `ℓᵖ(ℤ)`-inputs (with the extended family defined as the pointwise limit of the values on
-- the approximations), which is what the (5.5) composition needs.  Over `ℤ` with `Measure.count` all
-- functions are measurable, so Fatou needs no measurability hypothesis.
theorem varRhoFrom_lintegral_le_of_finsupp_bound {p : ℝ} (hp : 1 < p) (κ : ℕ)
    {T : ℕ → (ℤ → ℂ) → (ℤ → ℂ)} {T₀ : ℕ → (ℤ →₀ ℂ) → (ℤ → ℂ)} {B : ℝ} (hB : 0 ≤ B)
    (hbound : ∀ f : ℤ →₀ ℂ,
      ∫⁻ k : ℤ, (Work.BourgainPlan.Maximal.varRhoFrom 2 κ (fun n => T₀ n f k)) ^ p
          ∂MeasureTheory.Measure.count
        ≤ ENNReal.ofReal (B ^ p)
          * ∫⁻ k : ℤ, ‖(⇑f : ℤ → ℂ) k‖ₑ ^ p ∂MeasureTheory.Measure.count)
    (h : ℤ → ℂ) (f : ℕ → ℤ →₀ ℂ)
    (hconv : ∀ (k : ℤ) (n : ℕ), Filter.Tendsto (fun j : ℕ => T₀ n (f j) k) Filter.atTop
      (nhds (T n h k)))
    (happ : Filter.Tendsto
      (fun j : ℕ => ∫⁻ k : ℤ, ‖(⇑(f j) : ℤ → ℂ) k‖ₑ ^ p ∂MeasureTheory.Measure.count)
      Filter.atTop (nhds (∫⁻ k : ℤ, ‖h k‖ₑ ^ p ∂MeasureTheory.Measure.count))) :
    ∫⁻ k : ℤ, (Work.BourgainPlan.Maximal.varRhoFrom 2 κ (fun n => T n h k)) ^ p
        ∂MeasureTheory.Measure.count
      ≤ ENNReal.ofReal (B ^ p) * ∫⁻ k : ℤ, ‖h k‖ₑ ^ p ∂MeasureTheory.Measure.count := by
  have hp0 : 0 < p := lt_trans zero_lt_one hp
  -- Step 1: pointwise lower semicontinuity of the `p`-th power of the variation.
  have hpoint : ∀ k : ℤ, (Work.BourgainPlan.Maximal.varRhoFrom 2 κ (fun n => T n h k)) ^ p
      ≤ Filter.liminf
          (fun j : ℕ => (Work.BourgainPlan.Maximal.varRhoFrom 2 κ (fun n => T₀ n (f j) k)) ^ p)
          Filter.atTop := by
    intro k
    refine le_trans (ENNReal.rpow_le_rpow
      (Work.BourgainPlan.IonescuWainger.varRhoFrom_two_le_liminf κ
        (fun n => T n h k) (fun j n => T₀ n (f j) k) (hconv k)) hp0.le) ?_
    exact Work.BourgainPlan.IonescuWainger.liminf_rpow_le_liminf_rpow hp0
      (fun j : ℕ => Work.BourgainPlan.Maximal.varRhoFrom 2 κ (fun n => T₀ n (f j) k))
  -- Step 2: the `j`-indexed liminf of the finitely-supported family is bounded by the bound.
  have hkey : Filter.liminf
      (fun j : ℕ => ∫⁻ k : ℤ,
        (Work.BourgainPlan.Maximal.varRhoFrom 2 κ (fun n => T₀ n (f j) k)) ^ p
        ∂MeasureTheory.Measure.count) Filter.atTop
      ≤ ENNReal.ofReal (B ^ p) * ∫⁻ k : ℤ, ‖h k‖ₑ ^ p ∂MeasureTheory.Measure.count := by
    have hlim : Filter.liminf
        (fun j : ℕ => ENNReal.ofReal (B ^ p)
          * ∫⁻ k : ℤ, ‖(⇑(f j) : ℤ → ℂ) k‖ₑ ^ p ∂MeasureTheory.Measure.count)
        Filter.atTop
        = ENNReal.ofReal (B ^ p) * ∫⁻ k : ℤ, ‖h k‖ₑ ^ p ∂MeasureTheory.Measure.count := by
      rw [(ENNReal.Tendsto.const_mul happ (Or.inr ENNReal.ofReal_ne_top)).liminf_eq]
    rw [← hlim]
    exact Filter.liminf_le_liminf (Filter.Eventually.of_forall (fun j => hbound (f j)))
  -- Step 3: Fatou.
  calc ∫⁻ k : ℤ, (Work.BourgainPlan.Maximal.varRhoFrom 2 κ (fun n => T n h k)) ^ p
        ∂MeasureTheory.Measure.count
      ≤ ∫⁻ k : ℤ, Filter.liminf
          (fun j : ℕ => (Work.BourgainPlan.Maximal.varRhoFrom 2 κ (fun n => T₀ n (f j) k)) ^ p)
          Filter.atTop ∂MeasureTheory.Measure.count := lintegral_mono hpoint
    _ ≤ Filter.liminf
          (fun j : ℕ => ∫⁻ k : ℤ,
            (Work.BourgainPlan.Maximal.varRhoFrom 2 κ (fun n => T₀ n (f j) k)) ^ p
            ∂MeasureTheory.Measure.count) Filter.atTop :=
        MeasureTheory.lintegral_liminf_le'
          (fun j => (Measurable.of_discrete : Measurable
            (fun k : ℤ => (Work.BourgainPlan.Maximal.varRhoFrom 2 κ
              (fun n => T₀ n (f j) k)) ^ p)).aemeasurable)
    _ ≤ ENNReal.ofReal (B ^ p) * ∫⁻ k : ℤ, ‖h k‖ₑ ^ p ∂MeasureTheory.Measure.count := hkey

end Work.BourgainPlan.Thm52
