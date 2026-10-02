import Mathlib
import Submission.Work.MRMT.Found.Defs
import Submission.Work.MRMT.Found.courantLebesgue_uniform

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# A uniform modulus of continuity on the unit scale for injective `C¹` maps with
bounded dilatation and bounded image area

We prove `Work.MRMT.Found.fw_exists_uniform_modulus`: if `F n : ℂ → ℂ` is a sequence of
injective `C¹` maps whose complex dilatations satisfy `‖∂̄F n‖ ≤ k ‖∂F n‖` pointwise with
`0 ≤ k < 1`, and if the images of all unit balls have area at most `A`, then the family
`{F n}` admits a *single* modulus of continuity `ω` on the unit scale,

`‖F n z - F n z'‖ ≤ ω ‖z - z'‖` whenever `‖z - z'‖ ≤ 1`,

with `ω r → 0` as `r → 0⁺`.

The proof combines the Courant–Lebesgue estimate
(`Work.MRMT.Found.courantLebesgue_uniform`)

`‖F z - F z₀‖² ≤ c(k) · area (F '' ball z₀ 1) / log (1/‖z - z₀‖)`  for `‖z - z₀‖ ≤ 1/4`

with an elementary four-step chaining along the segment `[z, z']`: split the segment into
four equal pieces of length `r/4 ≤ 1/4` (`r = ‖z - z'‖ ≤ 1`) and apply the estimate to each
piece with the unit ball centred at the left endpoint.  The resulting modulus is explicit,
`ω r = 4 √(c(k) A / log (4/r))` for `0 < r ≤ 1`.

-/

noncomputable section

open MeasureTheory Metric Filter Topology Complex Function
open scoped Topology ENNReal

namespace Work.MRMT.Found

/-- The uniform modulus of continuity produced by the Courant–Lebesgue estimate with
constant `C = c(k)·A`.  For `0 < r ≤ 1` it equals `4 √(C / log (4/r))`; on `r ≤ 0` it is
declared to be `0` (only pairs at distance `≤ 1` are ever tested against it). -/
def fwModulus (C : ℝ) : ℝ → ℝ :=
  fun r => if r ≤ 0 then 0 else 4 * Real.sqrt (C / Real.log (4 / min r 1))

lemma fwModulus_of_nonpos {C r : ℝ} (hr : r ≤ 0) : fwModulus C r = 0 := by
  simp [fwModulus, hr]

lemma fwModulus_of_pos_le_one {C : ℝ} {r : ℝ} (hr0 : 0 < r) (hr1 : r ≤ 1) :
    fwModulus C r = 4 * Real.sqrt (C / Real.log (4 / r)) := by
  rw [fwModulus]
  simp only [not_le.mpr hr0, ↓reduceIte, min_eq_left hr1]

/-- `fwModulus C r → 0` as `r → 0⁺` (for every `C`; the hypothesis `0 ≤ C` is the
geometrically meaningful one). -/
lemma fwModulus_tendsto (C : ℝ) :
    Filter.Tendsto (fwModulus C) (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
  have hg : Filter.Tendsto (fun r : ℝ => 4 * Real.sqrt (C / Real.log (4 / r)))
      (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
    have h1 : Filter.Tendsto (fun r : ℝ => r⁻¹)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) Filter.atTop := tendsto_inv_nhdsGT_zero
    have h2 : Filter.Tendsto (fun r : ℝ => 4 * r⁻¹)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) Filter.atTop :=
      h1.const_mul_atTop (by norm_num)
    have h3 : Filter.Tendsto (fun r : ℝ => 4 / r)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) Filter.atTop := by
      simpa [div_eq_mul_inv] using h2
    have h4 : Filter.Tendsto (fun r : ℝ => Real.log (4 / r))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) Filter.atTop :=
      Real.tendsto_log_atTop.comp h3
    have h5 : Filter.Tendsto (fun r : ℝ => (Real.log (4 / r))⁻¹)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := h4.inv_tendsto_atTop
    have h6 : Filter.Tendsto (fun r : ℝ => C * (Real.log (4 / r))⁻¹)
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
      simpa using h5.const_mul C
    have h7 : Filter.Tendsto (fun r : ℝ => Real.sqrt (C * (Real.log (4 / r))⁻¹))
        (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
      simpa using h6.sqrt
    simpa [div_eq_mul_inv] using h7.const_mul 4
  refine Filter.Tendsto.congr' ?_ hg
  filter_upwards [self_mem_nhdsWithin,
    nhdsWithin_le_nhds (eventually_lt_nhds (show (0 : ℝ) < 1 by norm_num))]
    with r hr0 hr1
  exact (fwModulus_of_pos_le_one (Set.mem_Ioi.mp hr0) hr1.le).symm

/-- **Four-step chaining.**  If `F : ℂ → ℂ` obeys the Courant–Lebesgue bound
`‖F z - F z₀‖² ≤ C / log (1/‖z - z₀‖)` on the scale `1/4`, then for all `z, z'` with
`‖z - z'‖ ≤ 1`,

`‖F z - F z'‖ ≤ fwModulus C ‖z - z'‖`. -/
lemma norm_sub_le_fwModulus {C : ℝ} (hC : 0 ≤ C) {F : ℂ → ℂ}
    (hb : ∀ z₀ z : ℂ, 0 < ‖z - z₀‖ → ‖z - z₀‖ ≤ 1 / 4 →
      ‖F z - F z₀‖ ^ 2 ≤ C / Real.log (1 / ‖z - z₀‖))
    {z z' : ℂ} (hr : ‖z - z'‖ ≤ 1) :
    ‖F z - F z'‖ ≤ fwModulus C ‖z - z'‖ := by
  set r : ℝ := ‖z - z'‖ with hrdef
  by_cases hr0 : r = 0
  · have hzz : z = z' := by
      have h0 : ‖z - z'‖ = 0 := by rw [← hrdef]; exact hr0
      exact sub_eq_zero.mp (norm_eq_zero.mp h0)
    subst hzz
    rw [sub_self, norm_zero, fwModulus_of_nonpos (le_of_eq hr0)]
  · have hrnneg : 0 ≤ r := by rw [hrdef]; exact norm_nonneg _
    have hrpos : 0 < r := lt_of_le_of_ne hrnneg (Ne.symm hr0)
    have hr1 : r ≤ 1 := by rw [hrdef]; exact hr
    set p : ℕ → ℂ := fun k => z + ((k : ℝ) / 4) * (z' - z) with hp
    have hp0 : p 0 = z := by simp [hp]
    have hp4 : p 4 = z' := by simp only [hp]; push_cast; norm_num
    have hdist : ∀ k : ℕ, ‖p (k + 1) - p k‖ = r / 4 := by
      intro k
      have h1 : p (k + 1) - p k = ((1 / 4 : ℝ) : ℂ) * (z' - z) := by
        simp only [hp]; push_cast; ring
      rw [h1, norm_mul, Complex.norm_real, Real.norm_of_nonneg (by norm_num : (0:ℝ) ≤ 1/4),
        hrdef, norm_sub_rev]
      ring
    have hlogpos : 0 < Real.log (4 / r) := by
      apply Real.log_pos
      rw [one_lt_div hrpos]
      linarith
    have hterm : ∀ i ∈ Finset.range 4,
        ‖F (p (i + 1)) - F (p i)‖ ≤ Real.sqrt (C / Real.log (4 / r)) := by
      intro i _
      have hd0 : 0 < ‖p (i + 1) - p i‖ := by rw [hdist i]; linarith
      have hd1 : ‖p (i + 1) - p i‖ ≤ 1 / 4 := by rw [hdist i]; linarith
      have hb' := hb (p i) (p (i + 1)) hd0 hd1
      have hlogeq : Real.log (1 / ‖p (i + 1) - p i‖) = Real.log (4 / r) := by
        rw [hdist i, one_div_div]
      rw [hlogeq] at hb'
      exact (Real.le_sqrt (norm_nonneg _) (div_nonneg hC hlogpos.le)).mpr hb'
    calc ‖F z - F z'‖
        = ‖∑ i ∈ Finset.range 4, (F (p (i + 1)) - F (p i))‖ := by
          rw [Finset.sum_range_sub (fun i => F (p i)) 4, hp0, hp4]
          exact norm_sub_rev (F z) (F z')
      _ ≤ ∑ i ∈ Finset.range 4, ‖F (p (i + 1)) - F (p i)‖ := norm_sum_le _ _
      _ ≤ ∑ i ∈ Finset.range 4, Real.sqrt (C / Real.log (4 / r)) := Finset.sum_le_sum hterm
      _ = 4 * Real.sqrt (C / Real.log (4 / r)) := by
          rw [Finset.sum_const, Finset.card_range]; simp
      _ = fwModulus C r := by rw [fwModulus_of_pos_le_one hrpos hr1]

theorem fw_exists_uniform_modulus {F : ℕ → ℂ → ℂ} {k A : ℝ} (hk0 : 0 ≤ k) (hk1 : k < 1)
    (hA : 0 ≤ A)
    (hF : ∀ n, ContDiff ℝ 1 (F n)) (hinj : ∀ n, Function.Injective (F n))
    (hdil : ∀ n z, ‖Work.MRMT.dzbar (F n) z‖ ≤ k * ‖Work.MRMT.dz (F n) z‖)
    (hvol : ∀ n : ℕ, ∀ z₀ : ℂ,
      (MeasureTheory.volume (F n '' Metric.ball z₀ (1 : ℝ))).toReal ≤ A) :
    ∃ ω : ℝ → ℝ, Filter.Tendsto ω (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) ∧
      ∀ n z z', ‖z - z'‖ ≤ 1 → ‖F n z - F n z'‖ ≤ ω ‖z - z'‖ := by
  obtain ⟨c, hc, hCL⟩ := courantLebesgue_uniform k hk0 hk1
  have hcA : 0 ≤ c * A := mul_nonneg hc.le hA
  refine ⟨fwModulus (c * A), fwModulus_tendsto (c * A), ?_⟩
  intro n z z' hzz
  refine norm_sub_le_fwModulus hcA ?_ hzz
  intro z₀ z₁ hd0 hd1
  have hcl := hCL (hF n) (hinj n) (hdil n) z₀ z₁ hd1
  have hlogpos : 0 < Real.log (1 / ‖z₁ - z₀‖) := by
    apply Real.log_pos
    rw [one_lt_div hd0]
    linarith
  have hmul : c * (MeasureTheory.volume (F n '' Metric.ball z₀ (1 : ℝ))).toReal ≤ c * A :=
    mul_le_mul_of_nonneg_left (hvol n z₀) hc.le
  exact hcl.trans (div_le_div_of_nonneg_right hmul hlogpos.le)

end Work.MRMT.Found
