import Mathlib.Tactic.Have
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseRowsFS.LatRiemann.cellInvNormDev
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseRowsFS.LatRiemann.farCellDevLipschitz`

The first-order (`Φ`-difference) estimate on a **far** half-open cell of the lattice `h·ℤ³`:
if `2√3 h ≤ ‖latPt h m‖` (the cell is far from the origin: its centre is at least the
diagonal of a cell away from `0`), then for every function `Φ` satisfying the weighted
Lipschitz bound `|Φ p - Φ q| ≤ B‖p-q‖((1+‖p‖)⁻² + (1+‖q‖)⁻²)`,

    ‖∫_{hbox h m} (Φ p - Φ (latPt h m))/‖p‖²‖
      ≤ (5 h √3/2) B ∫_{hbox h m} 1/((1+‖p‖)²‖p‖²).

This is Step 3a of the route of `Submission/Work/BoseRowsFS/FINDING_lattice_riemann_core.md`.

The proof is pointwise.  On a far cell `p` lies within `h√3/2 ≤ ‖latPt h m‖/4` of the centre
`k := latPt h m`, so `‖p‖ ≤ (5/4)‖k‖` and hence `1 + ‖p‖ ≤ 2(1 + ‖k‖)`, i.e.
`(1+‖k‖)⁻² ≤ 4(1+‖p‖)⁻²`.  Therefore the Lipschitz bound gives

    |Φ p - Φ k| ≤ B (h√3/2) ((1+‖p‖)⁻² + (1+‖k‖)⁻²) ≤ (5 h √3/2) B (1+‖p‖)⁻²,

and dividing by `‖p‖²` (positive on the cell of a non-central lattice point) yields the
majorant, which is integrable on the cell because it is bounded there by `4/h²`.
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace Work.BoseRowsFS.LatRiemann

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-! ## 1. The geometry of a far cell -/

/-- On a far cell the point `p` is at most `5/4` times as far from the origin as the centre
`latPt h m`. -/
lemma farCell_norm_le_center {h : ℝ} (hh : 0 < h) {m : Fin 3 → ℤ}
    (hfar : 2 * Real.sqrt 3 * h ≤ ‖Work.BoseRowsFS.latPt h m‖) {p : ℝ³}
    (hp : p ∈ hbox h m) : ‖p‖ ≤ 5 / 4 * ‖Work.BoseRowsFS.latPt h m‖ := by
  have hdel : ‖p - Work.BoseRowsFS.latPt h m‖ ≤ h * Real.sqrt 3 / 2 :=
    norm_sub_latPt_le hh hp
  have hdel' : ‖p - Work.BoseRowsFS.latPt h m‖ ≤ ‖Work.BoseRowsFS.latPt h m‖ / 4 := by
    have h2 : h * Real.sqrt 3 / 2 = (2 * Real.sqrt 3 * h) / 4 := by ring
    rw [h2] at hdel
    linarith
  have htri : ‖p‖ ≤ ‖p - Work.BoseRowsFS.latPt h m‖ + ‖Work.BoseRowsFS.latPt h m‖ := by
    have hn := norm_add_le (p - Work.BoseRowsFS.latPt h m) (Work.BoseRowsFS.latPt h m)
    have he : p - Work.BoseRowsFS.latPt h m + Work.BoseRowsFS.latPt h m = p := by abel
    rwa [he] at hn
  linarith

/-- On a far cell the weight `(1+‖·‖)⁻²` at the centre is at most `4` times its value at
`p`. -/
lemma farCell_weight_le {h : ℝ} (hh : 0 < h) {m : Fin 3 → ℤ}
    (hfar : 2 * Real.sqrt 3 * h ≤ ‖Work.BoseRowsFS.latPt h m‖) {p : ℝ³}
    (hp : p ∈ hbox h m) :
    1 / (1 + ‖Work.BoseRowsFS.latPt h m‖) ^ 2 ≤ 4 / (1 + ‖p‖) ^ 2 := by
  have hple := farCell_norm_le_center hh hfar hp
  have hk0 : (0 : ℝ) ≤ ‖Work.BoseRowsFS.latPt h m‖ := norm_nonneg _
  have h2 : 1 + ‖p‖ ≤ 2 * (1 + ‖Work.BoseRowsFS.latPt h m‖) := by linarith
  have hs2 : (1 + ‖p‖) ^ 2 ≤ 4 * (1 + ‖Work.BoseRowsFS.latPt h m‖) ^ 2 := by
    have h3 : 0 ≤ 1 + ‖p‖ := by positivity
    have h4 : (2 * (1 + ‖Work.BoseRowsFS.latPt h m‖)) ^ 2
        = 4 * (1 + ‖Work.BoseRowsFS.latPt h m‖) ^ 2 := by ring
    have h5 := pow_le_pow_left₀ h3 h2 2
    rw [h4] at h5
    exact h5
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  simpa using hs2

/-! ## 2. Integrability of the majorant on a cell -/

/-- The majorant `p ↦ 1/((1+‖p‖)²‖p‖²)` is integrable on the cell of a non-central lattice
point: there `‖p‖ ≥ h/2`, so the function is bounded by `4/h²` on the (finite volume) cell. -/
lemma integrableOn_hbox_majorant {h : ℝ} (hh : 0 < h) {m : Fin 3 → ℤ} (hm : m ≠ 0) :
    IntegrableOn (fun p : ℝ³ => 1 / ((1 + ‖p‖) ^ 2 * ‖p‖ ^ 2)) (hbox h m) := by
  refine integrableOn_hbox_of_bound (f := fun p : ℝ³ => 1 / ((1 + ‖p‖) ^ 2 * ‖p‖ ^ 2))
    (C := 4 / h ^ 2) ?_ ?_
  · measurability
  · intro p hp
    have hhalf : h / 2 ≤ ‖p‖ := norm_ge_of_mem_hbox hm hh hp
    have hp0 : (0 : ℝ) < ‖p‖ := by linarith
    have hden : 0 < (1 + ‖p‖) ^ 2 * ‖p‖ ^ 2 := by positivity
    rw [abs_of_nonneg (by positivity)]
    rw [div_le_div_iff₀ hden (by positivity)]
    nlinarith [hp0, hh, hhalf, sq_nonneg ‖p‖, sq_nonneg (1 + ‖p‖), sq_nonneg (2 * ‖p‖ - h)]

/-! ## 3. The pointwise bound on a far cell -/

/-- Pointwise form of the far-cell estimate. -/
lemma farCell_dev_ptwise {h B : ℝ} (hh : 0 < h) (hB : 0 ≤ B)
    {Φ : ℝ³ → ℝ}
    (hlip : ∀ p q, |Φ p - Φ q|
      ≤ B * ‖p - q‖ * (1 / (1 + ‖p‖) ^ 2 + 1 / (1 + ‖q‖) ^ 2))
    {m : Fin 3 → ℤ} (hm : m ≠ 0) (hfar : 2 * Real.sqrt 3 * h ≤ ‖Work.BoseRowsFS.latPt h m‖)
    {p : ℝ³} (hp : p ∈ hbox h m) :
    ‖(Φ p - Φ (Work.BoseRowsFS.latPt h m)) / ‖p‖ ^ 2‖
      ≤ (5 * h * Real.sqrt 3 / 2) * B * (1 / ((1 + ‖p‖) ^ 2 * ‖p‖ ^ 2)) := by
  have hw := farCell_weight_le hh hfar hp
  have hdel : ‖p - Work.BoseRowsFS.latPt h m‖ ≤ h * Real.sqrt 3 / 2 := norm_sub_latPt_le hh hp
  have hsum : 1 / (1 + ‖p‖) ^ 2 + 1 / (1 + ‖Work.BoseRowsFS.latPt h m‖) ^ 2
      ≤ 5 / (1 + ‖p‖) ^ 2 := by
    have h1 : 1 / (1 + ‖p‖) ^ 2 + 1 / (1 + ‖Work.BoseRowsFS.latPt h m‖) ^ 2
        ≤ 1 / (1 + ‖p‖) ^ 2 + 4 / (1 + ‖p‖) ^ 2 := add_le_add (le_refl _) hw
    have h2 : 1 / (1 + ‖p‖) ^ 2 + 4 / (1 + ‖p‖) ^ 2 = 5 / (1 + ‖p‖) ^ 2 := by ring
    rw [h2] at h1
    exact h1
  have hBd : B * ‖p - Work.BoseRowsFS.latPt h m‖ ≤ B * (h * Real.sqrt 3 / 2) :=
    mul_le_mul_of_nonneg_left hdel hB
  have hΦ : |Φ p - Φ (Work.BoseRowsFS.latPt h m)|
      ≤ (5 * h * Real.sqrt 3 / 2) * B * (1 / (1 + ‖p‖) ^ 2) := by
    calc |Φ p - Φ (Work.BoseRowsFS.latPt h m)|
        ≤ B * ‖p - Work.BoseRowsFS.latPt h m‖
            * (1 / (1 + ‖p‖) ^ 2 + 1 / (1 + ‖Work.BoseRowsFS.latPt h m‖) ^ 2) :=
          hlip p (Work.BoseRowsFS.latPt h m)
      _ ≤ B * (h * Real.sqrt 3 / 2) * (5 / (1 + ‖p‖) ^ 2) :=
          mul_le_mul hBd hsum (by positivity) (by positivity)
      _ = (5 * h * Real.sqrt 3 / 2) * B * (1 / (1 + ‖p‖) ^ 2) := by ring
  have hpnorm : 0 < ‖p‖ := by
    have h1 : h / 2 ≤ ‖p‖ := norm_ge_of_mem_hbox hm hh hp
    linarith
  have hden : 0 < ‖p‖ ^ 2 := by positivity
  have h1 : ‖(Φ p - Φ (Work.BoseRowsFS.latPt h m)) / ‖p‖ ^ 2‖
      = |Φ p - Φ (Work.BoseRowsFS.latPt h m)| / ‖p‖ ^ 2 := by
    rw [norm_div, Real.norm_of_nonneg (le_of_lt hden), Real.norm_eq_abs]
  rw [h1]
  calc |Φ p - Φ (Work.BoseRowsFS.latPt h m)| / ‖p‖ ^ 2
      ≤ ((5 * h * Real.sqrt 3 / 2) * B * (1 / (1 + ‖p‖) ^ 2)) / ‖p‖ ^ 2 :=
        div_le_div_of_nonneg_right hΦ (le_of_lt hden)
    _ = (5 * h * Real.sqrt 3 / 2) * B * (1 / ((1 + ‖p‖) ^ 2 * ‖p‖ ^ 2)) := by
        rw [mul_div_assoc, div_div]

/-! ## 4. The far-cell estimate -/

theorem farCellDevLipschitz {h B : ℝ} (hh : 0 < h) (hB : 0 ≤ B)
    {Φ : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hlip : ∀ p q, |Φ p - Φ q| ≤ B * ‖p - q‖ * (1 / (1 + ‖p‖) ^ 2 + 1 / (1 + ‖q‖) ^ 2))
    {m : Fin 3 → ℤ} (hm : m ≠ 0) (hfar : 2 * Real.sqrt 3 * h ≤ ‖Work.BoseRowsFS.latPt h m‖) :
    ‖∫ p in Work.BoseRowsFS.LatRiemann.hbox h m,
        (Φ p - Φ (Work.BoseRowsFS.latPt h m)) / ‖p‖ ^ 2‖
      ≤ (5 * h * Real.sqrt 3 / 2) * B *
        ∫ p in Work.BoseRowsFS.LatRiemann.hbox h m, 1 / ((1 + ‖p‖) ^ 2 * ‖p‖ ^ 2) := by
  have hg : IntegrableOn (fun p : ℝ³ => 1 / ((1 + ‖p‖) ^ 2 * ‖p‖ ^ 2))
      (Work.BoseRowsFS.LatRiemann.hbox h m) := integrableOn_hbox_majorant hh hm
  have hg' : Integrable (fun p : ℝ³ =>
      (5 * h * Real.sqrt 3 / 2) * B * (1 / ((1 + ‖p‖) ^ 2 * ‖p‖ ^ 2)))
      (volume.restrict (Work.BoseRowsFS.LatRiemann.hbox h m)) :=
    hg.const_mul _
  have hmono : ∫ p in Work.BoseRowsFS.LatRiemann.hbox h m,
        ‖(Φ p - Φ (Work.BoseRowsFS.latPt h m)) / ‖p‖ ^ 2‖
      ≤ ∫ p in Work.BoseRowsFS.LatRiemann.hbox h m,
        (5 * h * Real.sqrt 3 / 2) * B * (1 / ((1 + ‖p‖) ^ 2 * ‖p‖ ^ 2)) := by
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun p => norm_nonneg _) hg' ?_
    filter_upwards [ae_restrict_mem (measurableSet_hbox h m)] with p hp
    exact farCell_dev_ptwise hh hB hlip hm hfar hp
  calc ‖∫ p in Work.BoseRowsFS.LatRiemann.hbox h m,
        (Φ p - Φ (Work.BoseRowsFS.latPt h m)) / ‖p‖ ^ 2‖
      ≤ ∫ p in Work.BoseRowsFS.LatRiemann.hbox h m,
          ‖(Φ p - Φ (Work.BoseRowsFS.latPt h m)) / ‖p‖ ^ 2‖ :=
        norm_integral_le_integral_norm _
    _ ≤ ∫ p in Work.BoseRowsFS.LatRiemann.hbox h m,
        (5 * h * Real.sqrt 3 / 2) * B * (1 / ((1 + ‖p‖) ^ 2 * ‖p‖ ^ 2)) := hmono
    _ = (5 * h * Real.sqrt 3 / 2) * B *
        ∫ p in Work.BoseRowsFS.LatRiemann.hbox h m, 1 / ((1 + ‖p‖) ^ 2 * ‖p‖ ^ 2) := by
        rw [integral_const_mul]

end Work.BoseRowsFS.LatRiemann
