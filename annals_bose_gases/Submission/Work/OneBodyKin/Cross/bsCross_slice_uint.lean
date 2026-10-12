import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.OneBodyKin.CrossDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open MeasureTheory
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.OneBodyKin.Cross

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open Submission.BoseGases

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedVariables false

/-!
# `Work.OneBodyKin.Cross.bsCross_slice_uint`

The `(v,s)`-slice integrability of the cross-term integrand with the `u`-integration carried out
first and the momentum `p` frozen: for fixed `p`,

    `(v,s) ↦ ∫_u bsLf ℓ F p v · ψ(ℓ(v+u)) · ψ(ℓ(u+s))`

is integrable on `volume.prod (volume.restrict (acube 1))`.

The proof is pure domination, using the substitution `x = ℓ(u+s)` which identifies the `u`-integral
with the autocorrelation of `ψ`:

    `∫_u ψ(ℓ(v+u))·ψ(ℓ(u+s)) du = (ℓ³)⁻¹ ∫_x ψ(x + ℓ(v−s))·ψ x dx = (ℓ³)⁻¹ · bsAc ψ (ℓ(v−s))`,

and `|bsAc ψ d| ≤ Cψ² · |closedBall 0 R|` (`Work.OneBodyKin.abs_bsAc_le`).  Hence

    `|∫_u bsLf ℓ F p v · ψ(ℓ(v+u)) · ψ(ℓ(u+s))| ≤ |bsLf ℓ F p v| · (ℓ³)⁻¹ Cψ² |closedBall 0 R|`,

which is dominated by a constant times `|χ v|` via `Work.OneBodyKin.abs_bsLf_le`, an integrable
function on the product (the `s`-factor being the constant `1` on the finite measure
`volume.restrict (acube 1)`, `BoseGases.acube_lt_top`).  A.e. strong measurability comes from
`MeasureTheory.AEStronglyMeasurable.integral_prod_right'` applied to the (continuous) joint
integrand.  The hypotheses `0 < ℓ` and integrability of `p ↦ F ‖p‖` are not needed for this slice
(the second is unused; the first only through the substitution).
-/

/-- **Substitution `x = ℓ(u+s)`**: for arbitrary `ψ`,
`∫_u ψ(ℓ(v+u))·ψ(ℓ(u+s)) du = (ℓ³)⁻¹ ∫_x ψ(x + ℓ(v−s))·ψ x dx`. -/
private lemma integral_psi_core {ℓ : ℝ} (hℓ : 0 < ℓ) (ψ : ℝ³ → ℝ) (v s : ℝ³) :
    (∫ u : ℝ³, ψ (ℓ • (v + u)) * ψ (ℓ • (u + s)))
      = (ℓ ^ 3)⁻¹ * ∫ x : ℝ³, ψ (x + ℓ • (v - s)) * ψ x := by
  have hcancel : ∀ y : ℝ³, ℓ⁻¹ • (ℓ • y) = y := fun y => inv_smul_smul₀ (ne_of_gt hℓ) y
  have hcancel' : ∀ y : ℝ³, ℓ • (ℓ⁻¹ • y) = y := fun y => smul_inv_smul₀ (ne_of_gt hℓ) y
  have htrans : (∫ u : ℝ³, ψ (ℓ • (v + u)) * ψ (ℓ • (u + s)))
      = ∫ w : ℝ³, ψ (ℓ • (v + w - s)) * ψ (ℓ • w) := by
    have h := integral_add_right_eq_self (μ := (volume : Measure ℝ³))
      (f := fun w : ℝ³ => ψ (ℓ • (v + w - s)) * ψ (ℓ • w)) s
    rw [← h]
    apply integral_congr_ae
    filter_upwards with x
    have hx : v + (x + s) - s = v + x := by abel
    rw [hx]
  rw [htrans]
  have hg : (∫ x : ℝ³, ψ (x + ℓ • (v - s)) * ψ x)
      = ∫ x : ℝ³, (fun x : ℝ³ => ψ (ℓ • (v + ℓ⁻¹ • x - s)) * ψ x) x := by
    apply integral_congr_ae
    filter_upwards with x
    have hkey : ℓ • (v + ℓ⁻¹ • x - s) = x + ℓ • (v - s) := by
      rw [show v + ℓ⁻¹ • x - s = (v - s) + ℓ⁻¹ • x from by abel, smul_add, hcancel', add_comm]
    rw [hkey]
  rw [hg, ← Submission.BoseGases.integral_comp_smul_left
    (g := fun x : ℝ³ => ψ (ℓ • (v + ℓ⁻¹ • x - s)) * ψ x) hℓ]
  apply integral_congr_ae
  filter_upwards with y
  rw [hcancel]

/-- **The `u`-substitution with the `(p,v)`-factor frozen** (the factor `bsLf ℓ F p v` is constant
in `u` and `x`). -/
private lemma integral_bsLf_psi {ℓ : ℝ} (hℓ : 0 < ℓ) (F : ℝ → ℝ) {ψ : ℝ³ → ℝ}
    (p v s : ℝ³) :
    (∫ u : ℝ³, bsLf ℓ F p v * ψ (ℓ • (v + u)) * ψ (ℓ • (u + s)))
      = bsLf ℓ F p v * ((ℓ ^ 3)⁻¹ * ∫ x : ℝ³, ψ (x + ℓ • (v - s)) * ψ x) := by
  rw [show (∫ u : ℝ³, bsLf ℓ F p v * ψ (ℓ • (v + u)) * ψ (ℓ • (u + s)))
      = bsLf ℓ F p v * (∫ u : ℝ³, ψ (ℓ • (v + u)) * ψ (ℓ • (u + s))) from by
    rw [← integral_const_mul (bsLf ℓ F p v) (fun u : ℝ³ => ψ (ℓ • (v + u)) * ψ (ℓ • (u + s)))]
    apply integral_congr_ae
    filter_upwards with u
    ring]
  rw [integral_psi_core hℓ ψ v s]

lemma bsCross_slice_uint {ℓ : ℝ} (hℓ : 0 < ℓ) {F : ℝ → ℝ}
    (hFi : MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin 3) => F ‖p‖))
    {ψ : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hψ : ContDiff ℝ (⊤ : ENat) ψ) (hcs : HasCompactSupport ψ)
    (p : EuclideanSpace ℝ (Fin 3)) :
    MeasureTheory.Integrable
      (fun w : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
        ∫ u : EuclideanSpace ℝ (Fin 3),
          Work.OneBodyKin.bsLf ℓ F p w.1 * ψ (ℓ • (w.1 + u)) * ψ (ℓ • (u + w.2)))
      (MeasureTheory.volume.prod
        (MeasureTheory.volume.restrict (Submission.BoseGases.acube 1))) := by
  obtain ⟨Cψ, hCψ0, hCψ⟩ := exists_bound_of_contDiff_hasCompactSupport hψ hcs
  obtain ⟨R, hR0, hR⟩ := exists_radius_eq_zero_of_hasCompactSupport hcs
  set D : ℝ := (ℓ ^ 3)⁻¹ *
    (Cψ ^ 2 * (volume : Measure ℝ³).real (Metric.closedBall (0 : ℝ³) R)) with hD
  have hD0 : 0 ≤ D := by rw [hD]; positivity
  have hν : IsFiniteMeasure ((volume : Measure ℝ³).restrict (acube 1)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact acube_lt_top 1 (by norm_num)⟩
  have hχI : Integrable (fun z : ℝ³ => |chi z|) :=
    chi_continuous.abs.integrable_of_hasCompactSupport chi_hasCompactSupport.abs
  have hmaj : Integrable
      (fun w : ℝ³ × ℝ³ => (((∫ z : ℝ³, |chi z|) * |F ‖p‖|) * D) * |chi w.1|)
      ((volume : Measure ℝ³).prod ((volume : Measure ℝ³).restrict (acube 1))) :=
    (hχI.const_mul _).comp_fst _
  refine Integrable.mono' hmaj ?_ ?_
  · have hcont : Continuous (fun z : (ℝ³ × ℝ³) × ℝ³ =>
        bsLf ℓ F p z.1.1 * ψ (ℓ • (z.1.1 + z.2)) * ψ (ℓ • (z.2 + z.1.2))) := by
      unfold bsLf
      have h1 : Continuous (fun z : (ℝ³ × ℝ³) × ℝ³ => chi z.1.1) :=
        chi_continuous.comp (by fun_prop)
      have h2 : Continuous (fun z : (ℝ³ × ℝ³) × ℝ³ => Real.cos (inner ℝ (ℓ • p) z.1.1)) :=
        Real.continuous_cos.comp (continuous_const.inner (by fun_prop))
      have h3 : Continuous (fun z : (ℝ³ × ℝ³) × ℝ³ => ψ (ℓ • (z.1.1 + z.2))) :=
        hψ.continuous.comp (by fun_prop)
      have h4 : Continuous (fun z : (ℝ³ × ℝ³) × ℝ³ => ψ (ℓ • (z.2 + z.1.2))) :=
        hψ.continuous.comp (by fun_prop)
      exact ((((continuous_const.mul continuous_const).mul h1).mul h2).mul h3).mul h4
    exact hcont.aestronglyMeasurable.integral_prod_right'
  · refine Filter.Eventually.of_forall (fun w => ?_)
    rw [integral_bsLf_psi hℓ F p w.1 w.2]
    set Y : ℝ := ∫ x : ℝ³, ψ (x + ℓ • (w.1 - w.2)) * ψ x with hY
    have hAc : |Y| ≤ Cψ ^ 2 *
        (volume : Measure ℝ³).real (Metric.closedBall (0 : ℝ³) R) := by
      rw [hY]
      rw [show (∫ x : ℝ³, ψ (x + ℓ • (w.1 - w.2)) * ψ x)
          = bsAc ψ (ℓ • (w.1 - w.2)) from by
        rw [bsAc]
        apply integral_congr_ae
        filter_upwards with x
        ring]
      exact abs_bsAc_le hCψ hR _
    have hinv : 0 ≤ (ℓ ^ 3)⁻¹ := by positivity
    calc ‖bsLf ℓ F p w.1 * ((ℓ ^ 3)⁻¹ * Y)‖
        = |bsLf ℓ F p w.1| * ((ℓ ^ 3)⁻¹ * |Y|) := by
          rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hinv]
      _ ≤ |bsLf ℓ F p w.1| * ((ℓ ^ 3)⁻¹ *
            (Cψ ^ 2 * (volume : Measure ℝ³).real (Metric.closedBall (0 : ℝ³) R))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hAc hinv) (abs_nonneg _)
      _ = |bsLf ℓ F p w.1| * D := by rw [hD]
      _ ≤ (((∫ z : ℝ³, |chi z|) * |F ‖p‖|) * D) * |chi w.1| := by
          calc |bsLf ℓ F p w.1| * D
              ≤ ((∫ z : ℝ³, |chi z|) * |F ‖p‖| * |chi w.1|) * D :=
                mul_le_mul_of_nonneg_right (abs_bsLf_le ℓ F p w.1) hD0
            _ = (((∫ z : ℝ³, |chi z|) * |F ‖p‖|) * D) * |chi w.1| := by ring

end Work.OneBodyKin.Cross
