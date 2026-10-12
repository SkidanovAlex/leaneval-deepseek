import Mathlib.Tactic.Have
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

set_option linter.style.haveILetI false
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.unusedVariables false

/-! ## Auxiliary facts about the autocorrelation `bsAc`

These are used to justify the Fubini exchange in `bsCross_swap`: the autocorrelation
`bsAc ψ d = ∫_x ψ x · ψ(x+d)` of a continuous compactly supported `ψ` is continuous, and it
is dominated by `C²·|closedBall 0 R|` whenever `|ψ| ≤ C` and `ψ` vanishes outside the ball of
radius `R`. -/

/-- `|χ|` is integrable (χ is continuous with compact support). -/
private lemma integrable_abs_chi : Integrable (fun z : ℝ³ => |chi z|) :=
  chi_continuous.abs.integrable_of_hasCompactSupport chi_hasCompactSupport.abs

/-- **The autocorrelation of a continuous compactly supported function is continuous.**

`bsAc ψ d = ∫_x ψ x · ψ(x+d)`; the integrand is dominated by `C^2 · 1_{closedBall 0 R}`
(with `|ψ| ≤ C` and `ψ = 0` outside the ball of radius `R`), which is integrable, and is
continuous in `d` for every `x`; dominated convergence gives the result. -/
private lemma continuous_bsAc {ψ : ℝ³ → ℝ} (hψ : Continuous ψ) (hcs : HasCompactSupport ψ) :
    Continuous (fun d : ℝ³ => bsAc ψ d) := by
  obtain ⟨C, hC⟩ := hcs.exists_bound_of_continuous hψ
  have hC0 : 0 ≤ C := le_trans (norm_nonneg (ψ 0)) (hC 0)
  obtain ⟨R, hR0, hR⟩ := exists_radius_eq_zero_of_hasCompactSupport hcs
  have hbound_int : Integrable (fun x : ℝ³ =>
      C ^ 2 * (Metric.closedBall (0 : ℝ³) R).indicator (fun _ => (1 : ℝ)) x) := by
    have h1 : Integrable ((Metric.closedBall (0 : ℝ³) R).indicator (fun _ : ℝ³ => (1 : ℝ))) := by
      rw [integrable_indicator_iff measurableSet_closedBall]
      exact integrableOn_const (isCompact_closedBall (0 : ℝ³) R).measure_lt_top.ne (by simp)
    simpa using h1.const_mul (C ^ 2)
  change Continuous (fun d : ℝ³ => ∫ x : ℝ³, ψ x * ψ (x + d))
  refine MeasureTheory.continuous_of_dominated
    (F := fun (d : ℝ³) (x : ℝ³) => ψ x * ψ (x + d))
    (bound := fun x : ℝ³ =>
      C ^ 2 * (Metric.closedBall (0 : ℝ³) R).indicator (fun _ => (1 : ℝ)) x)
    ?_ ?_ hbound_int ?_
  · intro d
    exact ((by fun_prop : Continuous (fun x : ℝ³ => ψ x * ψ (x + d)))).aestronglyMeasurable
  · intro d
    refine Filter.Eventually.of_forall (fun x => ?_)
    by_cases hx : x ∈ Metric.closedBall (0 : ℝ³) R
    · rw [Set.indicator_of_mem hx, mul_one]
      calc ‖ψ x * ψ (x + d)‖ = |ψ x| * |ψ (x + d)| := by
            rw [Real.norm_eq_abs, abs_mul]
        _ ≤ C * C := mul_le_mul (hC x) (hC (x + d)) (abs_nonneg _) hC0
        _ = C ^ 2 := by ring
    · rw [Set.indicator_of_notMem hx, mul_zero]
      have hx' : R < ‖x‖ := by
        rw [Metric.mem_closedBall, dist_eq_norm, sub_zero, not_le] at hx
        exact hx
      rw [hR x (le_of_lt hx'), zero_mul, norm_zero]
  · refine Filter.Eventually.of_forall (fun x => ?_)
    exact continuous_const.mul (hψ.comp (continuous_const.add continuous_id))

/-! ## The two substitutions -/

/-- **First substitution** `x = ℓ(u+s)`: for arbitrary `ψ`,
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

/-- **The `u`-substitution for the cross integrand** (with the `(p,v)`-factor `bsLf` constant
in `u` and in `x`). -/
private lemma bsCross_u_subst {ℓ : ℝ} (hℓ : 0 < ℓ) (F : ℝ → ℝ) {ψ : ℝ³ → ℝ}
    (p v s : ℝ³) :
    (∫ u : ℝ³, bsLf ℓ F p v * ψ (ℓ • (v + u)) * ψ (ℓ • (u + s)))
      = (ℓ ^ 3)⁻¹ * ∫ x : ℝ³, bsLf ℓ F p v * (ψ (x + ℓ • (v - s)) * ψ x) := by
  rw [show (∫ u : ℝ³, bsLf ℓ F p v * ψ (ℓ • (v + u)) * ψ (ℓ • (u + s)))
      = bsLf ℓ F p v * (∫ u : ℝ³, ψ (ℓ • (v + u)) * ψ (ℓ • (u + s))) from by
    rw [← integral_const_mul (bsLf ℓ F p v) (fun u : ℝ³ => ψ (ℓ • (v + u)) * ψ (ℓ • (u + s)))]
    apply integral_congr_ae
    filter_upwards with u
    ring]
  rw [integral_psi_core hℓ ψ v s,
    integral_const_mul (bsLf ℓ F p v) (fun x : ℝ³ => ψ (x + ℓ • (v - s)) * ψ x)]
  ring

/-- **The `v`-substitution for the cross integrand** `d = ℓ(v−s)`: writing the inner
`x`-integral as `bsAc ψ (ℓ(v−s))`, the change of variables `v = s + ℓ⁻¹d` turns the `v`-integral
into `(ℓ³)⁻¹ ∫_d bsLf p (s + ℓ⁻¹d)·bsAc ψ d`. -/
private lemma bsCross_v_subst {ℓ : ℝ} (hℓ : 0 < ℓ) (F : ℝ → ℝ) {ψ : ℝ³ → ℝ}
    (p s : ℝ³) :
    (∫ v : ℝ³, bsLf ℓ F p v * (∫ x : ℝ³, ψ (x + ℓ • (v - s)) * ψ x))
      = (ℓ ^ 3)⁻¹ * ∫ d : ℝ³, bsLf ℓ F p (s + ℓ⁻¹ • d) * bsAc ψ d := by
  have hcancel : ∀ y : ℝ³, ℓ⁻¹ • (ℓ • y) = y := fun y => inv_smul_smul₀ (ne_of_gt hℓ) y
  have hinner : ∀ d : ℝ³, (∫ x : ℝ³, ψ (x + ℓ • d) * ψ x) = bsAc ψ (ℓ • d) := by
    intro d
    rw [bsAc]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    ring
  have htrans : (∫ v : ℝ³, bsLf ℓ F p v * (∫ x : ℝ³, ψ (x + ℓ • (v - s)) * ψ x))
      = ∫ w : ℝ³, bsLf ℓ F p (w + s) * (∫ x : ℝ³, ψ (x + ℓ • w) * ψ x) := by
    rw [← integral_add_right_eq_self (μ := (volume : Measure ℝ³))
      (f := fun v : ℝ³ => bsLf ℓ F p v * (∫ x : ℝ³, ψ (x + ℓ • (v - s)) * ψ x)) s]
    apply integral_congr_ae
    filter_upwards with w
    have hw : w + s - s = w := by abel
    rw [hw]
  rw [htrans, show (∫ w : ℝ³, bsLf ℓ F p (w + s) * (∫ x : ℝ³, ψ (x + ℓ • w) * ψ x))
      = ∫ w : ℝ³, bsLf ℓ F p (w + s) * bsAc ψ (ℓ • w) from by
    apply integral_congr_ae
    filter_upwards with w
    rw [hinner w]]
  rw [← Submission.BoseGases.integral_comp_smul_left
    (g := fun d : ℝ³ => bsLf ℓ F p (s + ℓ⁻¹ • d) * bsAc ψ d) hℓ]
  apply integral_congr_ae
  filter_upwards with y
  rw [hcancel]
  rw [add_comm]

/-! ## The Fubini exchanges -/

/-- The `(v,s)`-integrand `bsLf ℓ F p v · bsAc ψ (ℓ(v−s))` is continuous. -/
private lemma continuous_bsLf (ℓ : ℝ) (F : ℝ → ℝ) (p : ℝ³) :
    Continuous (fun v : ℝ³ => bsLf ℓ F p v) := by
  have hχ : Continuous (fun v : ℝ³ => chi v) := chi_continuous
  have hcos : Continuous (fun v : ℝ³ => Real.cos (inner ℝ (ℓ • p) v)) :=
    Real.continuous_cos.comp (continuous_const.inner continuous_id)
  unfold bsLf
  exact ((continuous_const.mul continuous_const).mul hχ).mul hcos

/-- **Fubini `(v,s)`-exchange.**  After the inner `x`-integral is recognised as
`bsLf ℓ F p v · bsAc ψ (ℓ(v−s))` (via `hpt`), the joint integrand is continuous (by
`continuous_bsAc`) and dominated by an integrable function of `v` alone
(`abs_bsLf_le` + `abs_bsAc_le`), so `MeasureTheory.integral_integral_swap` interchanges the
`v`- and `s`-integrations.  This is the only genuinely measure-theoretic step of the
computation. -/
private lemma bsCross_swap {ℓ : ℝ} (hℓ : 0 < ℓ) (F : ℝ → ℝ) {ψ : ℝ³ → ℝ}
    (hψ : ContDiff ℝ (⊤ : ENat) ψ) (hcs : HasCompactSupport ψ) (p : ℝ³) :
    (∫ v : ℝ³, ∫ s in acube 1, ∫ x : ℝ³,
        bsLf ℓ F p v * (ψ (x + ℓ • (v - s)) * ψ x))
      = ∫ s in acube 1, ∫ v : ℝ³, ∫ x : ℝ³,
        bsLf ℓ F p v * (ψ (x + ℓ • (v - s)) * ψ x) := by
  have hcont : Continuous (fun d : ℝ³ => bsAc ψ d) := continuous_bsAc hψ.continuous hcs
  have hpt : ∀ v s : ℝ³, (∫ x : ℝ³, bsLf ℓ F p v * (ψ (x + ℓ • (v - s)) * ψ x))
      = bsLf ℓ F p v * bsAc ψ (ℓ • (v - s)) := by
    intro v s
    rw [integral_const_mul (bsLf ℓ F p v) (fun x : ℝ³ => ψ (x + ℓ • (v - s)) * ψ x)]
    congr 1
    rw [bsAc]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
    ring
  obtain ⟨Cψ, hCψ0, hCψ⟩ := exists_bound_of_contDiff_hasCompactSupport hψ hcs
  obtain ⟨R, hR0, hR⟩ := exists_radius_eq_zero_of_hasCompactSupport hcs
  haveI hν : IsFiniteMeasure ((volume : Measure ℝ³).restrict (acube 1)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact acube_lt_top 1 (by norm_num)⟩
  have hdom : Integrable (fun w : ℝ³ × ℝ³ =>
      (((∫ z : ℝ³, |chi z|) * |F ‖p‖|)
        * (Cψ ^ 2 * (volume : Measure ℝ³).real (Metric.closedBall 0 R))) * |chi w.1|)
      ((volume : Measure ℝ³).prod ((volume : Measure ℝ³).restrict (acube 1))) :=
    (integrable_abs_chi.comp_fst ((volume : Measure ℝ³).restrict (acube 1))).const_mul _
  have hInt : Integrable (Function.uncurry (fun (v : ℝ³) (s : ℝ³) =>
      bsLf ℓ F p v * bsAc ψ (ℓ • (v - s))))
      ((volume : Measure ℝ³).prod ((volume : Measure ℝ³).restrict (acube 1))) := by
    refine Integrable.mono' hdom ?_ ?_
    · exact (((continuous_bsLf ℓ F p).comp continuous_fst).mul
        (hcont.comp (by fun_prop))).aestronglyMeasurable
    · refine Filter.Eventually.of_forall (fun w => ?_)
      show ‖bsLf ℓ F p w.1 * bsAc ψ (ℓ • (w.1 - w.2))‖ ≤
        (((∫ z : ℝ³, |chi z|) * |F ‖p‖|)
          * (Cψ ^ 2 * (volume : Measure ℝ³).real (Metric.closedBall 0 R))) * |chi w.1|
      rw [Real.norm_eq_abs, abs_mul]
      have h1 : |bsLf ℓ F p w.1| ≤ (∫ z : ℝ³, |chi z|) * |F ‖p‖| * |chi w.1| :=
        abs_bsLf_le ℓ F p w.1
      have h2 : |bsAc ψ (ℓ • (w.1 - w.2))| ≤
          Cψ ^ 2 * (volume : Measure ℝ³).real (Metric.closedBall 0 R) := abs_bsAc_le hCψ hR _
      calc |bsLf ℓ F p w.1| * |bsAc ψ (ℓ • (w.1 - w.2))|
          ≤ (((∫ z : ℝ³, |chi z|) * |F ‖p‖| * |chi w.1|) *
              (Cψ ^ 2 * (volume : Measure ℝ³).real (Metric.closedBall 0 R))) :=
            mul_le_mul h1 h2 (abs_nonneg _) (by positivity)
        _ = (((∫ z : ℝ³, |chi z|) * |F ‖p‖|)
              * (Cψ ^ 2 * (volume : Measure ℝ³).real (Metric.closedBall 0 R))) * |chi w.1| := by
            ring
  calc (∫ v : ℝ³, ∫ s in acube 1, ∫ x : ℝ³,
        bsLf ℓ F p v * (ψ (x + ℓ • (v - s)) * ψ x))
      = ∫ v : ℝ³, ∫ s in acube 1, bsLf ℓ F p v * bsAc ψ (ℓ • (v - s)) := by
        apply integral_congr_ae
        filter_upwards with v
        apply integral_congr_ae
        filter_upwards with s
        exact hpt v s
    _ = ∫ s in acube 1, ∫ v : ℝ³, bsLf ℓ F p v * bsAc ψ (ℓ • (v - s)) :=
        integral_integral_swap hInt
    _ = ∫ s in acube 1, ∫ v : ℝ³, ∫ x : ℝ³,
        bsLf ℓ F p v * (ψ (x + ℓ • (v - s)) * ψ x) := by
        apply integral_congr_ae
        filter_upwards with s
        apply integral_congr_ae
        filter_upwards with v
        exact (hpt v s).symm

/-- The two substitutions `x = ℓ(u+s)` and `d = ℓ(v−s)` in the four-fold integral of the cross
term; the constant is `(ℓ^6)⁻¹ = (ℓ³)⁻¹·(ℓ³)⁻¹`.

Intended proof (with `K v x s := bsLf ℓ F p v * ψ(x + ℓ•(v−s)) * ψ x` and `p` outermost, so only
pointwise-in-`p` facts are needed):

1. innermost `u`-integral, fixed `(p,v,s)`: the substitution `x = ℓ(u+s)` (`u = ℓ⁻¹x − s`) via
   `MeasureTheory.integral_add_right_eq_self` (translation) and then
   `Submission.BoseGases.integral_comp_smul_left` (`∫ y, G (ℓ•y) = (ℓ³)⁻¹ ∫ G`), using the
   pointwise identity `ℓ(v + (ℓ⁻¹x − s)) = x + ℓ(v−s)` (`module`), so
   `∫_u ψ(ℓ(v+u)) ψ(ℓ(u+s)) du = (ℓ³)⁻¹ ∫_x ψ(x+ℓ(v−s)) ψ x dx`, and the four-fold integral
   becomes `(ℓ³)⁻¹ ∫_p ∫_v ∫_{s∈acube1} ∫_x K v x s`;
2. **Fubini `(v,s)`-interchange** (`s` is bound inside the `v`-integral; the set integral
   `∫ s in acube 1, ·` *is* the integral against `volume.restrict (acube 1)`):
   `MeasureTheory.integral_integral_swap` with measures `volume` and
   `(volume : Measure ℝ³).restrict (acube 1)` and the joint integrand `(v,s) ↦ ∫_x K v x s`.
   Integrability: for fixed `p`, `|∫_x K v x s| ≤ Cψ²·|ball 0 R|·|bsLf ℓ F p v|` and
   `|bsLf ℓ F p v| ≤ (∫|χ|)·|F ‖p‖|·|χ v|` (`Work.OneBodyKin.abs_bsLf_le`) with `χ` compactly
   supported/integrable; use `Integrable.mul_prod` + `Integrable.mono'`;
3. `v`-substitution `d = ℓ(v−s)` (`v = s + ℓ⁻¹•d`, `dv = ℓ⁻³dd`), again translation +
   `integral_comp_smul_left`: `∫_v bsLf p v ψ(x+ℓ(v−s)) dv = (ℓ³)⁻¹ ∫_d bsLf p (s+ℓ⁻¹•d) ψ(x+d) dd`;
4. pull the `x`-integral out: `∫_x bsLf p (s+ℓ⁻¹•d) ψ(x+d) ψ x dx
   = bsLf p (s+ℓ⁻¹•d) · bsAc ψ d` by `MeasureTheory.integral_mul_const`, where
   `bsAc ψ d = ∫_x ψ x ψ(x+d)` (`OneBodyKin/CrossDefs`).

No hypothesis on `F` is needed: the `p`-integral stays outermost on both sides, so only the
pointwise-in-`p` identity is used. -/
theorem bsCross_subst {ℓ : ℝ} (hℓ : 0 < ℓ) {F : ℝ → ℝ}
    {ψ : EuclideanSpace ℝ (Fin 3) → ℝ} (hψ : ContDiff ℝ (⊤ : ENat) ψ)
    (hcs : HasCompactSupport ψ) :
    (∫ p : EuclideanSpace ℝ (Fin 3), ∫ v : EuclideanSpace ℝ (Fin 3),
        ∫ s in Submission.BoseGases.acube 1, ∫ u : EuclideanSpace ℝ (Fin 3),
          Work.OneBodyKin.bsLf ℓ F p v * ψ (ℓ • (v + u)) * ψ (ℓ • (u + s)))
      = (ℓ ^ 6)⁻¹ * ∫ p : EuclideanSpace ℝ (Fin 3),
          ∫ s in Submission.BoseGases.acube 1, ∫ d : EuclideanSpace ℝ (Fin 3),
            Work.OneBodyKin.bsLf ℓ F p (s + ℓ⁻¹ • d) * Work.OneBodyKin.bsAc ψ d := by
  have key : ∀ p : ℝ³,
      (∫ v : ℝ³, ∫ s in acube 1, ∫ u : ℝ³,
          bsLf ℓ F p v * ψ (ℓ • (v + u)) * ψ (ℓ • (u + s)))
        = (ℓ ^ 6)⁻¹ * (∫ s in acube 1, ∫ d : ℝ³,
            bsLf ℓ F p (s + ℓ⁻¹ • d) * bsAc ψ d) := by
    intro p
    calc (∫ v : ℝ³, ∫ s in acube 1, ∫ u : ℝ³,
            bsLf ℓ F p v * ψ (ℓ • (v + u)) * ψ (ℓ • (u + s)))
        = ∫ v : ℝ³, ∫ s in acube 1,
            (ℓ ^ 3)⁻¹ * ∫ x : ℝ³, bsLf ℓ F p v * (ψ (x + ℓ • (v - s)) * ψ x) := by
          apply integral_congr_ae
          filter_upwards with v
          apply integral_congr_ae
          filter_upwards with s
          exact bsCross_u_subst hℓ F p v s
      _ = (ℓ ^ 3)⁻¹ * ∫ v : ℝ³, ∫ s in acube 1, ∫ x : ℝ³,
            bsLf ℓ F p v * (ψ (x + ℓ • (v - s)) * ψ x) := by
          rw [show (∫ v : ℝ³, ∫ s in acube 1,
                ((ℓ ^ 3)⁻¹ * ∫ x : ℝ³, bsLf ℓ F p v * (ψ (x + ℓ • (v - s)) * ψ x)))
              = ∫ v : ℝ³, (ℓ ^ 3)⁻¹ * (∫ s in acube 1, ∫ x : ℝ³,
                  bsLf ℓ F p v * (ψ (x + ℓ • (v - s)) * ψ x)) from by
              apply integral_congr_ae
              filter_upwards with v
              rw [integral_const_mul]]
          rw [integral_const_mul]
      _ = (ℓ ^ 3)⁻¹ * ∫ s in acube 1, ∫ v : ℝ³, ∫ x : ℝ³,
            bsLf ℓ F p v * (ψ (x + ℓ • (v - s)) * ψ x) := by
          congr 1
          exact bsCross_swap hℓ F hψ hcs p
      _ = (ℓ ^ 3)⁻¹ * ∫ s in acube 1, ∫ v : ℝ³,
            bsLf ℓ F p v * (∫ x : ℝ³, ψ (x + ℓ • (v - s)) * ψ x) := by
          congr 1
          apply integral_congr_ae
          filter_upwards with s
          apply integral_congr_ae
          filter_upwards with v
          rw [integral_const_mul]
      _ = (ℓ ^ 3)⁻¹ * ∫ s in acube 1,
            (ℓ ^ 3)⁻¹ * ∫ d : ℝ³, bsLf ℓ F p (s + ℓ⁻¹ • d) * bsAc ψ d := by
          congr 1
          apply integral_congr_ae
          filter_upwards with s
          exact bsCross_v_subst hℓ F p s
      _ = (ℓ ^ 6)⁻¹ * ∫ s in acube 1, ∫ d : ℝ³,
            bsLf ℓ F p (s + ℓ⁻¹ • d) * bsAc ψ d := by
          rw [integral_const_mul]
          rw [show (ℓ ^ 6)⁻¹ = (ℓ ^ 3)⁻¹ * (ℓ ^ 3)⁻¹ from by
            rw [show (6 : ℕ) = 3 + 3 from rfl, pow_add, mul_inv]]
          ring
  calc (∫ p : ℝ³, ∫ v : ℝ³, ∫ s in acube 1, ∫ u : ℝ³,
        bsLf ℓ F p v * ψ (ℓ • (v + u)) * ψ (ℓ • (u + s)))
      = ∫ p : ℝ³, (ℓ ^ 6)⁻¹ * (∫ s in acube 1, ∫ d : ℝ³,
          bsLf ℓ F p (s + ℓ⁻¹ • d) * bsAc ψ d) := by
          apply integral_congr_ae
          filter_upwards with p
          exact key p
    _ = (ℓ ^ 6)⁻¹ * ∫ p : ℝ³, ∫ s in acube 1, ∫ d : ℝ³,
          bsLf ℓ F p (s + ℓ⁻¹ • d) * bsAc ψ d := by
          rw [integral_const_mul]

end Work.OneBodyKin.Cross
