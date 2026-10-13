/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/EpsApprox/HkNorm_Jeps_sub_le.lean`

**The `ℋ^k`-norm form of the mollifier-approximation estimate.**

For every admissible mollifier kernel `ρ` there is a constant `C` such that, for every
`α ∈ (0,1]`, every `k`, every `ε ∈ (0,1]` and every profile `f` which is `C^∞` on the open
quadrant with `HkMem α (k+1) f`,

  `‖J_ε f - f‖_{ℋ^k} ≤ C · ε · ‖f‖_{ℋ^{k+1}}`.

Since `HkNorm α k g = √(HkSq α k g)`, this is the norm form of the quantitative estimate
`HkSq α k (J_ε f - f) ≤ (C ε)² · HkSq α (k+1) f`, which is proved below (`HkSq_sub_est_aux`)
from the `DiffAux` chain of `Submission/Work/FTS/StrongEps/`:

* the pointwise bound `HkIntegrand_sub_le` (`DiffAux/HkIntegrandSub.lean`), obtained from the
  mean-value estimate `Jeps_sub_sq_le` of a single slot and the `D_z`/`D_θ` commutation
  `DzIter_sub_Jeps`, `mixed_sub_Jeps`;
* Tonelli and the product-measure bookkeeping (`DiffAux/MainSetup.lean`);
* the log-coordinate shift invariance (`DiffAux/lintegral_shift_le_gen.lean`) with the weight
  comparisons `HkSqAux.wdiv_shift_le`, `HkSqAux.Wt_shift_le`, `HkSqAux.logJac_shift_le`;
* the combinatorial bound `shadow_le` (`DiffAux/Shadow.lean`).

Everything in the cone of this file is fully proved (the axiom list of both theorems below
is exactly `propext`, `Classical.choice`, `Quot.sound`).
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.StrongEps.Basic
import Submission.Work.FTS.StrongEps.Kernel
import Submission.Work.FTS.StrongEps.Weights
import Submission.Work.FTS.StrongEps.HkSqAux.Defs
import Submission.Work.FTS.StrongEps.HkSqAux.LogCoord
import Submission.Work.FTS.StrongEps.HkSqAux.Chain
import Submission.Work.FTS.StrongEps.HkSqAux.wdiv_shift_le
import Submission.Work.FTS.StrongEps.HkSqAux.Wt_shift_le
import Submission.Work.FTS.StrongEps.HkSqAux.logJac_shift_le
import Submission.Work.FTS.StrongEps.DiffAux.Defs
import Submission.Work.FTS.StrongEps.DiffAux.Shadow
import Submission.Work.FTS.StrongEps.DiffAux.lintegral_shift_le_gen
import Submission.Work.FTS.StrongEps.DiffAux.MainSetup
import Submission.Work.FTS.StrongEps.DiffAux.ShadowPointwise
import Submission.Work.FTS.StrongEps.DiffAux.HkIntegrandSub
import Submission.Work.FTS.StrongEps.DiffAux.JepsSubPointwise
import Submission.Work.FTS.StrongEps.DiffAux.shiftPath_sub
import Submission.Work.FTS.StrongEps.DiffAux.Jeps_sub_eq_integral
import Submission.Work.FTS.StrongEps.DiffAux.DzIter_sub_Jeps
import Submission.Work.FTS.StrongEps.DiffAux.mixed_sub_Jeps
import Submission.Work.FTS.StrongEps.HkSqAux.sq_integral_Jker_mul_le
import Submission.Work.FTS.StrongEps.HkSq_Jeps_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.EpsApprox

open Work.FTS.StrongEps.DiffAux
open Work.FTS.StrongEps (Quad zShift thShift Jker Jeps IsMollKernel sin_two_pos
  Jker_continuous zShift_pos thShift_mem)

set_option maxHeartbeats 4000000

/-! ## The quantitative estimate in square (`HkSq`) form

This is the `ℝ≥0∞`-integration of the pointwise bound `HkIntegrand_sub_le`: after Tonelli,
the log-coordinate shift invariance replaces the shifted shadow by `e^{δ(|p₁|+|p₂|)}` times the
unshifted one, the kernel mass contributes `e^{2δε}`, and the combinatorial bound
`shadow_le` identifies the result with `2 · HkSq α (k+1) f`. -/
theorem HkSq_sub_est_aux {ρ : ℝ × ℝ → ℝ} {α : ℝ} (hα : α ∈ Set.Ioc 0 1) (hρ : IsMollKernel ρ)
    {k : ℕ} {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) {f : ℝ → ℝ → ℝ}
    (hf : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Work.FTS.EllipticEst.Q0)
    (hF : Work.Spaces.HkMem α (k + 1) f)
    {c δ : ℝ} (hc : 0 ≤ c) (hδ0 : 0 ≤ δ)
    (hWη : ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo 0 (π / 2) → ∀ q : ℝ × ℝ,
      wE z θ ≤ Real.exp (c * (|q.1| + |q.2|)) * wE (zShift z q.1) (thShift θ q.2))
    (hWγ : ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo 0 (π / 2) → ∀ q : ℝ × ℝ,
      Work.Spaces.Wt α z θ ≤ Real.exp (c * (|q.1| + |q.2|))
        * Work.Spaces.Wt α (zShift z q.1) (thShift θ q.2))
    (hJac : ∀ s ζ p₁ p₂ : ℝ, HkSqAux.logJac s ζ
      ≤ Real.exp (δ * (|p₁| + |p₂|)) * HkSqAux.logJac (s - p₁) (ζ - p₂)) :
    Work.Spaces.HkSq α k (fun z θ => Jeps ρ ε f z θ - f z θ)
      ≤ 4 * Real.exp (4 * c + 2 * δ) * ε ^ 2 * Work.Spaces.HkSq α (k + 1) f := by
  have hfQ : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Quad := hf
  have hmeasure : μX = (volume.prod volume).restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
    Measure.prod_restrict (μ := volume) (ν := volume) (s := Work.Spaces.Iz)
      (t := Work.Spaces.Iθ)
  have hmeasureY : μY = (volume.prod volume).restrict (Set.univ ×ˢ Set.Icc (0:ℝ) 1) := by
    show volume.prod (volume.restrict (Set.Icc (0:ℝ) 1)) = _
    rw [← Measure.prod_restrict (μ := volume) (ν := volume) (s := Set.univ)
      (t := Set.Icc (0:ℝ) 1), Measure.restrict_univ]
  have h2ne : (2 : ℝ≥0∞) ≠ ⊤ := by
    rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 from (ENNReal.ofReal_ofNat 2).symm]
    exact ENNReal.ofReal_ne_top
  -- the joint measurability of the four-variable integrand
  have hF4 : AEMeasurable (fun q : (ℝ × ℝ) × ((ℝ × ℝ) × ℝ) => ENNReal.ofReal (Jker ρ ε q.2.1)
      * ENNReal.ofReal (shadow α k f (zShift q.1.1 (q.2.2 * q.2.1.1))
          (thShift q.1.2 (q.2.2 * q.2.1.2)))) (μX.prod μY) :=
    aemeasurable_pair_comp hρ hε (continuousOn_shadow (k := k) hfQ)
  -- the reference value: `ofReal (HkSq α (k+1) f)` as an iterated `lintegral`
  have hHkSq : ENNReal.ofReal (Work.Spaces.HkSq α (k + 1) f)
      = ∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal (Work.Spaces.HkIntegrand α (k + 1) f z θ) := by
    rw [Work.Spaces.HkSq]
    rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal hF.2
      (Eventually.of_forall fun z =>
        integral_nonneg fun θ => Work.Spaces.HkIntegrand_nonneg α (k + 1) f z θ)]
    exact MeasureTheory.setLIntegral_congr_fun measurableSet_Ici
      (fun z hz => MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hF.1 z hz)
        (Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α (k + 1) f z θ))
  -- (A) the left-hand side as an iterated `lintegral`
  have hA : ENNReal.ofReal (Work.Spaces.HkSq α k (fun z θ => Jeps ρ ε f z θ - f z θ))
      ≤ ∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal (Work.Spaces.HkIntegrand α k (fun z θ => Jeps ρ ε f z θ - f z θ)
            z θ) := by
    rw [Work.Spaces.HkSq]
    refine (ofReal_integral_le_lintegral (volume.restrict Work.Spaces.Iz) ?_).trans ?_
    · intro z
      exact integral_nonneg fun θ' =>
        Work.Spaces.HkIntegrand_nonneg α k (fun z θ => Jeps ρ ε f z θ - f z θ) z θ'
    · refine lintegral_mono fun z => ?_
      exact ofReal_integral_le_lintegral (volume.restrict Work.Spaces.Iθ)
        fun θ' => Work.Spaces.HkIntegrand_nonneg α k (fun z θ => Jeps ρ ε f z θ - f z θ) z θ'
  -- (B) the pointwise bound, integrated
  have hB : (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal (Work.Spaces.HkIntegrand α k (fun z θ => Jeps ρ ε f z θ - f z θ)
            z θ))
      ≤ ENNReal.ofReal (2 * ε ^ 2 * Real.exp (4 * c * ε))
        * ∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ, lintegral μY (fun y =>
            ENNReal.ofReal (Jker ρ ε y.1)
              * ENNReal.ofReal (shadow α k f (zShift z (y.2 * y.1.1))
                  (thShift θ (y.2 * y.1.2)))) := by
    rw [← MeasureTheory.lintegral_const_mul' (μ := volume.restrict Work.Spaces.Iz)
      (ENNReal.ofReal (2 * ε ^ 2 * Real.exp (4 * c * ε)))
      (fun z => ∫⁻ θ in Work.Spaces.Iθ, lintegral μY (fun y => ENNReal.ofReal (Jker ρ ε y.1)
          * ENNReal.ofReal (shadow α k f (zShift z (y.2 * y.1.1)) (thShift θ (y.2 * y.1.2)))))
      ENNReal.ofReal_ne_top]
    refine MeasureTheory.setLIntegral_mono' measurableSet_Ici fun z hz => ?_
    rw [← MeasureTheory.lintegral_const_mul' (μ := volume.restrict Work.Spaces.Iθ)
      (ENNReal.ofReal (2 * ε ^ 2 * Real.exp (4 * c * ε)))
      (fun θ => lintegral μY (fun y => ENNReal.ofReal (Jker ρ ε y.1)
          * ENNReal.ofReal (shadow α k f (zShift z (y.2 * y.1.1))
              (thShift θ (y.2 * y.1.2))))) ENNReal.ofReal_ne_top]
    refine MeasureTheory.setLIntegral_mono' measurableSet_Icc fun θ hθ => ?_
    exact HkIntegrand_sub_le (ε := ε) hα hρ hε hfQ hc hWη hWγ hz hθ
  -- (C) the shift variables as a product measure
  have hCK : (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ, lintegral μY (fun y =>
        ENNReal.ofReal (Jker ρ ε y.1)
          * ENNReal.ofReal (shadow α k f (zShift z (y.2 * y.1.1))
              (thShift θ (y.2 * y.1.2)))))
      = lintegral μX (fun x => lintegral μY (fun y => ENNReal.ofReal (Jker ρ ε y.1)
          * ENNReal.ofReal (shadow α k f (zShift x.1 (y.2 * y.1.1))
              (thShift x.2 (y.2 * y.1.2))))) := by
    have hG : AEMeasurable (fun x : ℝ × ℝ => lintegral μY (fun y => ENNReal.ofReal (Jker ρ ε y.1)
        * ENNReal.ofReal (shadow α k f (zShift x.1 (y.2 * y.1.1))
            (thShift x.2 (y.2 * y.1.2)))))
        ((volume.prod volume).restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) := by
      rw [← hmeasure]
      exact hF4.lintegral_prod_right'
    rw [lintegral_μX_eq hG]
  -- (D) Tonelli
  have hCD : lintegral μX (fun x => lintegral μY (fun y => ENNReal.ofReal (Jker ρ ε y.1)
        * ENNReal.ofReal (shadow α k f (zShift x.1 (y.2 * y.1.1))
            (thShift x.2 (y.2 * y.1.2)))))
      = lintegral μY (fun y => lintegral μX (fun x => ENNReal.ofReal (Jker ρ ε y.1)
          * ENNReal.ofReal (shadow α k f (zShift x.1 (y.2 * y.1.1))
              (thShift x.2 (y.2 * y.1.2))))) :=
    lintegral_swap4 hF4
  -- (E) the shift step: pull out the kernel, shift the shadow, and spend the kernel mass
  have hDE : lintegral μY (fun y => lintegral μX (fun x => ENNReal.ofReal (Jker ρ ε y.1)
          * ENNReal.ofReal (shadow α k f (zShift x.1 (y.2 * y.1.1))
              (thShift x.2 (y.2 * y.1.2)))))
      ≤ ENNReal.ofReal (Real.exp (2 * δ * ε))
        * (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
            ENNReal.ofReal (shadow α k f z θ)) := by
    -- the joint measurability of the `(p,t)`-integrand
    have hmeas : AEMeasurable (fun y : (ℝ × ℝ) × ℝ => ENNReal.ofReal (Jker ρ ε y.1)
        * ENNReal.ofReal (Real.exp (δ * (|y.2 * y.1.1| + |y.2 * y.1.2|)))) μY := by
      have hJk : Continuous (Jker ρ ε) := Jker_continuous hρ ε
      have h1 : AEMeasurable (fun y : (ℝ × ℝ) × ℝ => ENNReal.ofReal (Jker ρ ε y.1)) μY :=
        (ENNReal.continuous_ofReal.comp (hJk.comp continuous_fst)).aemeasurable
      have h2 : AEMeasurable (fun y : (ℝ × ℝ) × ℝ =>
          ENNReal.ofReal (Real.exp (δ * (|y.2 * y.1.1| + |y.2 * y.1.2|)))) μY :=
        (ENNReal.continuous_ofReal.comp (Real.continuous_exp.comp (continuous_const.mul
          ((continuous_abs.comp (continuous_snd.mul continuous_fst.fst)).add
            (continuous_abs.comp (continuous_snd.mul continuous_fst.snd)))))).aemeasurable
      exact h1.mul h2
    have hmeasY : AEMeasurable (fun y : (ℝ × ℝ) × ℝ => ENNReal.ofReal (Jker ρ ε y.1)
        * ENNReal.ofReal (Real.exp (δ * (|y.2 * y.1.1| + |y.2 * y.1.2|))))
        ((volume.prod volume).restrict (Set.univ ×ˢ Set.Icc (0:ℝ) 1)) := by
      rw [← hmeasureY]
      exact hmeas
    have hstep : ∀ y : (ℝ × ℝ) × ℝ,
        lintegral μX (fun x => ENNReal.ofReal (Jker ρ ε y.1)
            * ENNReal.ofReal (shadow α k f (zShift x.1 (y.2 * y.1.1))
                (thShift x.2 (y.2 * y.1.2))))
        = ENNReal.ofReal (Jker ρ ε y.1)
          * (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
              ENNReal.ofReal (shadow α k f (zShift z (y.2 * y.1.1))
                (thShift θ (y.2 * y.1.2)))) := by
      intro y
      rw [MeasureTheory.lintegral_const_mul' (μ := μX) (ENNReal.ofReal (Jker ρ ε y.1)) _
        ENNReal.ofReal_ne_top]
      congr 1
      exact lintegral_μX_eq (by
        rw [← hmeasure]
        exact aemeasurable_μX_comp (continuousOn_shadow (k := k) hfQ) y)
    rw [lintegral_congr hstep]
    have hshift : ∀ y ∈ (Set.univ : Set ((ℝ × ℝ) × ℝ)),
        (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
            ENNReal.ofReal (shadow α k f (zShift z (y.2 * y.1.1))
              (thShift θ (y.2 * y.1.2))))
          ≤ ENNReal.ofReal (Real.exp (δ * (|y.2 * y.1.1| + |y.2 * y.1.2|)))
            * (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
                ENNReal.ofReal (shadow α k f z θ)) := by
      intro y _
      exact lintegral_shift_le_gen (V := fun u v => shadow α k f u v) hJac
        (y.2 * y.1.1, y.2 * y.1.2)
    have hmass : lintegral μY (fun y => ENNReal.ofReal (Jker ρ ε y.1)
        * ENNReal.ofReal (Real.exp (δ * (|y.2 * y.1.1| + |y.2 * y.1.2|))))
        ≤ ENNReal.ofReal (Real.exp (2 * δ * ε)) := by
      rw [lintegral_μY_eq hmeasY]
      have hstep1 : ∀ p : ℝ × ℝ, (∫⁻ t in Set.Icc (0 : ℝ) 1, ENNReal.ofReal (Jker ρ ε p)
            * ENNReal.ofReal (Real.exp (δ * (|t * p.1| + |t * p.2|))))
          ≤ ENNReal.ofReal (Jker ρ ε p)
            * ENNReal.ofReal (Real.exp (δ * (|p.1| + |p.2|))) := by
        intro p
        have hexp : ∀ t ∈ Set.Icc (0 : ℝ) 1, ENNReal.ofReal (Jker ρ ε p)
              * ENNReal.ofReal (Real.exp (δ * (|t * p.1| + |t * p.2|)))
            ≤ ENNReal.ofReal (Jker ρ ε p)
              * ENNReal.ofReal (Real.exp (δ * (|p.1| + |p.2|))) := by
          intro t ht
          refine mul_le_mul_of_nonneg_left (ENNReal.ofReal_le_ofReal ?_) zero_le
          rw [Real.exp_le_exp]
          have ht1 : |t| ≤ 1 := by rw [abs_of_nonneg ht.1]; exact ht.2
          have h1 : |t * p.1| ≤ |p.1| := by
            rw [abs_mul]; exact mul_le_of_le_one_left (abs_nonneg _) ht1
          have h2 : |t * p.2| ≤ |p.2| := by
            rw [abs_mul]; exact mul_le_of_le_one_left (abs_nonneg _) ht1
          nlinarith [h1, h2, hδ0]
        calc (∫⁻ t in Set.Icc (0 : ℝ) 1, ENNReal.ofReal (Jker ρ ε p)
              * ENNReal.ofReal (Real.exp (δ * (|t * p.1| + |t * p.2|))))
            ≤ ∫⁻ t in Set.Icc (0 : ℝ) 1, ENNReal.ofReal (Jker ρ ε p)
              * ENNReal.ofReal (Real.exp (δ * (|p.1| + |p.2|))) :=
              MeasureTheory.setLIntegral_mono' measurableSet_Icc hexp
          _ = ENNReal.ofReal (Jker ρ ε p)
              * ENNReal.ofReal (Real.exp (δ * (|p.1| + |p.2|))) := by
              rw [MeasureTheory.setLIntegral_const, Real.volume_Icc]
              simp
      refine (lintegral_mono hstep1).trans ?_
      have hker := HkSqAux.Jker_exp_integral_le hρ hε (c := 0) (δ := δ)
        (by norm_num) hδ0
      simpa only [mul_zero, zero_add] using hker
    calc lintegral μY (fun y => ENNReal.ofReal (Jker ρ ε y.1)
          * (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
              ENNReal.ofReal (shadow α k f (zShift z (y.2 * y.1.1))
                (thShift θ (y.2 * y.1.2)))))
        ≤ lintegral μY (fun y => ENNReal.ofReal (Jker ρ ε y.1)
            * (ENNReal.ofReal (Real.exp (δ * (|y.2 * y.1.1| + |y.2 * y.1.2|)))
              * (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
                  ENNReal.ofReal (shadow α k f z θ)))) := by
          refine lintegral_mono fun y => ?_
          exact mul_le_mul_of_nonneg_left (hshift y (Set.mem_univ y)) zero_le
      _ = (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
              ENNReal.ofReal (shadow α k f z θ))
            * lintegral μY (fun y => ENNReal.ofReal (Jker ρ ε y.1)
                * ENNReal.ofReal (Real.exp (δ * (|y.2 * y.1.1| + |y.2 * y.1.2|)))) := by
          calc lintegral μY (fun y => ENNReal.ofReal (Jker ρ ε y.1)
                * (ENNReal.ofReal (Real.exp (δ * (|y.2 * y.1.1| + |y.2 * y.1.2|)))
                  * (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
                      ENNReal.ofReal (shadow α k f z θ))))
              = lintegral μY (fun y => (ENNReal.ofReal (Jker ρ ε y.1)
                  * ENNReal.ofReal (Real.exp (δ * (|y.2 * y.1.1| + |y.2 * y.1.2|))))
                  * (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
                      ENNReal.ofReal (shadow α k f z θ))) :=
                lintegral_congr fun y => by ring
            _ = (lintegral μY (fun y => ENNReal.ofReal (Jker ρ ε y.1)
                  * ENNReal.ofReal (Real.exp (δ * (|y.2 * y.1.1| + |y.2 * y.1.2|)))))
                  * (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
                      ENNReal.ofReal (shadow α k f z θ)) :=
                MeasureTheory.lintegral_mul_const''
                  (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
                      ENNReal.ofReal (shadow α k f z θ)) hmeas
            _ = (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
                      ENNReal.ofReal (shadow α k f z θ))
                  * lintegral μY (fun y => ENNReal.ofReal (Jker ρ ε y.1)
                      * ENNReal.ofReal (Real.exp (δ * (|y.2 * y.1.1| + |y.2 * y.1.2|)))) := by
                rw [mul_comm]
      _ ≤ (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
              ENNReal.ofReal (shadow α k f z θ)) * ENNReal.ofReal (Real.exp (2 * δ * ε)) :=
          mul_le_mul_of_nonneg_left hmass zero_le
      _ = ENNReal.ofReal (Real.exp (2 * δ * ε))
            * (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
                ENNReal.ofReal (shadow α k f z θ)) := by rw [mul_comm]
  -- (F) the shadow bound
  have hEF : (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal (shadow α k f z θ))
      ≤ 2 * ENNReal.ofReal (Work.Spaces.HkSq α (k + 1) f) := by
    rw [hHkSq]
    calc (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal (shadow α k f z θ))
        ≤ ∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
            ENNReal.ofReal (2 * Work.Spaces.HkIntegrand α (k + 1) f z θ) := by
          refine MeasureTheory.setLIntegral_mono' measurableSet_Ici fun z _ => ?_
          refine MeasureTheory.setLIntegral_mono' measurableSet_Icc fun θ _ => ?_
          exact ENNReal.ofReal_le_ofReal (shadow_le α k f z θ)
      _ = ∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
            2 * ENNReal.ofReal (Work.Spaces.HkIntegrand α (k + 1) f z θ) := by
          refine lintegral_congr fun z => lintegral_congr fun θ => ?_
          rw [ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2)]
          norm_num
      _ = 2 * (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
            ENNReal.ofReal (Work.Spaces.HkIntegrand α (k + 1) f z θ)) := by
          have hinner : ∀ z : ℝ, (∫⁻ θ in Work.Spaces.Iθ,
                2 * ENNReal.ofReal (Work.Spaces.HkIntegrand α (k + 1) f z θ))
              = 2 * ∫⁻ θ in Work.Spaces.Iθ,
                  ENNReal.ofReal (Work.Spaces.HkIntegrand α (k + 1) f z θ) :=
            fun z => MeasureTheory.lintegral_const_mul'
              (μ := volume.restrict Work.Spaces.Iθ) 2 _ h2ne
          rw [lintegral_congr hinner]
          rw [MeasureTheory.lintegral_const_mul' (μ := volume.restrict Work.Spaces.Iz)
            2 _ h2ne]
  -- assembling
  have hchain : ENNReal.ofReal (Work.Spaces.HkSq α k (fun z θ => Jeps ρ ε f z θ - f z θ))
      ≤ 2 * ENNReal.ofReal (2 * ε ^ 2 * Real.exp (4 * c * ε))
        * ENNReal.ofReal (Real.exp (2 * δ * ε))
        * ENNReal.ofReal (Work.Spaces.HkSq α (k + 1) f) := by
    refine (hA.trans (hB.trans ?_))
    rw [hCK, hCD]
    calc ENNReal.ofReal (2 * ε ^ 2 * Real.exp (4 * c * ε))
          * lintegral μY (fun y => lintegral μX (fun x => ENNReal.ofReal (Jker ρ ε y.1)
              * ENNReal.ofReal (shadow α k f (zShift x.1 (y.2 * y.1.1))
                  (thShift x.2 (y.2 * y.1.2)))))
        ≤ ENNReal.ofReal (2 * ε ^ 2 * Real.exp (4 * c * ε))
          * (ENNReal.ofReal (Real.exp (2 * δ * ε))
            * (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
                ENNReal.ofReal (shadow α k f z θ))) :=
          mul_le_mul_of_nonneg_left hDE zero_le
      _ ≤ ENNReal.ofReal (2 * ε ^ 2 * Real.exp (4 * c * ε))
          * (ENNReal.ofReal (Real.exp (2 * δ * ε))
            * (2 * ENNReal.ofReal (Work.Spaces.HkSq α (k + 1) f))) := by
          refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hEF zero_le) zero_le
      _ = 2 * ENNReal.ofReal (2 * ε ^ 2 * Real.exp (4 * c * ε))
          * ENNReal.ofReal (Real.exp (2 * δ * ε))
          * ENNReal.ofReal (Work.Spaces.HkSq α (k + 1) f) := by ring
  -- merge the `ofReal`s into a single one
  have hmerge : 2 * ENNReal.ofReal (2 * ε ^ 2 * Real.exp (4 * c * ε))
        * ENNReal.ofReal (Real.exp (2 * δ * ε))
        * ENNReal.ofReal (Work.Spaces.HkSq α (k + 1) f)
      = ENNReal.ofReal (2 * (2 * ε ^ 2 * Real.exp (4 * c * ε)) * Real.exp (2 * δ * ε)
          * Work.Spaces.HkSq α (k + 1) f) := by
    rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 from (ENNReal.ofReal_ofNat 2).symm,
      ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 2),
      ← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ 2 * (2 * ε ^ 2 * Real.exp (4 * c * ε))),
      ← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ 2 * (2 * ε ^ 2 * Real.exp (4 * c * ε))
          * Real.exp (2 * δ * ε))]
  rw [hmerge] at hchain
  have hY : (0:ℝ) ≤ Work.Spaces.HkSq α (k + 1) f := Work.Spaces.HkSq_nonneg α (k + 1) f
  have hgoal : Work.Spaces.HkSq α k (fun z θ => Jeps ρ ε f z θ - f z θ)
      ≤ 2 * (2 * ε ^ 2 * Real.exp (4 * c * ε)) * Real.exp (2 * δ * ε)
          * Work.Spaces.HkSq α (k + 1) f := by
    refine (ENNReal.ofReal_le_ofReal_iff ?_).mp hchain
    exact mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (by positivity))
      (Real.exp_pos _).le) hY
  have hexp : Real.exp (4 * c * ε) * Real.exp (2 * δ * ε) ≤ Real.exp (4 * c + 2 * δ) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.mpr (by nlinarith [hε.le, hε1, hc, hδ0])
  calc Work.Spaces.HkSq α k (fun z θ => Jeps ρ ε f z θ - f z θ)
      ≤ 2 * (2 * ε ^ 2 * Real.exp (4 * c * ε)) * Real.exp (2 * δ * ε)
          * Work.Spaces.HkSq α (k + 1) f := hgoal
    _ = 4 * ε ^ 2 * (Real.exp (4 * c * ε) * Real.exp (2 * δ * ε))
          * Work.Spaces.HkSq α (k + 1) f := by ring
    _ ≤ 4 * ε ^ 2 * Real.exp (4 * c + 2 * δ) * Work.Spaces.HkSq α (k + 1) f := by
        have hfac : (0:ℝ) ≤ 4 * ε ^ 2 * Work.Spaces.HkSq α (k + 1) f :=
          mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg ε)) hY
        calc 4 * ε ^ 2 * (Real.exp (4 * c * ε) * Real.exp (2 * δ * ε))
              * Work.Spaces.HkSq α (k + 1) f
            = (Real.exp (4 * c * ε) * Real.exp (2 * δ * ε))
                * (4 * ε ^ 2 * Work.Spaces.HkSq α (k + 1) f) := by ring
          _ ≤ Real.exp (4 * c + 2 * δ)
                * (4 * ε ^ 2 * Work.Spaces.HkSq α (k + 1) f) :=
              mul_le_mul_of_nonneg_right hexp hfac
          _ = 4 * ε ^ 2 * Real.exp (4 * c + 2 * δ)
                * Work.Spaces.HkSq α (k + 1) f := by ring
    _ = 4 * Real.exp (4 * c + 2 * δ) * ε ^ 2 * Work.Spaces.HkSq α (k + 1) f := by ring

/-! ## The norm form -/

/-- **The mollifier-approximation estimate in the weighted `ℋ^k` norm**: for every admissible
mollifier kernel `ρ` there is a constant `C` with
`‖J_ε f - f‖_{ℋ^k} ≤ C ε ‖f‖_{ℋ^{k+1}}` for all `α ∈ (0,1]`, `k`, `ε ∈ (0,1]` and all
`f` which are `C^∞` on the open quadrant with `HkMem α (k+1) f`.

It is the square root of `HkSq_sub_est_aux`, since `HkNorm = √HkSq`. -/
theorem HkNorm_Jeps_sub_le (ρ : ℝ × ℝ → ℝ) (hρ : Work.FTS.StrongEps.IsMollKernel ρ) :
    ∃ C : ℝ, 0 < C ∧ ∀ α : ℝ, α ∈ Set.Ioc 0 1 → ∀ k : ℕ, ∀ ε : ℝ, ε ∈ Set.Ioc 0 1 →
      ∀ f : ℝ → ℝ → ℝ,
        (∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Work.FTS.EllipticEst.Q0) →
        Work.Spaces.HkMem α (k + 1) f →
        Work.Spaces.HkMem α k (Work.FTS.StrongEps.Jeps ρ ε f) →
        Work.Spaces.HkNorm α k (fun z θ => Work.FTS.StrongEps.Jeps ρ ε f z θ - f z θ)
          ≤ C * ε * Work.Spaces.HkNorm α (k + 1) f := by
  obtain ⟨cη, hcη, hWη0⟩ := HkSqAux.wdiv_shift_le
  obtain ⟨cγ, hcγ, hWγ0⟩ := HkSqAux.Wt_shift_le
  obtain ⟨δ, hδ, hJac⟩ := HkSqAux.logJac_shift_le
  refine ⟨Real.sqrt (4 * Real.exp (4 * max cη cγ + 2 * δ)), Real.sqrt_pos.2 (by positivity), ?_⟩
  intro α hα k ε hε f hf hF _
  have hc : 0 ≤ max cη cγ := le_of_lt (lt_of_lt_of_le hcη (le_max_left _ _))
  have hδ0 : 0 ≤ δ := le_of_lt hδ
  have hWη : ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo 0 (π / 2) → ∀ q : ℝ × ℝ,
      wE z θ ≤ Real.exp (max cη cγ * (|q.1| + |q.2|)) * wE (zShift z q.1) (thShift θ q.2) := by
    intro z θ hz hθ q
    refine (hWη0 z θ q.1 q.2 hz hθ).trans (mul_le_mul_of_nonneg_right ?_ ?_)
    · exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
    · exact wE_nonneg (thShift_mem hθ)
  have hWt_nn : ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo 0 (π / 2) → ∀ p₁ p₂ : ℝ,
      0 ≤ Work.Spaces.Wt α (zShift z p₁) (thShift θ p₂) := fun z θ hz hθ p₁ p₂ =>
    Wt_nonneg ⟨le_of_lt (thShift_mem hθ).1, le_of_lt (thShift_mem hθ).2⟩
  have hWγ : ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo 0 (π / 2) → ∀ q : ℝ × ℝ,
      Work.Spaces.Wt α z θ ≤ Real.exp (max cη cγ * (|q.1| + |q.2|))
        * Work.Spaces.Wt α (zShift z q.1) (thShift θ q.2) := by
    intro z θ hz hθ q
    refine (hWγ0 α hα z θ q.1 q.2 hz hθ).trans
      (mul_le_mul_of_nonneg_right ?_ (hWt_nn z θ hz hθ q.1 q.2))
    exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity))
  have hmain := HkSq_sub_est_aux hα hρ hε.1 hε.2 hf hF hc hδ0 hWη hWγ hJac
  have hY : (0:ℝ) ≤ Work.Spaces.HkSq α (k + 1) f := Work.Spaces.HkSq_nonneg α (k + 1) f
  have hstep : Work.Spaces.HkSq α k (fun z θ => Jeps ρ ε f z θ - f z θ)
      ≤ (Real.sqrt (4 * Real.exp (4 * max cη cγ + 2 * δ)) * ε
          * Work.Spaces.HkNorm α (k + 1) f) ^ 2 := by
    have hsq : (Real.sqrt (4 * Real.exp (4 * max cη cγ + 2 * δ)) * ε
          * Work.Spaces.HkNorm α (k + 1) f) ^ 2
        = 4 * Real.exp (4 * max cη cγ + 2 * δ) * ε ^ 2 * Work.Spaces.HkSq α (k + 1) f := by
      rw [mul_pow, mul_pow,
        Real.sq_sqrt (by positivity : (0:ℝ) ≤ 4 * Real.exp (4 * max cη cγ + 2 * δ)),
        Work.Spaces.HkNorm, Real.sq_sqrt hY]
    rw [hsq]
    exact hmain
  have hle := Real.sqrt_le_sqrt hstep
  have hnn : (0:ℝ) ≤ Real.sqrt (4 * Real.exp (4 * max cη cγ + 2 * δ)) * ε
      * Work.Spaces.HkNorm α (k + 1) f :=
    mul_nonneg (mul_nonneg (Real.sqrt_nonneg _) hε.1.le) (Real.sqrt_nonneg _)
  rw [Real.sqrt_sq hnn] at hle
  simpa only [Work.Spaces.HkNorm] using hle

end Work.FTS.StrongEps.EpsApprox
