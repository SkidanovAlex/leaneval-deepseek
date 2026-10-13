/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/DiffAux/MainEst.lean`

The assembly of the mollifier approximation estimate `HkSq_Jeps_sub_le`: the pointwise difference
estimate of `DiffAux/JepsSubPointwise.lean`, summed over the finitely many slots of the level-`k`
integrand, Tonelli's theorem, the log-coordinate shift invariance, and the combinatorial shadow
bound `DiffAux/shadow_le`.
-/
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.StrongEps.Basic
import Submission.Work.FTS.StrongEps.Kernel
import Submission.Work.FTS.StrongEps.Weights
import Submission.Work.FTS.StrongEps.mixed_Jeps
import Submission.Work.FTS.StrongEps.HkSqAux.Defs
import Submission.Work.FTS.StrongEps.HkSqAux.LogCoord
import Submission.Work.FTS.StrongEps.HkSqAux.lintegral_quad_log_subst
import Submission.Work.FTS.StrongEps.HkSqAux.lintegral_prod_shift
import Submission.Work.FTS.StrongEps.HkSqAux.logJac_shift_le
import Submission.Work.FTS.StrongEps.HkSqAux.continuousOn_mixed_Quad
import Submission.Work.FTS.StrongEps.HkSqAux.sq_integral_Jker_mul_le
import Submission.Work.FTS.StrongEps.HkSqAux.Chain
import Submission.Work.FTS.StrongEps.DiffAux.Defs
import Submission.Work.FTS.StrongEps.DiffAux.Shadow
import Submission.Work.FTS.StrongEps.DiffAux.shiftPath_sub
import Submission.Work.FTS.StrongEps.DiffAux.Jeps_sub_eq_integral
import Submission.Work.FTS.StrongEps.DiffAux.hasDerivAt_Jeps_slice_z
import Submission.Work.FTS.StrongEps.DiffAux.hasDerivAt_Jeps_slice_th
import Submission.Work.FTS.StrongEps.DiffAux.lintegral_shift_le_gen
import Submission.Work.FTS.StrongEps.DiffAux.JepsSubPointwise
import Submission.Work.FTS.StrongEps.DiffAux.DzIter_sub_Jeps
import Submission.Work.FTS.StrongEps.DiffAux.mixed_sub_Jeps
import Submission.Work.FTS.EllipticEst.ThetaU.OpenSliceAux.DthIter_DzIter_eqOn_of_isOpen
import Submission.Work.FTS.LocData.SmoothChain

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.DiffAux

open Work.FTS.StrongEps (Quad zShift thShift Jker Jeps sin_two_pos)

set_option autoImplicit false
set_option maxHeartbeats 4000000

variable {ρ : ℝ × ℝ → ℝ} {ε c δ : ℝ} {k : ℕ} {f : ℝ → ℝ → ℝ}

/-! ## The two auxiliary measures -/

/-- The measure on the profile variables `(z,θ)`. -/
abbrev μX : Measure (ℝ × ℝ) := (volume.restrict Work.Spaces.Iz).prod
  (volume.restrict Work.Spaces.Iθ)

/-- The measure on the shift variables `(p,t)`. -/
abbrev μY : Measure ((ℝ × ℝ) × ℝ) := volume.prod (volume.restrict (Set.Icc (0 : ℝ) 1))

theorem lintegral_μX_eq {G : ℝ × ℝ → ℝ≥0∞}
    (hG : AEMeasurable G ((volume.prod volume).restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ))) :
    (lintegral μX (fun x => G x)) = ∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ, G (z, θ) := by
  have hμ : μX = (volume.prod volume).restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
    Measure.prod_restrict (μ := volume) (ν := volume) (s := Work.Spaces.Iz)
      (t := Work.Spaces.Iθ)
  rw [hμ]
  exact MeasureTheory.setLIntegral_prod (fun x : ℝ × ℝ => G x) hG

theorem lintegral_μY_eq {G : (ℝ × ℝ) × ℝ → ℝ≥0∞}
    (hG : AEMeasurable G ((volume.prod volume).restrict (Set.univ ×ˢ Set.Icc (0 : ℝ) 1))) :
    (lintegral μY (fun y => G y)) = ∫⁻ p : ℝ × ℝ, ∫⁻ t in Set.Icc (0 : ℝ) 1, G (p, t) := by
  have hμ : μY = (volume.prod volume).restrict (Set.univ ×ˢ Set.Icc (0 : ℝ) 1) := by
    show volume.prod (volume.restrict (Set.Icc (0 : ℝ) 1)) = _
    rw [← Measure.prod_restrict (μ := volume) (ν := volume) (s := Set.univ)
      (t := Set.Icc (0 : ℝ) 1), Measure.restrict_univ]
  rw [hμ]
  simpa only [Measure.restrict_univ] using
    (MeasureTheory.setLIntegral_prod (fun y : (ℝ × ℝ) × ℝ => G y) hG)

/-- The "iterated to product" conversion for the shift variables. -/
theorem lintegral_iterated_eq_prodY {F : ℝ × ℝ → ℝ → ℝ≥0∞}
    (hF : AEMeasurable (fun y : (ℝ × ℝ) × ℝ => F y.1 y.2) μY) :
    (∫⁻ p : ℝ × ℝ, ∫⁻ t in Set.Icc (0 : ℝ) 1, F p t) = lintegral μY (fun y => F y.1 y.2) := by
  rw [← lintegral_μY_eq (G := fun y => F y.1 y.2) (by
    rw [← Measure.prod_restrict (μ := volume) (ν := volume) (s := Set.univ)
      (t := Set.Icc (0 : ℝ) 1), Measure.restrict_univ]
    exact hF)]

/-! ## Bookkeeping lemmas -/

/-- A finite sum of `lintegral`s is at most the `lintegral` of the sum.  (No measurability
hypothesis: this is the inequality direction supplied by `le_lintegral_add`.) -/
theorem lintegral_finsetSum_le {ι : Type*} {γ : Type*} [MeasurableSpace γ] (μ : Measure γ)
    (s : Finset ι) (F : ι → γ → ℝ≥0∞) :
    (∑ i ∈ s, ∫⁻ x, F i x ∂μ) ≤ ∫⁻ x, ∑ i ∈ s, F i x ∂μ := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s has ih =>
    have h1 : (∑ i ∈ insert a s, ∫⁻ x, F i x ∂μ)
        = ∫⁻ x, F a x ∂μ + ∑ i ∈ s, ∫⁻ x, F i x ∂μ := by
      rw [Finset.sum_insert has]
    have h2 : (∫⁻ x, ∑ i ∈ insert a s, F i x ∂μ)
        = ∫⁻ x, (F a x + ∑ i ∈ s, F i x) ∂μ := by
      congr 1
      funext x
      rw [Finset.sum_insert has]
    rw [h1, h2]
    exact (add_le_add le_rfl ih).trans
      (MeasureTheory.le_lintegral_add (μ := μ) (F a) (fun x => ∑ i ∈ s, F i x))

/-- `ofReal` of an integral is at most the `lintegral` of `ofReal`. -/
theorem ofReal_integral_le_lintegral {γ : Type*} [MeasurableSpace γ] (μ : Measure γ)
    {F : γ → ℝ} (hnn : ∀ x, 0 ≤ F x) :
    ENNReal.ofReal (∫ x, F x ∂μ) ≤ ∫⁻ x, ENNReal.ofReal (F x) ∂μ := by
  by_cases h : Integrable F μ
  · rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal h (Eventually.of_forall hnn)]
  · rw [MeasureTheory.integral_undef h, ENNReal.ofReal_zero]
    exact bot_le

/-- Continuity of a finite sum of continuous functions. -/
theorem continuousOn_finsetSum {ι : Type*} (s : Finset ι) {F : ι → ℝ × ℝ → ℝ}
    {t : Set (ℝ × ℝ)} (h : ∀ i ∈ s, ContinuousOn (F i) t) :
    ContinuousOn (fun x => ∑ i ∈ s, F i x) t := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using continuousOn_const
  | insert a s has ih =>
    have h1 : ContinuousOn (F a) t := h a (Finset.mem_insert_self a s)
    have h2 : ContinuousOn (fun x => ∑ i ∈ s, F i x) t :=
      ih fun i hi => h i (Finset.mem_insert_of_mem hi)
    refine (h1.add h2).congr fun x _ => ?_
    simp only [Pi.add_apply, Finset.sum_insert has]

/-! ## Continuity on the quadrant -/

theorem continuousOn_w : ContinuousOn (fun q : ℝ × ℝ => Work.Spaces.w q.1) Quad := by
  have h1 : ContinuousOn (fun q : ℝ × ℝ => (1 + q.1) ^ 2) Quad :=
    (continuous_const.add continuous_fst).continuousOn.pow 2
  have h2 : ContinuousOn (fun q : ℝ × ℝ => q.1 ^ 2) Quad :=
    continuous_fst.continuousOn.pow 2
  exact h1.div h2 fun q hq => pow_ne_zero 2 (ne_of_gt hq.1)

theorem continuousOn_wE : ContinuousOn (fun q : ℝ × ℝ => wE q.1 q.2) Quad := by
  have h2 : ContinuousOn (fun q : ℝ × ℝ =>
      (Real.sin (2 * q.2)) ^ (Work.Spaces.eta / 2)) Quad :=
    (Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn.rpow_const
      (fun q hq => Or.inl (ne_of_gt (sin_two_pos hq.2)))
  exact (continuousOn_w).div h2 fun q hq =>
    ne_of_gt (Real.rpow_pos_of_pos (sin_two_pos hq.2) _)

theorem continuousOn_wTheta {α : ℝ} : ContinuousOn (fun q : ℝ × ℝ =>
    (Real.sin (2 * q.2)) ^ (-(Work.Spaces.gam α / 2))) Quad :=
  (Real.continuous_sin.comp (continuous_const.mul continuous_snd)).continuousOn.rpow_const
    (fun q hq => Or.inl (ne_of_gt (sin_two_pos hq.2)))

theorem continuousOn_Wt {α : ℝ} :
    ContinuousOn (fun q : ℝ × ℝ => Work.Spaces.Wt α q.1 q.2) Quad := by
  have h := continuousOn_w.mul (continuousOn_wTheta (α := α))
  refine h.congr fun q _ => ?_
  simp only [Pi.mul_apply, Work.Spaces.Wt, Work.Spaces.wTheta]

theorem continuousOn_DzIter (hf : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Quad)
    (m : ℕ) : ContinuousOn (fun q : ℝ × ℝ => Work.Spaces.DzIter m f q.1 q.2) Quad := by
  simpa only [Work.Spaces.mixed_zero_right] using HkSqAux.continuousOn_mixed_Quad hf m 0

theorem continuousOn_mixed (hf : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Quad)
    (j i : ℕ) : ContinuousOn (fun q : ℝ × ℝ => Work.Spaces.mixed j i f q.1 q.2) Quad :=
  HkSqAux.continuousOn_mixed_Quad hf j i

/-- The level-`k` shadow is continuous on the open quadrant. -/
theorem continuousOn_shadow {α : ℝ} (hf : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Quad) :
    ContinuousOn (fun q : ℝ × ℝ => shadow α k f q.1 q.2) Quad := by
  have h : ContinuousOn (fun q : ℝ × ℝ =>
      (∑ i ∈ Finset.range (k + 1), (Work.Spaces.DzIter (i + 1) f q.1 q.2 * wE q.1 q.2) ^ 2)
        + 1 / 4 * (∑ i ∈ Finset.range (k + 1),
            (Work.Spaces.mixed i 1 f q.1 q.2 * Work.Spaces.Wt α q.1 q.2) ^ 2)
        + (∑ q' ∈ slots k,
            (Work.Spaces.mixed (q'.2 + 1) q'.1 f q.1 q.2 * Work.Spaces.Wt α q.1 q.2) ^ 2)
        + 1 / 4 * (∑ q' ∈ slots k,
            (Work.Spaces.mixed q'.2 (q'.1 + 1) f q.1 q.2 * Work.Spaces.Wt α q.1 q.2) ^ 2)) Quad := by
    refine ContinuousOn.add (ContinuousOn.add (ContinuousOn.add ?_ ?_) ?_) ?_
    · exact continuousOn_finsetSum _ fun i _ =>
        ((continuousOn_DzIter hf (i + 1)).mul continuousOn_wE).pow 2
    · exact (continuousOn_finsetSum _ fun i _ =>
        ((continuousOn_mixed hf i 1).mul continuousOn_Wt).pow 2).const_mul _
    · exact continuousOn_finsetSum _ fun q _ =>
        ((continuousOn_mixed hf (q.2 + 1) q.1).mul continuousOn_Wt).pow 2
    · exact (continuousOn_finsetSum _ fun q _ =>
        ((continuousOn_mixed hf q.2 (q.1 + 1)).mul continuousOn_Wt).pow 2).const_mul _
  simpa only [shadow] using h

/-! ## Measurability in the shift variables -/

theorem shift_mem_Quad {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2))
    (y : (ℝ × ℝ) × ℝ) :
    (zShift z (y.2 * y.1.1), thShift θ (y.2 * y.1.2)) ∈ Quad :=
  ⟨zShift_pos hz, thShift_mem hθ⟩

/-- A function continuous on the quadrant, composed with the shift, is continuous on the support
of the kernel. -/
theorem continuousOn_shift_comp {A : ℝ → ℝ → ℝ}
    (hA : ContinuousOn (fun q : ℝ × ℝ => A q.1 q.2) Quad)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    ContinuousOn (fun y : (ℝ × ℝ) × ℝ => A (zShift z (y.2 * y.1.1))
      (thShift θ (y.2 * y.1.2))) (Metric.closedBall (0 : ℝ × ℝ) ε ×ˢ Set.univ) := by
  have hg : ContinuousOn (fun y : (ℝ × ℝ) × ℝ =>
      (zShift z (y.2 * y.1.1), thShift θ (y.2 * y.1.2)))
      (Metric.closedBall (0 : ℝ × ℝ) ε ×ˢ Set.univ) := by
    refine ContinuousOn.prodMk ?_ ?_
    · show ContinuousOn (fun y : (ℝ × ℝ) × ℝ => z * Real.exp (-(y.2 * y.1.1))) _
      fun_prop
    · show ContinuousOn (fun y : (ℝ × ℝ) × ℝ =>
        Real.arctan (Real.tan θ * Real.exp (-(y.2 * y.1.2)))) _
      fun_prop
  exact hA.comp hg (fun y _ => shift_mem_Quad hz hθ y)

/-- The composition of a function continuous on the quadrant with the shift is a.e. measurable
for the shift measure `μY`. -/
theorem aemeasurable_μY_comp {A : ℝ → ℝ → ℝ}
    (hρ : IsMollKernel ρ) (hε : 0 < ε)
    (hA : ContinuousOn (fun q : ℝ × ℝ => A q.1 q.2) Quad)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    AEMeasurable (fun y : (ℝ × ℝ) × ℝ => ENNReal.ofReal (Jker ρ ε y.1)
      * ENNReal.ofReal (A (zShift z (y.2 * y.1.1)) (thShift θ (y.2 * y.1.2)))) μY := by
  set K : Set ((ℝ × ℝ) × ℝ) := Metric.closedBall (0 : ℝ × ℝ) ε ×ˢ Set.univ with hK
  have hKmeas : MeasurableSet K := (Metric.isClosed_closedBall.prod isClosed_univ).measurableSet
  have hKae : AEMeasurable (fun y : (ℝ × ℝ) × ℝ =>
      ENNReal.ofReal (Jker ρ ε y.1)) (μY.restrict K) :=
    ENNReal.measurable_ofReal.comp_aemeasurable
      (((Jker_continuous hρ ε).measurable.comp measurable_fst).aemeasurable)
  have hAae : AEMeasurable (fun y : (ℝ × ℝ) × ℝ => ENNReal.ofReal
      (A (zShift z (y.2 * y.1.1)) (thShift θ (y.2 * y.1.2)))) (μY.restrict K) :=
    ENNReal.measurable_ofReal.comp_aemeasurable
      (((continuousOn_shift_comp (ε := ε) hA hz hθ).aemeasurable hKmeas))
  have hΦae : AEMeasurable (fun y : (ℝ × ℝ) × ℝ => ENNReal.ofReal (Jker ρ ε y.1)
      * ENNReal.ofReal (A (zShift z (y.2 * y.1.1)) (thShift θ (y.2 * y.1.2))))
      (μY.restrict K) := hKae.mul hAae
  have hind := (aemeasurable_indicator_iff hKmeas).mpr hΦae
  have hEq : K.indicator (fun y : (ℝ × ℝ) × ℝ => ENNReal.ofReal (Jker ρ ε y.1)
      * ENNReal.ofReal (A (zShift z (y.2 * y.1.1)) (thShift θ (y.2 * y.1.2))))
      = fun y : (ℝ × ℝ) × ℝ => ENNReal.ofReal (Jker ρ ε y.1)
      * ENNReal.ofReal (A (zShift z (y.2 * y.1.1)) (thShift θ (y.2 * y.1.2))) := by
    funext y
    by_cases hy : y ∈ K
    · rw [Set.indicator_of_mem hy]
    · rw [Set.indicator_of_notMem hy]
      have hnotmem : y.1 ∉ Metric.closedBall (0 : ℝ × ℝ) ε := fun h => hy ⟨h, trivial⟩
      rw [Jker_eq_zero_of_not_mem hρ hε hnotmem, ENNReal.ofReal_zero, zero_mul]
  rw [hEq] at hind
  exact hind

/-- The bracket form of the shift measurability. -/
theorem aemeasurable_μY_bracket {g W : ℝ → ℝ → ℝ}
    (hρ : IsMollKernel ρ) (hε : 0 < ε)
    (hWc : ContinuousOn (fun q : ℝ × ℝ => W q.1 q.2) Quad)
    (hDz : ContinuousOn (fun q : ℝ × ℝ => Work.Spaces.Dz g q.1 q.2) Quad)
    (hDth : ContinuousOn (fun q : ℝ × ℝ => Work.Spaces.Dth g q.1 q.2) Quad)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    AEMeasurable (fun y : (ℝ × ℝ) × ℝ => ENNReal.ofReal (Jker ρ ε y.1)
      * ENNReal.ofReal (bracket g W z θ y.1 y.2)) μY := by
  have hA : ContinuousOn (fun q : ℝ × ℝ =>
      (W q.1 q.2 * Work.Spaces.Dz g q.1 q.2) ^ 2
        + 1 / 4 * (W q.1 q.2 * Work.Spaces.Dth g q.1 q.2) ^ 2) Quad :=
    ((hWc.mul hDz).pow 2).add (((hWc.mul hDth).pow 2).const_mul _)
  exact aemeasurable_μY_comp (A := fun u v =>
    (W u v * Work.Spaces.Dz g u v) ^ 2 + 1 / 4 * (W u v * Work.Spaces.Dth g u v) ^ 2)
    hρ hε hA hz hθ

/-- The pointwise difference estimate, in the `μY` form. -/
theorem slot_ofReal_le {g W : ℝ → ℝ → ℝ}
    (hρ : IsMollKernel ρ) (hε : 0 < ε) (hc : 0 ≤ c)
    (hg : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry g) Quad)
    (hWc : ContinuousOn (fun q : ℝ × ℝ => W q.1 q.2) Quad)
    (hDz : ContinuousOn (fun q : ℝ × ℝ => Work.Spaces.Dz g q.1 q.2) Quad)
    (hDth : ContinuousOn (fun q : ℝ × ℝ => Work.Spaces.Dth g q.1 q.2) Quad)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) (hWnn : 0 ≤ W z θ)
    (hW : ∀ q : ℝ × ℝ, W z θ ≤ Real.exp (c * (|q.1| + |q.2|)) * W (zShift z q.1) (thShift θ q.2)) :
    ENNReal.ofReal ((W z θ * (Jeps ρ ε g z θ - g z θ)) ^ 2)
      ≤ ENNReal.ofReal (2 * ε ^ 2 * Real.exp (4 * c * ε))
        * lintegral μY (fun y => ENNReal.ofReal (Jker ρ ε y.1)
            * ENNReal.ofReal (bracket g W z θ y.1 y.2)) := by
  have h := ofReal_Jeps_sub_sq_le (ρ := ρ) (ε := ε) (g := g) (W := W) hρ hε hc hg hWc hDz hDth
    hz hθ hWnn hW
  have hconv : (∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Jker ρ ε p)
        * ∫⁻ t in Set.Icc (0 : ℝ) 1, ENNReal.ofReal (bracket g W z θ p t))
      = ∫⁻ p : ℝ × ℝ, ∫⁻ t in Set.Icc (0 : ℝ) 1,
          ENNReal.ofReal (Jker ρ ε p) * ENNReal.ofReal (bracket g W z θ p t) := by
    refine lintegral_congr fun p => ?_
    rw [← MeasureTheory.lintegral_const_mul' (ENNReal.ofReal (Jker ρ ε p)) _
      ENNReal.ofReal_ne_top]
  rw [hconv, lintegral_iterated_eq_prodY
    (aemeasurable_μY_bracket hρ hε hWc hDz hDth hz hθ)] at h
  exact h

/-! ## Measurability in the profile variables, and Tonelli -/

theorem measure_quad_compl : μX (Quadᶜ) = 0 := by
  have hsub : Quadᶜ ⊆ (Set.Ioi (0 : ℝ))ᶜ ×ˢ (Set.univ : Set ℝ) ∪
      (Set.univ : Set ℝ) ×ˢ (Set.Ioo (0 : ℝ) (π / 2))ᶜ := by
    intro x hx
    simp only [Quad, Set.mem_compl_iff, Set.mem_prod, Set.mem_Ioi, Set.mem_Ioo, not_and,
      Set.mem_union, Set.mem_univ, and_true, true_and] at hx ⊢
    tauto
  have hIz : (volume.restrict Work.Spaces.Iz) (Set.Ioi (0 : ℝ))ᶜ = 0 := by
    rw [Measure.restrict_apply measurableSet_Ioi.compl]
    refine measure_mono_null ?_ (measure_singleton (0 : ℝ))
    intro x hx
    simp only [Work.Spaces.Iz, Set.mem_inter_iff, Set.mem_Ici, Set.mem_compl_iff,
      Set.mem_Ioi, Set.mem_singleton_iff] at hx ⊢
    exact le_antisymm (not_lt.mp hx.1) hx.2
  have hIθ : (volume.restrict Work.Spaces.Iθ) (Set.Ioo (0 : ℝ) (π / 2))ᶜ = 0 := by
    rw [Measure.restrict_apply measurableSet_Ioo.compl]
    refine measure_mono_null ?_ (measure_union_null (measure_singleton 0)
      (measure_singleton (π / 2)))
    intro x hx
    simp only [Work.Spaces.Iθ, Set.mem_inter_iff, Set.mem_Icc, Set.mem_compl_iff,
      Set.mem_Ioo, Set.mem_union, Set.mem_singleton_iff] at hx ⊢
    obtain ⟨hxn, hxI⟩ := hx
    rcases lt_or_ge (0 : ℝ) x with h | h
    · rcases lt_or_ge x (π / 2) with h2 | h2
      · exact absurd ⟨h, h2⟩ hxn
      · exact Or.inr (le_antisymm hxI.2 h2)
    · exact Or.inl (le_antisymm h hxI.1)
  have h1 : μX ((Set.Ioi (0 : ℝ))ᶜ ×ˢ (Set.univ : Set ℝ) ∪
      (Set.univ : Set ℝ) ×ˢ (Set.Ioo (0 : ℝ) (π / 2))ᶜ) = 0 := by
    rw [measure_union_null_iff]
    refine ⟨?_, ?_⟩
    · rw [μX, Measure.prod_prod, hIz, zero_mul]
    · rw [μX, Measure.prod_prod, hIθ, mul_zero]
  exact measure_mono_null hsub h1

theorem measure_quad_compl_pair : (μX.prod μY) {q : (ℝ × ℝ) × ((ℝ × ℝ) × ℝ) | q.1 ∈ Quad}ᶜ = 0 := by
  have hset : {q : (ℝ × ℝ) × ((ℝ × ℝ) × ℝ) | q.1 ∈ Quad}ᶜ
      = Quadᶜ ×ˢ (Set.univ : Set ((ℝ × ℝ) × ℝ)) := by
    ext q
    simp only [Set.mem_compl_iff, Set.mem_ofPred_eq, Set.mem_prod, Set.mem_univ, and_true]
  rw [hset, Measure.prod_prod, measure_quad_compl, zero_mul]

/-- The shadow, composed with the shift in the profile variables, is measurable for `μX` (for
every fixed shift variable). -/
theorem aemeasurable_μX_comp {A : ℝ → ℝ → ℝ}
    (hA : ContinuousOn (fun q : ℝ × ℝ => A q.1 q.2) Quad) (y : (ℝ × ℝ) × ℝ) :
    AEMeasurable (fun x : ℝ × ℝ =>
      ENNReal.ofReal (A (zShift x.1 (y.2 * y.1.1)) (thShift x.2 (y.2 * y.1.2)))) μX := by
  have hcont : ContinuousOn (fun x : ℝ × ℝ =>
      A (zShift x.1 (y.2 * y.1.1)) (thShift x.2 (y.2 * y.1.2))) Quad := by
    have hg : ContinuousOn (fun x : ℝ × ℝ =>
        (zShift x.1 (y.2 * y.1.1), thShift x.2 (y.2 * y.1.2))) Quad := by
      refine ContinuousOn.prodMk ?_ ?_
      · show ContinuousOn (fun x : ℝ × ℝ => x.1 * Real.exp (-(y.2 * y.1.1))) Quad
        fun_prop
      · show ContinuousOn (fun x : ℝ × ℝ =>
          Real.arctan (Real.tan x.2 * Real.exp (-(y.2 * y.1.2)))) Quad
        refine Real.continuous_arctan.comp_continuousOn ?_
        refine ContinuousOn.mul ?_ (Real.continuous_exp.comp_continuousOn (by fun_prop))
        exact Real.continuousOn_tan.comp continuousOn_snd
          (fun x hx => (Real.cos_pos_of_mem_Ioo ⟨by linarith [hx.2.1, Real.pi_pos],
            hx.2.2⟩).ne')
    exact hA.comp hg (fun x hx => ⟨zShift_pos hx.1, thShift_mem hx.2⟩)
  have hQae : Quad =ᵐ[μX] Set.univ := by
    filter_upwards [compl_mem_ae_iff.mpr measure_quad_compl] with x hx
    refine propext ⟨fun _ => trivial, fun _ => ?_⟩
    simpa only [Set.mem_compl_iff, not_not] using hx
  have heq : μX = μX.restrict Quad :=
    ((Measure.restrict_congr_set hQae).trans Measure.restrict_univ).symm
  rw [heq]
  exact (ENNReal.continuous_ofReal.comp_continuousOn hcont).aemeasurable
    isOpen_Quad.measurableSet

/-- The joint measurability needed for Tonelli's theorem. -/
theorem aemeasurable_pair_comp {A : ℝ → ℝ → ℝ}
    (hρ : IsMollKernel ρ) (hε : 0 < ε)
    (hA : ContinuousOn (fun q : ℝ × ℝ => A q.1 q.2) Quad) :
    AEMeasurable (fun q : (ℝ × ℝ) × ((ℝ × ℝ) × ℝ) => ENNReal.ofReal (Jker ρ ε q.2.1)
      * ENNReal.ofReal (A (zShift q.1.1 (q.2.2 * q.2.1.1))
          (thShift q.1.2 (q.2.2 * q.2.1.2)))) (μX.prod μY) := by
  set S : Set ((ℝ × ℝ) × ((ℝ × ℝ) × ℝ)) := {q | q.1 ∈ Quad} with hS
  have hSmeas : MeasurableSet S := (isOpen_Quad.preimage continuous_fst).measurableSet
  have hshift : ContinuousOn (fun q : (ℝ × ℝ) × ((ℝ × ℝ) × ℝ) =>
      (zShift q.1.1 (q.2.2 * q.2.1.1), thShift q.1.2 (q.2.2 * q.2.1.2))) S := by
    refine ContinuousOn.prodMk ?_ ?_
    · show ContinuousOn (fun q : (ℝ × ℝ) × ((ℝ × ℝ) × ℝ) =>
        q.1.1 * Real.exp (-(q.2.2 * q.2.1.1))) S
      fun_prop
    · show ContinuousOn (fun q : (ℝ × ℝ) × ((ℝ × ℝ) × ℝ) =>
        Real.arctan (Real.tan q.1.2 * Real.exp (-(q.2.2 * q.2.1.2)))) S
      refine Real.continuous_arctan.comp_continuousOn ?_
      refine ContinuousOn.mul ?_ (Real.continuous_exp.comp_continuousOn (by fun_prop))
      exact Real.continuousOn_tan.comp continuousOn_fst.snd
        (fun q hq => (Real.cos_pos_of_mem_Ioo ⟨by linarith [hq.2.1, Real.pi_pos],
          hq.2.2⟩).ne')
  have hAsm : ContinuousOn (fun q : (ℝ × ℝ) × ((ℝ × ℝ) × ℝ) =>
      A (zShift q.1.1 (q.2.2 * q.2.1.1)) (thShift q.1.2 (q.2.2 * q.2.1.2))) S :=
    hA.comp hshift (fun q hq => ⟨zShift_pos hq.1, thShift_mem hq.2⟩)
  have h1 : AEMeasurable (fun q : (ℝ × ℝ) × ((ℝ × ℝ) × ℝ) =>
      ENNReal.ofReal (Jker ρ ε q.2.1)) ((μX.prod μY).restrict S) :=
    ENNReal.measurable_ofReal.comp_aemeasurable
      (((Jker_continuous hρ ε).measurable.comp measurable_snd.fst).aemeasurable)
  have h2 : AEMeasurable (fun q : (ℝ × ℝ) × ((ℝ × ℝ) × ℝ) =>
      ENNReal.ofReal (A (zShift q.1.1 (q.2.2 * q.2.1.1))
        (thShift q.1.2 (q.2.2 * q.2.1.2)))) ((μX.prod μY).restrict S) :=
    ENNReal.measurable_ofReal.comp_aemeasurable (hAsm.aemeasurable hSmeas)
  have hAe : AEMeasurable (fun q : (ℝ × ℝ) × ((ℝ × ℝ) × ℝ) =>
      ENNReal.ofReal (Jker ρ ε q.2.1)
      * ENNReal.ofReal (A (zShift q.1.1 (q.2.2 * q.2.1.1))
          (thShift q.1.2 (q.2.2 * q.2.1.2)))) ((μX.prod μY).restrict S) := h1.mul h2
  have hSae : S =ᵐ[μX.prod μY] Set.univ := by
    filter_upwards [compl_mem_ae_iff.mpr measure_quad_compl_pair] with q hq
    refine propext ⟨fun _ => trivial, fun _ => ?_⟩
    rw [hS]
    simpa only [Set.mem_compl_iff, not_not, Set.mem_ofPred_eq] using hq
  have hcongr : μX.prod μY = (μX.prod μY).restrict S :=
    ((Measure.restrict_congr_set hSae).trans Measure.restrict_univ).symm
  rw [hcongr]
  exact hAe

/-- **Tonelli's theorem for the difference estimate.** -/
theorem lintegral_swap4 {F : ℝ × ℝ → (ℝ × ℝ) × ℝ → ℝ≥0∞}
    (hF : AEMeasurable (fun q : (ℝ × ℝ) × ((ℝ × ℝ) × ℝ) => F q.1 q.2) (μX.prod μY)) :
    (lintegral μX (fun x => lintegral μY (fun y => F x y))) =
      lintegral μY (fun y => lintegral μX (fun x => F x y)) :=
  MeasureTheory.lintegral_lintegral_swap hF


end Work.FTS.StrongEps.DiffAux
