/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/EpsSqTools/EpsSqIter_mixed_Jeps_le6.lean`

**The smoothing estimate for the mixed slots of the log-coordinate mollifier `J_ε` up to order
six, in the *iterated* `lintegral` form.**

For every smooth admissible kernel `ρ` there is a constant `C > 0` (depending on `ρ` only) such
that for every `α ∈ (0,1]`, every `ε ∈ (0,1]` and every profile `f` which is smooth on the open
quadrant and belongs to the weighted space `X = (EpsSq, EpsMem)` of `EpsSpace.lean`, the mollified
profile `J_ε f` again belongs to `X` and

  `∫⁻_z ∫⁻_θ ENNReal.ofReal ((D_z^j D_θ^i (J_ε f) · epsW α)²)
      ≤ ENNReal.ofReal (C · (C/ε)^{2(j+i)} · EpsSq α f)`   for all `j + i ≤ 6`.

Two differences with the sibling `EpsSq_mixed_Jeps_le` (order `≤ 3`, `EpsSq`-form):

* the threshold is `j + i ≤ 6` instead of `≤ 3` (this only changes the constants: the mass of a
  routed kernel is bounded by `Ksm ρ 1 6` instead of `Ksm ρ 1 3`, and `4^i ≤ 4^6 = 4096`);
* the conclusion is the **iterated `lintegral`** of the squared integrand rather than the Bochner
  integral `EpsSq α (mixed j i (Jeps ρ ε f))`.  This is the *junk-safe* form: it carries the
  finiteness of the slot together with its size, and it is implied by nothing but the pointwise
  gain `MixedJepsEpsWpt` and the generic integration chain `iter_le_of_pointwise`, which is exactly
  how the sibling is proved (there the chain `hZ` is a step, here it is the conclusion).

Route.

1. `MixedJepsEpsWpt` (all `(j,i)`, no restriction) bounds the slot pointwise:
   `ofReal ((mixed j i (J_ε f) · epsW)²) ≤ ofReal (4^i ∫|KdK|) · ∫⁻_p ofReal (Λ p)
      · ofReal ((f∘shift · epsW)²)`,  `Λ p = |KdK ρ ε j i p| · e^{2c(|p₁|+|p₂|)}`.
2. `iter_le_of_pointwise` integrates this over `Iz × Iθ`: Tonelli + the mass bound for `Λ` +
   the log-Jacobian comparison `logJac_shift_le` give
   `≤ ofReal (C₀ · Kmass · EpsSq α f)` with `C₀ = 4^i ∫|KdK|`, `Kmass = e^{2(2c+δ)} ∫|KdK|`.
3. `KdKFacts` + the order-six mass bound `integral_abs_KdK_one_le_Ksm6` estimate the constant:
   `∫|KdK ρ ε j i| = ε⁻¹^{j+i} ∫|KdK ρ 1 j i| ≤ ε⁻¹^{j+i} · Ksm ρ 1 6`, and `4^i ≤ 4096`.
4. The `(j,i) = (0,0)` instance of step 2 shows that the iterated integral of the `J_ε f`-slot is
   finite; combined with the continuity of `J_ε f` on the open quadrant this gives
   `EpsMem α (J_ε f)`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.StrongEps.EpsSqTools.EpsSq_mixed_Jeps_le
import Submission.Work.FTS.StrongEps.EpsSqTools.KdKFacts
import Submission.Work.FTS.StrongEps.EpsSqTools.MixedJepsEpsWpt
import Submission.Work.FTS.StrongEps.JepsHkMem.continuousOn_Jeps
import Submission.Work.Spaces.aesm_of_continuousOn_Qd

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsSqTools

noncomputable section

open scoped Real Topology ENNReal
open MeasureTheory Set Filter

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 2000000

/-! ## The order-six mass bound for the routed kernels -/

/-- **The mass of a routed kernel is at most the order-six mass** `Ksm ρ 1 6`.  This is the
order-six analogue of the order-three bound contained in `KdKFacts` (`Ksm` is the double sum of
the masses of all routed kernels of order `≤ M`, so every slot of order `≤ 6` is dominated by
`Ksm ρ 1 6`). -/
theorem integral_abs_KdK_one_le_Ksm6 (ρ : ℝ × ℝ → ℝ) {a b : ℕ} (ha : a ≤ 6) (hb : b ≤ 6) :
    ∫ p : ℝ × ℝ, |Work.FTS.StrongEps.EpsE4Thr.KdK ρ 1 a b p|
      ≤ Work.FTS.StrongEps.EpsE4Thr.Ksm ρ 1 6 := by
  simp only [Work.FTS.StrongEps.EpsE4Thr.Ksm]
  calc ∫ p : ℝ × ℝ, |Work.FTS.StrongEps.EpsE4Thr.KdK ρ 1 a b p|
      ≤ ∑ a' ∈ Finset.range (6 + 1),
          ∫ p : ℝ × ℝ, |Work.FTS.StrongEps.EpsE4Thr.KdK ρ 1 a' b p| :=
        Finset.single_le_sum (f := fun a' => ∫ p : ℝ × ℝ,
            |Work.FTS.StrongEps.EpsE4Thr.KdK ρ 1 a' b p|)
          (fun _ _ => integral_nonneg fun p => abs_nonneg _)
          (Finset.mem_range.mpr (by omega))
    _ ≤ ∑ a' ∈ Finset.range (6 + 1), ∑ b' ∈ Finset.range (6 + 1),
          ∫ p : ℝ × ℝ, |Work.FTS.StrongEps.EpsE4Thr.KdK ρ 1 a' b' p| :=
        Finset.sum_le_sum fun a' _ => Finset.single_le_sum
          (f := fun b' => ∫ p : ℝ × ℝ, |Work.FTS.StrongEps.EpsE4Thr.KdK ρ 1 a' b' p|)
          (fun _ _ => integral_nonneg fun p => abs_nonneg _)
          (Finset.mem_range.mpr (by omega))

/-! ## The main theorem -/

theorem EpsSqIter_mixed_Jeps_le6 (ρ : ℝ × ℝ → ℝ) (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ) :
    ∃ C : ℝ, 0 < C ∧ ∀ α : ℝ, α ∈ Set.Ioc 0 1 → ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      ∀ f : Work.FTS.Galerkin.Fn,
        (∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Work.FTS.StrongEps.Quad) →
        Work.FTS.StrongEps.EpsMem α f →
          Work.FTS.StrongEps.EpsMem α (Work.FTS.StrongEps.Jeps ρ ε f) ∧
          ∀ j i : ℕ, j + i ≤ 6 →
            (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
                ENNReal.ofReal ((Work.Spaces.mixed j i (Work.FTS.StrongEps.Jeps ρ ε f) z θ
                  * Work.FTS.StrongEps.epsW α z θ) ^ 2))
              ≤ ENNReal.ofReal (C * (C / ε) ^ (2 * (j + i)) * Work.FTS.StrongEps.EpsSq α f) := by
  obtain ⟨c, hcpos, hWc⟩ := Work.FTS.StrongEps.HkSqAux.Wt_shift_le
  obtain ⟨δ, hδpos, hJac0⟩ := Work.FTS.StrongEps.HkSqAux.logJac_shift_le
  have hc0 : 0 ≤ c := hcpos.le
  have hδ0 : 0 ≤ δ := hδpos.le
  obtain ⟨kscale, ksm_le, kint, ksupp, kmom⟩ := KdKFacts ρ hρ
  set Cv : ℝ := max 1 (4096 * (Work.FTS.StrongEps.EpsE4Thr.Ksm ρ 1 6) ^ 2
    * Real.exp (2 * (2 * c + δ))) with hCv
  have hCv1 : 1 ≤ Cv := le_max_left _ _
  have hCvpos : 0 < Cv := lt_of_lt_of_le zero_lt_one hCv1
  have hCvbig : 4096 * (Work.FTS.StrongEps.EpsE4Thr.Ksm ρ 1 6) ^ 2
      * Real.exp (2 * (2 * c + δ)) ≤ Cv := le_max_right _ _
  refine ⟨Cv, hCvpos, ?_⟩
  intro α hα ε hε0 hε1 f hf hfmem
  have hα0 : 0 < α := hα.1
  have hfcont : ContinuousOn (fun q : ℝ × ℝ => f q.1 q.2) Work.FTS.StrongEps.Quad :=
    (hf 0).continuousOn
  have hFcont : ContinuousOn (fun q : ℝ × ℝ => f q.1 q.2
      * Work.FTS.StrongEps.epsW α q.1 q.2) Work.FTS.StrongEps.Quad :=
    hfcont.mul (continuousOn_epsW_quad α)
  have hFmeas : AEMeasurable (fun q : ℝ × ℝ => ENNReal.ofReal
      ((f q.1 q.2 * Work.FTS.StrongEps.epsW α q.1 q.2) ^ 2))
      (MeasureTheory.volume.restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) :=
    ENNReal.measurable_ofReal.comp_aemeasurable hfmem.aestronglyMeasurable.aemeasurable
  -- the generic chain, for every slot `(j,i)`
  have hgen : ∀ j i : ℕ,
      (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
          ENNReal.ofReal ((Work.Spaces.mixed j i (Work.FTS.StrongEps.Jeps ρ ε f) z θ
            * Work.FTS.StrongEps.epsW α z θ) ^ 2))
        ≤ ENNReal.ofReal ((((4 : ℝ) ^ i
              * ∫ p : ℝ × ℝ, |Work.FTS.StrongEps.EpsE4Thr.KdK ρ ε j i p|)
            * (Real.exp (2 * (2 * c + δ))
              * ∫ p : ℝ × ℝ, |Work.FTS.StrongEps.EpsE4Thr.KdK ρ ε j i p|))
            * Work.FTS.StrongEps.EpsSq α f) := by
    intro j i
    set A : ℝ := ∫ p : ℝ × ℝ, |Work.FTS.StrongEps.EpsE4Thr.KdK ρ ε j i p| with hAdef
    set Λ : ℝ × ℝ → ℝ := fun p =>
      |Work.FTS.StrongEps.EpsE4Thr.KdK ρ ε j i p| * Real.exp (2 * c * (|p.1| + |p.2|))
      with hΛdef
    have hA0 : 0 ≤ A := by
      rw [hAdef]
      exact integral_nonneg fun p => abs_nonneg _
    have hΛ0 : ∀ p : ℝ × ℝ, 0 ≤ Λ p := by
      intro p
      rw [hΛdef]
      exact mul_nonneg (abs_nonneg _) (Real.exp_pos _).le
    have hpt : ∀ {z θ : ℝ}, 0 < z → θ ∈ Set.Ioo 0 (π / 2) →
        ENNReal.ofReal ((Work.Spaces.mixed j i (Work.FTS.StrongEps.Jeps ρ ε f) z θ
              * Work.FTS.StrongEps.epsW α z θ) ^ 2)
          ≤ ENNReal.ofReal (4 ^ i * A) * ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Λ p)
              * ENNReal.ofReal ((f (Work.FTS.StrongEps.zShift z p.1)
                    (Work.FTS.StrongEps.thShift θ p.2)
                  * Work.FTS.StrongEps.epsW α (Work.FTS.StrongEps.zShift z p.1)
                      (Work.FTS.StrongEps.thShift θ p.2)) ^ 2) := by
      intro z θ hz hθ
      exact MixedJepsEpsWpt ρ hρ (ε := ε) (α := α) (c := c) hε0 (f := f) hf hz hθ
        (fun p => hWc α hα z θ p.1 p.2 hz hθ) j i
    have hP : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
        ENNReal.ofReal ((Work.Spaces.mixed j i (Work.FTS.StrongEps.Jeps ρ ε f) z θ
              * Work.FTS.StrongEps.epsW α z θ) ^ 2)
          ≤ ENNReal.ofReal (4 ^ i * A) * ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Λ p)
              * ENNReal.ofReal ((f (Work.FTS.StrongEps.zShift z p.1)
                    (Work.FTS.StrongEps.thShift θ p.2)
                  * Work.FTS.StrongEps.epsW α (Work.FTS.StrongEps.zShift z p.1)
                      (Work.FTS.StrongEps.thShift θ p.2)) ^ 2) := by
      intro z hz θ hθ
      by_cases hc' : 0 < z ∧ θ ∈ Set.Ioo 0 (π / 2)
      · exact hpt hc'.1 hc'.2
      · rw [epsW_eq_zero_of_not_mem_quad hα0 hz hθ hc', mul_zero,
          zero_pow (by norm_num : (2 : ℕ) ≠ 0), ENNReal.ofReal_zero]
        exact zero_le
    have hΛexp : ∀ p : ℝ × ℝ, Λ p * Real.exp (δ * (|p.1| + |p.2|))
        = |Work.FTS.StrongEps.EpsE4Thr.KdK ρ ε j i p|
            * Real.exp ((2 * c + δ) * (|p.1| + |p.2|)) := by
      intro p
      rw [hΛdef, mul_assoc, ← Real.exp_add]
      congr 1
      ring_nf
    have hΛfin : ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Λ p * Real.exp (δ * (|p.1| + |p.2|)))
        ≤ ENNReal.ofReal (Real.exp (2 * (2 * c + δ)) * A) := by
      refine le_trans (le_of_eq (lintegral_congr (fun p => by rw [hΛexp p]))) ?_
      simpa only [hAdef] using kmom hε0 hε1 hc0 hδ0 j i
    have hΛcont : Continuous Λ := by
      rw [hΛdef]
      refine (Work.FTS.StrongEps.EpsE4Thr.KdK_continuous hρ ε j i).abs.mul ?_
      refine Real.continuous_exp.comp ?_
      exact continuous_const.mul
        ((continuous_abs.comp continuous_fst).add (continuous_abs.comp continuous_snd))
    have hAe : AEMeasurable (fun z : (ℝ × ℝ) × (ℝ × ℝ) => ENNReal.ofReal (Λ z.2)
        * ENNReal.ofReal ((f (Work.FTS.StrongEps.zShift z.1.1 z.2.1)
              (Work.FTS.StrongEps.thShift z.1.2 z.2.2)
            * Work.FTS.StrongEps.epsW α (Work.FTS.StrongEps.zShift z.1.1 z.2.1)
                (Work.FTS.StrongEps.thShift z.1.2 z.2.2)) ^ 2))
        (((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)).prod MeasureTheory.volume) := by
      have h2 := aemeasurable_shift_comp'
        (F := fun q : ℝ × ℝ => ENNReal.ofReal
          ((f q.1 q.2 * Work.FTS.StrongEps.epsW α q.1 q.2) ^ 2)) hFmeas
      have h1 : AEMeasurable (fun z : (ℝ × ℝ) × (ℝ × ℝ) => ENNReal.ofReal (Λ z.2))
          (((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ)).prod MeasureTheory.volume) :=
        (ENNReal.measurable_ofReal.comp hΛcont.measurable).comp_aemeasurable
          measurable_snd.aemeasurable
      exact h1.mul h2
    have hC₀ : 0 ≤ (4 : ℝ) ^ i * A := mul_nonneg (by positivity) hA0
    have hKmass : 0 ≤ Real.exp (2 * (2 * c + δ)) * A :=
      mul_nonneg (Real.exp_pos _).le hA0
    exact iter_le_of_pointwise (α := α) (c := c) (δ := δ) (Λ := Λ)
      (C₀ := (4 : ℝ) ^ i * A) (Kmass := Real.exp (2 * (2 * c + δ)) * A)
      (f := f) (g := Work.Spaces.mixed j i (Work.FTS.StrongEps.Jeps ρ ε f))
      hC₀ hKmass hΛ0 hΛfin hfmem hJac0 hFcont hAe hP
  -- finiteness of the `(0,0)` slot, hence `EpsMem α (J_ε f)`
  have hlin0 : (∫⁻ z in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
      ENNReal.ofReal (((Work.FTS.StrongEps.Jeps ρ ε f) z θ
        * Work.FTS.StrongEps.epsW α z θ) ^ 2)) < ⊤ := by
    have h := hgen 0 0
    simp only [Work.Spaces.mixed_zero_left, Work.Spaces.DthIter_zero] at h
    exact lt_of_le_of_lt h ENNReal.ofReal_lt_top
  have hEmem : Work.FTS.StrongEps.EpsMem α (Work.FTS.StrongEps.Jeps ρ ε f) := by
    have hJcont : ContinuousOn (fun q : ℝ × ℝ => Work.FTS.StrongEps.Jeps ρ ε f q.1 q.2)
        Work.FTS.StrongEps.Quad :=
      Work.FTS.StrongEps.JepsHkMem.continuousOn_Jeps hρ.moll hε0 hfcont
    have hcont2 : ContinuousOn (fun q : ℝ × ℝ =>
        ((Work.FTS.StrongEps.Jeps ρ ε f) q.1 q.2 * Work.FTS.StrongEps.epsW α q.1 q.2) ^ 2)
        Work.FTS.StrongEps.Quad :=
      (hJcont.mul (continuousOn_epsW_quad α)).pow 2
    have hAESM : AEStronglyMeasurable (fun q : ℝ × ℝ =>
        ((Work.FTS.StrongEps.Jeps ρ ε f) q.1 q.2 * Work.FTS.StrongEps.epsW α q.1 q.2) ^ 2)
        ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) :=
      Work.Spaces.aesm_of_continuousOn_Qd _
        (by simpa only [Work.FTS.StrongEps.Quad] using hcont2)
    have hfin : MeasureTheory.HasFiniteIntegral (fun q : ℝ × ℝ =>
        ((Work.FTS.StrongEps.Jeps ρ ε f) q.1 q.2 * Work.FTS.StrongEps.epsW α q.1 q.2) ^ 2)
        ((MeasureTheory.volume.restrict Work.Spaces.Iz).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
      rw [MeasureTheory.hasFiniteIntegral_iff_ofReal
        (Filter.Eventually.of_forall fun q => sq_nonneg _)]
      rw [← MeasureTheory.lintegral_lintegral (f := fun z θ => ENNReal.ofReal
          (((Work.FTS.StrongEps.Jeps ρ ε f) z θ * Work.FTS.StrongEps.epsW α z θ) ^ 2))
        (hAESM.aemeasurable.ennreal_ofReal)]
      exact hlin0
    have hmeas : (MeasureTheory.volume : MeasureTheory.Measure (ℝ × ℝ)).restrict
          (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)
        = (MeasureTheory.volume.restrict Work.Spaces.Iz).prod
            (MeasureTheory.volume.restrict Work.Spaces.Iθ) := by
      rw [MeasureTheory.Measure.volume_eq_prod, MeasureTheory.Measure.prod_restrict]
    rw [Work.FTS.StrongEps.EpsMem, MeasureTheory.IntegrableOn, hmeas]
    exact ⟨hAESM, hfin⟩
  refine ⟨hEmem, ?_⟩
  intro j i hji
  have hj6 : j ≤ 6 := by omega
  have hi6 : i ≤ 6 := by omega
  have hZ := hgen j i
  -- the constants
  have hKsm0 : 0 ≤ Work.FTS.StrongEps.EpsE4Thr.Ksm ρ 1 6 :=
    Work.FTS.StrongEps.EpsE4Thr.Ksm_nonneg hρ 1 6
  set A : ℝ := ∫ p : ℝ × ℝ, |Work.FTS.StrongEps.EpsE4Thr.KdK ρ ε j i p| with hAdef
  have hA0 : 0 ≤ A := by
    rw [hAdef]
    exact integral_nonneg fun p => abs_nonneg _
  have hA_bound : A ≤ ε⁻¹ ^ (j + i) * Work.FTS.StrongEps.EpsE4Thr.Ksm ρ 1 6 := by
    rw [hAdef, kscale hε0 j i]
    exact mul_le_mul_of_nonneg_left (integral_abs_KdK_one_le_Ksm6 ρ hj6 hi6) (by positivity)
  have hAA : A ^ 2 ≤ (ε⁻¹ ^ (j + i) * Work.FTS.StrongEps.EpsE4Thr.Ksm ρ 1 6) ^ 2 :=
    pow_le_pow_left₀ hA0 hA_bound 2
  have h4i : (4 : ℝ) ^ i ≤ 4096 := by
    have h1 : (4 : ℝ) ^ i ≤ 4 ^ 6 := pow_le_pow_right₀ (by norm_num) hi6
    norm_num at h1
    exact h1
  have hexp2 : (ε⁻¹ ^ (j + i) * Work.FTS.StrongEps.EpsE4Thr.Ksm ρ 1 6) ^ 2
      = ε⁻¹ ^ (2 * (j + i)) * (Work.FTS.StrongEps.EpsE4Thr.Ksm ρ 1 6) ^ 2 := by
    rw [mul_pow, ← pow_mul, Nat.mul_comm]
  have hconst : (4 ^ i * A) * (Real.exp (2 * (2 * c + δ)) * A)
      ≤ Cv * ε⁻¹ ^ (2 * (j + i)) := by
    have h2 : A ^ 2 ≤ ε⁻¹ ^ (2 * (j + i))
        * (Work.FTS.StrongEps.EpsE4Thr.Ksm ρ 1 6) ^ 2 := by
      rw [← hexp2]
      exact hAA
    calc (4 ^ i * A) * (Real.exp (2 * (2 * c + δ)) * A)
        = (4 ^ i * Real.exp (2 * (2 * c + δ))) * A ^ 2 := by ring
      _ ≤ (4 ^ i * Real.exp (2 * (2 * c + δ)))
            * (ε⁻¹ ^ (2 * (j + i))
              * (Work.FTS.StrongEps.EpsE4Thr.Ksm ρ 1 6) ^ 2) :=
          mul_le_mul_of_nonneg_left h2 (by positivity)
      _ = (4 ^ i * (Work.FTS.StrongEps.EpsE4Thr.Ksm ρ 1 6) ^ 2
              * Real.exp (2 * (2 * c + δ))) * ε⁻¹ ^ (2 * (j + i)) := by ring
      _ ≤ (4096 * (Work.FTS.StrongEps.EpsE4Thr.Ksm ρ 1 6) ^ 2
              * Real.exp (2 * (2 * c + δ))) * ε⁻¹ ^ (2 * (j + i)) := by
          have hfe : (4 : ℝ) ^ i * (Work.FTS.StrongEps.EpsE4Thr.Ksm ρ 1 6) ^ 2
                * Real.exp (2 * (2 * c + δ))
              = (4 : ℝ) ^ i * ((Work.FTS.StrongEps.EpsE4Thr.Ksm ρ 1 6) ^ 2
                  * Real.exp (2 * (2 * c + δ))) := by ring
          have hfe2 : 4096 * (Work.FTS.StrongEps.EpsE4Thr.Ksm ρ 1 6) ^ 2
                * Real.exp (2 * (2 * c + δ))
              = 4096 * ((Work.FTS.StrongEps.EpsE4Thr.Ksm ρ 1 6) ^ 2
                  * Real.exp (2 * (2 * c + δ))) := by ring
          rw [hfe, hfe2]
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          exact mul_le_mul_of_nonneg_right h4i
            (mul_nonneg (sq_nonneg _) (Real.exp_pos _).le)
      _ ≤ Cv * ε⁻¹ ^ (2 * (j + i)) := mul_le_mul_of_nonneg_right hCvbig (by positivity)
  have hCeps : Cv * ε⁻¹ ^ (2 * (j + i)) ≤ Cv * (Cv / ε) ^ (2 * (j + i)) := by
    refine mul_le_mul_of_nonneg_left ?_ hCvpos.le
    rw [div_eq_mul_inv]
    refine pow_le_pow_left₀ (by positivity) ?_ _
    simpa using mul_le_mul_of_nonneg_right hCv1 (by positivity : (0 : ℝ) ≤ ε⁻¹)
  refine hZ.trans ?_
  refine ENNReal.ofReal_le_ofReal ?_
  calc ((4 : ℝ) ^ i * A) * (Real.exp (2 * (2 * c + δ)) * A)
        * Work.FTS.StrongEps.EpsSq α f
      ≤ (Cv * ε⁻¹ ^ (2 * (j + i))) * Work.FTS.StrongEps.EpsSq α f :=
        mul_le_mul_of_nonneg_right hconst (Work.FTS.StrongEps.EpsSq_nonneg α f)
    _ ≤ (Cv * (Cv / ε) ^ (2 * (j + i))) * Work.FTS.StrongEps.EpsSq α f :=
        mul_le_mul_of_nonneg_right hCeps (Work.FTS.StrongEps.EpsSq_nonneg α f)

end

end Work.FTS.StrongEps.EpsSqTools
