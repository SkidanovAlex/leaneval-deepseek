/-
Copyright: work module for the Elgindi finite-time singularity project.

# `HkMem_Jeps`: `J_ε` preserves the weighted spaces `ℋ^k`

The log-coordinate mollifier `Jeps ρ ε` of `Submission/Work/FTS/StrongEps/Basic.lean` maps
`Work.Spaces.HkMem α k` into itself: if `f` is `C^n` on the open quadrant for every `n` and
`HkMem α k f`, then `HkMem α k (Jeps ρ ε f)`.

`HkMem` is integrability of the two iterated integrals of the weighted `H^k`-integrand, so the
proof has two halves.

* **The angular slices.**  For `z > 0` the `ℝ≥0∞`-valued pointwise bound `ofReal_GJ_le`
  (`HkSqAux/Chain.lean`) dominates `ofReal (HkIntegrand α k (J_ε f) z θ)` by the `p`-integral of
  the shifted weighted integrand of `f`; Tonelli (with the pair measurability
  `JepsHkMem.aemeasurable_pair_slice`) exchanges `θ` and `p`, the `θ`-shift is bounded by
  `JepsHkMem.lintegral_thShift_le`, the remaining `θ`-integral is `ofReal` of the honest slice
  integral of `f` (finite for *every* `z' ∈ Iz` because `HkMem α k f` holds), and the
  `p`-integral is finite by `JepsHkMem.Jker_comp_zShift_lt_top` (the shift `p₁ ↦ z e^{-p₁}`
  is a change of variables on the support `|p₁| ≤ ε`, using the total integral of `f`'s slice
  norm).  At `z = 0` the integrand vanishes identically.
* **The `z`-integral.**  `ofReal (∫ θ, HkIntegrand (J_ε f) z θ)` is bounded by the double
  `lintegral` `JepsHkMem.lintegral_HkIntegrand_Jeps_lt_top`, and the second `HkMem` component
  follows from `JepsHkMem.integrableOn_sliceIntegral_of_lintegral_lt_top`.

The a.e. strong measurability of the integrand (both jointly and slicewise) is in
`Submission/Work/FTS/StrongEps/JepsHkMem/AuxMeas.lean`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.StrongEps.Basic
import Submission.Work.FTS.StrongEps.Kernel
import Submission.Work.FTS.StrongEps.mixed_Jeps
import Submission.Work.FTS.StrongEps.HkSq_Jeps_le
import Submission.Work.FTS.StrongEps.HkSqAux.Defs
import Submission.Work.FTS.StrongEps.HkSqAux.logJac_shift_le
import Submission.Work.FTS.StrongEps.HkSqAux.HkIntegrand_Jeps_le_integral
import Submission.Work.FTS.StrongEps.HkSqAux.Chain
import Submission.Work.FTS.StrongEps.HkSqAux.continuousOn_HkIntegrand_Quad
import Submission.Work.FTS.StrongEps.JepsHkMem.AuxMeas
import Submission.Work.FTS.StrongEps.JepsHkMem.lintegral_thShift_le
import Submission.Work.FTS.StrongEps.JepsHkMem.Jker_comp_zShift_lt_top
import Submission.Work.FTS.StrongEps.JepsHkMem.aemeasurable_pair_slice
import Submission.Work.FTS.StrongEps.JepsHkMem.integrableOn_sliceIntegral_of_lintegral_lt_top
import Submission.Work.FTS.StrongEps.JepsHkMem.lintegral_HkIntegrand_Jeps_lt_top

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps

open scoped Real Topology
open MeasureTheory Set Filter

set_option maxHeartbeats 1000000

/-! ## The main theorem -/

theorem HkMem_Jeps {ρ : ℝ × ℝ → ℝ} (hρ : IsMollKernel ρ) {α : ℝ}
    (hα : α ∈ Set.Ioc 0 1) {k : ℕ} {ε : ℝ} (hε : 0 < ε) {f : ℝ → ℝ → ℝ}
    (hsm : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Quad)
    (hmem : Work.Spaces.HkMem α k f) :
    Work.Spaces.HkMem α k (Jeps ρ ε f) := by
  -- the two weight-shift constants
  obtain ⟨cη, hcηpos, hWη0⟩ := HkSqAux.wdiv_shift_le
  obtain ⟨cγ, hcγpos, hWγ0⟩ := HkSqAux.Wt_shift_le
  set c : ℝ := max cη cγ with hcdef
  have hc0 : 0 ≤ c := le_of_lt (lt_of_lt_of_le hcηpos (le_max_left _ _))
  have hWη : ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo 0 (π / 2) → ∀ p : ℝ × ℝ,
      Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2)
        ≤ Real.exp (c * (|p.1| + |p.2|))
          * (Work.Spaces.w (zShift z p.1)
              / (Real.sin (2 * thShift θ p.2)) ^ (Work.Spaces.eta / 2)) := by
    intro z θ hz hθ p
    refine (hWη0 z θ p.1 p.2 hz hθ).trans (mul_le_mul_of_nonneg_right ?_ ?_)
    · exact Real.exp_le_exp.mpr
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity))
    · exact div_nonneg (Work.FTS.StrongEps.w_nonneg _)
        (Real.rpow_nonneg (le_of_lt (sin_two_pos (thShift_mem hθ))) _)
  have hWγ : ∀ z θ : ℝ, 0 < z → θ ∈ Set.Ioo 0 (π / 2) → ∀ p : ℝ × ℝ,
      Work.Spaces.Wt α z θ
        ≤ Real.exp (c * (|p.1| + |p.2|))
          * Work.Spaces.Wt α (zShift z p.1) (thShift θ p.2) := by
    intro z θ hz hθ p
    exact (hWγ0 α hα z θ p.1 p.2 hz hθ).trans (mul_le_mul_of_nonneg_right
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)))
      (mul_nonneg (Work.FTS.StrongEps.w_nonneg _)
        (Real.rpow_nonneg (le_of_lt (sin_two_pos (thShift_mem hθ))) _)))
  -- continuity of the integrand of `f` on the open quadrant
  have hcontf : ContinuousOn (fun q : ℝ × ℝ => Work.Spaces.HkIntegrand α k f q.1 q.2) Quad :=
    HkSqAux.continuousOn_HkIntegrand_Quad α k hsm
  -- the pointwise bound in `ℝ≥0∞`
  have hpt : ∀ z ∈ Work.Spaces.Iz, ∀ θ ∈ Work.Spaces.Iθ,
      ENNReal.ofReal (Work.Spaces.HkIntegrand α k (Jeps ρ ε f) z θ)
        ≤ ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Jker ρ ε p)
            * ENNReal.ofReal (Real.exp (2 * c * (|p.1| + |p.2|)))
            * ENNReal.ofReal (Work.Spaces.HkIntegrand α k f (zShift z p.1) (thShift θ p.2)) :=
    fun z hz θ hθ => HkSqAux.ofReal_GJ_le ρ hρ hε hα hsm hWη hWγ hz hθ k
  -- the finiteness of each angular slice
  have hslice_fin : ∀ z ∈ Work.Spaces.Iz,
      (∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal (Work.Spaces.HkIntegrand α k (Jeps ρ ε f) z θ)) < ⊤ := by
    intro z hz
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with hz0 | hzpos
    · rw [← hz0]
      have hzero : (fun θ : ℝ => ENNReal.ofReal (Work.Spaces.HkIntegrand α k (Jeps ρ ε f) 0 θ))
          = fun _ => 0 := by
        funext θ
        simp only [Work.Spaces.HkIntegrand, Work.Spaces.w, Work.Spaces.Wt]
        simp
      rw [hzero]
      simp
    · -- measurability of the pair `(θ, p) ↦ kernel · shifted integrand`
      have hpair : AEMeasurable (fun q : ℝ × (ℝ × ℝ) =>
          ENNReal.ofReal (Jker ρ ε q.2)
            * ENNReal.ofReal (Real.exp (2 * c * (|q.2.1| + |q.2.2|)))
            * ENNReal.ofReal (Work.Spaces.HkIntegrand α k f (zShift z q.2.1)
                (thShift q.1 q.2.2)))
          ((MeasureTheory.volume.restrict Work.Spaces.Iθ).prod MeasureTheory.volume) :=
        JepsHkMem.aemeasurable_pair_slice hcontf hρ.cont hzpos
      set G : ℝ → ENNReal := fun z' => ∫⁻ θ in Work.Spaces.Iθ,
        ENNReal.ofReal (Work.Spaces.HkIntegrand α k f z' θ) with hGdef
      have hGmeas : AEMeasurable (fun p₁ : ℝ => G (z * Real.exp (-p₁))) MeasureTheory.volume :=
        (JepsHkMem.aemeasurable_shift_z_pair hcontf hzpos).lintegral_prod_right'
      have hGfin : (∫⁻ z' in Set.Ioi 0, G z') < ⊤ := by
        have hHk : ENNReal.ofReal (Work.Spaces.HkSq α k f)
            = ∫⁻ z' in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
                ENNReal.ofReal (Work.Spaces.HkIntegrand α k f z' θ) := by
          rw [Work.Spaces.HkSq]
          rw [MeasureTheory.ofReal_integral_eq_lintegral_ofReal hmem.2
            (Eventually.of_forall fun z' => integral_nonneg fun θ =>
              Work.Spaces.HkIntegrand_nonneg α k f z' θ)]
          exact MeasureTheory.setLIntegral_congr_fun measurableSet_Ici (fun z' hz' =>
            MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hmem.1 z' hz')
              (Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α k f z' θ))
        have hIoi : (∫⁻ z' in Set.Ioi 0, ∫⁻ θ in Work.Spaces.Iθ,
              ENNReal.ofReal (Work.Spaces.HkIntegrand α k f z' θ))
            = ∫⁻ z' in Work.Spaces.Iz, ∫⁻ θ in Work.Spaces.Iθ,
              ENNReal.ofReal (Work.Spaces.HkIntegrand α k f z' θ) :=
          MeasureTheory.setLIntegral_congr (f := fun z' : ℝ => ∫⁻ θ in Work.Spaces.Iθ,
            ENNReal.ofReal (Work.Spaces.HkIntegrand α k f z' θ))
            (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := 0))
        rw [hIoi, ← hHk]
        exact ENNReal.ofReal_lt_top
      -- the constant dominating the kernel factor
      set D : ℝ := Real.exp (4 * c * ε) * Real.exp (3 * ε) with hDdef
      have hD0 : 0 ≤ D := by rw [hDdef]; positivity
      have hkern : ∀ p : ℝ × ℝ,
          ENNReal.ofReal (Jker ρ ε p) * ENNReal.ofReal (Real.exp (2 * c * (|p.1| + |p.2|)))
              * ENNReal.ofReal (Real.exp (3 * |p.2|))
            ≤ ENNReal.ofReal D * ENNReal.ofReal (Jker ρ ε p) := by
        intro p
        rcases eq_or_ne (Jker ρ ε p) 0 with hp | hp
        · simp [hp]
        · have hb : |p.2| ≤ ε := by
            have h := Jker_ne_zero_support hρ hε hp
            have h2 : p.2 ^ 2 ≤ ε ^ 2 := by nlinarith [sq_nonneg p.1]
            rw [sq_le_sq] at h2
            rwa [abs_of_nonneg hε.le] at h2
          have h1 : Real.exp (2 * c * (|p.1| + |p.2|)) ≤ Real.exp (4 * c * ε) := by
            rw [Real.exp_le_exp]
            have hsupp := HkSqAux.Jker_support_abs hρ hε hp
            nlinarith [hc0, abs_nonneg p.1, abs_nonneg p.2]
          have h2 : Real.exp (3 * |p.2|) ≤ Real.exp (3 * ε) := by
            rw [Real.exp_le_exp]
            linarith [mul_le_mul_of_nonneg_left hb (by norm_num : (0 : ℝ) ≤ 3)]
          have hprod : Real.exp (2 * c * (|p.1| + |p.2|)) * Real.exp (3 * |p.2|) ≤ D := by
            rw [hDdef]
            exact mul_le_mul h1 h2 (Real.exp_pos _).le (Real.exp_pos _).le
          have hjk : 0 ≤ Jker ρ ε p := HkSqAux.Jker_nonneg ρ hρ ε p
          have hmul : Jker ρ ε p * Real.exp (2 * c * (|p.1| + |p.2|)) * Real.exp (3 * |p.2|)
              ≤ D * Jker ρ ε p := by
            rw [mul_assoc, mul_comm D (Jker ρ ε p)]
            exact mul_le_mul_of_nonneg_left hprod hjk
          calc ENNReal.ofReal (Jker ρ ε p)
                * ENNReal.ofReal (Real.exp (2 * c * (|p.1| + |p.2|)))
                * ENNReal.ofReal (Real.exp (3 * |p.2|))
              = ENNReal.ofReal (Jker ρ ε p * Real.exp (2 * c * (|p.1| + |p.2|))
                  * Real.exp (3 * |p.2|)) := by
                rw [ENNReal.ofReal_mul (mul_nonneg hjk (Real.exp_pos _).le),
                  ENNReal.ofReal_mul hjk]
            _ ≤ ENNReal.ofReal (D * Jker ρ ε p) := ENNReal.ofReal_le_ofReal hmul
            _ = ENNReal.ofReal D * ENNReal.ofReal (Jker ρ ε p) :=
                ENNReal.ofReal_mul (p := D) hD0
      -- the chain of inequalities
      have hchain : (∫⁻ θ in Work.Spaces.Iθ,
            ENNReal.ofReal (Work.Spaces.HkIntegrand α k (Jeps ρ ε f) z θ))
          ≤ ENNReal.ofReal D * (∫⁻ p : ℝ × ℝ,
              ENNReal.ofReal (Jker ρ ε p) * G (zShift z p.1)) := by
        calc (∫⁻ θ in Work.Spaces.Iθ,
              ENNReal.ofReal (Work.Spaces.HkIntegrand α k (Jeps ρ ε f) z θ))
            ≤ (∫⁻ θ in Work.Spaces.Iθ, ∫⁻ p : ℝ × ℝ, ENNReal.ofReal (Jker ρ ε p)
                * ENNReal.ofReal (Real.exp (2 * c * (|p.1| + |p.2|)))
                * ENNReal.ofReal (Work.Spaces.HkIntegrand α k f (zShift z p.1)
                    (thShift θ p.2))) :=
              MeasureTheory.setLIntegral_mono' measurableSet_Icc
                (fun θ hθ => hpt z hzpos.le θ hθ)
          _ = (∫⁻ p : ℝ × ℝ, (ENNReal.ofReal (Jker ρ ε p)
                * ENNReal.ofReal (Real.exp (2 * c * (|p.1| + |p.2|))))
                * (∫⁻ θ in Work.Spaces.Iθ,
                    ENNReal.ofReal (Work.Spaces.HkIntegrand α k f (zShift z p.1)
                      (thShift θ p.2)))) := by
              rw [MeasureTheory.lintegral_lintegral_swap
                (μ := MeasureTheory.volume.restrict Work.Spaces.Iθ)
                (ν := MeasureTheory.volume) hpair]
              refine lintegral_congr fun p => ?_
              exact MeasureTheory.lintegral_const_mul' _
                (fun θ : ℝ => ENNReal.ofReal (Work.Spaces.HkIntegrand α k f (zShift z p.1)
                  (thShift θ p.2)))
                (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top)
          _ ≤ (∫⁻ p : ℝ × ℝ, (ENNReal.ofReal (Jker ρ ε p)
                * ENNReal.ofReal (Real.exp (2 * c * (|p.1| + |p.2|))))
                * (ENNReal.ofReal (Real.exp (3 * |p.2|))
                    * (∫⁻ θ in Work.Spaces.Iθ,
                        ENNReal.ofReal (Work.Spaces.HkIntegrand α k f (zShift z p.1) θ)))) := by
              refine lintegral_mono fun p => ?_
              exact mul_le_mul_right
                (JepsHkMem.lintegral_thShift_le
                  (fun θ => ENNReal.ofReal (Work.Spaces.HkIntegrand α k f (zShift z p.1) θ))
                  p.2) _
          _ = (∫⁻ p : ℝ × ℝ, (ENNReal.ofReal (Jker ρ ε p)
                * ENNReal.ofReal (Real.exp (2 * c * (|p.1| + |p.2|)))
                * ENNReal.ofReal (Real.exp (3 * |p.2|))) * G (zShift z p.1)) := by
              refine lintegral_congr fun p => ?_
              have hAz : (∫⁻ θ in Work.Spaces.Iθ,
                    ENNReal.ofReal (Work.Spaces.HkIntegrand α k f (zShift z p.1) θ))
                  = ENNReal.ofReal (∫ θ in Work.Spaces.Iθ,
                      Work.Spaces.HkIntegrand α k f (zShift z p.1) θ) :=
                (MeasureTheory.ofReal_integral_eq_lintegral_ofReal
                  (hmem.1 _ (zShift_pos hzpos).le)
                  (Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α k f _ θ)).symm
              simp only [hGdef]
              simp only [mul_assoc]
          _ ≤ ENNReal.ofReal D * (∫⁻ p : ℝ × ℝ,
                ENNReal.ofReal (Jker ρ ε p) * G (zShift z p.1)) := by
              rw [← MeasureTheory.lintegral_const_mul' (ENNReal.ofReal D)
                (fun p : ℝ × ℝ => ENNReal.ofReal (Jker ρ ε p) * G (zShift z p.1))
                ENNReal.ofReal_ne_top]
              refine lintegral_mono fun p => ?_
              calc (ENNReal.ofReal (Jker ρ ε p)
                    * ENNReal.ofReal (Real.exp (2 * c * (|p.1| + |p.2|)))
                    * ENNReal.ofReal (Real.exp (3 * |p.2|))) * G (zShift z p.1)
                  ≤ (ENNReal.ofReal D * ENNReal.ofReal (Jker ρ ε p)) * G (zShift z p.1) :=
                    mul_le_mul_left (hkern p) _
                _ = ENNReal.ofReal D * (ENNReal.ofReal (Jker ρ ε p) * G (zShift z p.1)) := by
                    rw [mul_assoc]
      refine lt_of_le_of_lt hchain (ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_)
      exact JepsHkMem.Jker_comp_zShift_lt_top hρ hε hzpos hGmeas hGfin
  -- membership in each slice
  have hSliceInt : ∀ z ∈ Work.Spaces.Iz,
      IntegrableOn (fun θ => Work.Spaces.HkIntegrand α k (Jeps ρ ε f) z θ)
        Work.Spaces.Iθ := by
    intro z hz
    rcases eq_or_lt_of_le (show (0 : ℝ) ≤ z from hz) with hz0 | hzpos
    · rw [← hz0]
      have hzero : (fun θ : ℝ => Work.Spaces.HkIntegrand α k (Jeps ρ ε f) 0 θ) = fun _ => 0 := by
        funext θ
        simp only [Work.Spaces.HkIntegrand, Work.Spaces.w, Work.Spaces.Wt]
        simp
      rw [hzero]
      exact integrableOn_zero
    · refine ⟨JepsHkMem.aestronglyMeasurable_HkIntegrand_Jeps_slice hρ hε hsm hzpos, ?_⟩
      rw [hasFiniteIntegral_iff_enorm]
      refine lt_of_le_of_lt (lintegral_mono fun θ => ?_) (hslice_fin z hzpos.le)
      rw [Real.enorm_eq_ofReal (Work.Spaces.HkIntegrand_nonneg α k (Jeps ρ ε f) z θ)]
  exact ⟨hSliceInt,
    JepsHkMem.integrableOn_sliceIntegral_of_lintegral_lt_top
      (fun z θ => Work.Spaces.HkIntegrand_nonneg α k (Jeps ρ ε f) z θ) hSliceInt
      (JepsHkMem.aestronglyMeasurable_HkIntegrand_Jeps hρ hε hsm)
      (JepsHkMem.lintegral_HkIntegrand_Jeps_lt_top hρ hα hε hsm hmem)⟩

end Work.FTS.StrongEps
