import Submission.SqueezeCore
import Mathlib.Tactic

/-! # Child task: uniform log-kernel bound for the Serre measure.

Prove the lemma `uniform_abs_log_kernel_bound` below (whose statement mirrors
`Submission.SqueezeCore.uniform_abs_log_kernel_bound`).  You may add any helper
lemmas **in this file**, in namespace `Submission.SqzKernel`.  Useful available
tools (all already imported through `Submission.SqueezeCore`):

* the single-variable integrability facts
  `Submission.SqueezeCore.integrable_abs_log_sub (x : ℝ)`,
  `Submission.PotentialContinuity.logAbs_bound_far`,
  `Submission.PotentialContinuity.local_log_bound`,
  with `Kloc`, `Cmu_pos`, `muS` = the Serre measure (same as `muSerre` up to
  definitional equality), `aSerre`, `bSerre` (`aSerre ≤ bSerre`, interval
  contained in `(0,∞)`, `muSerre (Set.Icc aSerre bSerre) = 1`);
* the identity `muSerre` = the measure used by `PotentialContinuity.logAbs_bound_far`
  (`muS`), `Submission.SqueezeCore.muSerre_Icc` etc.

## What to prove

    ∃ C : ℝ, 0 ≤ C ∧
      ∀ x : ℝ, x ∈ Set.Icc aSerre bSerre →
        (∫ y : ℝ, |Real.log (|x - y|)| ∂muSerre) ≤ C

Suggested route: split `∫_y |log|x−y||` = (integral over `{y | |x−y| ≤ 1}`) +
(integral over `{y | |x−y| > 1}`).  The first is controlled by
`local_log_bound` with `r = 1` (the bound `Kloc·√1·(2 + |log 1|)`), valid for
every centre `x` and w.r.t. `muS`; rewrite measure to `muSerre`.  The second:
for `y ∈ [aSerre,bSerre]` use `logAbs_bound_far`, outside the interval the
integrand's mass is 0 (`muSerre_compl_Icc`); bound `|x| ≤ bSerre` for `x` in
the interval.  Combine.
-/

noncomputable section

open MeasureTheory Polynomial
open scoped Real BigOperators ENNReal Topology

namespace Submission.SqzKernel

open Submission.SqueezeCore
open Submission.Contracts
open Submission.SerreExample
open Submission.PotentialContinuity
open Filter

/-- Near-field estimate: `∫_{|y-x| ≤ 1} |log|x−y|| dμ` is bounded uniformly in `x`. -/
lemma near_log_kernel_bound (x : ℝ) :
    (∫ y : ℝ, Set.indicator {y : ℝ | |y - x| ≤ 1} (fun y : ℝ => |Real.log (|x - y|)|) y ∂muSerre)
      ≤ Kloc * (Real.sqrt 1 * (2 + |Real.log 1|)) := by
  have hLL := local_log_bound x (r := 1) (by norm_num : (0 : ℝ) < 1) (by norm_num : (1 : ℝ) ≤ 1)
  have hLL' : (∫ y : ℝ, Set.indicator {y : ℝ | |y - x| ≤ 1} (fun y : ℝ => |Real.log (|y - x|)|) y ∂muSerre)
      ≤ Kloc * (Real.sqrt 1 * (2 + |Real.log 1|)) := by
    simpa [muSerre] using hLL
  convert hLL' using 1
  · apply MeasureTheory.integral_congr_ae
    refine Eventually.of_forall (fun t => ?_)
    by_cases ht : t ∈ {y : ℝ | |y - x| ≤ 1}
    · rw [Set.indicator_of_mem ht]
      rw [Set.indicator_of_mem ht]
      congr 1
      rw [abs_sub_comm]
    · simp [ht]

/-- Far-field estimate: `∫_{1 < |y-x|} |log|x−y|| dμ ≤ |x| + |aSerre| + |bSerre| + 1`.
The only singular support of μ is `[aSerre, bSerre]`, on which `logAbs_bound_far`
bounds the kernel whenever `|x-y| ≥ 1`. -/
lemma far_log_kernel_bound (x : ℝ) :
    (∫ y : ℝ, Set.indicator {y : ℝ | 1 < |y - x|} (fun y : ℝ => |Real.log (|x - y|)|) y ∂muSerre)
      ≤ |x| + |aSerre| + |bSerre| + 1 := by
  let S : Set ℝ := {y : ℝ | 1 < |y - x|} ∩ Set.Icc aSerre bSerre
  let Kx : ℝ := |x| + |aSerre| + |bSerre| + 1
  have hfint : Integrable (fun y : ℝ => |Real.log (|x - y|)|) muSerre := integrable_abs_log_sub x
  have hSmeas : MeasurableSet S := by
    dsimp [S]
    refine MeasurableSet.inter ?_ isClosed_Icc.measurableSet
    have h : {y : ℝ | 1 < |y - x|} = (fun y : ℝ => |y - x|) ⁻¹' (Set.Ioi 1) := by
      ext y; simp
    rw [h]
    exact measurableSet_Ioi.preimage (by fun_prop)
  have hfg_ae :
      (Set.indicator {y : ℝ | 1 < |y - x|} (fun y : ℝ => |Real.log (|x - y|)|)) =ᵐ[muSerre]
        Set.indicator S (fun y : ℝ => |Real.log (|x - y|)|) := by
    apply MeasureTheory.mem_ae_iff.mpr
    have hsubset : {t : ℝ |
        Set.indicator {y : ℝ | 1 < |y - x|} (fun y : ℝ => |Real.log (|x - y|)|) t ≠
          Set.indicator S (fun y : ℝ => |Real.log (|x - y|)|) t} ⊆ (Set.Icc aSerre bSerre)ᶜ := by
      intro t ht
      rw [Set.mem_compl_iff]
      intro htI
      have hagree :
          Set.indicator {y : ℝ | 1 < |y - x|} (fun y : ℝ => |Real.log (|x - y|)|) t =
            Set.indicator S (fun y : ℝ => |Real.log (|x - y|)|) t := by
        dsimp [S]
        by_cases hfarb : 1 < |t - x|
        · simp [hfarb, htI]
        · simp [hfarb, htI]
      exact ht hagree
    have hle : muSerre {t : ℝ |
        Set.indicator {y : ℝ | 1 < |y - x|} (fun y : ℝ => |Real.log (|x - y|)|) t ≠
          Set.indicator S (fun y : ℝ => |Real.log (|x - y|)|) t} ≤ 0 := by
      calc
        muSerre {t : ℝ |
            Set.indicator {y : ℝ | 1 < |y - x|} (fun y : ℝ => |Real.log (|x - y|)|) t ≠
              Set.indicator S (fun y : ℝ => |Real.log (|x - y|)|) t}
            ≤ muSerre (Set.Icc aSerre bSerre)ᶜ := measure_mono hsubset
        _ = 0 := muSerre_compl_Icc
    exact le_antisymm hle (zero_le : (0 : ℝ≥0∞) ≤ muSerre {t : ℝ |
        Set.indicator {y : ℝ | 1 < |y - x|} (fun y : ℝ => |Real.log (|x - y|)|) t ≠
          Set.indicator S (fun y : ℝ => |Real.log (|x - y|)|) t})
  calc
    (∫ y : ℝ, Set.indicator {y : ℝ | 1 < |y - x|} (fun y : ℝ => |Real.log (|x - y|)|) y ∂muSerre)
        = (∫ y : ℝ, Set.indicator S (fun y : ℝ => |Real.log (|x - y|)|) y ∂muSerre) := by
          exact MeasureTheory.integral_congr_ae hfg_ae
    _ ≤ (∫ y : ℝ, Set.indicator S (fun _ : ℝ => Kx) y ∂muSerre) := by
          have hcst_int : Integrable (fun _ : ℝ => (Kx : ℝ)) muSerre := integrable_const Kx
          refine MeasureTheory.integral_mono_ae
            (Integrable.indicator hfint hSmeas) (Integrable.indicator hcst_int hSmeas) ?_
          refine Eventually.of_forall (fun t => ?_)
          by_cases ht : t ∈ S
          · have htc : t ∈ Set.Icc aSerre bSerre := by
              dsimp [S] at ht
              exact ht.2
            have hfar1 : 1 < |t - x| := by
              dsimp [S] at ht
              exact ht.1
            have hfar : 1 ≤ |x - t| := by
              rw [abs_sub_comm]
              exact le_of_lt hfar1
            have hb := logAbs_bound_far x t htc hfar
            simpa [Kx, ht] using hb
          · have hz1 : Set.indicator S (fun y : ℝ => |Real.log (|x - y|)|) t = 0 := by simp [ht]
            have hz2 : Set.indicator S (fun _ : ℝ => Kx) t = 0 := by simp [ht]
            rw [hz1, hz2]
    _ ≤ Kx := by
          rw [MeasureTheory.integral_indicator hSmeas]
          rw [MeasureTheory.setIntegral_const]
          simp [MeasureTheory.measureReal_def]
          have hmono1 : muSerre S ≤ 1 := by
            calc
              muSerre S ≤ muSerre (Set.Icc aSerre bSerre) := by
                exact measure_mono (by intro y hy; exact hy.2)
              _ = 1 := muSerre_Icc
          have htoReal : (muSerre S).toReal ≤ 1 := by
            have hfinS : muSerre S ≠ ∞ := ne_of_lt (lt_of_le_of_lt hmono1 (by simp : (1 : ℝ≥0∞) < ∞))
            have hle := (ENNReal.toReal_le_toReal hfinS (by simp : (1 : ℝ≥0∞) ≠ ∞)).2 hmono1
            simpa using hle
          have hKx0 : 0 ≤ Kx := by
            dsimp [Kx]
            positivity
          nlinarith

/-- Pointwise decomposition of the kernel into near and far pieces. -/
lemma abs_log_kernel_decomp (x : ℝ) :
    (∫ y : ℝ, |Real.log (|x - y|)| ∂muSerre)
      = (∫ y : ℝ, Set.indicator {z : ℝ | |z - x| ≤ 1} (fun z : ℝ => |Real.log (|x - z|)|) y ∂muSerre)
        + (∫ y : ℝ, Set.indicator {z : ℝ | 1 < |z - x|} (fun z : ℝ => |Real.log (|x - z|)|) y ∂muSerre) := by
  let g : ℝ → ℝ := fun y : ℝ => |Real.log (|x - y|)|
  let N : Set ℝ := {z : ℝ | |z - x| ≤ 1}
  let F : Set ℝ := {z : ℝ | 1 < |z - x|}
  have hg : (fun y : ℝ => Set.indicator N g y + Set.indicator F g y) = g := by
    funext y
    by_cases hN : |y - x| ≤ 1
    · have hF : ¬ 1 < |y - x| := by linarith
      dsimp [g, N, F]
      simp [hN, hF]
    · have hF : 1 < |y - x| := by linarith
      dsimp [g, N, F]
      simp [hN, hF]
  have hg_int : Integrable g muSerre := by
    dsimp [g]
    exact integrable_abs_log_sub x
  have hNmeas : MeasurableSet N := by
    dsimp [N]
    exact GenericLocalLog.ball_measurableSet x 1
  have hFmeas : MeasurableSet F := by
    dsimp [F]
    have h : {z : ℝ | 1 < |z - x|} = (fun z : ℝ => |z - x|) ⁻¹' (Set.Ioi 1) := by
      ext z; simp
    rw [h]
    exact measurableSet_Ioi.preimage (by fun_prop)
  calc
    (∫ y : ℝ, g y ∂muSerre) = (∫ y : ℝ, Set.indicator N g y + Set.indicator F g y ∂muSerre) := by
      rw [hg]
    _ = (∫ y : ℝ, Set.indicator N g y ∂muSerre) + (∫ y : ℝ, Set.indicator F g y ∂muSerre) := by
      exact MeasureTheory.integral_add (Integrable.indicator hg_int hNmeas) (Integrable.indicator hg_int hFmeas)

lemma uniform_abs_log_kernel_bound :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ x : ℝ, x ∈ Set.Icc aSerre bSerre →
        (∫ y : ℝ, |Real.log (|x - y|)| ∂muSerre) ≤ C := by
  let Cnear : ℝ := Kloc * (Real.sqrt 1 * (2 + |Real.log 1|))
  let Cfarb : ℝ := |bSerre| + |aSerre| + |bSerre| + 1
  refine ⟨Cnear + Cfarb, ?_, ?_⟩
  · have hKloc0 : 0 ≤ Kloc := by
      dsimp [Kloc]
      exact mul_nonneg (by linarith [Cmu_pos]) (by norm_num)
    have hCnear0 : 0 ≤ Cnear := by
      dsimp [Cnear]
      have hsqrt1 : Real.sqrt 1 = 1 := by simp
      have hlog1 : Real.log 1 = 0 := by simp
      rw [hsqrt1, hlog1]
      norm_num
      nlinarith [hKloc0]
    have hCfarb0 : 0 ≤ Cfarb := by
      dsimp [Cfarb]
      positivity
    nlinarith
  · intro x hx
    have hxpos : 0 < x := lt_of_lt_of_le aSerre_pos hx.1
    have habsx : |x| ≤ |bSerre| := by
      rw [abs_of_pos hxpos, abs_of_pos bSerre_pos]
      exact hx.2
    calc
      (∫ y : ℝ, |Real.log (|x - y|)| ∂muSerre)
          = (∫ y : ℝ, Set.indicator {z : ℝ | |z - x| ≤ 1} (fun z : ℝ => |Real.log (|x - z|)|) y ∂muSerre)
            + (∫ y : ℝ, Set.indicator {z : ℝ | 1 < |z - x|} (fun z : ℝ => |Real.log (|x - z|)|) y ∂muSerre) :=
              abs_log_kernel_decomp x
      _ ≤ Cnear + (|x| + |aSerre| + |bSerre| + 1) := by
            exact add_le_add (near_log_kernel_bound x) (far_log_kernel_bound x)
      _ ≤ Cnear + Cfarb := by
            dsimp [Cfarb]
            nlinarith [habsx]
      _ = Cnear + Cfarb := rfl

end Submission.SqzKernel
