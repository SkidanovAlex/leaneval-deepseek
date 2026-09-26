/-
# The cusp-`i∞` expansion of the kernel on the tangency-arc region `arcT`

The last piece of the `arcT`-analysis: on the tangency-arc region the difference between the
CKMRV kernel along the contour and its non-decaying part `Aexp` decays like `e^{-πt}`, uniformly
for `τ ∈ arcT` and `t ≥ 1`.

## Architecture

* the *large-`t`* part is the already proved expansion `Work.Asymptotics.kernel_axis_bound`,
  which needs only a *compact* parameter set `K ⊆ ℍ` (no `K ⊆ 𝒟` hypothesis); we apply it to
  `K = closure arcT`, which is compact (`Work.Asymptotics.isCompact_closure_arcT'`);
* the *small-`t`* part `1 ≤ t ≤ max T 1` is the boundedness statement
  `Work.Asymptotics.arcT_smallT` of the module `Submission/Work/Asymptotics/arcT_smallT.lean`,
  where the grazing analysis of the region is carried out: the only poles of
  `z ↦ Kfun ℓ d τ z` that meet the contour `iℝ` in the closure of `arcT` lie on the two
  tangency arcs, where they are removable
  (`Work.Asymptotics.Graze.key_bound_arc'` at the tangency points and
  `Work.Asymptotics.graze_branch_bound` along the grazing branches);
  the two parts are glued by absorbing the bound of the compact window into the constants.
-/
import Mathlib
import Submission.Work.Asymptotics.arcRegion
import Submission.Work.Asymptotics.F2LayerDefs
import Submission.Work.Asymptotics.GcuspDefs
import Submission.Work.HFN.cuspExpansionKernel
import Submission.Work.Asymptotics.arcT_smallT

noncomputable section

open UpperHalfPlane ModularGroup
open scoped MatrixGroups UpperHalfPlane Topology

namespace Work.HFN
open Work.Asymptotics  -- ck-hfn-fix: fork moved out of Work.Asymptotics

/-- **The cusp-`i∞` expansion of the kernel on the tangency-arc region.** -/
theorem arcT_tail (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24) :
    ∃ C M T₀ : ℝ, 0 < C ∧ 0 ≤ M ∧ 0 ≤ T₀ ∧ ∀ (τ : UpperHalfPlane) (t : ℝ),
      τ ∈ Work.Asymptotics.arcT → 1 ≤ t →
        ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
          - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t‖
          ≤ C * (1 + t) ^ M * Real.exp (-(Real.pi * (t - T₀))) := by
  -- the large-`t` part: the expansion on the compact set `closure arcT`
  obtain ⟨C₁, M₁, T₁, hC₁, hM₁, hT₁, hb₁⟩ :=
    kernel_axis_bound ℓ d hd (K := closure (arcT : Set ℍ)) isCompact_closure_arcT'
  -- the small-`t` part
  obtain ⟨B, hB0, hB⟩ := arcT_smallT ℓ d hd (max T₁ 1) (le_max_right _ _)
  have hT₁pos : 1 ≤ max T₁ 1 := le_max_right _ _
  refine ⟨max C₁ (B * Real.exp (Real.pi * max T₁ 1) + 1), max M₁ 0, 0,
    lt_of_lt_of_le hC₁ (le_max_left _ _), le_max_right _ _, le_refl 0, ?_⟩
  intro τ t hτ ht
  rcases le_or_gt (max T₁ 1) t with ht' | ht'
  · -- large `t`: the expansion, with the `e^{-π(t-T₀)}` renormalised to `T₀ = 0`
    have hbig := hb₁ τ (subset_closure hτ) t (le_trans (le_max_left _ _) ht')
    refine le_trans hbig ?_
    have h1 : (1 + t) ^ M₁ ≤ (1 + t) ^ max M₁ 0 :=
      Real.rpow_le_rpow_of_exponent_le (by linarith) (le_max_left _ _)
    have h2 : (0 : ℝ) ≤ (1 + t) ^ max M₁ 0 := Real.rpow_nonneg (by linarith) _
    have h3 : (0 : ℝ) < Real.exp (-(Real.pi * t)) := Real.exp_pos _
    have h4 : Real.exp (-(Real.pi * (t - 0))) = Real.exp (-(Real.pi * t)) := by ring_nf
    rw [h4]
    calc C₁ * (1 + t) ^ M₁ * Real.exp (-(Real.pi * t))
        ≤ C₁ * (1 + t) ^ max M₁ 0 * Real.exp (-(Real.pi * t)) := by
          exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hC₁.le) h3.le
      _ ≤ max C₁ (B * Real.exp (Real.pi * max T₁ 1) + 1) * (1 + t) ^ max M₁ 0
            * Real.exp (-(Real.pi * t)) := by
          refine mul_le_mul_of_nonneg_right ?_ h3.le
          exact mul_le_mul_of_nonneg_right (le_max_left _ _) h2
  · -- small `t`: absorb the constant bound into the prefactor
    have htsmall := hB τ t hτ ht (le_of_lt ht')
    refine le_trans htsmall ?_
    have h1 : (1 : ℝ) ≤ (1 + t) ^ max M₁ 0 := Real.one_le_rpow (by linarith) (le_max_right _ _)
    have h2 : (0 : ℝ) ≤ (1 + t) ^ max M₁ 0 := Real.rpow_nonneg (by linarith) _
    have h3 : Real.exp (-(Real.pi * max T₁ 1)) ≤ Real.exp (-(Real.pi * t)) :=
      Real.exp_le_exp.mpr (by nlinarith [Real.pi_pos, le_of_lt ht', ht])
    have h5 : Real.exp (-(Real.pi * max T₁ 1)) * Real.exp (Real.pi * max T₁ 1) = 1 := by
      rw [← Real.exp_add]; ring_nf; simp
    have h6 : (0 : ℝ) < Real.exp (-(Real.pi * max T₁ 1)) := Real.exp_pos _
    have h7 : (0 : ℝ) < Real.exp (Real.pi * max T₁ 1) := Real.exp_pos _
    have h8 : (1 : ℝ) ≤ Real.exp (-(Real.pi * (t - 0))) * Real.exp (Real.pi * max T₁ 1) := by
      have : Real.exp (-(Real.pi * t)) = Real.exp (-(Real.pi * (t - 0))) := by ring_nf
      rw [this] at h3
      calc (1 : ℝ) = Real.exp (-(Real.pi * max T₁ 1)) * Real.exp (Real.pi * max T₁ 1) := h5.symm
        _ ≤ Real.exp (-(Real.pi * (t - 0))) * Real.exp (Real.pi * max T₁ 1) :=
            mul_le_mul_of_nonneg_right h3 h7.le
    have hkey : B ≤ (B * Real.exp (Real.pi * max T₁ 1) + 1)
        * ((1 + t) ^ max M₁ 0 * Real.exp (-(Real.pi * (t - 0)))) := by
      have hone : (1 : ℝ) ≤ (1 + t) ^ max M₁ 0
          * (Real.exp (-(Real.pi * (t - 0))) * Real.exp (Real.pi * max T₁ 1)) :=
        (by
          have := mul_le_mul h1 h8 (by norm_num : (0:ℝ) ≤ 1)
            (le_trans (by norm_num : (0:ℝ) ≤ 1) h1)
          simpa using this)
      have hstep : B ≤ B * ((1 + t) ^ max M₁ 0
          * (Real.exp (-(Real.pi * (t - 0))) * Real.exp (Real.pi * max T₁ 1))) :=
        le_mul_of_one_le_right hB0 hone
      calc B ≤ B * ((1 + t) ^ max M₁ 0
            * (Real.exp (-(Real.pi * (t - 0))) * Real.exp (Real.pi * max T₁ 1))) := hstep
        _ = (B * Real.exp (Real.pi * max T₁ 1))
              * ((1 + t) ^ max M₁ 0 * Real.exp (-(Real.pi * (t - 0)))) := by ring
        _ ≤ (B * Real.exp (Real.pi * max T₁ 1) + 1)
              * ((1 + t) ^ max M₁ 0 * Real.exp (-(Real.pi * (t - 0)))) := by
            refine mul_le_mul_of_nonneg_right (by linarith) ?_
            exact mul_nonneg h2 (Real.exp_pos _).le
    refine le_trans hkey ?_
    calc (B * Real.exp (Real.pi * max T₁ 1) + 1)
          * ((1 + t) ^ max M₁ 0 * Real.exp (-(Real.pi * (t - 0))))
        = (B * Real.exp (Real.pi * max T₁ 1) + 1) * (1 + t) ^ max M₁ 0
            * Real.exp (-(Real.pi * (t - 0))) := by ring
      _ ≤ max C₁ (B * Real.exp (Real.pi * max T₁ 1) + 1) * (1 + t) ^ max M₁ 0
            * Real.exp (-(Real.pi * (t - 0))) := by
          refine mul_le_mul_of_nonneg_right ?_ (Real.exp_pos _).le
          exact mul_le_mul_of_nonneg_right (le_max_right _ _) h2

end Work.HFN
