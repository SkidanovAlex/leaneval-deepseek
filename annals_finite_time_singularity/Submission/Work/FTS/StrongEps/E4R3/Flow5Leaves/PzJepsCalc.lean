import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.InnerProductSpace.Basic
import Submission.Work.FTS.StrongEps.E4R3.Flow5
import Submission.Work.FTS.StrongEps.PZeroAux.PzHkNormFour
import Submission.Work.FTS.StrongEps.PZeroAux.PzJepsHkMem
import Submission.Work.FTS.StrongEps.HkSq_Jeps_le
import Submission.Work.FTS.StrongEps.EpsLocalPStar.profRHS_sub_sup_le
import Submission.Work.FTS.StrongEps.EpsE4Work.Jeps_smul
import Submission.Work.FTS.GalBasis.exists_cc_of_honClass

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Flow5Leaves/PzJepsCalc.lean` — linearity and pricing of the projected mollifier `Pz ∘ J_ε`

The three facts about `W_ε = Pz ∘ J_ε` that the level-four product rule
(`Flow5Leaves/IP4_JfamP_hasDerivWithinAt_of_flow.lean`) consumes:

* `Pz_const_mul`      — `Pz` commutes with multiplication by a scalar (`L₁₂` is homogeneous,
                        `GalBasis.L12_const_mul`);
* `PzJeps_const_mul`  — `W_ε` is homogeneous (`EpsE4Work.Jeps_smul` + the previous);
* `PzJeps_pricing`    — `W_ε f ∈ HQo α 4` and `‖W_ε f‖_{ℋ⁴} ≤ K ‖f‖_{ℋ⁶}` (`PzHkNormFour` +
                        `HkSq_Jeps_le` + monotonicity of the norm in the order).

Nothing here is analytic beyond the two cited estimates.
-/

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E4R3.Flow5Leaves

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **`Pz` commutes with multiplication by a scalar** (`L₁₂` is homogeneous,
`GalBasis.L12_const_mul`). -/
theorem Pz_const_mul (c : ℝ) (f : Fn) :
    Work.FTS.StrongEps.Pz (fun z θ => c * f z θ)
      = fun z θ => c * Work.FTS.StrongEps.Pz f z θ := by
  funext z θ
  rw [Work.FTS.StrongEps.Pz_apply, Work.FTS.StrongEps.Pz_apply,
    Work.FTS.GalBasis.L12_const_mul c f 0]
  ring

/-- **The projected mollifier is homogeneous**: `Pz (J_ε (c • f)) = c • Pz (J_ε f)`
(`Jeps_smul` + `Pz_const_mul`). -/
theorem PzJeps_const_mul (ρ : ℝ × ℝ → ℝ) (ε c : ℝ) (f : Fn) :
    Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε (fun z θ => c * f z θ))
      = fun z θ => c * Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε f) z θ := by
  have h : (fun z θ => c * f z θ) = c • f := by
    funext z θ
    simp only [Pi.smul_apply, smul_eq_mul]
  have h2 : c • Work.FTS.StrongEps.Jeps ρ ε f
      = fun z θ => c * Work.FTS.StrongEps.Jeps ρ ε f z θ := by
    funext z θ
    simp only [Pi.smul_apply, smul_eq_mul]
  rw [h, Work.FTS.StrongEps.EpsE4Work.Jeps_smul, h2,
    Pz_const_mul c (Work.FTS.StrongEps.Jeps ρ ε f)]

/-- **Pricing of the projected mollified profile**: `Pz (J_ε f)` is honestly `ℋ⁴` and its
`ℋ⁴`-norm is controlled by the `ℋ⁶`-norm of `f`.  (`PzHkNormFour` gives the `ℋ⁴`-boundedness of
`Pz`, `HkSq_Jeps_le` the `E1`-boundedness of `J_ε`, and the `ℋ⁶`-input is read through the
monotonicity of the norm in the order.) -/
theorem PzJeps_pricing {α ε : ℝ} {ρ : ℝ × ℝ → ℝ}
    (hρ : Work.FTS.StrongEps.IsSmoothKernel ρ)
    (hα : α ∈ Set.Ioc (0 : ℝ) 1) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ K : ℝ, 0 < K ∧ ∀ {f : Fn}, Work.FTS.EllipticEst.SmoothOpen f →
      Work.Spaces.HkMem α 6 f →
      Work.FTS.VocabO.HQo α 4 (Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε f)) ∧
      Work.Spaces.HkNorm α 4 (Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε f))
        ≤ K * Work.Spaces.HkNorm α 6 f := by
  obtain ⟨A, hApos, hA⟩ := Work.FTS.StrongEps.PZeroAux.PzHkNormFour
  obtain ⟨C, hCpos, hC⟩ := Work.FTS.StrongEps.HkSq_Jeps_le ρ hρ.moll
  refine ⟨A * Real.exp (C / 2) + 1, by positivity, ?_⟩
  intro f hsm hm6
  have hsmc : ∀ n : ℕ, ContDiffOn ℝ n (Function.uncurry f) Work.FTS.StrongEps.Quad :=
    (Work.FTS.EllipticEst.smoothOpen_iff_forall f).mp hsm
  have hm4 : Work.Spaces.HkMem α 4 f :=
    Work.FTS.OpenPkg.HkMem_mono_open hsm 4 (by norm_num) hm6
  have hsmJ : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.StrongEps.Jeps ρ ε f) :=
    Work.FTS.StrongEps.smoothOpen_Jeps ρ hρ hε hsmc
  have hmJ4 : Work.Spaces.HkMem α 4 (Work.FTS.StrongEps.Jeps ρ ε f) :=
    Work.FTS.StrongEps.HkMem_Jeps hρ.moll hα hε hsmc hm4
  refine ⟨⟨Work.FTS.StrongEps.EpsLocalPStar.smoothOpen_Pz hsmJ,
    Work.FTS.StrongEps.PZeroAux.PzJepsHkMem 4 hρ hα hε hsmc hm4⟩, ?_⟩
  have hJ := hC α hα 4 ε hε hε1 f hsmc hm4 hmJ4
  have hsqrt : Real.sqrt (Real.exp (C * ε)) = Real.exp (C * ε / 2) := by
    have h2 : (Real.exp (C * ε / 2)) ^ 2 = Real.exp (C * ε) := by
      rw [sq, ← Real.exp_add]
      ring_nf
    rw [← h2, Real.sqrt_sq_eq_abs, abs_of_nonneg (Real.exp_pos _).le]
  have hNJ : Work.Spaces.HkNorm α 4 (Work.FTS.StrongEps.Jeps ρ ε f)
      ≤ Real.exp (C / 2) * Work.Spaces.HkNorm α 6 f := by
    rw [Work.Spaces.HkNorm, Work.Spaces.HkNorm]
    calc Real.sqrt (Work.Spaces.HkSq α 4 (Work.FTS.StrongEps.Jeps ρ ε f))
        ≤ Real.sqrt (Real.exp (C * ε) * Work.Spaces.HkSq α 4 f) := Real.sqrt_le_sqrt hJ
      _ = Real.sqrt (Real.exp (C * ε)) * Real.sqrt (Work.Spaces.HkSq α 4 f) :=
          Real.sqrt_mul (Real.exp_pos _).le _
      _ = Real.exp (C * ε / 2) * Real.sqrt (Work.Spaces.HkSq α 4 f) := by rw [hsqrt]
      _ ≤ Real.exp (C / 2) * Real.sqrt (Work.Spaces.HkSq α 6 f) := by
          refine mul_le_mul (Real.exp_le_exp.mpr ?_) (Real.sqrt_le_sqrt ?_)
            (Real.sqrt_nonneg _) (Real.exp_pos _).le
          · have hε0 : 0 ≤ ε := hε.le
            nlinarith [hCpos, hε1, hε0]
          · have h45 : Work.Spaces.HkSq α 4 f ≤ Work.Spaces.HkSq α 5 f :=
              Work.Coercivity.HkSq_mono α 4
                (Work.FTS.OpenPkg.HkMem_mono_open hsm 5 (by norm_num) hm6)
            have h56 : Work.Spaces.HkSq α 5 f ≤ Work.Spaces.HkSq α 6 f :=
              Work.Coercivity.HkSq_mono α 5 hm6
            exact le_trans h45 h56
      _ = Real.exp (C / 2) * Work.Spaces.HkNorm α 6 f := rfl
  calc Work.Spaces.HkNorm α 4 (Work.FTS.StrongEps.Pz (Work.FTS.StrongEps.Jeps ρ ε f))
      ≤ A * Work.Spaces.HkNorm α 4 (Work.FTS.StrongEps.Jeps ρ ε f) :=
        hA α hα 4 le_rfl _ hsmJ hmJ4
    _ ≤ A * (Real.exp (C / 2) * Work.Spaces.HkNorm α 6 f) :=
        mul_le_mul_of_nonneg_left hNJ hApos.le
    _ ≤ (A * Real.exp (C / 2) + 1) * Work.Spaces.HkNorm α 6 f := by
        have h6 : (0 : ℝ) ≤ Work.Spaces.HkNorm α 6 f := Work.Spaces.HkNorm_nonneg α 6 f
        have he : (0 : ℝ) < Real.exp (C / 2) := Real.exp_pos _
        nlinarith

end Work.FTS.StrongEps.E4R3.Flow5Leaves
