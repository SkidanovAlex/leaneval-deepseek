import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.FinalV2.Defs
import Submission.Work.FTS_RegExport.RXA1w.abs_mixed_le_HkNorm_C4_w_proved
import Submission.Work.FTS_RegExport.RXR1.classC_sub_hyp
import Submission.Work.FTS.EllipticEst.TT.Slot11.ZsqAux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS_RegExport.RXR5.Pieces.mixed_slice_tau_modulus`

The mixed slots `D_z^bD_θ^a g(·,·,τ)` of the limit family of `LimApprox` are Lipschitz in the
fake time `τ` on every horizon `[0,T]`, for `a + b ≤ 2`, with the *weighted* space-time factor
`z^{3/2}/(1+z)²`:

`|D_z^bD_θ^a g(·,·,τ) - D_z^bD_θ^a g(·,·,τ')| ≤ L · z^{3/2}/(1+z)² · |τ - τ'|`.

This is the weighted refinement of `Work.FTS_RegExport.RXT.lim_mixed_lip` (which uses the
*constant* interior trade-off `ClassC_mixed_sup_le`).  The argument is the same:

* the approximating families `gn` of `LimApprox` are class-`C` slices whose `ℋ⁴`-difference is
  Lipschitz in `τ` (`Xn αG (slice (gn n) τ - slice (gn n) τ') = HkNorm αG 4 (…) ≤ L₀|τ - τ'|`);
* `ClassC` is a subspace, so the difference `slice (gn n) τ - slice (gn n) τ'` is again of class
  `C` (`EComparison.classC_sub`), hence `SmoothOpen`, honestly in `ℋ⁴` and satisfying the
  boundary traces up to order `4` (`classC_sub_hyp`);
* the **weighted** interior `L^∞`–`ℋ⁴` trade-off `abs_mixed_le_HkNorm_C4_w_proved` turns the
  `ℋ⁴`-Lipschitz bound into the pointwise weighted bound on every slot of the difference;
* `mixed_sub_open` identifies the slot of the difference with the difference of the slots, and
  the `C⁴`-jet convergence of `LimApprox` passes the bound to the limit.
-/

namespace Work.FTS_RegExport.RXR5.Pieces

open scoped Real Topology
open Filter

theorem mixed_slice_tau_modulus {αG C₀ : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn →ₗ[ℝ] Work.FTS.Galerkin.Fn} {g : Work.FTS.Galerkin.Fam}
    (hA : Work.FTS.FinalV2.LimApprox αG C₀ Φs E g) (hαG : 0 < αG) (hαG1 : αG ≤ 1)
    (T : ℝ) (hT : 0 < T) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ τ ∈ Set.Icc 0 T, ∀ τ' ∈ Set.Icc 0 T, ∀ b a : ℕ, a + b ≤ 2 →
      ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      |Work.Spaces.mixed b a (Work.FTS.Galerkin.slice g τ) z θ
        - Work.Spaces.mixed b a (Work.FTS.Galerkin.slice g τ') z θ|
        ≤ L * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2) * |τ - τ'| := by
  -- the weighted interior `L^∞`–`ℋ⁴` trade-off, with a constant independent of the datum
  obtain ⟨Cw, hCw0, hCw⟩ :=
    Work.FTS_RegExport.RXA1w.abs_mixed_le_HkNorm_C4_w_proved hαG hαG1
  -- the class-`C` approximants of the `LimApprox` clause
  obtain ⟨gn, _B, L₀, hC, hLip, hjet, _hmu⟩ := hA T hT
  refine ⟨Cw * max L₀ 0, mul_nonneg hCw0 (le_max_right _ _), ?_⟩
  intro τ hτ τ' hτ' b a hab z θ hz hθ0 hθ1
  have hzθ : (z, θ) ∈ Work.Construction.Qd := ⟨hz, hθ0, hθ1⟩
  have hw0 : 0 ≤ z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2 :=
    div_nonneg (Real.rpow_nonneg hz.le _) (by positivity)
  -- the slotwise bound on every approximant
  have hbd : ∀ᶠ n : ℕ in atTop,
      |Work.Spaces.mixed b a (Work.FTS.Galerkin.slice (gn n) τ) z θ
        - Work.Spaces.mixed b a (Work.FTS.Galerkin.slice (gn n) τ') z θ|
      ≤ Cw * max L₀ 0 * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2) * |τ - τ'| := by
    refine Eventually.of_forall (fun n => ?_)
    set F : Work.FTS.Galerkin.Fn := Work.FTS.Galerkin.slice (gn n) τ with hF
    set G : Work.FTS.Galerkin.Fn := Work.FTS.Galerkin.slice (gn n) τ' with hG
    have hclsF : Work.FTS.ClassC.ClassC αG F := (hC n τ hτ).1
    have hclsG : Work.FTS.ClassC.ClassC αG G := (hC n τ' hτ').1
    -- the difference is again of class `C`, hence `ℋ⁴`-honest with the traces
    have hsub : Work.FTS.ClassC.ClassC αG (fun z θ => F z θ - G z θ) :=
      Work.FTS.StrongEps.EComparison.classC_sub hclsF hclsG
    have h4 : ContDiffOn ℝ 4 (Function.uncurry (fun z θ => F z θ - G z θ))
        Work.FTS.EllipticEst.Q0 :=
      (Work.FTS.EllipticEst.smoothOpen_iff_forall _).mp hsub.reg 4
    have hmem : Work.Spaces.HkMem αG 4 (fun z θ => F z θ - G z θ) :=
      Work.FTS.OpenPkg.HkMem_mono_open hsub.reg 4 (by norm_num) hsub.mem
    have htr : Work.FTS.Nonlin.BdryTraces αG 4 (fun z θ => F z θ - G z θ) :=
      Work.FTS.ClassC.bdryTraces_mono (by norm_num) hsub.tr
    have h1 := hCw (fun z θ => F z θ - G z θ) h4 hmem htr b a hab z θ hz hθ0 hθ1
    -- the slot of the difference is the difference of the slots
    have hlin := Work.FTS.EllipticEst.TTSlot11Aux.mixed_sub_open
      hclsF.reg hclsG.reg b a z θ hz hθ0 hθ1
    -- the `ℋ⁴`-Lipschitz clause of `LimApprox`
    have hlip : Work.Spaces.HkNorm αG 4 (fun z θ => F z θ - G z θ) ≤ max L₀ 0 * |τ - τ'| :=
      le_trans (hLip n τ hτ τ' hτ')
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _))
    calc |Work.Spaces.mixed b a F z θ - Work.Spaces.mixed b a G z θ|
        = |Work.Spaces.mixed b a (fun z θ => F z θ - G z θ) z θ| := by rw [hlin]
      _ ≤ Cw * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2)
            * Work.Spaces.HkNorm αG 4 (fun z θ => F z θ - G z θ) := h1
      _ ≤ Cw * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2) * (max L₀ 0 * |τ - τ'|) :=
          mul_le_mul_of_nonneg_left hlip (mul_nonneg hCw0 hw0)
      _ = Cw * max L₀ 0 * (z ^ ((3 : ℝ) / 2) / (1 + z) ^ 2) * |τ - τ'| := by ring
  -- pass the slotwise bound to the limit along the jet convergence of `LimApprox`
  have htend : Filter.Tendsto (fun n : ℕ =>
      |Work.Spaces.mixed b a (Work.FTS.Galerkin.slice (gn n) τ) z θ
        - Work.Spaces.mixed b a (Work.FTS.Galerkin.slice (gn n) τ') z θ|) atTop
      (𝓝 |Work.Spaces.mixed b a (Work.FTS.Galerkin.slice g τ) z θ
        - Work.Spaces.mixed b a (Work.FTS.Galerkin.slice g τ') z θ|) :=
    ((hjet τ hτ b a (by omega) z θ hzθ).sub (hjet τ' hτ' b a (by omega) z θ hzθ)).abs
  exact le_of_tendsto htend hbd

end Work.FTS_RegExport.RXR5.Pieces
