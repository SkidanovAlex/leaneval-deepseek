import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.Nonlinear.Pieces.RNP.GamSharpAux
import Submission.Work.FTS.OpenPkg.WtohWin.Assembly
import Submission.Work.FTS.PhiStar.Honesty.SlotsLimit.integrableOn_term
import Submission.Work.FTS.StrongEps.EpsE4Thr.ZeroOrder
import Submission.Work.FTS.StrongEps.EpsE4Thr.regQo_const_mul
import Submission.Work.FTS.StrongEps.SupPort.classC_mixed_sup_le
import Submission.Work.FTS.StrongEps.Weights
import Submission.Work.FTS.StrongGlobal.Defs
import Submission.Work.FTS.TransportS.GalSide
import Submission.Work.FTS_EllLimOK.IsBslSolPos_add
import Submission.Work.FTS_MuLipC.RowN.FaSlice
import Submission.Work.FTS_RegExport.RXT.jc3_aux
import Submission.Work.FTS_RegExport.RXT.velVanish2Star
import Submission.Work.FTS_RegExport.THL.theta_holder_of_HkMem
-- ===== merged: Submission.Work.FTS.EpsEngine.BlocksConcrete =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology ENNReal
open MeasureTheory Set Filter
open Work.FTS.Galerkin (Fn Fam slice)

namespace Work.FTS.EpsEngine

set_option autoImplicit false





end Work.FTS.EpsEngine
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.E5G.LimMixedBnds =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.E5G

open Work.FTS.Galerkin (Fn Fam slice)

set_option linter.unusedVariables false

/-- **The convergence package of a constant sequence**: a `C⁴`-profile honest in `ℋ⁶` up to `B` is
the locally uniform limit of the constant sequence of its own copies (every slot converges
trivially). -/
theorem convLocUnifH6_const {α B : ℝ} {f : Fn}
    (h4 : ContDiffOn ℝ 4 (Function.uncurry f) Work.FTS.EllipticEst.Q0)
    (hB : Work.Spaces.HkNorm α 6 f ≤ B) :
    ConvLocUnifH6 α B (fun _ : ℕ => f) f := by
  refine ⟨?_, h4, hB⟩
  intro K hK hKQ j i hji
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  exact Eventually.of_forall (fun _ _ _ => by simpa using hε)

/-- **The slot bounds and the slot `τ`-Lipschitz property of a `LimApproxOn` family.**  For a family
`g` which is the `Qd`-jet limit of class-`C` approximants with uniform `ℋ⁴`-smallness `C₀α²` and a
uniform `ℋ⁴`-Lipschitz modulus `L` in the fake time (`LimApproxOn α C₀ T Φs E g`), every mixed slot
of order `≤ 2` of `slice g τ` is bounded by `10/√(γ-1)·(C₀α²)` and is `τ`-Lipschitz, both on the
whole open quadrant and uniformly in `τ, τ' ∈ [0,T]`.

The proof is that of `Work.FTS_RegExport.RXA2.lim_mixed_bounds_proved`: the class-`C` interior
`L^∞`–`ℋ⁴` trade-off `SupPort.classC_mixed_sup_le` applied to the approximants (resp. to their
* differences*, which are again class-`C` by `EComparison.classC_sub`) gives the bounds along the
sequence, and `le_of_tendsto` passes them to the limit through the `Qd`-jet convergence clause. -/
theorem limMixedBndsOn {α C₀ T : ℝ} {Φs : Fn} {E : Fn → Fn} {g : Fam}
    (hα : 0 < α) (hα1 : α ≤ 1) (hA : LimApproxOn α C₀ T Φs E g) :
    ∃ L : ℝ, 0 ≤ L ∧
      ∀ τ ∈ Set.Icc (0 : ℝ) T, ∀ τ' ∈ Set.Icc (0 : ℝ) T, ∀ b a : ℕ, a + b ≤ 2 →
        ∀ z θ : ℝ, 0 < z → 0 < θ → θ < π / 2 →
          |Work.Spaces.mixed b a (slice g τ) z θ|
              ≤ 10 / Real.sqrt (Work.Spaces.gam α - 1) * (C₀ * α ^ 2) ∧
            |Work.Spaces.mixed b a (slice g τ) z θ
                - Work.Spaces.mixed b a (slice g τ') z θ| ≤ L * |τ - τ'| := by
  obtain ⟨gn, B, L₀, hC, hLip, hjet, _hmu⟩ := hA
  have hc : (0 : ℝ) ≤ 10 / Real.sqrt (Work.Spaces.gam α - 1) :=
    div_nonneg (by norm_num) (Real.sqrt_nonneg _)
  refine ⟨10 / Real.sqrt (Work.Spaces.gam α - 1) * max L₀ 0,
    mul_nonneg hc (le_max_right _ _), ?_⟩
  intro τ hτ τ' hτ' b a hab z θ hz hθ0 hθ1
  have hzθ : (z, θ) ∈ Work.Construction.Qd := ⟨hz, hθ0, hθ1⟩
  refine ⟨?_, ?_⟩
  · -- the uniform bound, as a limit of the approximants' bounds
    have h1 : ∀ n : ℕ,
        |Work.Spaces.mixed b a (slice (gn n) τ) z θ|
          ≤ 10 / Real.sqrt (Work.Spaces.gam α - 1) * (C₀ * α ^ 2) := by
      intro n
      refine le_trans (Work.FTS.StrongEps.SupPort.classC_mixed_sup_le hα hα1
        (hC n τ hτ).1 b a hab hzθ) ?_
      exact mul_le_mul_of_nonneg_left (hC n τ hτ).2.1 hc
    have h2 : Tendsto (fun n : ℕ =>
        |Work.Spaces.mixed b a (slice (gn n) τ) z θ|) atTop
        (nhds |Work.Spaces.mixed b a (slice g τ) z θ|) :=
      (hjet τ hτ b a (by omega) z θ hzθ).abs
    exact le_of_tendsto h2 (Eventually.of_forall h1)
  · -- the `τ`-Lipschitz bound, from the difference profiles
    have hbd : ∀ᶠ n : ℕ in atTop,
        |Work.Spaces.mixed b a (slice (gn n) τ) z θ
          - Work.Spaces.mixed b a (slice (gn n) τ') z θ|
        ≤ 10 / Real.sqrt (Work.Spaces.gam α - 1) * max L₀ 0 * |τ - τ'| := by
      refine Eventually.of_forall (fun n => ?_)
      set F : Fn := slice (gn n) τ with hF
      set G : Fn := slice (gn n) τ' with hG
      have hsub : Work.FTS.ClassC.ClassC α (fun z θ => F z θ - G z θ) :=
        Work.FTS.StrongEps.EComparison.classC_sub (hC n τ hτ).1 (hC n τ' hτ').1
      have hsup := Work.FTS.StrongEps.SupPort.classC_mixed_sup_le hα hα1 hsub b a hab hzθ
      have hlin := Work.FTS.EllipticEst.TTSlot11Aux.mixed_sub_open
        (hC n τ hτ).1.reg (hC n τ' hτ').1.reg b a z θ hz hθ0 hθ1
      have hlip : Work.FTS.Nonlin.Xn α (fun z θ => F z θ - G z θ)
          ≤ max L₀ 0 * |τ - τ'| :=
        le_trans (hLip n τ hτ τ' hτ')
          (mul_le_mul_of_nonneg_right (le_max_left _ _) (abs_nonneg _))
      calc |Work.Spaces.mixed b a F z θ - Work.Spaces.mixed b a G z θ|
          = |Work.Spaces.mixed b a (fun z θ => F z θ - G z θ) z θ| := by rw [hlin]
        _ ≤ 10 / Real.sqrt (Work.Spaces.gam α - 1) * Work.FTS.Nonlin.Xn α
              (fun z θ => F z θ - G z θ) := hsup
        _ ≤ 10 / Real.sqrt (Work.Spaces.gam α - 1) * (max L₀ 0 * |τ - τ'|) :=
            mul_le_mul_of_nonneg_left hlip hc
        _ = 10 / Real.sqrt (Work.Spaces.gam α - 1) * max L₀ 0 * |τ - τ'| := by ring
    have h2 : Tendsto (fun n : ℕ =>
        |Work.Spaces.mixed b a (slice (gn n) τ) z θ
          - Work.Spaces.mixed b a (slice (gn n) τ') z θ|) atTop
        (nhds |Work.Spaces.mixed b a (slice g τ) z θ
          - Work.Spaces.mixed b a (slice g τ') z θ|) :=
      ((hjet τ hτ b a (by omega) z θ hzθ).sub (hjet τ' hτ' b a (by omega) z θ hzθ)).abs
    exact le_of_tendsto h2 hbd

end Work.FTS.StrongEps.E5G
end
end
-- ===== merged: Submission.Work.FTS_EllLimOK.ProducerH.BoxAux.classCThetaHolder =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_EllLimOK.ProducerH.BoxAux

theorem classCThetaHolder {α : ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4) :
    ∃ C : ℝ, 0 < C ∧ ∀ g : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC α g →
      ∀ z ∈ Set.Ioi (0 : ℝ), ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
        ∀ θ' ∈ Set.Ioo 0 (Real.pi / 2),
          |g z θ - g z θ'| ≤ C * Work.FTS.StrongGlobal.Xn6 α g * |θ - θ'| ^ (α / 20) := by
  -- `θ`-Hölder continuity of a class-`C` profile, uniformly in `z > 0`.
  --
  -- The trace-free Hölder leaf `THL.theta_holder_of_HkMem` at exponent `β = α` gives, for any
  -- `C^4`-function on the open quadrant which is honestly in `ℋ⁴`,
  --
  --   `|f z θ - f z θ'| ≤ C · min z 1 · |f|_{ℋ⁴} · |θ-θ'|^((γ-1)/2)`,
  --
  -- and `(γ-1)/2 = (α/10)/2 = α/20` is exactly the exponent of the claim.  A class-`C` profile has
  -- the required regularity (`ClassC.reg`) and the required honesty at *every* level up to `10`
  -- (`ClassC.mem10`), so in particular `HkMem α 4 g` and `HkMem α 6 g`.
  --
  -- It remains to remove the two superfluous factors: `min z 1 ≤ 1`, and the order-monotonicity
  -- `HkNorm α 4 g ≤ HkNorm α 6 g = Xn6 α g` of the `ℋ^k`-norm (the integrand is a sum of
  -- nonnegative slots, so increasing the order only adds terms).
  have hα1 : α ≤ 1 := by linarith
  obtain ⟨C, hC0, hmain⟩ :=
    Work.FTS_RegExport.THL.theta_holder_of_HkMem (β := α) hα hα1
  refine ⟨C + 1, by linarith, ?_⟩
  intro g hg z hz θ hθ θ' hθ'
  have hmem4 : Work.Spaces.HkMem α 4 g :=
    Work.FTS.OpenPkg.HkMem_mono_open hg.reg 4 (by norm_num) hg.mem
  have hmem6 : Work.Spaces.HkMem α 6 g :=
    Work.FTS.OpenPkg.HkMem_mono_open hg.reg 6 (by norm_num) hg.mem
  have h4 : ContDiffOn ℝ 4 (Function.uncurry g) Work.FTS.EllipticEst.Q0 :=
    Work.FTS.StrongLWP.SmoothOpen.contDiffOn_four hg.reg
  have hkey := hmain g h4 hmem4 z hz θ hθ θ' hθ'
  have hgam : (Work.Spaces.gam α - 1) / 2 = α / 20 := by
    rw [Work.Spaces.gam_sub_one]; ring
  rw [hgam] at hkey
  have hX : 0 ≤ Work.FTS.StrongGlobal.Xn6 α g := Work.Spaces.HkNorm_nonneg α 6 g
  have hB : 0 ≤ Work.Spaces.HkNorm α 4 g := Work.Spaces.HkNorm_nonneg α 4 g
  have hnorm_mono : Work.Spaces.HkNorm α 4 g ≤ Work.FTS.StrongGlobal.Xn6 α g :=
    Work.FTS.StrongLWP.HkNorm_mono_of_mem (k := 6) (k' := 4) (by norm_num) hmem6
  have hmin : min z 1 ≤ 1 := min_le_right z 1
  have hr : 0 ≤ |θ - θ'| ^ (α / 20) := Real.rpow_nonneg (abs_nonneg _) _
  have hAB : C * min z 1 * Work.Spaces.HkNorm α 4 g
      ≤ (C + 1) * Work.FTS.StrongGlobal.Xn6 α g := by
    have h1 : min z 1 * Work.Spaces.HkNorm α 4 g ≤ Work.FTS.StrongGlobal.Xn6 α g :=
      calc min z 1 * Work.Spaces.HkNorm α 4 g
          ≤ 1 * Work.Spaces.HkNorm α 4 g := mul_le_mul_of_nonneg_right hmin hB
        _ = Work.Spaces.HkNorm α 4 g := one_mul _
        _ ≤ Work.FTS.StrongGlobal.Xn6 α g := hnorm_mono
    calc C * min z 1 * Work.Spaces.HkNorm α 4 g
        = C * (min z 1 * Work.Spaces.HkNorm α 4 g) := by ring
      _ ≤ C * Work.FTS.StrongGlobal.Xn6 α g := mul_le_mul_of_nonneg_left h1 hC0
      _ ≤ (C + 1) * Work.FTS.StrongGlobal.Xn6 α g :=
          mul_le_mul_of_nonneg_right (by linarith) hX
  calc |g z θ - g z θ'|
      ≤ C * min z 1 * Work.Spaces.HkNorm α 4 g * |θ - θ'| ^ (α / 20) := hkey
    _ ≤ (C + 1) * Work.FTS.StrongGlobal.Xn6 α g * |θ - θ'| ^ (α / 20) :=
        mul_le_mul_of_nonneg_right hAB hr

end Work.FTS_EllLimOK.ProducerH.BoxAux
end
