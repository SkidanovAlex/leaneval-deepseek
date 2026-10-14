import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Basic.Real.Basic
import Mathlib.Order.Filter.Defs
import Submission.Work.FTS.IPGen.IP4Lin
import Submission.Work.FTS.IPGen.N4ExtraQ
import Submission.Work.FTS.IPGen.headline_IP4_of_errors
import Submission.Work.FTS.NonlinRows.HkMem_mul_pth_flat
import Submission.Work.FTS.StrongPersist.L3Aux.ZmulBound
import Submission.Work.FTS.StrongPersist.N6Trans.SixRoute.sixExpansion
import Submission.Work.FTS.StrongPersist.StarPkg6Assembly
import Submission.Work.FTS.TransportS.T3SlotAux.Remainder
import Submission.Work.FTS.TransportS.t3SlotGuarded
import Submission.Work.FTS_RegExport.RXT.Slots.JetCalc.Expand
import Submission.Work.FTS_RegExport.RXT.jc3_aux
import Submission.Work.FTS_StreamBdry.Inputs.theta_part_theta
-- ===== merged: Submission.Work.FTS.IPGen.Assembly =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.IPGen

open Work.FTS.Galerkin (Fn)
open Work.FTS.Nonlin (Xn)

set_option autoImplicit false



set_option linter.defProp false


end Work.FTS.IPGen
end
end
-- ===== merged: Submission.Work.FTS.StrongEps.E4R3.N4C.T4HonestGen =====
section

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E4R3.N4C

theorem T4HonestGen (c₁ c₂ c₁' c₂' c₁'' c₂'' : ℝ) (h₁ : 0 < c₁) (h₂ : 0 < c₂)
    (h₁' : 0 < c₁') (h₂' : 0 < c₂') (h₁'' : 0 < c₁'') (h₂'' : 0 < c₂'') :
    ∃ Ct α₂ : ℝ, 0 < Ct ∧ 0 < α₂ ∧
      ∀ α ∈ Set.Ioc 0 α₂, ∀ f g : Work.FTS.Galerkin.Fn,
        Work.FTS.EllipticEst.SmoothOpen f → Work.FTS.VocabO.WDMem 4 f →
        Work.FTS.EllipticEst.SmoothOpen g → Work.Spaces.HkMem α 4 g →
        Work.Spaces.HkMem α 5 g → Work.Spaces.DecayAll 4 g →
        |Work.FTS.CoercivityFix.Assembly.IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α
            (fun z θ => f z θ * Work.Spaces.Dth g z θ) g|
          ≤ Ct * α ^ (-(1 / 2 : ℝ)) * Work.FTS.VocabO.WDp 4 f
              * (Work.Spaces.HkNorm α 4 g) ^ 2 := by
  obtain ⟨Cb, hCb, hLeaf⟩ := Work.FTS.StrongEps.E4R3.N4C.T4Honest.T4LeafSumBound
  set K : ℝ := max 1 (max c₁ (max c₂ (max c₁' (max c₂' (max c₁'' c₂''))))) ^ 3 * 3 ^ 3
    * 10 ^ 22 with hKdef
  have hD := Work.FTS.IPGen.ip4SlotDomGen (c₁ := c₁) (c₂ := c₂) (c₁' := c₁')
    (c₂' := c₂') (c₁'' := c₁'') (c₂'' := c₂'') h₁.le h₂.le h₁'.le h₂'.le h₁''.le h₂''.le
  rw [← hKdef] at hD
  refine ⟨K * Cb, 1, mul_pos hD.1 hCb, one_pos, ?_⟩
  intro α hα f g hsf hWD hsg hmg4 hmg5 hdec
  have hα1 : α ≤ 1 := hα.2
  set u : Work.FTS.Galerkin.Fn := fun z θ => f z θ * Work.Spaces.Dth g z θ with hu
  have hsu : Work.FTS.EllipticEst.SmoothOpen u := hsf.mul (Work.FTS.EllipticEst.SmoothOpen.Dth hsg)
  have hmain : |Work.FTS.CoercivityFix.Assembly.IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α u g|
      ≤ K * Work.FTS.TransportS.leafSum α u g := hD.2 α hα u g hsu hsg
  have hleaf := hLeaf α f g hα.1 hα1 hsf hWD hsg hmg4 hdec
  rw [← hu] at hleaf
  -- the final arithmetic
  have hWnn : 0 ≤ Work.FTS.VocabO.WDp 4 f := Work.FTS.OpenPkg.WDp_nonneg 4 f
  have hαpow : (1 : ℝ) ≤ α ^ (-(1 / 2 : ℝ)) := by
    have h := Real.rpow_le_rpow_of_exponent_ge hα.1 hα1
      (show -(1 / 2 : ℝ) ≤ 0 by norm_num)
    rwa [Real.rpow_zero] at h
  have hHk : Work.Spaces.HkSq α 4 g = (Work.Spaces.HkNorm α 4 g) ^ 2 :=
    (Work.FTS.H2.HkNorm_sq α g).symm
  have hK0 : 0 ≤ K := hD.1.le
  have hKC0 : 0 ≤ K * Cb := mul_nonneg hK0 hCb.le
  calc |Work.FTS.CoercivityFix.Assembly.IP4 c₁ c₂ c₁' c₂' c₁'' c₂'' α u g|
      ≤ K * Work.FTS.TransportS.leafSum α u g := hmain
    _ ≤ K * (Cb * Work.FTS.VocabO.WDp 4 f * Work.Spaces.HkSq α 4 g) :=
        mul_le_mul_of_nonneg_left hleaf hK0
    _ = (K * Cb) * Work.FTS.VocabO.WDp 4 f * Work.Spaces.HkSq α 4 g := by ring
    _ = (K * Cb) * Work.FTS.VocabO.WDp 4 f * (Work.Spaces.HkNorm α 4 g) ^ 2 := by rw [hHk]
    _ ≤ (K * Cb) * α ^ (-(1 / 2 : ℝ)) * Work.FTS.VocabO.WDp 4 f
          * (Work.Spaces.HkNorm α 4 g) ^ 2 := by
        have h2 : 0 ≤ Work.FTS.VocabO.WDp 4 f * (Work.Spaces.HkNorm α 4 g) ^ 2 :=
          mul_nonneg hWnn (sq_nonneg _)
        calc (K * Cb) * Work.FTS.VocabO.WDp 4 f * (Work.Spaces.HkNorm α 4 g) ^ 2
            = (K * Cb) * 1 * (Work.FTS.VocabO.WDp 4 f
                * (Work.Spaces.HkNorm α 4 g) ^ 2) := by ring
          _ ≤ (K * Cb) * α ^ (-(1 / 2 : ℝ)) * (Work.FTS.VocabO.WDp 4 f
                * (Work.Spaces.HkNorm α 4 g) ^ 2) :=
              mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hαpow hKC0) h2
          _ = (K * Cb) * α ^ (-(1 / 2 : ℝ)) * Work.FTS.VocabO.WDp 4 f
                * (Work.Spaces.HkNorm α 4 g) ^ 2 := by ring

end Work.FTS.StrongEps.E4R3.N4C
end
