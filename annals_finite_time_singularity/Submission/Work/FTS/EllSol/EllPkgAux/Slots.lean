import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.EllExist.LevelK
import Submission.Work.FTS.EllSol.ClassC
import Submission.Work.FTS.EllipticEst.integrableOn_HkIntegrand_terms
import Submission.Work.FTS.H2.HQ.Glue
import Submission.Work.FTS.StrongPersist.N6Trans.OpenTwins.bt_prod_integrable_open
import Submission.Work.FTS.VocabO
import Submission.Work.FTS_EllLimOK.ProducerH.BoxAux.th2EgMid

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllSol.EllPkgAux

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-- The `ℛ`-slot at level `4` over level-`7` solutions. -/
def RopSlotLe4 (C : ℝ) : Prop :=
  ∀ (α : ℝ) (g Ψ : Fn), 0 < α → α ≤ 1 / 4 → ClassC α g →
    Work.FTS.EllExist.EllClassOk 7 α g Ψ →
    Work.FTS.VocabO.HQo α 4 (Work.Construction.Rop α (Work.Construction.PhiTil α g Ψ)) ∧
    Work.Spaces.HkNorm α 4 (Work.Construction.Rop α (Work.Construction.PhiTil α g Ψ))
      ≤ C * Work.Spaces.HkNorm α 4 g

/-- The `U/sin 2θ`-slot at level `4` over level-`7` solutions. -/
def UopSlotLe4 (C : ℝ) : Prop :=
  ∀ (α : ℝ) (g Ψ : Fn), 0 < α → α ≤ 1 / 4 → ClassC α g →
    Work.FTS.EllExist.EllClassOk 7 α g Ψ →
    Work.FTS.VocabO.HQo α 4 (fun z θ =>
        Work.Construction.Uop α (Work.Construction.PhiTil α g Ψ) z θ / Work.Construction.s2 θ) ∧
    Work.Spaces.HkNorm α 4 (fun z θ =>
        Work.Construction.Uop α (Work.Construction.PhiTil α g Ψ) z θ / Work.Construction.s2 θ)
      ≤ C * Work.Spaces.HkNorm α 4 g

/-- The `V`-slot at level `4` over level-`7` solutions. -/
def VopSlotLe4 (C : ℝ) : Prop :=
  ∀ (α : ℝ) (g Ψ : Fn), 0 < α → α ≤ 1 / 4 → ClassC α g →
    Work.FTS.EllExist.EllClassOk 7 α g Ψ →
    Work.FTS.VocabO.HQo α 4 (Work.Construction.Vop (Work.Construction.PhiTil α g Ψ)) ∧
    Work.Spaces.HkNorm α 4 (Work.Construction.Vop (Work.Construction.PhiTil α g Ψ))
      ≤ C * Work.Spaces.HkNorm α 4 g

/-- The `V^{th}`-slot at level `4` over level-`7` solutions. -/
def VthSlotLe4 (C : ℝ) : Prop :=
  ∀ (α : ℝ) (g Ψ : Fn), 0 < α → α ≤ 1 / 4 → ClassC α g →
    Work.FTS.EllExist.EllClassOk 7 α g Ψ →
    Work.FTS.VocabO.CoefThMem 1 (Work.Construction.Vop (Work.Construction.PhiTil α g Ψ)) ∧
    Work.FTS.VocabO.CoefTh 1 (Work.Construction.Vop (Work.Construction.PhiTil α g Ψ))
      ≤ C * α ^ (-(1 / 2 : ℝ)) * Work.Spaces.HkNorm α 4 g

/-- **The packaging**: the four slot estimates give the level-`4` package `EllPkgGo` on the class,
with constants added and `α₀ = 1/4`. -/
theorem ellPkgGoOfClassOk_of
    (hR : ∃ C : ℝ, 0 < C ∧ RopSlotLe4 C) (hU : ∃ C : ℝ, 0 < C ∧ UopSlotLe4 C)
    (hV : ∃ C : ℝ, 0 < C ∧ VopSlotLe4 C) (hT : ∃ C : ℝ, 0 < C ∧ VthSlotLe4 C) :
    ∃ Ce α₀ : ℝ, 0 < Ce ∧ 0 < α₀ ∧
      ∀ (α : ℝ) (g Ψ : Fn), 0 < α → α ≤ α₀ → ClassC α g →
        Work.FTS.EllExist.EllClassOk 7 α g Ψ → Work.FTS.VocabO.EllPkgGo α Ce g Ψ := by
  obtain ⟨CR, hCR, hR⟩ := hR
  obtain ⟨CU, hCU, hU⟩ := hU
  obtain ⟨CV, hCV, hV⟩ := hV
  obtain ⟨CT, hCT, hT⟩ := hT
  refine ⟨CR + CU + CV + CT, 1 / 4, by positivity, by norm_num, ?_⟩
  intro α g Ψ hα hα4 hC hΨ
  obtain ⟨hRm, hRb⟩ := hR α g Ψ hα hα4 hC hΨ
  obtain ⟨hUm, hUb⟩ := hU α g Ψ hα hα4 hC hΨ
  obtain ⟨hVm, hVb⟩ := hV α g Ψ hα hα4 hC hΨ
  obtain ⟨hTm, hTb⟩ := hT α g Ψ hα hα4 hC hΨ
  have hgnn : (0 : ℝ) ≤ Work.FTS.Nonlin.Xn α g := Work.Spaces.HkNorm_nonneg α 4 g
  have hαpow : (0 : ℝ) ≤ α ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hα.le _
  have hRle : CR ≤ CR + CU + CV + CT := by linarith
  have hUle : CU ≤ CR + CU + CV + CT := by linarith
  have hVle : CV ≤ CR + CU + CV + CT := by linarith
  have hTle : CT ≤ CR + CU + CV + CT := by linarith
  have h1 : CR * Work.FTS.Nonlin.Xn α g
      ≤ (CR + CU + CV + CT) * Work.FTS.Nonlin.Xn α g :=
    mul_le_mul_of_nonneg_right hRle hgnn
  have h2 : CU * Work.FTS.Nonlin.Xn α g
      ≤ (CR + CU + CV + CT) * Work.FTS.Nonlin.Xn α g :=
    mul_le_mul_of_nonneg_right hUle hgnn
  have h3 : CV * Work.FTS.Nonlin.Xn α g
      ≤ (CR + CU + CV + CT) * Work.FTS.Nonlin.Xn α g :=
    mul_le_mul_of_nonneg_right hVle hgnn
  have h4 : CT * α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g
      ≤ (CR + CU + CV + CT) * α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hTle hαpow) hgnn
  exact ⟨hΨ.1, hΨ.2.1, ⟨hRm, le_trans hRb h1⟩,
    ⟨hUm, le_trans hUb h2⟩, ⟨hVm, le_trans hVb h3⟩,
    Work.FTS.ClassC.vanishU_of_classOk hΨ, ⟨hTm, le_trans hTb h4⟩⟩

end Work.FTS.EllSol.EllPkgAux
