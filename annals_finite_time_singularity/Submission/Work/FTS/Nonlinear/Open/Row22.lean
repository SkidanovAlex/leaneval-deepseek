import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.OpenPkg.Defs
import Submission.Work.FTS.VocabO
import Submission.Work.FTS.Nonlinear.Pieces.Rows
import Submission.Work.FTS.Nonlinear.Defs
import Submission.Work.FTS.Nonlinear.Pieces.RNP.row22
import Submission.Work.FTS.Nonlinear.FstarPkgAll
import Submission.Work.FTS.OpenPkg.WDp_le_WlInf
import Submission.Work.FTS.NonlinRows.NRow1_7Aux
import Submission.Work.FTS.CoercivityFix.QuadPorts.RegQ_dth

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.Nonlinear.Open

open Work.FTS.Galerkin (Fn)

set_option maxHeartbeats 1600000

/-! ## Row 22 of the §8 table in the open-quadrant (primed) vocabulary

`Work.FTS.Nonlin.N4sg α g = -(1/2)·FK(F_*)·D_θ g` is the slot of the transport estimate in which
the coefficient `-(1/2)·FK(F_*)` is a function of `z` alone and the derivative `D_θ g` falls on
the test function.  The relevant clause of the primed `IP`-interface is `N4Extra'.t4`,

  `|IP α (f·D_θ g) g| ≤ Ct·α^{-1/2}·WDp 4 f·|g|²`,

so everything reduces to the open-quadrant `D`-sup norm `WDp 4` of the radial coefficient.

The two facts needed about the coefficient, both established below:

* `FK (F_*(α)) z = α·(2z/(1+z)²) = α·2·hKer z` (`FstarPkg.FK_Fstar`), so the coefficient is
  `-α·hKer`, a constant multiple of the radial profile `hKer`;
* `WDp 4 (c·hKer) ≤ 200·C_W·|c|` (`hKerConstWlInf` for the `𝒲^{4,∞}`-membership and
  `WDp_le_WlInf` for the comparison `WDp ≤ C_W·WlInf`).

The loss `α^{-1/2}·α = √α` is what produces the `√α` of the stated bound, with the constant
`K = Ct·C_W·200 + 1` (positive because `Ct > 0`).

### The `ℋ⁴`-honesty conjunct

`N₄^{sg} = (-α·hKer)·D_θ g` is a `𝒲^{4,∞}`-coefficient times `D_θ g`, so the mixed product rule
`N4Norm'.wprod` applies (once `D_θ g ∈ ℋ⁴`, which follows from `RegQ α 5 g` by
`CoercivityFix.QuadPorts.RegQ_dth`).

The hypotheses `StarPkgo α Cs Φs` and `EllPkgGo α Ce g Φg` are not needed for this row;
`GalClass α g` is used only through `galClass_regQ4` and the `RegQ α 5 g` slice of its
`RegQ α 6`-membership.
-/

/-- `(z,θ) ↦ c·z/(1+z)²` is `C^∞` on the open quadrant. -/
theorem smoothOpen_hKerConst (c : ℝ) :
    Work.FTS.EllipticEst.SmoothOpen (fun z _ => c * Work.Spaces.hKer z) := by
  refine Work.FTS.NonlinRows.smoothOpen_radial (r := fun z => c * Work.Spaces.hKer z) ?_
  intro n
  have hker : ContDiffOn ℝ n (fun z : ℝ => Work.Spaces.hKer z) (Set.Ioi 0) := by
    simp only [Work.Spaces.hKer_apply]
    refine ContDiffOn.div (n := (n : WithTop ℕ∞)) (s := Set.Ioi 0)
      (contDiffOn_id (𝕜 := ℝ) (s := Set.Ioi 0))
      (((contDiffOn_const (c := (1 : ℝ)) (s := Set.Ioi 0)).add
        (contDiffOn_id (𝕜 := ℝ) (s := Set.Ioi 0))).pow 2) ?_
    intro z hz
    have hz' : (0 : ℝ) < z := hz
    exact pow_ne_zero 2 (by linarith)
  exact ContDiffOn.const_smul c hker

theorem Row22 (IP : ℝ → Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn → ℝ) {α₂ Ci Ct Ce Cs : ℝ}
    (hN : Work.FTS.OpenPkg.N4Norm' Ci α₂) (hE : Work.FTS.OpenPkg.N4Extra' IP α₂ Ct) :
    ∃ K : ℝ, 0 < K ∧ ∀ {α : ℝ} {g Φs Φg : Work.FTS.Galerkin.Fn},
      0 < α → α ≤ 1 → α ≤ α₂ → Work.FTS.Nonlin.GalClass α g →
      Work.FTS.VocabO.StarPkgo α Cs Φs → Work.FTS.VocabO.EllPkgGo α Ce g Φg →
      Work.Spaces.HkMem α 4 (Work.FTS.Nonlin.N4sg α g) ∧
      |IP α (Work.FTS.Nonlin.N4sg α g) g| ≤ K * (Real.sqrt α * Work.FTS.Nonlin.Xn α g ^ 2) := by
  obtain ⟨hCi, hα₂pos⟩ := hN.pos
  have hCt0 : 0 < Ct := hE.pos.1
  obtain ⟨CW, hCW0, hCW⟩ := Work.FTS.OpenPkg.WDp_le_WlInf
  refine ⟨Ct * (CW * 200) + 1, by positivity, ?_⟩
  intro α g Φs Φg hα hα1 hαα₂ hgal hstar hell
  have hIoc : α ∈ Set.Ioc 0 α₂ := ⟨hα, hαα₂⟩
  have hreg4 : Work.FTS.Nonlin.RegQ α 4 g := Work.FTS.Nonlin.galClass_regQ4 hgal
  have hX0 : 0 ≤ Work.FTS.Nonlin.Xn α g := Work.Spaces.HkNorm_nonneg α 4 g
  -- the radial coefficient `f = -(1/2)·FK(F_*)`
  set f : Fn := fun z _ => -(1 / 2) * Work.Construction.FK (Work.Construction.Fstar α) z with hfdef
  -- `FK(F_*) = α·2z/(1+z)²`, so `f = (-α)·hKer`
  have hcoef : f = fun z _ => (-α) * Work.Spaces.hKer z := by
    funext z θ
    rw [hfdef]
    simp only [Work.FTS.Nonlin.FK_Fstar hα hα1, Work.Spaces.hKer_apply]
    ring
  have hsm_f : Work.FTS.EllipticEst.SmoothOpen f := by
    rw [hcoef]
    exact smoothOpen_hKerConst (-α)
  have hker := Work.FTS.Nonlinear.Pieces.RNP.hKerConstWlInf α (-α)
  have hWmem : Work.Spaces.WlInfMem α 4 f := by
    rw [hcoef]
    exact hker.1
  have hWle : Work.Spaces.WlInf α 4 f ≤ 200 * α := by
    rw [hcoef]
    have h := hker.2
    rw [abs_neg, abs_of_pos hα] at h
    exact h
  -- the `D`-sup norm of the coefficient, through `WDp ≤ C_W·WlInf`
  have hWDmem : Work.FTS.VocabO.WDMem 4 f := fun b j hbj =>
    ⟨200 * Work.Spaces.WlInf α 4 f, fun z θ hz hθ1 hθ2 =>
      Work.FTS.OpenPkg.mixed_le_WlInf_200 hα hα1 hsm_f hWmem hbj hz ⟨hθ1, hθ2⟩⟩
  have hWDp : Work.FTS.VocabO.WDp 4 f ≤ CW * (200 * α) :=
    (hCW α f hα hα1 hsm_f hWmem).trans (mul_le_mul_of_nonneg_left hWle hCW0.le)
  -- the test function `D_θ g` is honest
  have hsm : Work.FTS.LocData.SmoothQuad g := hgal.reg.1
  have hmem6 : Work.Spaces.HkMem α 6 g := hgal.reg.2.1
  have hmem5 : Work.Spaces.HkMem α 5 g := Work.GalerkinFix.RegQ.HkMem_mono_Q hsm hmem6
  have hreg5 : Work.FTS.Nonlin.RegQ α 5 g :=
    ⟨hsm, hmem5, fun a b hab => hgal.reg.2.2 a b (by omega)⟩
  have hregh : Work.FTS.Nonlin.RegQ α 4 (Work.Spaces.Dth g) :=
    Work.FTS.CoercivityFix.QuadPorts.RegQ_dth α hα hreg5
  have hqo : Work.FTS.VocabO.HQo α 4 (Work.Spaces.Dth g) :=
    ⟨Work.FTS.OpenPkg.smoothOpen_of_smoothQuad hregh.1, hregh.2.1⟩
  -- `N₄^{sg}` is the product of the coefficient with `D_θ g`
  have hN4eq : Work.FTS.Nonlin.N4sg α g = fun z θ => f z θ * Work.Spaces.Dth g z θ := by
    funext z θ
    rw [hfdef]
    simp only [Work.FTS.Nonlin.N4sg]
  constructor
  · -- the `ℋ⁴`-honesty, by the mixed product rule `wprod`
    rw [hN4eq]
    exact (hN.wprod α hIoc f (Work.Spaces.Dth g) hsm_f hWmem hqo).1
  · -- the `IP`-bound, by the transport clause `t4`
    rw [hN4eq]
    have ht4 := hE.t4 α hIoc f g hWDmem hreg4
    have hA0 : 0 ≤ Ct * α ^ (-(1 / 2 : ℝ)) :=
      mul_nonneg hCt0.le (Real.rpow_nonneg hα.le _)
    refine ht4.trans ?_
    refine (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hWDp hA0)
      (pow_nonneg hX0 2)).trans ?_
    -- `α^{-1/2}·α = √α`
    have hsqrt : Real.sqrt α = α * α ^ (-(1 / 2 : ℝ)) := by
      rw [Real.sqrt_eq_rpow]
      have h := Real.rpow_add hα (1 : ℝ) (-(1 / 2 : ℝ))
      rw [Real.rpow_one, show (1 : ℝ) + -(1 / 2) = 1 / 2 by norm_num] at h
      exact h
    rw [hsqrt]
    have h1 : Ct * α ^ (-(1 / 2 : ℝ)) * (CW * (200 * α)) * Work.FTS.Nonlin.Xn α g ^ 2
        = Ct * (CW * 200) * (α * α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g ^ 2) := by
      ring
    rw [h1]
    exact mul_le_mul_of_nonneg_right (by linarith)
      (mul_nonneg (mul_nonneg hα.le (Real.rpow_nonneg hα.le _)) (pow_nonneg hX0 2))

end Work.FTS.Nonlinear.Open
