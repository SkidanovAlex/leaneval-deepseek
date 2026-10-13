/-
# `E4R3/N4C/rows/rowsN4b` — rows 22, 23 of the honest §8 table

`Work.FTS.StrongEps.E4R3.N4C.rows.rowsN4b` proves the two `N₄^{sg}`/`N₄^{ss}` rows of the
honest (class-`C`) §8 table:

* row 22: `|IP α (N₄^{sg} α g) g| ≤ K·√α·|g|²`, where `N₄^{sg} = -(1/2)·FK(F_*)·D_θ g`;
* row 23: `Xn α (N₄^{ss} α) ≤ K·α³`, where `N₄^{ss} = -(1/2)·sin(2θ)·FK(F_*)·∂_θF_*`,

in the honest context `CtxT` (profile data `ClassC α g ∧ CoerAdmO α g`, open-quadrant elliptic
packages) and using only the clause bundle `N4ExtraH` (whose `t4` clause is the `D_θ`-transport
with a `𝒲^{4,∞}`-coefficient, priced by the `D`-sup norm `WDp`).

## Route

Row 22 is the honest copy of the frozen `NonlinRows.NRow22`: the coefficient
`-(1/2)·FK(F_*) = -α·hKer` is *radial*, and `FK(F_*) = α·2z/(1+z)²` (`Nonlin.FK_Fstar`), so
`WlInf α 4 (fun z _ => c·hKer z) ≤ 200|c|` (`RNP.hKerConstWlInf`) together with the universal
comparison `WDp 4 f ≤ C_W·WlInf α 4 f` (`OpenPkg.WDp_le_WlInf`) prices the coefficient by
`C_W·200·α`; the clause `t4` then gives `Ct·α^{-1/2}·(C_W·200α)·|g|² = (Ct·C_W·200)·√α·|g|²`.

Row 23 is the honest copy of the frozen `Nonlinear.Open.Row23`, whose proof never uses the
Galerkin class of `g` nor the `IP`-interface: it factors `N₄^{ss} = a(θ)·r(z)` with
`a = -(2α²/c)·D_θΓ` and `r = hKer²`, and applies the angular × radial separated estimate
`RNP.Xn_ang_rad_le_gen` with the *sharp* angular majorant `Γ(θ)·(α + sin 2θ)` (whose weighted
square is integrable uniformly in `α`, `RNP.gamWeightInt`).  This half is delivered by the
child lemma `N4bRow23.rowN4ssHon`.

Both constants are absolute (they depend only on `Ct`, `C_W` and `Cs`).
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.StrongEps.E4R3.N4C.Defs
import Submission.Work.FTS.StrongEps.E4R3.N4C.rows.Hon
import Submission.Work.FTS.StrongEps.E4R3.N4C.rows.HonDecay
import Submission.Work.FTS.StrongEps.E4R3.N4C.rows.N4bRow23.rowN4ssHon
import Submission.Work.FTS.Nonlinear.Pieces.RNP.row22
import Submission.Work.FTS.OpenPkg.WDp_le_WlInf
import Submission.Work.FTS.NonlinRows.NRow1_7Aux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E4R3.N4C.rows

open scoped Real Topology
open MeasureTheory Set Filter

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! ## The radial coefficient

`-(1/2)·FK(F_*) = -α·hKer`, so all the one-dimensional facts of
`Nonlinear/Pieces/RNP/row22.lean` apply: `hKer` is `C^∞` on `(0,∞)` and the `𝒲^{4,∞}`-norm of
`c·hKer` is at most `200|c|`. -/

/-- `(z,θ) ↦ c·z/(1+z)²` is `C^∞` on the open quadrant. -/
private theorem hKerConst_smoothOpenN4b (c : ℝ) :
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
    exact pow_ne_zero 2 (by linarith [Set.mem_Ioi.mp hz])
  exact ContDiffOn.const_smul c hker

/-- **Row 22 of the honest §8 table** (pairing bound only): for every honest context,

  `|IP α (N₄^{sg} α g) g| ≤ K·√α·(Xn α g)²`,   `N₄^{sg} α g = -(1/2)·FK(F_*)·D_θ g`.

Constant `K = Ct·(C_W·200) + 1`, with `C_W` the constant of `OpenPkg.WDp_le_WlInf`. -/
theorem rowN4sgHon (IP : ℝ → Fn → Fn → ℝ) {α₂ Ci Ct Cs : ℝ}
    (hN : Work.FTS.OpenPkg.N4Norm' Ci α₂)
    (hE : Work.FTS.StrongEps.E4R3.N4C.N4ExtraH IP α₂ Ct) :
    ∃ K : ℝ, 0 < K ∧ ∀ {α Ce : ℝ} {g Φs Φg : Fn},
      Work.FTS.StrongEps.E4R3.N4C.CtxT Cs Ce α₂ α g Φs Φg →
      |IP α (Work.FTS.Nonlin.N4sg α g) g|
        ≤ K * (Real.sqrt α * Work.FTS.Nonlin.Xn α g ^ 2) := by
  obtain ⟨CW, hCW0, hCW⟩ := Work.FTS.OpenPkg.WDp_le_WlInf
  have hCt0 : 0 < Ct := hE.pos.1
  refine ⟨Ct * (CW * 200) + 1, by positivity, ?_⟩
  intro α Ce g Φs Φg hctx
  have hα : 0 < α := hctx.hα
  have hα1 : α ≤ 1 := hctx.hα1
  have hIoc : α ∈ Set.Ioc 0 α₂ := ⟨hα, hctx.hαα₂⟩
  have hX0 : 0 ≤ Work.FTS.Nonlin.Xn α g := Work.Spaces.HkNorm_nonneg α 4 g
  -- ## the radial coefficient `f = -(1/2)·FK(F_*)`
  set f : Fn := fun z _ => -(1 / 2) * Work.Construction.FK (Work.Construction.Fstar α) z
    with hfdef
  -- `FK(F_*) = α·2z/(1+z)²`, so `f = (-α)·hKer`
  have hcoef : f = fun z _ => (-α) * Work.Spaces.hKer z := by
    funext z θ
    rw [hfdef]
    simp only [Work.FTS.Nonlin.FK_Fstar hα hα1, Work.Spaces.hKer_apply]
    ring
  have hsm_f : Work.FTS.EllipticEst.SmoothOpen f := by
    rw [hcoef]
    exact hKerConst_smoothOpenN4b (-α)
  have hker := Work.FTS.Nonlinear.Pieces.RNP.hKerConstWlInf α (-α)
  have hWmem : Work.Spaces.WlInfMem α 4 f := by
    rw [hcoef]
    exact hker.1
  have hWle : Work.Spaces.WlInf α 4 f ≤ 200 * α := by
    rw [hcoef]
    have h := hker.2
    rw [abs_neg, abs_of_pos hα] at h
    exact h
  -- ## the `D`-sup norm of the coefficient, through `WDp ≤ C_W·WlInf`
  have hWDmem : Work.FTS.VocabO.WDMem 4 f := fun b j hbj =>
    ⟨200 * Work.Spaces.WlInf α 4 f, fun z θ hz hθ1 hθ2 =>
      Work.FTS.OpenPkg.mixed_le_WlInf_200 hα hα1 hsm_f hWmem hbj hz ⟨hθ1, hθ2⟩⟩
  have hWDp : Work.FTS.VocabO.WDp 4 f ≤ CW * (200 * α) :=
    (hCW α f hα hα1 hsm_f hWmem).trans (mul_le_mul_of_nonneg_left hWle hCW0.le)
  -- ## `N₄^{sg}` is the product of the coefficient with `D_θ g`
  have hN4eq : Work.FTS.Nonlin.N4sg α g = fun z θ => f z θ * Work.Spaces.Dth g z θ := by
    funext z θ
    rw [hfdef]
    simp only [Work.FTS.Nonlin.N4sg]
  rw [hN4eq]
  -- ## the transport clause `t4`
  have ht4 := hE.t4 α hIoc f g hsm_f hWDmem hctx.hSmoothOpen hctx.hkMem4 hctx.hkMem5
    hctx.hdecay
  have hXn2 : 0 ≤ Work.FTS.Nonlin.Xn α g ^ 2 := pow_nonneg hX0 2
  have hA0 : 0 ≤ Ct * α ^ (-(1 / 2 : ℝ)) :=
    mul_nonneg hCt0.le (Real.rpow_nonneg hα.le _)
  -- `α^{-1/2}·α = √α`
  have hsqrt : α ^ (-(1 / 2 : ℝ)) * α = Real.sqrt α := by
    have h := (Real.rpow_add hα (-(1 / 2 : ℝ)) (1 : ℝ)).symm
    rw [Real.rpow_one, show -(1 / 2 : ℝ) + 1 = 1 / 2 by norm_num] at h
    rw [h, Real.sqrt_eq_rpow]
  have hchain : |IP α (fun z θ => f z θ * Work.Spaces.Dth g z θ) g|
      ≤ Ct * (CW * 200) * (Real.sqrt α * Work.FTS.Nonlin.Xn α g ^ 2) := by
    refine ht4.trans ?_
    refine (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hWDp hA0) hXn2).trans ?_
    rw [show Ct * α ^ (-(1 / 2 : ℝ)) * (CW * (200 * α)) * Work.FTS.Nonlin.Xn α g ^ 2
        = Ct * (CW * 200) * (α ^ (-(1 / 2 : ℝ)) * α)
          * Work.FTS.Nonlin.Xn α g ^ 2 from by ring, hsqrt]
    exact le_of_eq (by ring)
  refine hchain.trans ?_
  refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg (Real.sqrt_nonneg α) hXn2)
  linarith

theorem rowsN4b (IP : ℝ → Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn → ℝ)
    {α₂ Ci Ct Ce Cs : ℝ} (hN : Work.FTS.OpenPkg.N4Norm' Ci α₂)
    (hE : Work.FTS.StrongEps.E4R3.N4C.N4ExtraH IP α₂ Ct) :
    ∃ K : ℝ, 0 < K ∧ ∀ {α : ℝ} {g Φs Φg : Work.FTS.Galerkin.Fn},
      Work.FTS.StrongEps.E4R3.N4C.CtxT Cs Ce α₂ α g Φs Φg →
      |IP α (Work.FTS.Nonlin.N4sg α g) g| ≤ K * (Real.sqrt α * Work.FTS.Nonlin.Xn α g ^ 2) ∧
      Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N4ss α) ≤ K * α ^ 3 := by
  obtain ⟨K1, hK1, h1⟩ := rowN4sgHon IP hN hE
  obtain ⟨K2, hK2, h2⟩ :=
    Work.FTS.StrongEps.E4R3.N4C.rows.N4bRow23.rowN4ssHon IP hN hE
  refine ⟨max K1 K2, lt_of_lt_of_le hK1 (le_max_left K1 K2), ?_⟩
  intro α g Φs Φg hctx
  refine ⟨?_, ?_⟩
  · refine (h1 hctx).trans (mul_le_mul_of_nonneg_right (le_max_left K1 K2) ?_)
    exact mul_nonneg (Real.sqrt_nonneg α) (sq_nonneg _)
  · refine (h2 hctx).trans (mul_le_mul_of_nonneg_right (le_max_right K1 K2) ?_)
    exact pow_nonneg hctx.hα.le 3

end Work.FTS.StrongEps.E4R3.N4C.rows
