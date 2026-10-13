/-
# `E4R3/N4C/rows/rowsN4a` — rows 20, 21 of the honest §8 table

`Work.FTS.StrongEps.E4R3.N4C.rows.rowsN4a` proves the two `N₄^{gg}`/`N₄^{gs}` rows of the
honest (class-`C`) §8 table:

* row 20: `|IP α (N₄^{gg} α g) g| ≤ K·α^{-1/2}·|g|³`, where
  `N₄^{gg} = -(1/2)·FK(g)·D_θ g`;
* row 21: `|N₄^{gs} α g| ≤ K·α^{3/2}·|g|`, where
  `N₄^{gs} = -(1/2)·sin(2θ)·FK(g)·∂_θF_*`,

in the honest context `CtxT` (profile data `ClassC α g ∧ CoerAdmO α g`, open-quadrant elliptic
packages) and using only the clause bundle `N4ExtraH` (whose `t1` clause is the `D_θ`-transport
with an `ℋ⁴`-coefficient) plus the interface clauses of `OpenPkg.N4Norm'`.

## Route

Row 20 is the honest copy of the frozen `Nonlinear.Open.Row20`: with `r z = -(1/2)FK(g)(z)` and
the `t1`-clause,

  `|IP α (r·D_θ g) g| ≤ Ct·α^{-1/2}·|r|_{ℋ⁴}·|g|²`,

and `|r|_{ℋ⁴} = (1/2)|FK g|_{ℋ⁴} ≤ (1/2)·Ci·|g|` (`N4Norm'.fkH`), which gives the stated rate.
The only honest ingredient needed is the *smoothness* of the radial coefficient `r`:
`FK(g)` is `C^∞` on the open quadrant because `FK(F) = 3F_*(F)` and the all-order smoothness
of the angular moment `F_*(g)` is the field `ClassC.fsm`
(`StrongEps.EpsZero.ClassCHk.so_FKw`).

Row 21 uses the identity `sin(2θ)·∂_θF_* = D_θF_*`, i.e.

  `N₄^{gs} = -(1/2)·(D_θF_*)·FK(g)`,

together with the `𝒲^{4,∞}`-product clause `N4Norm'.wprod` at the coefficient
`D_θF_*` (`|D_θF_*|_{𝒲^{4,∞}} ≤ Cdth·α²`, the delivered `Nonlin.DthFstar_W`):

  `|(D_θF_*)·FK g|_{ℋ⁴} ≤ Ci·α^{-1/2}·(Cdth α²)·Ci|g| = (Ci²Cdth)·α^{3/2}·|g|`,

and `α^{-1/2}·α² = α^{3/2}` for `α > 0`.

Both constants are absolute (depending only on `Ci`, `Ct` and the universal `Cdth`). -/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.StrongEps.E4R3.N4C.Defs
import Submission.Work.FTS.StrongEps.E4R3.N4C.rows.Hon
import Submission.Work.FTS.StrongEps.E4R3.N4C.rows.HonDecay
import Submission.Work.FTS.StrongEps.EpsZero.ClassCHk.NMemAux
import Submission.Work.FTS.Nonlinear.FstarPkgAll
import Submission.Work.FTS.Nonlinear.Pieces.Basic
import Submission.Work.FTS.LocData.SmoothQuad_Fstar
import Submission.Work.FTS.LocData.HkMem_const_mul
import Submission.Work.FTS.NonlinRows.NRow1_7Aux

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E4R3.N4C.rows

open scoped Real Topology
open MeasureTheory Set Filter

set_option maxHeartbeats 1600000

theorem rowsN4a (IP : ℝ → Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn → ℝ)
    {α₂ Ci Ct Ce Cs : ℝ} (hN : Work.FTS.OpenPkg.N4Norm' Ci α₂)
    (hE : Work.FTS.StrongEps.E4R3.N4C.N4ExtraH IP α₂ Ct) :
    ∃ K : ℝ, 0 < K ∧ ∀ {α : ℝ} {g Φs Φg : Work.FTS.Galerkin.Fn},
      Work.FTS.StrongEps.E4R3.N4C.CtxT Cs Ce α₂ α g Φs Φg →
      |IP α (Work.FTS.Nonlin.N4gg α g) g|
          ≤ K * (α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g ^ 3) ∧
      Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N4gs α g)
          ≤ K * (α ^ (3 / 2 : ℝ) * Work.FTS.Nonlin.Xn α g) := by
  obtain ⟨Cdth, hCdth0, hDthW⟩ := Work.FTS.Nonlin.DthFstar_W
  have hCi0 : 0 < Ci := hN.pos.1
  have hCt0 : 0 < Ct := hE.pos.1
  -- the two row constants
  have hKpos : 0 < (Ct * Ci / 2 + 1) + (Ci * Ci * Cdth / 2 + 1) := by
    nlinarith [hCi0, hCt0, hCdth0]
  refine ⟨(Ct * Ci / 2 + 1) + (Ci * Ci * Cdth / 2 + 1), hKpos, ?_⟩
  intro α g Φs Φg hctx
  have hα : 0 < α := hctx.hα
  have hα1 : α ≤ 1 := hctx.hα1
  have hIoc : α ∈ Set.Ioc 0 α₂ := ⟨hα, hctx.hαα₂⟩
  have hX0 : 0 ≤ Work.FTS.Nonlin.Xn α g := Work.Spaces.HkNorm_nonneg α 4 g
  -- ## the reference coefficient `D_θF_*`
  have hDthF_sm : Work.FTS.EllipticEst.SmoothOpen
      (Work.Spaces.Dth (Work.Construction.Fstar α)) :=
    (Work.FTS.OpenPkg.smoothOpen_of_smoothQuad (Work.FTS.LocData.SmoothQuad_Fstar α)).Dth
  have hDthF_mem : Work.Spaces.WlInfMem α 4 (Work.Spaces.Dth (Work.Construction.Fstar α)) :=
    (hDthW α hα hα1).1
  have hDthF_bnd : Work.Spaces.WlInf α 4 (Work.Spaces.Dth (Work.Construction.Fstar α))
      ≤ Cdth * α ^ 2 := (hDthW α hα hα1).2
  -- ## `FK(g)` is smooth on the open quadrant (the field `ClassC.fsm`) and honest
  have hFKsm : Work.FTS.EllipticEst.SmoothOpen (fun z _ => Work.Construction.FK g z) :=
    Work.FTS.StrongEps.EpsZero.ClassCHk.so_FKw hctx.hg
  have hfk := hN.fkH α hIoc g hctx.hqo4 hctx.hL12
  -- ## the radial coefficient `r = -(1/2)·FK(g)`
  set r : ℝ → ℝ := fun z => -(1 / 2) * Work.Construction.FK g z with hrdef
  have hrsm : Work.FTS.EllipticEst.SmoothOpen (fun z _ => r z) := by
    rw [hrdef]
    exact Work.FTS.NonlinRows.smoothOpen_const_mul (-(1 / 2)) hFKsm
  have hrmem : Work.Spaces.HkMem α 4 (fun z _ => r z) := by
    rw [hrdef]
    exact Work.FTS.LocData.HkMem_const_mul α 4 (-(1 / 2)) hfk.1
  have hXr : Work.FTS.Nonlin.Xn α (fun z _ => r z)
      ≤ (1 / 2) * (Ci * Work.FTS.Nonlin.Xn α g) := by
    rw [hrdef, Work.FTS.Nonlinear.Pieces.RowsN0Aux.Xn_const_mul,
      show |(-(1 / 2) : ℝ)| = (1 / 2) by norm_num]
    exact mul_le_mul_of_nonneg_left hfk.2 (by norm_num)
  have hqo : Work.FTS.VocabO.HQo α 4 (fun z _ => r z) := ⟨hrsm, hrmem⟩
  -- ## row 20
  have ht1 := hE.t1 α hIoc (fun z _ => r z) g hqo hctx.hSmoothOpen hctx.hkMem4 hctx.hdecay
  have heq20 : Work.FTS.Nonlin.N4gg α g
      = fun z θ => r z * Work.Spaces.Dth g z θ := by
    funext z θ
    simp only [Work.FTS.Nonlin.N4gg, hrdef]
  have h20 : |IP α (Work.FTS.Nonlin.N4gg α g) g|
      ≤ (Ct * Ci / 2) * (α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g ^ 3) := by
    rw [heq20]
    refine ht1.trans ?_
    have hstep : Ct * α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α (fun z _ => r z)
          * Work.FTS.Nonlin.Xn α g ^ 2
        ≤ Ct * α ^ (-(1 / 2 : ℝ)) * ((1 / 2) * (Ci * Work.FTS.Nonlin.Xn α g))
          * Work.FTS.Nonlin.Xn α g ^ 2 :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hXr
          (mul_nonneg hCt0.le (Real.rpow_nonneg hα.le _)))
        (pow_nonneg hX0 2)
    refine hstep.trans ?_
    have harith : Ct * α ^ (-(1 / 2 : ℝ)) * ((1 / 2) * (Ci * Work.FTS.Nonlin.Xn α g))
          * Work.FTS.Nonlin.Xn α g ^ 2
        = (Ct * Ci / 2) * (α ^ (-(1 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g ^ 3) := by ring
    rw [harith]
  -- ## row 21
  have hαpow : α ^ (-(1 / 2 : ℝ)) * (α : ℝ) ^ 2 = α ^ (3 / 2 : ℝ) := by
    rw [← Real.rpow_natCast α 2, ← Real.rpow_add hα]
    norm_num
  have heq21 : Work.FTS.Nonlin.N4gs α g
      = fun z θ => -(1 / 2) * (Work.Spaces.Dth (Work.Construction.Fstar α) z θ
          * Work.Construction.FK g z) := by
    funext z θ
    simp only [Work.FTS.Nonlin.N4gs, Work.Spaces.Dth, Work.Construction.s2]
    ring
  have hw := hN.wprod α hIoc (Work.Spaces.Dth (Work.Construction.Fstar α))
    (fun z _ => Work.Construction.FK g z) hDthF_sm hDthF_mem ⟨hFKsm, hfk.1⟩
  have h21 : Work.FTS.Nonlin.Xn α (Work.FTS.Nonlin.N4gs α g)
      ≤ (Ci * Ci * Cdth / 2) * (α ^ (3 / 2 : ℝ) * Work.FTS.Nonlin.Xn α g) := by
    rw [heq21, Work.FTS.Nonlinear.Pieces.RowsN0Aux.Xn_const_mul,
      show |(-(1 / 2) : ℝ)| = (1 / 2) by norm_num]
    have hb2 : Work.FTS.Nonlin.Xn α
          (fun z θ => Work.Spaces.Dth (Work.Construction.Fstar α) z θ
            * Work.Construction.FK g z)
        ≤ Ci * α ^ (-(1 / 2 : ℝ)) * (Cdth * α ^ 2) * (Ci * Work.FTS.Nonlin.Xn α g) := by
      refine hw.2.trans ?_
      have h1 : Ci * α ^ (-(1 / 2 : ℝ))
            * Work.Spaces.WlInf α 4 (Work.Spaces.Dth (Work.Construction.Fstar α))
            * Work.FTS.Nonlin.Xn α (fun z _ => Work.Construction.FK g z)
          ≤ Ci * α ^ (-(1 / 2 : ℝ)) * (Cdth * α ^ 2)
            * Work.FTS.Nonlin.Xn α (fun z _ => Work.Construction.FK g z) :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hDthF_bnd
            (mul_nonneg hCi0.le (Real.rpow_nonneg hα.le _)))
          (Work.Spaces.HkNorm_nonneg α 4 _)
      exact h1.trans (mul_le_mul_of_nonneg_left hfk.2 (by positivity))
    refine (mul_le_mul_of_nonneg_left hb2 (by norm_num : (0 : ℝ) ≤ (1 / 2))).trans ?_
    have harith : (1 / 2) * (Ci * α ^ (-(1 / 2 : ℝ)) * (Cdth * α ^ 2)
          * (Ci * Work.FTS.Nonlin.Xn α g))
        = (Ci * Ci * Cdth / 2) * (α ^ (3 / 2 : ℝ) * Work.FTS.Nonlin.Xn α g) := by
      rw [← hαpow]
      ring
    rw [harith]
  -- ## the two bounds with the common constant
  have hK1 : Ct * Ci / 2 ≤ (Ct * Ci / 2 + 1) + (Ci * Ci * Cdth / 2 + 1) := by
    nlinarith [hCi0, hCdth0]
  have hK2 : Ci * Ci * Cdth / 2 ≤ (Ct * Ci / 2 + 1) + (Ci * Ci * Cdth / 2 + 1) := by
    nlinarith [hCi0, hCt0, hCdth0]
  exact ⟨h20.trans (mul_le_mul_of_nonneg_right hK1
      (mul_nonneg (Real.rpow_nonneg hα.le _) (pow_nonneg hX0 3))),
    h21.trans (mul_le_mul_of_nonneg_right hK2
      (mul_nonneg (Real.rpow_nonneg hα.le _) hX0))⟩

end Work.FTS.StrongEps.E4R3.N4C.rows
