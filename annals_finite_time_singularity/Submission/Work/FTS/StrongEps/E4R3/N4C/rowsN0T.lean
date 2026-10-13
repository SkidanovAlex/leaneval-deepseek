import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.StrongEps.E4R3.N4C.Defs
import Submission.Work.FTS.StrongEps.E4R3.N4C.decayAll_of_classC
import Submission.Work.FTS.StrongEps.E4R3.N4C.HonRowsU.n0row2u
import Submission.Work.FTS.StrongEps.E4R3.N4C.HonRowsU.n0row3u
import Submission.Work.FTS.StrongEps.E4R3.N4C.HonRowsU.n0row4u
import Submission.Work.FTS.StrongEps.E4R3.N4C.HonRowsU.n0row5u
import Submission.Work.FTS.StrongEps.E4R3.N4C.HonRowsU.n0row6u
import Submission.Work.FTS.StrongEps.E4R3.N4C.HonRowsU.n0row7u
import Submission.Work.FTS.Nonlinear.Pieces.Basic
import Submission.Work.FTS.Nonlinear.Pieces.Rows

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E4R3.N4C

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false

/-!
# `E4R3/N4C/rowsN0T` — the `N₀`-block of the honest §8 table over the class-`C` context

`N0Rows IP α K g Φs Φg` (rows 1--7 of design §3.4) over the honest context `CtxT`, from the two
interfaces `N4Norm'`, `N4ExtraH`.

The seven rows are the honest (open-quadrant) twins of `Work.FTS.NonlinRows.NRow1_7`, proved in
the sibling modules of this directory:

* rows 2--7 in `Work.FTS.StrongEps.E4R3.N4C.HonRowsU.n0row{2..7}u` (uniform in the package
  constants `Cs`, `Ce`, which the target quantifies *after* the `∃ K`);
* row 1 is unconditional: `Work.FTS.Nonlinear.Pieces.RowsN0Aux.N0fix_bound`.

The passage from `CtxT` to the hypothesis list of each row is elementary: `ClassC` supplies
`SmoothOpen g`, `HkMem α k g` (`k ≤ 7`) and `L12 g 0 = 0`, and `decayAll_of_classC` supplies the
`L¹`-decay `DecayAll 4 g` used by the `ℋ⁴`-transport clauses of `N4ExtraH`; the two elliptic
packages are the `StarPkgo2`/`EllPkgGo` fields of the context itself.
-/

theorem rowsN0T (IP : ℝ → Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn → ℝ)
    {α₂ Ci Ct : ℝ} (hN : Work.FTS.OpenPkg.N4Norm' Ci α₂)
    (hE : Work.FTS.StrongEps.E4R3.N4C.N4ExtraH IP α₂ Ct) :
    ∃ K : ℝ, 0 < K ∧ ∀ {Cs Ce α : ℝ} {g Φs Φg : Work.FTS.Galerkin.Fn},
      Work.FTS.StrongEps.E4R3.N4C.CtxT Cs Ce α₂ α g Φs Φg →
      Work.FTS.Nonlinear.Pieces.N0Rows IP α K g Φs Φg := by
  obtain ⟨K1, hK1, h1⟩ := Work.FTS.Nonlinear.Pieces.RowsN0Aux.N0fix_bound
  obtain ⟨K2, hK2, h2⟩ := HonRowsU.n0row2u IP hN hE
  obtain ⟨K3, hK3, h3⟩ := HonRowsU.n0row3u IP hN hE
  obtain ⟨K4, hK4, h4⟩ := HonRowsU.n0row4u IP hN hE
  obtain ⟨K5, hK5, h5⟩ := HonRowsU.n0row5u IP hN hE
  obtain ⟨K6, hK6, h6⟩ := HonRowsU.n0row6u IP hN hE
  obtain ⟨K7, hK7, h7⟩ := HonRowsU.n0row7u IP hN hE
  refine ⟨K1 + K2 + K3 + K4 + K5 + K6 + K7 + 1, by linarith, ?_⟩
  intro Cs Ce α g Φs Φg hctx
  have hK1' : K1 ≤ K1 + K2 + K3 + K4 + K5 + K6 + K7 + 1 := by linarith
  have hK2' : K2 ≤ K1 + K2 + K3 + K4 + K5 + K6 + K7 + 1 := by linarith
  have hK3' : K3 ≤ K1 + K2 + K3 + K4 + K5 + K6 + K7 + 1 := by linarith
  have hK4' : K4 ≤ K1 + K2 + K3 + K4 + K5 + K6 + K7 + 1 := by linarith
  have hK5' : K5 ≤ K1 + K2 + K3 + K4 + K5 + K6 + K7 + 1 := by linarith
  have hK6' : K6 ≤ K1 + K2 + K3 + K4 + K5 + K6 + K7 + 1 := by linarith
  have hK7' : K7 ≤ K1 + K2 + K3 + K4 + K5 + K6 + K7 + 1 := by linarith
  have hX : 0 ≤ Work.FTS.Nonlin.Xn α g := Work.Spaces.HkNorm_nonneg α 4 g
  have hα0 : (0 : ℝ) ≤ α := hctx.hα.le
  have hsp : (0 : ℝ) ≤ Real.sqrt α := Real.sqrt_nonneg α
  have hA1 : (0 : ℝ) ≤ α ^ (-(1 : ℝ)) := Real.rpow_nonneg hα0 _
  have hA3 : (0 : ℝ) ≤ α ^ (-(3 / 2 : ℝ)) := Real.rpow_nonneg hα0 _
  have hA2 : (0 : ℝ) ≤ α ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hα0 _
  have hsm : Work.FTS.EllipticEst.SmoothOpen g := hctx.hg.reg
  have hm4 : Work.Spaces.HkMem α 4 g :=
    Work.FTS.OpenPkg.HkMem_mono_open hctx.hg.reg 4 (by norm_num) hctx.hg.mem
  have hm5 : Work.Spaces.HkMem α 5 g :=
    Work.FTS.OpenPkg.HkMem_mono_open hctx.hg.reg 5 (by norm_num) hctx.hg.mem
  have hl12 : Work.Construction.L12 g 0 = 0 := hctx.hg.l12
  have hdec : Work.Spaces.DecayAll 4 g := decayAll_of_classC hctx.hα hctx.hg hctx.hco
  obtain ⟨-, hr2⟩ := h2 hctx.hα hctx.hα1 hctx.hαα₂ hsm hm4 hm5 hl12 hdec hctx.hs hctx.hell
  obtain ⟨-, hr3⟩ := h3 hctx.hα hctx.hα1 hctx.hαα₂ hsm hm4 hm5 hl12 hdec hctx.hs hctx.hell
  obtain ⟨-, hr4⟩ := h4 hctx.hα hctx.hα1 hctx.hαα₂ hsm hm4 hm5 hl12 hdec hctx.hs hctx.hell
  obtain ⟨-, hr5⟩ := h5 hctx.hα hctx.hα1 hctx.hαα₂ hsm hm4 hm5 hl12 hdec hctx.hs hctx.hell
  obtain ⟨-, hr6⟩ := h6 hctx.hα hctx.hα1 hctx.hαα₂ hsm hm4 hm5 hl12 hdec hctx.hs hctx.hell
  obtain ⟨-, hr7⟩ := h7 hctx.hα hctx.hα1 hctx.hαα₂ hsm hm4 hm5 hl12 hdec hctx.hs hctx.hell
  exact
    { r1 := le_trans (h1 α hctx.hα hctx.hα1)
        (mul_le_mul_of_nonneg_right hK1' (sq_nonneg α))
      r2 := le_trans hr2
        (mul_le_mul_of_nonneg_right hK2' (mul_nonneg hA1 (pow_nonneg hX 2)))
      r3 := le_trans hr3
        (mul_le_mul_of_nonneg_right hK3' (mul_nonneg hsp hX))
      r4 := le_trans hr4
        (mul_le_mul_of_nonneg_right hK4' (mul_nonneg hA3 (pow_nonneg hX 3)))
      r5 := le_trans hr5
        (mul_le_mul_of_nonneg_right hK5' (mul_nonneg hsp hX))
      r6 := le_trans hr6
        (mul_le_mul_of_nonneg_right hK6' (mul_nonneg hA2 (pow_nonneg hX 3)))
      r7 := le_trans hr7
        (mul_le_mul_of_nonneg_right hK7' (mul_nonneg hsp (pow_nonneg hX 2))) }

end Work.FTS.StrongEps.E4R3.N4C
