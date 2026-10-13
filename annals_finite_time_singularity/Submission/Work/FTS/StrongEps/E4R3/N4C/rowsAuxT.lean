/-
# `E4R3/N4C/rowsAuxT` — the four auxiliary rows of the honest (class-`C`) §8 table

The auxiliary rows of the level-four table (`Work.FTS.Nonlinear.Pieces.AuxRows`) are

* `rak`  : `|AK α|_{ℋ⁴} ≤ K`,
* `rl0`  : `|L₁₂(N₀ α (F_*+g) g)(0)| ≤ K (α² + √α|g| + α^{-3/2}|g|²)`,
* `rl1`  : `|L₁₂(N α (F_*+g) (Φs+Φg))(0)| ≤ K (α² + √α|g| + α^{-3/2}|g|²)`,
* `rl2`  : `|L₁₂(3D_θg/(1+z))(0)| ≤ K |g|`,

with a single constant `K` independent of `α, g, Φs, Φg`.  In the frozen (closed-quadrant)
formulation they are `Work.FTS.Nonlinear.Pieces.rowsAux`, proved against `GalClass`/`N4Norm`.

This file establishes them in the **honest** class of the route: the context is
`N4C.CtxT Cs Ce α₂ α g Φs Φg` (`ClassC α g` + the open coercivity class `CoerAdmO α g` +
`StarPkgo2 α Cs Φs` + `EllPkgGo α Ce g Φg`), i.e. open-quadrant smoothness and `ℋ^k`-honesty
only — no `SmoothQuad`, no decay.

Nothing here needs the two interface bundles `N4Norm'`/`N4ExtraH`: each of the four rows is a
*profile-level* estimate.  The four pieces are already available, fully proved, in the tree:

* `rak` — `Work.FTS.Nonlinear.Pieces.rak_bound` (no hypothesis besides `0 < α ≤ 1`);
* `rl0` — `Work.FTS_MuLamOK.Rows.Rl0Open` (`SmoothOpen f`, `HkMem α 4 f`);
* `rl1` — `Work.FTS_MuLamOK.Rows.Rl1Open` (`SmoothOpen f`, `HkMem α 4 f`, `StarPkgo`,
  `EllPkgGo`, constant depending only on `Ce`, `Cs`);
* `rl2` — `Work.FTS_MuLamOK.Rows.Rl2Open` (`SmoothOpen f`, `HkMem α 4 f`).

The only work here is to extract from `CtxT` the fragment each piece needs
(`ClassC.reg` for `SmoothOpen`, `OpenPkg.HkMem_mono_open` for `HkMem α 4`) and to add the four
constants.  `ClassC α g` carries `HkMem α 7 g`, and `StarPkgo2` extends `StarPkgo`.
-/
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.StrongEps.E4R3.N4C.Defs
import Submission.Work.FTS.Nonlinear.Pieces.rowsAux
import Submission.Work.FTS.Nonlinear.Pieces.Rows
import Submission.Work.FTS_MuLamOK.Rows.Rl0Open
import Submission.Work.FTS_MuLamOK.Rows.Rl1Open
import Submission.Work.FTS_MuLamOK.Rows.Rl2Open

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E4R3.N4C

theorem rowsAuxT (IP : ℝ → Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn → ℝ)
    {α₂ Ci Ct Ce Cs : ℝ} (hN : Work.FTS.OpenPkg.N4Norm' Ci α₂)
    (hE : Work.FTS.StrongEps.E4R3.N4C.N4ExtraH IP α₂ Ct) :
    ∃ K : ℝ, 0 < K ∧ ∀ {α : ℝ} {g Φs Φg : Work.FTS.Galerkin.Fn},
      Work.FTS.StrongEps.E4R3.N4C.CtxT Cs Ce α₂ α g Φs Φg →
      Work.FTS.Nonlinear.Pieces.AuxRows IP α K g Φs Φg := by
  obtain ⟨K1, hK1pos, hK1⟩ := Work.FTS.Nonlinear.Pieces.rak_bound
  obtain ⟨K2, hK2pos, hK2⟩ := Work.FTS_MuLamOK.Rows.Rl0Open
  obtain ⟨K3, hK3pos, hK3⟩ := Work.FTS_MuLamOK.Rows.Rl1Open Ce Cs
  obtain ⟨K4, hK4pos, hK4⟩ := Work.FTS_MuLamOK.Rows.Rl2Open
  refine ⟨K1 + K2 + K3 + K4 + 1, by linarith, ?_⟩
  intro α g Φs Φg hctx
  have hα : 0 < α := hctx.hα
  have hα1 : α ≤ 1 := hctx.hα1
  -- the fragment of `ClassC` consumed by the four rows
  have hso : Work.FTS.EllipticEst.SmoothOpen g := hctx.hg.reg
  have hmem : Work.Spaces.HkMem α 4 g :=
    Work.FTS.OpenPkg.HkMem_mono_open hso 4 (by norm_num) hctx.hg.mem
  have hs : Work.FTS.VocabO.StarPkgo α Cs Φs := hctx.hs.toStarPkgo
  have hell : Work.FTS.VocabO.EllPkgGo α Ce g Φg := hctx.hell
  have hX : 0 ≤ Work.FTS.Nonlin.Xn α g := Work.Spaces.HkNorm_nonneg α 4 g
  have hB : 0 ≤ α ^ 2 + Real.sqrt α * Work.FTS.Nonlin.Xn α g
      + α ^ (-(3 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g ^ 2 := by
    have h1 : (0 : ℝ) ≤ α ^ 2 := sq_nonneg α
    have h2 : (0 : ℝ) ≤ Real.sqrt α * Work.FTS.Nonlin.Xn α g :=
      mul_nonneg (Real.sqrt_nonneg α) hX
    have h3 : (0 : ℝ) ≤ α ^ (-(3 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g ^ 2 :=
      mul_nonneg (Real.rpow_nonneg hα.le _) (sq_nonneg _)
    linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact (hK1 hα hα1).trans (by linarith)
  · exact (hK2 hα hα1 hso hmem).trans (mul_le_mul_of_nonneg_right (by linarith) hB)
  · exact (hK3 hα hα1 hso hmem hs hell).trans (mul_le_mul_of_nonneg_right (by linarith) hB)
  · exact (hK4 hα hα1 hso hmem).trans (mul_le_mul_of_nonneg_right (by linarith) hX)

end Work.FTS.StrongEps.E4R3.N4C
