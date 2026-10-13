/-
# `E4R3/N4C/rowsNT` — the honest (class-`C`) §8 row table, rows 8–26

`Work.FTS.VocabO2.NRows2 IP α K g Φs Φg` is rows 8–26 of the §8 design table (Elgindi,
§8: the nineteen pieces `N₁^{gg}, …, N₅^{ss}` of the split of `N`), in the *open-quadrant*
vocabulary: the `ℋ⁴`-norm bounds of the `N₁`, `N₂^{g*}`, `N₃^{g*}`, `N₄^{g*}` and `N₅`-pieces,
and the `IP`-pairing bounds of the `N₂^{gg}`, `N₂^{*g}`, `N₃^{gg}`, `N₃^{*g}`, `N₄^{gg}` and
`N₄^{*g}`-pieces.

The frozen chapter `FTS/NonlinRows` proves this table over the Galerkin class
`Work.FTS.Nonlin.GalClass α g` (which carries `SmoothQuad g`, i.e. `C^∞` *through* `z = 0`), and
its re-export `FTS/Nonlinear.Open` over the same class.  The route of the `StrongEps` chapter
only supplies the *honest* class `N4C.CtxT`:

  `0 < α ∧ α ≤ 1 ∧ α ≤ α₂ ∧ ClassC α g ∧ CoerAdmO α g ∧ StarPkgo2 α Cs Φs ∧ EllPkgGo α Ce g Φg`

with `ClassC` (open-quadrant `C^∞`, `ℋ⁷`/`ℋ⁸`/`ℋ¹⁰`-honesty, `BdryTraces` up to order `6`,
`F_*(g)`-smoothness, the axis condition, `L₁₂ g 0 = 0`, the `θ`-traces) in place of `GalClass`.
The class-`C` replacement of the frozen `RegQ`-classes is the open class
`StrongEps.EpsE4Thr.RegQo` (`SmoothOpen` + `HkMem` + `BdryTraces`), and the `z = ∞` decay
`Work.Spaces.DecayAll 4 g` — the hypothesis of the transport clauses of the honest interface
`N4C.N4ExtraH` — is a consequence of `ClassC` alone
(`N4C.decayAll_of_classC`, consumed through `rows/HonDecay`).

This file proves `NRows2` in that honest context, by assembling the nine per-row bundles of
`Submission/Work/FTS/StrongEps/E4R3/N4C/rows/` (see `rows/NOTES_rowsNT.md` for the per-row
routes and the frozen sources each bundle is ported from).  `K` is a single constant, obtained
by adding the nine bundle constants.

Every declaration of this module is fully proved.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.StrongEps.E4R3.N4C.Defs
import Submission.Work.FTS.Nonlinear.Open.Main
import Submission.Work.FTS.VocabO2
import Submission.Work.FTS.StrongEps.E4R3.N4C.rows.rowsN1
import Submission.Work.FTS.StrongEps.E4R3.N4C.rows.rowsN2a
import Submission.Work.FTS.StrongEps.E4R3.N4C.rows.rowsN2b
import Submission.Work.FTS.StrongEps.E4R3.N4C.rows.rowsN3a
import Submission.Work.FTS.StrongEps.E4R3.N4C.rows.rowsN3b
import Submission.Work.FTS.StrongEps.E4R3.N4C.rows.rowsN4a
import Submission.Work.FTS.StrongEps.E4R3.N4C.rows.rowsN4b
import Submission.Work.FTS.StrongEps.E4R3.N4C.rows.rowsN5a
import Submission.Work.FTS.StrongEps.E4R3.N4C.rows.rowsN5b

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.E4R3.N4C

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-- **The honest §8 row table, rows 8–26** (the `NRows2` obligation of the level-four
nonlinear estimate), in the class-`C` context `CtxT`. -/
theorem rowsNT (IP : ℝ → Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn → ℝ)
    {α₂ Ci Ct Ce Cs : ℝ} (hN : Work.FTS.OpenPkg.N4Norm' Ci α₂)
    (hE : Work.FTS.StrongEps.E4R3.N4C.N4ExtraH IP α₂ Ct) :
    ∃ K : ℝ, 0 < K ∧ ∀ {α : ℝ} {g Φs Φg : Work.FTS.Galerkin.Fn},
      Work.FTS.StrongEps.E4R3.N4C.CtxT Cs Ce α₂ α g Φs Φg →
      Work.FTS.VocabO2.NRows2 IP α K g Φs Φg := by
  obtain ⟨K1, hK1, h1⟩ := rows.rowsN1 IP hN hE
  obtain ⟨K2, hK2, h2⟩ := rows.rowsN2a IP hN hE
  obtain ⟨K3, hK3, h3⟩ := rows.rowsN2b IP hN hE
  obtain ⟨K4, hK4, h4⟩ := rows.rowsN3a IP hN hE
  obtain ⟨K5, hK5, h5⟩ := rows.rowsN3b IP hN hE
  obtain ⟨K6, hK6, h6⟩ := rows.rowsN4a IP hN hE
  obtain ⟨K7, hK7, h7⟩ := rows.rowsN4b IP hN hE
  obtain ⟨K8, hK8, h8⟩ := rows.rowsN5a IP hN hE
  obtain ⟨K9, hK9, h9⟩ := rows.rowsN5b IP hN hE
  set K : ℝ := K1 + K2 + K3 + K4 + K5 + K6 + K7 + K8 + K9 + 1 with hKdef
  have hKpos : 0 < K := by rw [hKdef]; linarith
  have hle1 : K1 ≤ K := by rw [hKdef]; linarith
  have hle2 : K2 ≤ K := by rw [hKdef]; linarith
  have hle3 : K3 ≤ K := by rw [hKdef]; linarith
  have hle4 : K4 ≤ K := by rw [hKdef]; linarith
  have hle5 : K5 ≤ K := by rw [hKdef]; linarith
  have hle6 : K6 ≤ K := by rw [hKdef]; linarith
  have hle7 : K7 ≤ K := by rw [hKdef]; linarith
  have hle8 : K8 ≤ K := by rw [hKdef]; linarith
  have hle9 : K9 ≤ K := by rw [hKdef]; linarith
  refine ⟨K, hKpos, ?_⟩
  intro α g Φs Φg hctx
  obtain ⟨hr8, hr9, hr10, hr11⟩ := h1 hctx
  obtain ⟨hr12, hr13⟩ := h2 hctx
  obtain ⟨hr14, hr15⟩ := h3 hctx
  obtain ⟨hr16, hr17⟩ := h4 hctx
  obtain ⟨hr18, hr19⟩ := h5 hctx
  obtain ⟨hr20, hr21⟩ := h6 hctx
  obtain ⟨hr22, hr23⟩ := h7 hctx
  have hr24 := h8 hctx
  obtain ⟨hr25, hr26⟩ := h9 hctx
  -- the four elementary factors occurring on the right-hand sides
  have hX0 : 0 ≤ Work.FTS.Nonlin.Xn α g := Work.Spaces.HkNorm_nonneg α 4 g
  have hA : 0 ≤ α ^ (-(1 / 2 : ℝ)) := Real.rpow_nonneg hctx.hα.le _
  have hB : 0 ≤ α ^ (3 / 2 : ℝ) := Real.rpow_nonneg hctx.hα.le _
  have hS : 0 ≤ Real.sqrt α := Real.sqrt_nonneg α
  have hP : 0 ≤ α ^ 2 := pow_nonneg hctx.hα.le 2
  have hQ : 0 ≤ α ^ 3 := pow_nonneg hctx.hα.le 3
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hr8.trans (mul_le_mul_of_nonneg_right hle1 (mul_nonneg hA (pow_nonneg hX0 2)))
  · exact hr9.trans (mul_le_mul_of_nonneg_right hle1 (mul_nonneg hS hX0))
  · exact hr10.trans (mul_le_mul_of_nonneg_right hle1 (mul_nonneg hS hX0))
  · exact hr11.trans (mul_le_mul_of_nonneg_right hle1 hP)
  · exact hr12.trans (mul_le_mul_of_nonneg_right hle2 (mul_nonneg hA (pow_nonneg hX0 3)))
  · exact hr13.trans (mul_le_mul_of_nonneg_right hle2 (mul_nonneg hB hX0))
  · exact hr14.trans (mul_le_mul_of_nonneg_right hle3 (mul_nonneg hS (pow_nonneg hX0 2)))
  · exact hr15.trans (mul_le_mul_of_nonneg_right hle3 hP)
  · exact hr16.trans (mul_le_mul_of_nonneg_right hle4 (pow_nonneg hX0 3))
  · exact hr17.trans (mul_le_mul_of_nonneg_right hle4 (mul_nonneg hB hX0))
  · exact hr18.trans (mul_le_mul_of_nonneg_right hle5 (mul_nonneg hB (pow_nonneg hX0 2)))
  · exact hr19.trans (mul_le_mul_of_nonneg_right hle5 hQ)
  · exact hr20.trans (mul_le_mul_of_nonneg_right hle6 (mul_nonneg hA (pow_nonneg hX0 3)))
  · exact hr21.trans (mul_le_mul_of_nonneg_right hle6 (mul_nonneg hB hX0))
  · exact hr22.trans (mul_le_mul_of_nonneg_right hle7 (mul_nonneg hS (pow_nonneg hX0 2)))
  · exact hr23.trans (mul_le_mul_of_nonneg_right hle7 hQ)
  · exact hr24.trans (mul_le_mul_of_nonneg_right hle8 (pow_nonneg hX0 2))
  · exact hr25.trans (mul_le_mul_of_nonneg_right hle9 (mul_nonneg hS hX0))
  · exact hr26.trans (mul_le_mul_of_nonneg_right hle9 hP)

end Work.FTS.StrongEps.E4R3.N4C
