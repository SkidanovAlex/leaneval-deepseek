/-
# `Submission/Work/FTS_MuLamOK/Rows/Rl1Open.lean` — the `rl1` zero-mode estimate in the
open-quadrant class, against the *tight* envelope

`|L₁₂(N α (F_*+f)(Φ_s+Φ_f))(0)| ≤ K·(α² + √α·|f|_{ℋ⁴} + α^{-3/2}·|f|²_{ℋ⁴})`

from the *honest* (interior) hypotheses only: `SmoothOpen f` (`C^∞` on the open quadrant),
`HkMem α 4 f`, `StarPkgo α Cs Φs`, `EllPkgGo α Ce f Φg`, with a single constant `K` depending
only on `Ce` and `Cs` — in particular **independent of `α`**.  This is the primed counterpart
of `Work.FTS.NonlinRows.rl1`, which needs the closed-quadrant package `GalClass` (hence
`SmoothQuad`) and the `N₄Norm`/`N₄Extra` interfaces.

## Route

* `|L₁₂(N)(0)|` is dominated by the absolute density `Fa N = ∫⁻_r r⁻¹ ∫⁻_θ |K θ·N r θ|`
  (`Work.FTS.Nonlinear.Pieces.ofReal_L12_le`).
* `N` splits on the open quadrant into its twenty summands `pv α f Φ_s Φ_g k`
  (`Rl1.splitOpen`), whose three inputs are `NZeroAux.L12add` (additivity and
  differentiability of `z ↦ L₁₂(f)(z)`) and `Rl1Defs.FKaddOpen` (additivity of the angular
  moment).
* The `L¹(dr/r)`-triangle inequality is `rl1Tools.FaSumAE`, with the a.e. strong
  measurability of the twenty pieces from `RowMuAux.meas_open` — both in the honest class.
* Each piece is bounded by a multiple of `Env α f` (`Rl1Pieces.piecesEnv`), and the twenty
  constants are added.

The auxiliary material lives in the sibling modules of this directory: `Rl1Defs` (the
angular moment `FKaddOpen`, the constant conversions and the rate comparisons), the three
delivered row blocks `GgRowsEnv`, `SgRowsEnv`, `SsRowsEnv`, and `Rl1Pieces` (the
twenty-piece table `piecesEnv`).

Everything here rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS_MuLamOK.Rows.Rl1Pieces
import Submission.Work.FTS_MuLamOK.Rows.Rl1Defs
import Submission.Work.FTS.NonlinRows.Rl1.splitOpen
import Submission.Work.FTS.Nonlinear.Pieces.rl1Tools.FaSumAE
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.RowMuAux.meas_open
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.NZeroAux.L12add
import Submission.Work.FTS.Nonlinear.Pieces.rl1Bound

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS_MuLamOK.Rows

open scoped Real Topology ENNReal
open MeasureTheory Set Filter
open Work.FTS.Galerkin (Fn)
open Work.FTS.Nonlinear.Pieces (Fa)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

theorem Rl1Open : ∀ Ce Cs : ℝ, ∃ K : ℝ, 0 < K ∧
    ∀ {α : ℝ} {f Φs Φg : ℝ → ℝ → ℝ},
    0 < α → α ≤ 1 → Work.FTS.EllipticEst.SmoothOpen f → Work.Spaces.HkMem α 4 f →
    Work.FTS.VocabO.StarPkgo α Cs Φs → Work.FTS.VocabO.EllPkgGo α Ce f Φg →
    |Work.Construction.L12 (Work.Construction.N α (Work.Construction.Ftot α f)
        (fun z θ => Φs z θ + Φg z θ)) 0|
      ≤ K * (α ^ 2 + Real.sqrt α * Work.FTS.Nonlin.Xn α f
          + α ^ (-(3 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α f ^ 2) := by
  intro Ce Cs
  obtain ⟨Kc, hKcpos, hpiece⟩ := piecesEnv Ce Cs
  refine ⟨20 * Kc + 1, by linarith, ?_⟩
  intro α f Φs Φg hα hα1 hso hmem hs hell
  have hX : 0 ≤ Work.FTS.Nonlin.Xn α f := Work.Spaces.HkNorm_nonneg α 4 f
  have hEnv0 : 0 ≤ Work.FTS.NonlinRows.Rl1.Env α f :=
    Work.FTS.NonlinRows.Rl1.Env_nonneg f hα.le
  -- the three inputs of the split
  have hadd := Work.FTS.StrongPersist.H6Pair6Aux.NZeroAux.L12add hα hα1 hso hmem
  have hL : ∀ z : ℝ, 0 < z → Work.Construction.L12 (Work.Construction.Ftot α f) z
      = Work.Construction.L12 (Work.Construction.Fstar α) z + Work.Construction.L12 f z :=
    fun z hz => hadd.1 z hz.le
  have hL12 : ∀ z : ℝ, 0 < z →
      DifferentiableAt ℝ (fun z' => Work.Construction.L12 f z') z := hadd.2.1
  have hsp := Work.FTS.NonlinRows.Rl1.splitOpen (α := α) (g := f) (Φs := Φs) (Φg := Φg)
    hα hα1 hso hs.smooth hell.smooth hL (FKaddOpen hα hso hmem) hL12
  -- the exact split of `N` into its twenty summands
  have hsplit : ∀ r θ : ℝ, (r, θ) ∈ Work.Construction.Qd →
      Work.Construction.N α (Work.Construction.Ftot α f)
        (fun z θ => Φs z θ + Φg z θ) r θ
        = ∑ k : Fin 20, Work.FTS.Nonlinear.Pieces.rl1Tools.pv α f Φs Φg k r θ := by
    intro r θ hq
    rw [hsp r θ hq]
    simp only [Work.FTS.Nonlinear.Pieces.rl1Tools.pv, Fin.sum_univ_succ, Matrix.cons_val_zero,
      Matrix.cons_val_succ]
    ring
  -- the measurability and the `L¹(dr/r)`-triangle inequality
  have hmeas := Work.FTS.StrongPersist.H6Pair6Aux.RowMuAux.meas_open hα hα1 hso hmem hs hell
  have htri := Work.FTS.Nonlinear.Pieces.rl1Tools.FaSumAE
    (N := Work.Construction.N α (Work.Construction.Ftot α f)
      (fun z θ => Φs z θ + Φg z θ))
    (p := Work.FTS.Nonlinear.Pieces.rl1Tools.pv α f Φs Φg) hsplit hmeas.1 hmeas.2
  -- the twenty per-piece bounds
  have hsum : (∑ k : Fin 20,
        Fa (Work.FTS.Nonlinear.Pieces.rl1Tools.pv α f Φs Φg k))
      ≤ ENNReal.ofReal (20 * Kc * Work.FTS.NonlinRows.Rl1.Env α f) := by
    have h1 : ∑ k : Fin 20, Fa (Work.FTS.Nonlinear.Pieces.rl1Tools.pv α f Φs Φg k)
        ≤ ∑ _k : Fin 20, ENNReal.ofReal (Kc * Work.FTS.NonlinRows.Rl1.Env α f) :=
      Finset.sum_le_sum (fun k _ => hpiece hα hα1 hso hmem hs hell k)
    have h2 : ∑ _k : Fin 20, ENNReal.ofReal (Kc * Work.FTS.NonlinRows.Rl1.Env α f)
        = 20 • ENNReal.ofReal (Kc * Work.FTS.NonlinRows.Rl1.Env α f) := by
      simp [Finset.sum_const, Finset.card_univ]
    have h3 : (20 : ℕ) • ENNReal.ofReal (Kc * Work.FTS.NonlinRows.Rl1.Env α f)
        = ENNReal.ofReal (20 * Kc * Work.FTS.NonlinRows.Rl1.Env α f) := by
      have h20 : (0 : ℝ) ≤ 20 := by norm_num
      have h20e : (20 : ENNReal) = ENNReal.ofReal 20 := (ENNReal.ofReal_natCast 20).symm
      calc (20 : ℕ) • ENNReal.ofReal (Kc * Work.FTS.NonlinRows.Rl1.Env α f)
          = (20 : ENNReal) * ENNReal.ofReal (Kc * Work.FTS.NonlinRows.Rl1.Env α f) :=
            nsmul_eq_mul 20 _
        _ = ENNReal.ofReal 20 * ENNReal.ofReal (Kc * Work.FTS.NonlinRows.Rl1.Env α f) := by
            rw [h20e]
        _ = ENNReal.ofReal (20 * (Kc * Work.FTS.NonlinRows.Rl1.Env α f)) :=
            (ENNReal.ofReal_mul h20).symm
        _ = ENNReal.ofReal (20 * Kc * Work.FTS.NonlinRows.Rl1.Env α f) := by
            congr 1
            ring
    rw [h2, h3] at h1
    exact h1
  -- the `ofReal`-glue and the passage to `|L₁₂(N)(0)|`
  have hkey : ENNReal.ofReal |Work.Construction.L12 (Work.Construction.N α
      (Work.Construction.Ftot α f) (fun z θ => Φs z θ + Φg z θ)) 0|
      ≤ ENNReal.ofReal (20 * Kc * Work.FTS.NonlinRows.Rl1.Env α f) :=
    (Work.FTS.Nonlinear.Pieces.ofReal_L12_le _).trans (htri.trans hsum)
  have hfin : |Work.Construction.L12 (Work.Construction.N α (Work.Construction.Ftot α f)
      (fun z θ => Φs z θ + Φg z θ)) 0|
      ≤ 20 * Kc * Work.FTS.NonlinRows.Rl1.Env α f :=
    (ENNReal.ofReal_le_ofReal_iff
      (mul_nonneg (mul_nonneg (by norm_num) hKcpos.le) hEnv0)).mp hkey
  -- unfold the envelope and enlarge the constant
  refine hfin.trans ?_
  rw [Work.FTS.NonlinRows.Rl1.Env]
  have hB0 : 0 ≤ α ^ 2 + Real.sqrt α * Work.FTS.Nonlin.Xn α f
      + α ^ (-(3 / 2 : ℝ)) * (Work.FTS.Nonlin.Xn α f) ^ 2 := by
    have h1 : (0 : ℝ) ≤ α ^ 2 := sq_nonneg α
    have h2 : (0 : ℝ) ≤ Real.sqrt α * Work.FTS.Nonlin.Xn α f :=
      mul_nonneg (Real.sqrt_nonneg α) hX
    have h3 : (0 : ℝ) ≤ α ^ (-(3 / 2 : ℝ)) * (Work.FTS.Nonlin.Xn α f) ^ 2 :=
      mul_nonneg (Real.rpow_nonneg hα.le _) (sq_nonneg _)
    linarith
  exact mul_le_mul_of_nonneg_right (by linarith) hB0

end Work.FTS_MuLamOK.Rows
