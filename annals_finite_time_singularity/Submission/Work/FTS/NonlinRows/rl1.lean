/-
# `Submission/Work/FTS/NonlinRows/rl1.lean` — the primed `AuxRows.rl1` zero-mode estimate

`|L₁₂(N α (F_* + g) (Φ_* + Φ_g))(0)| ≤ K·(α² + √α·|g|_{ℋ⁴} + α^{-3/2}·|g|²_{ℋ⁴})`,
uniformly in the data of `Ctx` (the two primed interfaces `N4Norm'`/`N4Extra'` fixed).

## The route

The functional `L₁₂(·)(0)` is dominated by the density `Fa f = ∫⁻_r r⁻¹ ∫⁻_θ |K(θ)f(r,θ)|`
(`Work.FTS.Nonlinear.Pieces.ofReal_L12_le`), and `N` splits into its twenty summands
`N_i^{gg}, N_i^{gs}, N_i^{sg}, N_i^{ss}` (`i = 1..5`) on the open quadrant
(`Work.FTS.NonlinRows.Rl1.splitOpen`), enumerated by `rl1Tools.pv : Fin 20 → Fn`.  Each
summand is estimated in `Fa` by a multiple of the envelope
`Env α g = α² + √α·Xn α g + α^{-3/2}·(Xn α g)²`:

| rows | module | lemma |
|---|---|---|
| `N₁^{gg}`, `N₂^{gg}`, `N₃^{gg}` | `Rl1/ggBounds.lean` | `Rl1.ggBounds` (constant `Ce`) |
| `N₄^{gg}`, `N₅^{gg}` | `Rl1/Rows45.lean` | `Rl1.ggRows45` |
| `N₁^{gs}`, `N₂^{gs}`, `N₃^{gs}` | `Rl1/gsBounds.lean` | `Rl1.gsBounds` (constant `Ce`) |
| `N₄^{gs}`, `N₅^{gs}` | `Rl1/Rows45.lean` | `Rl1.gsRows45` (constant `Ce`) |
| `N₁^{sg}`, `N₂^{sg}`, `N₃^{sg}` | `Rl1/sgBounds.lean` | `Rl1.sgBounds` (constant `Cs`) |
| `N₄^{sg}`, `N₅^{sg}` | `Rl1/Rows45.lean` | `Rl1.sgRows45` (constant `Cs`) |
| `N₁^{ss}` … `N₅^{ss}` | `Rl1/ssBounds.lean` | `Rl1.ssBounds` (constant `Cs`) |

The two inputs that make the estimate go through in the *primed* vocabulary are

* the angular pointwise bound `Work.FTS.NonlinRows.Rl1.angSupHk` (the `RegQ`-based `gPt` of the
  frozen vocabulary is unavailable for the `EllPkgGo`-coefficients, which are only `HQo`), and
  `Work.FTS.NonlinRows.Rl1.starUopBound` (a bound for `𝒰(Φ̃_*)`, which `StarPkgo` does not
  supply directly; it is reached through `K·𝒰 = -3cos³θ·(ℛ - 𝒱)`);
* the generic tools `Work.FTS.NonlinRows.Rl1.tools` (`outer_gen` for a `z`-dependent coefficient
  majorant, the slot data `slot0`/`slot1`/`slot2`, the star coefficient bounds, and the explicit
  `F_*`-profile bounds).

The bookkeeping is: `Fa N ≤ Σ_{k} Fa (pv k)` (`rl1Tools.FaSumAE`, with the measurability bundle
`Work.FTS.NonlinRows.Rl1.PvecMeasOpen`), then `≤ 20·K·Env α g`, then the `ofReal`-monotonicity
`ENNReal.ofReal_le_ofReal_iff`.
-/
import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.NonlinRows.Defs
import Submission.Work.FTS.OpenPkg.Defs
import Submission.Work.FTS.OpenPkg.Basic
import Submission.Work.FTS.NonlinRows.Rl1.tools
import Submission.Work.FTS.NonlinRows.Rl1.splitOpen
import Submission.Work.FTS.NonlinRows.Rl1.ggBounds
import Submission.Work.FTS.NonlinRows.Rl1.gsBounds
import Submission.Work.FTS.NonlinRows.Rl1.sgBounds
import Submission.Work.FTS.NonlinRows.Rl1.ssBounds
import Submission.Work.FTS.NonlinRows.Rl1.Rows45
import Submission.Work.FTS.NonlinRows.Rl1.PvecMeasOpen
import Submission.Work.FTS.Nonlinear.Pieces.rl1Bound
import Submission.Work.FTS.Nonlinear.Pieces.rl1Tools.FaSumAE
import Submission.Work.FTS.Nonlinear.Pieces.rl1Tools.PvecMeas

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS.NonlinRows

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false

theorem rl1 (IP : ℝ → Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn → ℝ) {α₂ Ci Ct Ce Cs : ℝ}
    (hN : Work.FTS.OpenPkg.N4Norm' Ci α₂) (hE : Work.FTS.OpenPkg.N4Extra' IP α₂ Ct) :
    ∃ K : ℝ, 0 < K ∧ ∀ {α : ℝ} {g Φs Φg : Work.FTS.Galerkin.Fn},
      Work.FTS.NonlinRows.Ctx α₂ Ci Ct Ce Cs α g Φs Φg →
      |Work.Construction.L12 (Work.Construction.N α (Work.Construction.Ftot α g)
          (fun z θ => Φs z θ + Φg z θ)) 0|
        ≤ K * (α ^ 2 + Real.sqrt α * Work.FTS.Nonlin.Xn α g
            + α ^ (-(3 / 2 : ℝ)) * Work.FTS.Nonlin.Xn α g ^ 2) := by
  -- ## the twenty per-piece constants
  obtain ⟨K1, hK1, hb1⟩ := Work.FTS.NonlinRows.Rl1.ggBounds (Ce := Ce)
  obtain ⟨K1', hK1', hb1'⟩ := Work.FTS.NonlinRows.Rl1.ggRows45
  obtain ⟨K2, hK2, hb2⟩ := Work.FTS.NonlinRows.Rl1.gsBounds (Ce := Ce)
  obtain ⟨K2', hK2', hb2'⟩ := Work.FTS.NonlinRows.Rl1.gsRows45 (Ce := Ce)
  obtain ⟨K3, hK3, hb3⟩ := Work.FTS.NonlinRows.Rl1.sgBounds (Cs := Cs)
  obtain ⟨K3', hK3', hb3'⟩ := Work.FTS.NonlinRows.Rl1.sgRows45 (Cs := Cs)
  obtain ⟨K4, hK4, hb4⟩ := Work.FTS.NonlinRows.Rl1.ssBounds (Cs := Cs)
  refine ⟨20 * (K1 + K1' + K2 + K2' + K3 + K3' + K4 + 1),
    by linarith [hK1, hK1', hK2, hK2', hK3, hK3', hK4], ?_⟩
  intro α g Φs Φg hctx
  obtain ⟨hα, hα1, hαα₂, hgal, hs, hell⟩ := hctx
  have hEnv : 0 ≤ Work.FTS.NonlinRows.Rl1.Env α g :=
    Work.FTS.NonlinRows.Rl1.Env_nonneg g hα.le
  -- ## the twenty per-piece bounds, at the common constant
  have hpiece : ∀ k : Fin 20, Work.FTS.Nonlinear.Pieces.Fa
      (Work.FTS.Nonlinear.Pieces.rl1Tools.pv α g Φs Φg k)
        ≤ ENNReal.ofReal ((K1 + K1' + K2 + K2' + K3 + K3' + K4 + 1)
            * Work.FTS.NonlinRows.Rl1.Env α g) := by
    have h1 := hb1 hα hα1 hgal hell
    have h1' := hb1' hα hα1 hgal
    have h2 := hb2 hα hα1 hgal hell
    have h2' := hb2' hα hα1 hgal hell
    have h3 := hb3 hα hα1 hgal hs
    have h3' := hb3' hα hα1 hgal hs
    have h4 := hb4 hα hα1 hgal hs
    have e1 : ∀ {F : Work.FTS.Galerkin.Fn}, Work.FTS.Nonlinear.Pieces.Fa F
        ≤ ENNReal.ofReal (K1 * Work.FTS.NonlinRows.Rl1.Env α g) →
        Work.FTS.Nonlinear.Pieces.Fa F ≤ ENNReal.ofReal
          ((K1 + K1' + K2 + K2' + K3 + K3' + K4 + 1)
            * Work.FTS.NonlinRows.Rl1.Env α g) :=
      fun h => h.trans (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right (by linarith) hEnv))
    have e1' : ∀ {F : Work.FTS.Galerkin.Fn}, Work.FTS.Nonlinear.Pieces.Fa F
        ≤ ENNReal.ofReal (K1' * Work.FTS.NonlinRows.Rl1.Env α g) →
        Work.FTS.Nonlinear.Pieces.Fa F ≤ ENNReal.ofReal
          ((K1 + K1' + K2 + K2' + K3 + K3' + K4 + 1)
            * Work.FTS.NonlinRows.Rl1.Env α g) :=
      fun h => h.trans (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right (by linarith) hEnv))
    have e2 : ∀ {F : Work.FTS.Galerkin.Fn}, Work.FTS.Nonlinear.Pieces.Fa F
        ≤ ENNReal.ofReal (K2 * Work.FTS.NonlinRows.Rl1.Env α g) →
        Work.FTS.Nonlinear.Pieces.Fa F ≤ ENNReal.ofReal
          ((K1 + K1' + K2 + K2' + K3 + K3' + K4 + 1)
            * Work.FTS.NonlinRows.Rl1.Env α g) :=
      fun h => h.trans (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right (by linarith) hEnv))
    have e2' : ∀ {F : Work.FTS.Galerkin.Fn}, Work.FTS.Nonlinear.Pieces.Fa F
        ≤ ENNReal.ofReal (K2' * Work.FTS.NonlinRows.Rl1.Env α g) →
        Work.FTS.Nonlinear.Pieces.Fa F ≤ ENNReal.ofReal
          ((K1 + K1' + K2 + K2' + K3 + K3' + K4 + 1)
            * Work.FTS.NonlinRows.Rl1.Env α g) :=
      fun h => h.trans (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right (by linarith) hEnv))
    have e3 : ∀ {F : Work.FTS.Galerkin.Fn}, Work.FTS.Nonlinear.Pieces.Fa F
        ≤ ENNReal.ofReal (K3 * Work.FTS.NonlinRows.Rl1.Env α g) →
        Work.FTS.Nonlinear.Pieces.Fa F ≤ ENNReal.ofReal
          ((K1 + K1' + K2 + K2' + K3 + K3' + K4 + 1)
            * Work.FTS.NonlinRows.Rl1.Env α g) :=
      fun h => h.trans (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right (by linarith) hEnv))
    have e3' : ∀ {F : Work.FTS.Galerkin.Fn}, Work.FTS.Nonlinear.Pieces.Fa F
        ≤ ENNReal.ofReal (K3' * Work.FTS.NonlinRows.Rl1.Env α g) →
        Work.FTS.Nonlinear.Pieces.Fa F ≤ ENNReal.ofReal
          ((K1 + K1' + K2 + K2' + K3 + K3' + K4 + 1)
            * Work.FTS.NonlinRows.Rl1.Env α g) :=
      fun h => h.trans (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right (by linarith) hEnv))
    have e4 : ∀ {F : Work.FTS.Galerkin.Fn}, Work.FTS.Nonlinear.Pieces.Fa F
        ≤ ENNReal.ofReal (K4 * Work.FTS.NonlinRows.Rl1.Env α g) →
        Work.FTS.Nonlinear.Pieces.Fa F ≤ ENNReal.ofReal
          ((K1 + K1' + K2 + K2' + K3 + K3' + K4 + 1)
            * Work.FTS.NonlinRows.Rl1.Env α g) :=
      fun h => h.trans (ENNReal.ofReal_le_ofReal
        (mul_le_mul_of_nonneg_right (by linarith) hEnv))
    intro k
    fin_cases k
    · exact e1 h1.1
    · exact e2 h2.1
    · exact e3 h3.1
    · exact e4 h4.1
    · exact e1 h1.2.1
    · exact e2 h2.2.1
    · exact e3 h3.2.1
    · exact e4 h4.2.1
    · exact e1 h1.2.2
    · exact e2 h2.2.2
    · exact e3 h3.2.2
    · exact e4 h4.2.2.1
    · exact e1' h1'.1
    · exact e2' h2'.1
    · exact e3' h3'.1
    · exact e4 h4.2.2.2.1
    · exact e1' h1'.2
    · exact e2' h2'.2
    · exact e3' h3'.2
    · exact e4 h4.2.2.2.2
  -- ## the measurability of the twenty pieces
  have hmeas := Work.FTS.NonlinRows.Rl1.PvecMeasOpen hα hα1 hgal hs hell
  -- ## the exact split of `N` into its twenty summands
  have hsmg : Work.FTS.EllipticEst.SmoothOpen g :=
    Work.FTS.OpenPkg.smoothOpen_of_smoothQuad hgal.reg.1
  have hmemg : Work.Spaces.HkMem α 4 g := (Work.FTS.Nonlin.galClass_regQ4 hgal).2.1
  have hL12 : ∀ z : ℝ, 0 < z →
      DifferentiableAt ℝ (fun z' => Work.Construction.L12 g z') z :=
    fun z hz => hN.l12diff α ⟨hα, hαα₂⟩ g ⟨hsmg, hmemg⟩ z hz
  have hsp := Work.FTS.NonlinRows.Rl1.splitOpen hα hα1 hsmg hs.smooth hell.smooth
    (fun z hz => (Work.FTS.Nonlinear.Pieces.L12FK_add_ge0 hα hα1 hgal).1 z hz.le)
    (fun z hz => (Work.FTS.Nonlinear.Pieces.L12FK_add_ge0 hα hα1 hgal).2 z hz.le) hL12
  have hsplit : ∀ r θ : ℝ, (r, θ) ∈ Work.Construction.Qd →
      Work.Construction.N α (Work.Construction.Ftot α g)
        (fun z θ => Φs z θ + Φg z θ) r θ
        = ∑ k : Fin 20, Work.FTS.Nonlinear.Pieces.rl1Tools.pv α g Φs Φg k r θ := by
    intro r θ hq
    rw [hsp r θ hq]
    simp only [Work.FTS.Nonlinear.Pieces.rl1Tools.pv, Fin.sum_univ_succ,
      Matrix.cons_val_zero, Matrix.cons_val_succ, Fin.reduceFinMk]
    ring
  -- ## the `L¹(r⁻¹dr)`-triangle inequality
  have htri := Work.FTS.Nonlinear.Pieces.rl1Tools.FaSumAE
    (N := Work.Construction.N α (Work.Construction.Ftot α g)
      (fun z θ => Φs z θ + Φg z θ))
    (p := Work.FTS.Nonlinear.Pieces.rl1Tools.pv α g Φs Φg) hsplit hmeas.1 hmeas.2
  -- ## adding the twenty constants
  have hsum : (∑ k : Fin 20, Work.FTS.Nonlinear.Pieces.Fa
        (Work.FTS.Nonlinear.Pieces.rl1Tools.pv α g Φs Φg k))
      ≤ ENNReal.ofReal ((20 * (K1 + K1' + K2 + K2' + K3 + K3' + K4 + 1))
          * Work.FTS.NonlinRows.Rl1.Env α g) := by
    refine (Finset.sum_le_sum fun k _ => hpiece k).trans ?_
    rw [Finset.sum_const, Finset.card_fin, nsmul_eq_mul,
      show ((20 : ℕ) : ENNReal) = ENNReal.ofReal 20 from (ENNReal.ofReal_natCast 20).symm,
      ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 20)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [mul_assoc]
  -- ## assembling
  have hglue := Work.FTS.Nonlinear.Pieces.ofReal_L12_le
    (Work.Construction.N α (Work.Construction.Ftot α g) (fun z θ => Φs z θ + Φg z θ))
  have hkey : ENNReal.ofReal |Work.Construction.L12 (Work.Construction.N α
      (Work.Construction.Ftot α g) (fun z θ => Φs z θ + Φg z θ)) 0|
      ≤ ENNReal.ofReal ((20 * (K1 + K1' + K2 + K2' + K3 + K3' + K4 + 1))
          * Work.FTS.NonlinRows.Rl1.Env α g) := hglue.trans (htri.trans hsum)
  have hfin := (ENNReal.ofReal_le_ofReal_iff
    (mul_nonneg (by positivity) hEnv)).mp hkey
  simpa only [Work.FTS.NonlinRows.Rl1.Env] using hfin

end Work.FTS.NonlinRows
