import Mathlib.Analysis.Calculus.FDeriv.Defs
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.OpenPkg.Pieces4
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.NZeroAux.L12add
import Submission.Work.FTS.StrongPersist.N6Trans.T1Hon.EasyLeibIntBound
import Submission.Work.FTS.VocabO2
import Submission.Work.FTS_MuLamOK.Rows.Rl1Defs
import Submission.Work.FTS_MuLamOK.Rows.Rl1Pieces
import Submission.Work.FTS_MuLamOK.Rows.Rl2Open
import Submission.Work.FTS_MuLipC.RowN.FaDens
import Submission.Work.FTS_MuLipC.RowN.FaSlice
import Submission.Work.FTS_MuLipC.RowN.PvAesmOpen
import Submission.Work.H2.T1Q.SupAbsThOAesm

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology ENNReal
open MeasureTheory Set Filter

namespace Work.FTS_MuLipC.RowN

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! ## The twenty-piece split of `N` -/

/-- **The split of `N` into the twenty pieces `pv` on the open quadrant** (the `SmoothOpen`
version of `splitOpen` in the vocabulary of the vector `pv`): the additivity of `L₁₂` along
`F_* + g` is `NZeroAux.L12add`, that of the angular moment `FK` is `Rl1Defs.FKaddOpen`. -/
theorem N_split_pv {α Ce Cs : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    {g Φs Ξg : Fn} (hg : Work.FTS.EllipticEst.SmoothOpen g) (hmem : Work.Spaces.HkMem α 4 g)
    (hs : Work.FTS.VocabO.StarPkgo α Cs Φs) (hell : Work.FTS.VocabO.EllPkgGo α Ce g Ξg) :
    ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
      Work.Construction.N α (Work.Construction.Ftot α g)
        (fun z θ => Φs z θ + Ξg z θ) z θ
        = ∑ k : Fin 20, Work.FTS.Nonlinear.Pieces.rl1Tools.pv α g Φs Ξg k z θ := by
  have hadd := Work.FTS.StrongPersist.H6Pair6Aux.NZeroAux.L12add hα hα1 hg hmem
  have hL : ∀ z : ℝ, 0 < z → Work.Construction.L12 (Work.Construction.Ftot α g) z
      = Work.Construction.L12 (Work.Construction.Fstar α) z + Work.Construction.L12 g z :=
    fun z hz => hadd.1 z hz.le
  have hL12 : ∀ z : ℝ, 0 < z →
      DifferentiableAt ℝ (fun z' => Work.Construction.L12 g z') z := hadd.2.1
  have hsp := Work.FTS.NonlinRows.Rl1.splitOpen (α := α) (g := g) (Φs := Φs) (Φg := Ξg)
    hα hα1 hg hs.smooth hell.smooth hL
    (Work.FTS_MuLamOK.Rows.FKaddOpen hα hg hmem) hL12
  intro z θ hq
  rw [hsp z θ hq]
  simp only [Work.FTS.Nonlinear.Pieces.rl1Tools.pv, Fin.sum_univ_succ, Matrix.cons_val_zero,
    Matrix.cons_val_succ]
  ring

/-! ## Finiteness of the `Fa`-functional -/

/-- **`Fa` of the `N`-field is finite.**  The `L¹(r⁻¹dr)`-triangle inequality over the
twenty-piece split (`rl1Tools.FaSumAE`, whose measurability inputs are the a.e. statements of
`RowMuAux.meas_open`) reduces this to the per-piece bounds
`Fa (pv α g Φ_s Ξ_g k) ≤ ofReal (K · Env α g)` of `FTS_MuLamOK.Rows.piecesEnv`. -/
theorem Fa_N_lt_top {α Ce Cs : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    {g Φs Ξg : Fn} (hg : Work.FTS.EllipticEst.SmoothOpen g) (hmem : Work.Spaces.HkMem α 4 g)
    (hs : Work.FTS.VocabO.StarPkgo α Cs Φs) (hell : Work.FTS.VocabO.EllPkgGo α Ce g Ξg) :
    Work.FTS.Nonlinear.Pieces.Fa (Work.Construction.N α (Work.Construction.Ftot α g)
      (fun z θ => Φs z θ + Ξg z θ)) < ⊤ := by
  obtain ⟨Kc, hKcpos, hpiece⟩ := Work.FTS_MuLamOK.Rows.piecesEnv Ce Cs
  have hEnv0 : 0 ≤ Work.FTS.NonlinRows.Rl1.Env α g :=
    Work.FTS.NonlinRows.Rl1.Env_nonneg g hα.le
  have hmeas := Work.FTS.StrongPersist.H6Pair6Aux.RowMuAux.meas_open hα hα1 hg hmem hs hell
  have htri := Work.FTS.Nonlinear.Pieces.rl1Tools.FaSumAE
    (N := Work.Construction.N α (Work.Construction.Ftot α g)
      (fun z θ => Φs z θ + Ξg z θ))
    (p := Work.FTS.Nonlinear.Pieces.rl1Tools.pv α g Φs Ξg)
    (N_split_pv hα hα1 hg hmem hs hell) hmeas.1 hmeas.2
  have hsum : (∑ k : Fin 20, Work.FTS.Nonlinear.Pieces.Fa
        (Work.FTS.Nonlinear.Pieces.rl1Tools.pv α g Φs Ξg k))
      ≤ ENNReal.ofReal (20 * Kc * Work.FTS.NonlinRows.Rl1.Env α g) := by
    have h1 : ∑ k : Fin 20, Work.FTS.Nonlinear.Pieces.Fa
        (Work.FTS.Nonlinear.Pieces.rl1Tools.pv α g Φs Ξg k)
        ≤ ∑ _k : Fin 20,
          ENNReal.ofReal (Kc * Work.FTS.NonlinRows.Rl1.Env α g) :=
      Finset.sum_le_sum (fun k _ => hpiece hα hα1 hg hmem hs hell k)
    have h2 : ∑ _k : Fin 20, ENNReal.ofReal (Kc * Work.FTS.NonlinRows.Rl1.Env α g)
        = 20 • ENNReal.ofReal (Kc * Work.FTS.NonlinRows.Rl1.Env α g) := by
      simp [Finset.sum_const, Finset.card_univ]
    have h3 : (20 : ℕ) • ENNReal.ofReal (Kc * Work.FTS.NonlinRows.Rl1.Env α g)
        = ENNReal.ofReal (20 * Kc * Work.FTS.NonlinRows.Rl1.Env α g) := by
      have h20 : (0 : ℝ) ≤ 20 := by norm_num
      have h20e : (20 : ENNReal) = ENNReal.ofReal 20 := (ENNReal.ofReal_natCast 20).symm
      calc (20 : ℕ) • ENNReal.ofReal (Kc * Work.FTS.NonlinRows.Rl1.Env α g)
          = (20 : ENNReal) * ENNReal.ofReal (Kc * Work.FTS.NonlinRows.Rl1.Env α g) :=
            nsmul_eq_mul 20 _
        _ = ENNReal.ofReal 20 * ENNReal.ofReal (Kc * Work.FTS.NonlinRows.Rl1.Env α g) := by
            rw [h20e]
        _ = ENNReal.ofReal (20 * (Kc * Work.FTS.NonlinRows.Rl1.Env α g)) :=
            (ENNReal.ofReal_mul h20).symm
        _ = ENNReal.ofReal (20 * Kc * Work.FTS.NonlinRows.Rl1.Env α g) := by
            congr 1
            ring
    rw [h2, h3] at h1
    exact h1
  exact lt_of_le_of_lt (htri.trans hsum) ENNReal.ofReal_lt_top

/-! ## Joint a.e. strong measurability -/

/-- **The `N`-field is jointly a.e. strongly measurable on the open quadrant.**  By the
twenty-piece split, `N` agrees a.e. with the finite sum of the `pv`-pieces, and each piece is
a.e. strongly measurable (`PvAesmOpen`). -/
theorem aesm_N_open {α Ce Cs : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    {g Φs Ξg : Fn} (hg : Work.FTS.EllipticEst.SmoothOpen g) (hmem : Work.Spaces.HkMem α 4 g)
    (hs : Work.FTS.VocabO.StarPkgo α Cs Φs) (hell : Work.FTS.VocabO.EllPkgGo α Ce g Ξg) :
    MeasureTheory.AEStronglyMeasurable (Function.uncurry (fun r θ =>
      Work.Construction.N α (Work.Construction.Ftot α g)
        (fun z θ => Φs z θ + Ξg z θ) r θ))
      ((MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))).prod
        (MeasureTheory.volume.restrict Work.Spaces.Iθ)) := by
  have hpv := PvAesmOpen (g := g) (Φs := Φs) (Ξg := Ξg) hα hα1 hg hmem hs hell
  have hsum := Finset.aestronglyMeasurable_sum Finset.univ (fun k _ => hpv k)
  refine hsum.congr ?_
  refine (Work.FTS.Nonlinear.Pieces.Rl1.ae_mem_Qd).mono ?_
  intro p hp
  show (∑ k, Function.uncurry
      (Work.FTS.Nonlinear.Pieces.rl1Tools.pv α g Φs Ξg k) p)
    = Work.Construction.N α (Work.Construction.Ftot α g)
        (fun z θ => Φs z θ + Ξg z θ) p.1 p.2
  rw [show (∑ k, Function.uncurry
        (Work.FTS.Nonlinear.Pieces.rl1Tools.pv α g Φs Ξg k) p)
      = ∑ k, Work.FTS.Nonlinear.Pieces.rl1Tools.pv α g Φs Ξg k p.1 p.2 from rfl]
  exact (N_split_pv hα hα1 hg hmem hs hell p.1 p.2 hp).symm

/-! ## The target -/

/-- Honesty of the field `N α (F_*+g) (Φ_s+Ξg)`: finiteness of its `Fa`-functional, joint a.e. strong measurability on the open quadrant, a.e. `θ`-slice integrability of the density integrand, and integrability of its `L₁₂`-density.  Route: `Work.FTS.NonlinRows.Rl1.splitOpen` for the twenty-piece split, `Work.FTS.MuLamOK.Rows.piecesEnv` + `Work.FTS.Nonlinear.Pieces.rl1Tools.FaSumAE` for `Fa < ⊤`, the internal twenty-case argument of `Work.FTS.StrongPersist.H6Pair6Aux.RowMuAux.meas_open` for the joint measurability, and `Work.FTS.Nonlinear.Pieces.Rl1.aesm_L12dens_of_aem_uncurry` + `norm_integral_le_lintegral_norm` for the density.  Consumers: `Submission/Work/FTS_MuLipC/RowN/diffRow1.lean`. -/
theorem NHonest {α Ce Cs : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    {g Φs Ξg : Work.FTS.Galerkin.Fn} (hg : Work.FTS.EllipticEst.SmoothOpen g)
    (hmem : Work.Spaces.HkMem α 4 g)
    (hs : Work.FTS.VocabO.StarPkgo α Cs Φs)
    (hell : Work.FTS.VocabO.EllPkgGo α Ce g Ξg) :
    Work.FTS.Nonlinear.Pieces.Fa (Work.Construction.N α (Work.Construction.Ftot α g)
        (fun z θ => Φs z θ + Ξg z θ)) < ⊤ ∧
    MeasureTheory.AEStronglyMeasurable (Function.uncurry (fun r θ => Work.Construction.N α
        (Work.Construction.Ftot α g) (fun z θ => Φs z θ + Ξg z θ) r θ))
        ((MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))).prod
          (MeasureTheory.volume.restrict Work.Spaces.Iθ)) ∧
    Filter.Eventually (fun r => MeasureTheory.IntegrableOn (fun θ => Work.Spaces.K θ
        * Work.Construction.N α (Work.Construction.Ftot α g)
          (fun z θ => Φs z θ + Ξg z θ) r θ / r) Work.Spaces.Iθ)
      (MeasureTheory.ae (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ)))) ∧
    MeasureTheory.IntegrableOn (fun r => Work.Construction.L12dens (Work.Construction.N α
        (Work.Construction.Ftot α g) (fun z θ => Φs z θ + Ξg z θ)) r) (Set.Ioi (0 : ℝ)) := by
  have hfa := Fa_N_lt_top hα hα1 hg hmem hs hell
  have haesm := aesm_N_open hα hα1 hg hmem hs hell
  refine ⟨hfa, haesm, ?_, ?_⟩
  · -- a.e. `θ`-slice integrability, from `Fa < ⊤` and a division by `r`
    have hsl := FaSlice haesm hfa
    filter_upwards [hsl] with r hr
    rw [show (fun θ => Work.Spaces.K θ * Work.Construction.N α (Work.Construction.Ftot α g)
        (fun z θ => Φs z θ + Ξg z θ) r θ / r)
        = fun θ => r⁻¹ * (Work.Spaces.K θ * Work.Construction.N α (Work.Construction.Ftot α g)
        (fun z θ => Φs z θ + Ξg z θ) r θ) from by funext θ; rw [div_eq_inv_mul]]
    exact hr.const_mul r⁻¹
  · -- integrability of the `L₁₂`-density
    have hdens_aesm : MeasureTheory.AEStronglyMeasurable
        (fun r => Work.Construction.L12dens (Work.Construction.N α (Work.Construction.Ftot α g)
          (fun z θ => Φs z θ + Ξg z θ)) r)
        (MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))) :=
      Work.FTS.Nonlinear.Pieces.Rl1.aesm_L12dens_of_aem_uncurry haesm.aemeasurable
    exact FaDens hdens_aesm hfa

end Work.FTS_MuLipC.RowN
