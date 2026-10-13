/-
# `OpenPkg/Galerkin` — the Galerkin existence chapter (N6) on the migrated route

The delivered chapter `Submission/Work/FTS/Galerkin/` proves the existence theorem of node N6
from the a-priori bundle `Work.FTS.Galerkin.DynInputs`, whose fields `hΦs : StarPkg α Cs Φs` and
`hEllSol : ∀ g, GalClass α g → EllPkgG α Ce g (EllSol g)` carry the **uninhabited** frozen
packages, and whose `hLimBound` would have to be supplied for a limit profile that is only
`C^∞` on the open quadrant.

This module re-runs the existence theorem on the migrated route:

* `DynCore` (`OpenPkg/Defs.lean`) is the projection of the bundle onto the fields that the
  ODE/existence layer actually consumes — the two packages and their constants are *not* among
  them;
* `galerkin_coeff_exists_core` and `exists_dynGSol_of_ode_core` are the two lemmas of the layer,
  proved for `DynCore` by the delivered proofs;
* `DynInputsOpen` is the full migrated bundle (`StarPkgo`/`EllPkgGo` + the open-quadrant limit
  bound `SmoothOpen`), and `exists_dynGSol_of_ode_open` is the existence theorem for it.

The only mathematical difference with the delivered chapter is that the limit bound is applied
to the `SmoothOpen` regularity of the limit slices, which `RegPkg.smooth`
(`RegPkg_smoothOpen_slice` below) supplies; the delivered field asked for `SmoothQuad`, which the
limit of the Galerkin family does **not** have (it inherits the `z^{2/α}` modes of the elliptic
equation).
-/
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.OpenPkg.Defs
import Submission.Work.FTS.Galerkin.GalerkinODE
import Submission.Work.FTS.Galerkin.Extraction
import Submission.Work.FTS.Galerkin.Compactness.exists_seq_dense_slab
import Submission.Work.FTS.GalerkinFix.Equicont
import Submission.Work.GalerkinFix.Extraction.exists_subseq_convLocUnif_of_equicont

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.OpenPkg

open Work.FTS.Nonlin
open Work.FTS.VocabO
open Work.FTS.Galerkin (Fn Fam slice galFun galField coeffOf IsSolOn IsGalFam ConvLocUnif
  IsGalerkinCoeff IsDynGSolWith GlobalODEExistence DenseSpan WeakDetermines IsDynWeakOn
  ProfileBdd EquicontSpace EquicontTau profileFam RegPkg prof galFam ProfileEquicont)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The regularity of the slices of the limit -/

/-- **The `SmoothOpen` regularity of the slices of a family in `RegPkg`.**  This is what replaces
the `SmoothQuad` requirement of the delivered `AprioriFields.hLimBound`: the limit profile of the
Galerkin family is `C^∞` on the open quadrant (`RegPkg.smooth`), and nothing more is true. -/
theorem RegPkg_smoothOpen_slice {α : ℝ} {g : Fam} (h : RegPkg α g) :
    ∀ τ : ℝ, 0 ≤ τ → Work.FTS.EllipticEst.SmoothOpen (slice g τ) := by
  intro τ hτ
  have hsm := h.smooth
  have hcomp : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => ((p.1 : ℝ), ((p.2 : ℝ), τ))) (Work.FTS.EllipticEst.Q0) := by fun_prop
  have hmaps : Set.MapsTo (fun p : ℝ × ℝ => ((p.1 : ℝ), ((p.2 : ℝ), τ)))
      Work.FTS.EllipticEst.Q0
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (π / 2) ×ˢ Set.Ioi (-1)) := by
    intro p hp
    obtain ⟨hp1, hp2⟩ := Work.FTS.EllipticEst.mem_Q0.mp hp
    refine ⟨Set.mem_Ioi.mpr hp1, ?_⟩
    exact ⟨Set.mem_Ioo.mpr hp2, Set.mem_Ioi.mpr (by linarith)⟩
  have hres := hsm.comp hcomp hmaps
  have hgoal : ContDiffOn ℝ Work.Stability.smoothOrder
      (fun p : ℝ × ℝ => g p.1 p.2 τ) Work.FTS.EllipticEst.Q0 := by
    convert hres using 1
    funext p
    rfl
  rw [Work.FTS.EllipticEst.SmoothOpen]
  exact hgoal

/-! ## The ODE layer of the chapter, for the core bundle -/

/-- **The Galerkin approximations exist globally**, for the core bundle (the delivered
`Work.FTS.Galerkin.galerkin_coeff_exists`). -/
theorem galerkin_coeff_exists_core (hODE : GlobalODEExistence) {Law : Fn → Fn → Prop}
    {α C₀ : ℝ} {g₀ : Fn} (hin : DynCore Law α g₀ C₀) (n : ℕ) :
    ∃ c : ℝ → Fin n → ℝ, c 0 = coeffOf (hin.IP α) g₀ hin.φ n ∧
      Work.FTS.Galerkin.IsGalerkinCoeff α (hin.IP α) hin.φ n hin.Psi c ∧
      (∀ τ, 0 ≤ τ → ∑ k : Fin n, (c τ k) ^ 2 ≤ hin.R ^ 2) ∧
      ∀ τ, 0 ≤ τ → c τ ∈ Metric.closedBall 0 hin.R := by
  have hRlt : hin.R < 2 * hin.R := by linarith [hin.hR]
  have hx₀ : coeffOf (hin.IP α) g₀ hin.φ n ∈ Metric.closedBall (0 : Fin n → ℝ) hin.R :=
    Work.FTS.Galerkin.mem_closedBall_of_sum_sq_le hin.hR.le (hin.hInit n)
  obtain ⟨c, hc, hball⟩ := hODE (Fin n → ℝ) (f := galField α (hin.IP α) hin.φ n hin.Psi)
    (x₀ := coeffOf (hin.IP α) g₀ hin.φ n) (R := hin.R) (R' := 2 * hin.R)
    (L := hin.L n) (K := hin.K n)
    hin.hR hRlt (hin.hL n) (hin.hK n) hx₀
    (fun t ht => hin.hField_lip n t ht)
    (fun t ht x hx => hin.hField_bound n t x ht hx)
    (fun x hx => hin.hField_cont n x hx)
    (fun T hT α' hα' τ hτ =>
      Work.FTS.Galerkin.mem_closedBall_of_sum_sq_le hin.hR.le (hin.hCoeffBound n T hT α' hα' τ hτ))
  refine ⟨c, hc.1, hc.2, ?_, hball⟩
  intro τ hτ
  exact hin.hCoeffBound n τ hτ c (hc.isSolOn τ) τ ⟨hτ, le_rfl⟩

/-- **Existence for the dynamic modulated equation**, from the core bundle (the delivered
`Work.FTS.Galerkin.exists_dynGSol_of_ode`). -/
theorem exists_dynGSol_of_ode_core (hODE : GlobalODEExistence) {Law : Fn → Fn → Prop}
    {α C₀ : ℝ} {g₀ : Fn} (hin : DynCore Law α g₀ C₀) :
    ∃ g Φ : Fam, IsDynGSolWith Law α Φ g ∧ (∀ z θ, g z θ 0 = g₀ z θ) ∧ RegPkg α g ∧
      (∀ τ, 0 ≤ τ → Work.Spaces.HkNorm α 4 (slice g τ) ≤ C₀ * α ^ 2) := by
  classical
  obtain ⟨e, he, hdense⟩ := Work.FTS.Galerkin.Compactness.exists_seq_dense_slab
  choose c hc using fun n : ℕ => galerkin_coeff_exists_core hODE hin n
  have hfam : IsGalFam α (hin.IP α) hin.φ hin.Psi hin.R c :=
    ⟨fun n => (hc n).2.1, fun n τ hτ => (hc n).2.2.1 τ hτ⟩
  have heq : ProfileEquicont (profileFam hin.φ c) :=
    Work.FTS.GalerkinFix.profileEquicont_of_box
      (Work.FTS.GalerkinFix.profileEquicontBox_of_parts
        (hin.hProfileSpace c hfam) (hin.hProfileTau c hfam))
  obtain ⟨ψ, g', hψ, hconv'⟩ :=
    Work.GalerkinFix.Extraction.exists_subseq_convLocUnif_of_equicont (G := prof hin.φ c)
      he hdense (hin.hProfileBdd c hfam) heq
  set g : Fam := fun z θ τ => g' (z, θ, τ) with hgdef
  have hconv : ConvLocUnif (fun n => galFam hin.φ (ψ n) (c (ψ n))) g := by
    intro K hK hKsub
    have h := hconv' K hK hKsub
    simpa [prof, galFam, g] using h
  obtain ⟨Φ, hconvΦ⟩ := hin.hPsiLim c hfam ψ g hψ hconv
  obtain ⟨hw, hl⟩ := hin.hGalWeak c hfam ψ g Φ hψ hconv hconvΦ
  have hsol : IsDynGSolWith Law α Φ g := ⟨hl, hin.hDetermines g Φ hw⟩
  have hdat : ∀ z θ, g z θ 0 = g₀ z θ := hin.hDataLimit c hfam ψ g hψ hconv
  refine ⟨g, Φ, hsol, hdat, hin.hRegLimit c hfam ψ g hψ hconv, ?_⟩
  exact hin.hLimBound c hfam ψ g hψ hconv
    (RegPkg_smoothOpen_slice (hin.hRegLimit c hfam ψ g hψ hconv))

/-! ## The migrated bundle -/

/-- The `DynCore` of a `DynInputsOpen`. -/
def DynInputsOpen.toCore {Law : Fn → Fn → Prop} {α : ℝ} {g₀ : Fn} {C₀ : ℝ}
    (hin : DynInputsOpen Law α g₀ C₀) : DynCore Law α g₀ C₀ := hin.core

/-- **Existence for the dynamic modulated equation on the migrated route**: the same statement as
`Work.FTS.Galerkin.exists_dynGSol_of_ode`, from the bundle whose stream-function packages are the
open-quadrant ones. -/
theorem exists_dynGSol_of_ode_open (hODE : GlobalODEExistence) {Law : Fn → Fn → Prop}
    {α C₀ : ℝ} {g₀ : Fn} (hin : DynInputsOpen Law α g₀ C₀) :
    ∃ g Φ : Fam, IsDynGSolWith Law α Φ g ∧ (∀ z θ, g z θ 0 = g₀ z θ) ∧ RegPkg α g ∧
      (∀ τ, 0 ≤ τ → Work.Spaces.HkNorm α 4 (slice g τ) ≤ C₀ * α ^ 2) :=
  exists_dynGSol_of_ode_core hODE hin.toCore

end Work.FTS.OpenPkg
