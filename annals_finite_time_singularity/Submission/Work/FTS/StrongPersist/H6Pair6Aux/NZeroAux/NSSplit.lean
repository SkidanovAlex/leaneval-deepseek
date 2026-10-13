import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.StrongPersist.Clauses
import Submission.Work.FTS.StrongPersist.Basic
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.SmoothN0
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.NZeroAux.NSBasic
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.NZeroAux.L12add
import Submission.Work.FTS.Nonlinear.Pieces.splitsDiff

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Pair6Aux.NZeroAux

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The split of the straightened stream function -/

/-- **`Φ̃ = Φ̃_* + Φ̃_g` on the open quadrant**, for `F = F_* + f` and `Ψ = Φ_s + E f`.
This is the linearity of `PhiTil` together with the `L₁₂`-additivity `L12add`. -/
theorem nzs_Xi_split {α Ce Cs : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn} {f Ψ Φs : Work.FTS.Galerkin.Fn}
    (hAdm : Work.FTS.StrongPersist.H6Adm α f)
    (hctx : Work.FTS.StrongPersist.Ell6Ctx α Ce Cs E Φs f Ψ) :
    ∀ z θ : ℝ, 0 < z →
      Work.Construction.PhiTil α (fun z θ => Work.Construction.Fstar α z θ + f z θ) Ψ z θ
        = Work.FTS.VocabO2.PhiTs α Φs z θ
          + Work.Construction.PhiTil α f (E f) z θ := by
  intro z θ hz
  have hso : Work.FTS.EllipticEst.SmoothOpen f := hAdm.reg.1
  have hmem4 : Work.Spaces.HkMem α 4 f :=
    Work.FTS.StrongPersist.HkMem_four_of_six hso hAdm.reg.2
  have hadd := (L12add hα hα1 hso hmem4).1 z hz.le
  have hsum : Ψ z θ = Φs z θ + E f z θ := by rw [hctx.hsum]
  have h1 : Work.Construction.PhiTil α (fun z θ => Work.Construction.Fstar α z θ + f z θ)
        Ψ z θ
      = Ψ z θ - (1 / (4 * α)) * Work.Construction.s2 θ
          * Work.Construction.L12 (fun z θ => Work.Construction.Fstar α z θ + f z θ) z := rfl
  have h2 : Work.FTS.VocabO2.PhiTs α Φs z θ
      = Φs z θ - (1 / (4 * α)) * Work.Construction.s2 θ
          * Work.Construction.L12 (Work.Construction.Fstar α) z := rfl
  have h3 : Work.Construction.PhiTil α f (E f) z θ
      = E f z θ - (1 / (4 * α)) * Work.Construction.s2 θ
          * Work.Construction.L12 f z := rfl
  rw [h1, h2, h3, hsum, hadd]
  ring

/-- **The operator identities of the split.**  On the open quadrant the four coefficient fields
of `N` evaluated on `Φ̃` are the sums of their star and perturbation parts. -/
theorem nzs_Xi_opsplit {α Ce Cs : ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn} {f Ψ Φs : Work.FTS.Galerkin.Fn}
    (hAdm : Work.FTS.StrongPersist.H6Adm α f)
    (hctx : Work.FTS.StrongPersist.Ell6Ctx α Ce Cs E Φs f Ψ) :
    (∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
        Work.Construction.Rop α
            (Work.Construction.PhiTil α (fun z θ => Work.Construction.Fstar α z θ + f z θ) Ψ)
            z θ
          = Work.Construction.Rop α (Work.FTS.VocabO2.PhiTs α Φs) z θ
            + Work.Construction.Rop α (Work.Construction.PhiTil α f (E f)) z θ) ∧
    (∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
        Work.Construction.Uop α
            (Work.Construction.PhiTil α (fun z θ => Work.Construction.Fstar α z θ + f z θ) Ψ)
            z θ / Work.Construction.s2 θ
          = Work.Construction.Uop α (Work.FTS.VocabO2.PhiTs α Φs) z θ
              / Work.Construction.s2 θ
            + Work.Construction.Uop α (Work.Construction.PhiTil α f (E f)) z θ
              / Work.Construction.s2 θ) ∧
    (∀ z θ : ℝ, (z, θ) ∈ Work.FTS.EllipticEst.Q0 →
        Work.Construction.Vop
            (Work.Construction.PhiTil α (fun z θ => Work.Construction.Fstar α z θ + f z θ) Ψ)
            z θ
          = Work.Construction.Vop (Work.FTS.VocabO2.PhiTs α Φs) z θ
            + Work.Construction.Vop (Work.Construction.PhiTil α f (E f)) z θ) := by
  have hso : Work.FTS.EllipticEst.SmoothOpen f := hAdm.reg.1
  have hmem4 : Work.Spaces.HkMem α 4 f :=
    Work.FTS.StrongPersist.HkMem_four_of_six hso hAdm.reg.2
  obtain ⟨hadd, hdiffl, hdiffF⟩ := L12add hα hα1 hso hmem4
  have hdiffFs : ∀ z : ℝ, 0 < z →
      DifferentiableAt ℝ (fun z' => Work.Construction.L12 (Work.Construction.Fstar α) z') z :=
    fun z hz => Work.FTS.Nonlinear.Pieces.differentiableAt_L12_Fstar hα hα1 hz
  have hΦssm : Work.FTS.EllipticEst.SmoothOpen Φs := hctx.hstar.toStarPkgo.smooth
  have hEfsm : Work.FTS.EllipticEst.SmoothOpen (E f) := hctx.hell.smooth
  have hΨsm : Work.FTS.EllipticEst.SmoothOpen Ψ := by
    rw [hctx.hsum]
    exact so_add hΦssm hEfsm
  -- the three `pz`-values
  have hpz_all : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.pz (Work.Construction.PhiTil α
          (fun z θ => Work.Construction.Fstar α z θ + f z θ) Ψ) z θ
        = Work.Spaces.pz (Work.FTS.VocabO2.PhiTs α Φs) z θ
          + Work.Spaces.pz (Work.Construction.PhiTil α f (E f)) z θ := by
    intro z θ hz hθ0 hθ1
    have hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨hθ0, hθ1⟩
    have hder : deriv (fun z' => Work.Construction.L12
          (fun z θ => Work.Construction.Fstar α z θ + f z θ) z') z
        = deriv (fun z' => Work.Construction.L12 (Work.Construction.Fstar α) z') z
          + deriv (fun z' => Work.Construction.L12 f z') z := by
      have hev : (fun z' => Work.Construction.L12
            (fun z θ => Work.Construction.Fstar α z θ + f z θ) z') =ᶠ[𝓝 z]
          (fun z' => Work.Construction.L12 (Work.Construction.Fstar α) z'
            + Work.Construction.L12 f z') := by
        filter_upwards [isOpen_Ioi.mem_nhds hz] with z' hz'
        exact hadd z' hz'.le
      rw [hev.deriv_eq]
      exact deriv_add (hdiffFs z hz) (hdiffl z hz)
    have hpzΨ : Work.Spaces.pz Ψ z θ
        = Work.Spaces.pz Φs z θ + Work.Spaces.pz (E f) z θ := by
      rw [hctx.hsum]
      exact Work.FTS.Nonlinear.Pieces.pz_add_of_diff
        ((hΦssm.hasDerivAt_slice hθ hz).differentiableAt)
        ((hEfsm.hasDerivAt_slice hθ hz).differentiableAt)
    rw [nzs_pz_PhiTil α (fun z θ => Work.Construction.Fstar α z θ + f z θ) Ψ z θ
        ((hΨsm.hasDerivAt_slice hθ hz).differentiableAt) (hdiffF z hz),
      nzs_pz_PhiTil α (Work.Construction.Fstar α) Φs z θ
        ((hΦssm.hasDerivAt_slice hθ hz).differentiableAt) (hdiffFs z hz),
      nzs_pz_PhiTil α f (E f) z θ
        ((hEfsm.hasDerivAt_slice hθ hz).differentiableAt) (hdiffl z hz),
      hpzΨ, hder]
    ring
  -- the three `pth`-values
  have hpth_all : ∀ z θ : ℝ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.pth (Work.Construction.PhiTil α
          (fun z θ => Work.Construction.Fstar α z θ + f z θ) Ψ) z θ
        = Work.Spaces.pth (Work.FTS.VocabO2.PhiTs α Φs) z θ
          + Work.Spaces.pth (Work.Construction.PhiTil α f (E f)) z θ := by
    intro z θ hz hθ0 hθ1
    have hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨hθ0, hθ1⟩
    have hdθ : ∀ {g : ℝ → ℝ → ℝ}, Work.FTS.EllipticEst.SmoothOpen g →
        DifferentiableAt ℝ (fun θ' => g z θ') θ :=
      fun hg => (((hg.curry_θ hz).differentiableOn (by simp)).differentiableAt
        (isOpen_Ioo.mem_nhds hθ))
    have hpthΨ : Work.Spaces.pth Ψ z θ
        = Work.Spaces.pth Φs z θ + Work.Spaces.pth (E f) z θ := by
      rw [hctx.hsum]
      exact Work.FTS.Nonlinear.Pieces.pth_add_of_diff (hdθ hΦssm) (hdθ hEfsm)
    rw [nzs_pth_PhiTil α (fun z θ => Work.Construction.Fstar α z θ + f z θ) Ψ z θ
        (hdθ hΨsm),
      nzs_pth_PhiTil α (Work.Construction.Fstar α) Φs z θ (hdθ hΦssm),
      nzs_pth_PhiTil α f (E f) z θ (hdθ hEfsm),
      hpthΨ, hadd z hz.le]
    ring
  refine ⟨?_, ?_, ?_⟩
  · intro z θ hzθ
    obtain ⟨hz, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hzθ
    have hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨hθ0, hθ1⟩
    have hsplit := nzs_Xi_split hα hα1 hAdm hctx z θ hz
    rw [show Work.Construction.Rop α
          (Work.Construction.PhiTil α
            (fun z θ => Work.Construction.Fstar α z θ + f z θ) Ψ) z θ
        = (2 * Real.sin θ * Work.Construction.PhiTil α
              (fun z θ => Work.Construction.Fstar α z θ + f z θ) Ψ z θ
            + α * Real.sin θ * z * Work.Spaces.pz (Work.Construction.PhiTil α
              (fun z θ => Work.Construction.Fstar α z θ + f z θ) Ψ) z θ
            + Real.cos θ * Work.Spaces.pth (Work.Construction.PhiTil α
              (fun z θ => Work.Construction.Fstar α z θ + f z θ) Ψ) z θ)
          / Real.cos θ from rfl,
      show Work.Construction.Rop α (Work.FTS.VocabO2.PhiTs α Φs) z θ
        = (2 * Real.sin θ * Work.FTS.VocabO2.PhiTs α Φs z θ
            + α * Real.sin θ * z * Work.Spaces.pz (Work.FTS.VocabO2.PhiTs α Φs) z θ
            + Real.cos θ * Work.Spaces.pth (Work.FTS.VocabO2.PhiTs α Φs) z θ)
          / Real.cos θ from rfl,
      show Work.Construction.Rop α (Work.Construction.PhiTil α f (E f)) z θ
        = (2 * Real.sin θ * Work.Construction.PhiTil α f (E f) z θ
            + α * Real.sin θ * z * Work.Spaces.pz (Work.Construction.PhiTil α f (E f)) z θ
            + Real.cos θ * Work.Spaces.pth (Work.Construction.PhiTil α f (E f)) z θ)
          / Real.cos θ from rfl,
      hsplit, hpz_all z θ hz hθ0 hθ1, hpth_all z θ hz hθ0 hθ1]
    ring
  · intro z θ hzθ
    obtain ⟨hz, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hzθ
    have hsplit := nzs_Xi_split hα hα1 hAdm hctx z θ hz
    rw [show Work.Construction.Uop α
          (Work.Construction.PhiTil α
            (fun z θ => Work.Construction.Fstar α z θ + f z θ) Ψ) z θ
        = -3 * Work.Construction.PhiTil α
              (fun z θ => Work.Construction.Fstar α z θ + f z θ) Ψ z θ
            - α * z * Work.Spaces.pz (Work.Construction.PhiTil α
              (fun z θ => Work.Construction.Fstar α z θ + f z θ) Ψ) z θ from rfl,
      show Work.Construction.Uop α (Work.FTS.VocabO2.PhiTs α Φs) z θ
        = -3 * Work.FTS.VocabO2.PhiTs α Φs z θ
            - α * z * Work.Spaces.pz (Work.FTS.VocabO2.PhiTs α Φs) z θ from rfl,
      show Work.Construction.Uop α (Work.Construction.PhiTil α f (E f)) z θ
        = -3 * Work.Construction.PhiTil α f (E f) z θ
            - α * z * Work.Spaces.pz (Work.Construction.PhiTil α f (E f)) z θ from rfl,
      hsplit, hpz_all z θ hz hθ0 hθ1]
    ring
  · intro z θ hzθ
    obtain ⟨hz, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hzθ
    have hsplit := nzs_Xi_split hα hα1 hAdm hctx z θ hz
    rw [show Work.Construction.Vop
          (Work.Construction.PhiTil α
            (fun z θ => Work.Construction.Fstar α z θ + f z θ) Ψ) z θ
        = Work.Spaces.pth (Work.Construction.PhiTil α
              (fun z θ => Work.Construction.Fstar α z θ + f z θ) Ψ) z θ
            - Real.tan θ * Work.Construction.PhiTil α
              (fun z θ => Work.Construction.Fstar α z θ + f z θ) Ψ z θ from rfl,
      show Work.Construction.Vop (Work.FTS.VocabO2.PhiTs α Φs) z θ
        = Work.Spaces.pth (Work.FTS.VocabO2.PhiTs α Φs) z θ
            - Real.tan θ * Work.FTS.VocabO2.PhiTs α Φs z θ from rfl,
      show Work.Construction.Vop (Work.Construction.PhiTil α f (E f)) z θ
        = Work.Spaces.pth (Work.Construction.PhiTil α f (E f)) z θ
            - Real.tan θ * Work.Construction.PhiTil α f (E f) z θ from rfl,
      hsplit, hpth_all z θ hz hθ0 hθ1]
    ring



end Work.FTS.StrongPersist.H6Pair6Aux.NZeroAux
