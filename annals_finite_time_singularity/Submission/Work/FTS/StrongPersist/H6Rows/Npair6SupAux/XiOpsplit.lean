/-
# `XiOpsplit` — the operator split of `Ξ = PhiTil α (F_* + f) (Φs + Ef)`

For `f` in the level-six class (`H6Adm α f`) and `Ef, Φs` smooth on the open quadrant, the
straightened stream function `Ξ = PhiTil α (F_* + f) (Φs + Ef)` splits on the open quadrant as

  `Ξ = PhiTs α Φs + PhiTil α f Ef`            (`PhiTs α Φs = PhiTil α (F_*) Φs`),

and consequently so do the three coefficient fields `ℛ(Ξ)`, `𝒰(Ξ)/sin 2θ`, `𝒱(Ξ)` of the
self-similar vorticity equation.

The only analytic input is the additivity `L₁₂(F_* + f) = L₁₂(F_*) + L₁₂(f)` of the integral
operator `L₁₂` (and the differentiability of `z ↦ L₁₂(f)(z)`, resp. of `z ↦ L₁₂(F_*)(z)`,
needed to split `∂_z`); both come from `H6Pair6Aux.NZeroAux.L12add`, which derives them from
`SmoothOpen f` + `HkMem α 4 f` (`HkMem α 6 f` gives the latter by `HkMem_four_of_six`).
The `θ`- and `z`-derivatives of the two pieces are the ones computed in
`NZeroAux.NSBasic` (`nzs_pz_PhiTil`, `nzs_pth_PhiTil`).

This is the `H6Rows` counterpart of the already-proved sibling
`Work.FTS.StrongPersist.H6Pair6Aux.NZeroAux.nzs_Xi_opsplit` (there stated for an elliptic
context `Ell6Ctx`, here for the raw hypotheses `SmoothOpen Ef`, `SmoothOpen Φs`).
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.NZeroAux.NSBasic
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.NZeroAux.L12add
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.NZeroAux.NSSplit
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.NDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Rows.Npair6SupAux

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 800000

open Work.FTS.StrongPersist.H6Pair6Aux.NZeroAux (nzs_pz_PhiTil nzs_pth_PhiTil L12add)

theorem XiOpsplit {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {f Ef Φs : Work.FTS.Galerkin.Fn}
    (hadm : Work.FTS.StrongPersist.H6Adm α f)
    (hEf : Work.FTS.EllipticEst.SmoothOpen Ef) (hΦs : Work.FTS.EllipticEst.SmoothOpen Φs) :
    (∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
      Work.Construction.PhiTil α (fun z θ => Work.Construction.Fstar α z θ + f z θ)
          (fun z θ => Φs z θ + Ef z θ) z θ
        = Work.FTS.VocabO2.PhiTs α Φs z θ + Work.Construction.PhiTil α f Ef z θ) ∧
    (∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
      Work.Construction.Rop α (Work.Construction.PhiTil α
          (fun z θ => Work.Construction.Fstar α z θ + f z θ)
          (fun z θ => Φs z θ + Ef z θ)) z θ
        = Work.Construction.Rop α (Work.FTS.VocabO2.PhiTs α Φs) z θ
          + Work.Construction.Rop α (Work.Construction.PhiTil α f Ef) z θ) ∧
    (∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
      Work.Construction.Uop α (Work.Construction.PhiTil α
          (fun z θ => Work.Construction.Fstar α z θ + f z θ)
          (fun z θ => Φs z θ + Ef z θ)) z θ / Work.Construction.s2 θ
        = Work.Construction.Uop α (Work.FTS.VocabO2.PhiTs α Φs) z θ / Work.Construction.s2 θ
          + Work.Construction.Uop α (Work.Construction.PhiTil α f Ef) z θ
              / Work.Construction.s2 θ) ∧
    (∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
      Work.Construction.Vop (Work.Construction.PhiTil α
          (fun z θ => Work.Construction.Fstar α z θ + f z θ)
          (fun z θ => Φs z θ + Ef z θ)) z θ
        = Work.Construction.Vop (Work.FTS.VocabO2.PhiTs α Φs) z θ
          + Work.Construction.Vop (Work.Construction.PhiTil α f Ef) z θ) := by
  -- ## the analytic inputs about `L₁₂`
  have hso : Work.FTS.EllipticEst.SmoothOpen f := hadm.reg.1
  have hmem4 : Work.Spaces.HkMem α 4 f :=
    Work.FTS.StrongPersist.HkMem_four_of_six hso hadm.reg.2
  obtain ⟨hadd, hdiffl, hdiffF⟩ := L12add hα hα1 hso hmem4
  have hdiffFs : ∀ z : ℝ, 0 < z → DifferentiableAt ℝ
      (fun z' => Work.Construction.L12 (Work.Construction.Fstar α) z') z :=
    fun z hz => Work.FTS.Nonlinear.Pieces.differentiableAt_L12_Fstar hα hα1 hz
  -- ## the value split
  have hsplit : ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
      Work.Construction.PhiTil α (fun z θ => Work.Construction.Fstar α z θ + f z θ)
          (fun z θ => Φs z θ + Ef z θ) z θ
        = Work.FTS.VocabO2.PhiTs α Φs z θ + Work.Construction.PhiTil α f Ef z θ := by
    intro z θ hq
    have hz : 0 < z := hq.1
    simp only [Work.Construction.PhiTil, Work.Construction.Theta]
    rw [hadd z hz.le]
    ring
  -- ## the `∂_z`-split
  have hpz_all : ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
      Work.Spaces.pz (Work.Construction.PhiTil α
          (fun z θ => Work.Construction.Fstar α z θ + f z θ)
          (fun z θ => Φs z θ + Ef z θ)) z θ
        = Work.Spaces.pz (Work.FTS.VocabO2.PhiTs α Φs) z θ
          + Work.Spaces.pz (Work.Construction.PhiTil α f Ef) z θ := by
    intro z θ hq
    have hz : 0 < z := hq.1
    have hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := hq.2
    have hdΦs : DifferentiableAt ℝ (fun z' => Φs z' θ) z :=
      (hΦs.hasDerivAt_slice hθ hz).differentiableAt
    have hdEf : DifferentiableAt ℝ (fun z' => Ef z' θ) z :=
      (hEf.hasDerivAt_slice hθ hz).differentiableAt
    have hpzP : Work.Spaces.pz (fun z θ => Φs z θ + Ef z θ) z θ
        = Work.Spaces.pz Φs z θ + Work.Spaces.pz Ef z θ :=
      Work.FTS.Nonlinear.Pieces.pz_add_of_diff hdΦs hdEf
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
    rw [nzs_pz_PhiTil α (fun z θ => Work.Construction.Fstar α z θ + f z θ)
          (fun z θ => Φs z θ + Ef z θ) z θ (hdΦs.add hdEf) (hdiffF z hz),
      nzs_pz_PhiTil α (Work.Construction.Fstar α) Φs z θ hdΦs (hdiffFs z hz),
      nzs_pz_PhiTil α f Ef z θ hdEf (hdiffl z hz),
      hpzP, hder]
    ring
  -- ## the `∂_θ`-split
  have hpth_all : ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
      Work.Spaces.pth (Work.Construction.PhiTil α
          (fun z θ => Work.Construction.Fstar α z θ + f z θ)
          (fun z θ => Φs z θ + Ef z θ)) z θ
        = Work.Spaces.pth (Work.FTS.VocabO2.PhiTs α Φs) z θ
          + Work.Spaces.pth (Work.Construction.PhiTil α f Ef) z θ := by
    intro z θ hq
    have hz : 0 < z := hq.1
    have hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := hq.2
    have hdθ : ∀ {g : ℝ → ℝ → ℝ}, Work.FTS.EllipticEst.SmoothOpen g →
        DifferentiableAt ℝ (fun θ' => g z θ') θ :=
      fun hg => (((hg.curry_θ hz).differentiableOn (by simp)).differentiableAt
        (isOpen_Ioo.mem_nhds hθ))
    have hpthP : Work.Spaces.pth (fun z θ => Φs z θ + Ef z θ) z θ
        = Work.Spaces.pth Φs z θ + Work.Spaces.pth Ef z θ :=
      Work.FTS.Nonlinear.Pieces.pth_add_of_diff (hdθ hΦs) (hdθ hEf)
    rw [nzs_pth_PhiTil α (fun z θ => Work.Construction.Fstar α z θ + f z θ)
          (fun z θ => Φs z θ + Ef z θ) z θ ((hdθ hΦs).add (hdθ hEf)),
      nzs_pth_PhiTil α (Work.Construction.Fstar α) Φs z θ (hdθ hΦs),
      nzs_pth_PhiTil α f Ef z θ (hdθ hEf),
      hpthP, hadd z hz.le]
    ring
  refine ⟨hsplit, ?_, ?_, ?_⟩
  · -- ## `ℛ`
    intro z θ hq
    have hval := hsplit z θ hq
    have hpz := hpz_all z θ hq
    have hpth := hpth_all z θ hq
    simp only [Work.Construction.Rop]
    rw [hval, hpz, hpth]
    ring
  · -- ## `𝒰/sin 2θ`
    intro z θ hq
    have hval := hsplit z θ hq
    have hpz := hpz_all z θ hq
    simp only [Work.Construction.Uop]
    rw [hval, hpz]
    ring
  · -- ## `𝒱`
    intro z θ hq
    have hval := hsplit z θ hq
    have hpth := hpth_all z θ hq
    simp only [Work.Construction.Vop]
    rw [hval, hpth]
    ring

end Work.FTS.StrongPersist.H6Rows.Npair6SupAux
