import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.NDefs
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6Aux.Unfold
import Submission.Work.FTS.StrongPersist.H6Rows.Npair6SupAux.XiOpsplit
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.NZeroAux.NSBasic
import Submission.Work.FTS.StrongPersist.H6Pair6Aux.SmoothN0
import Submission.Work.FTS.StrongPersist.L3Rhs.L3RhsFKadd
import Submission.Work.FTS.StrongPersist.IP6Clauses
import Submission.Work.FTS.Nonlinear.Pieces.splitsDiff
import Submission.Work.FTS.EllipticEst.OpenQDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Npair6SupAux/NSplit6` — the twenty-piece splitting of the level-six `N`-row

On the open quadrant `Qd` the nonlinear term of the modulated equation splits into the twenty
pieces of `NDefs`, because

* the straightened stream function splits, `Ξ = PhiTil α (F_* + f) (Φs + Ef) = Ξ₁ + Ξ₂` with
  `Ξ₁ = PhiTs α Φs`, `Ξ₂ = PhiTil α f Ef` (`XiOpsplit`), hence so do the three coefficient
  fields `ℛ(Ξ)`, `𝒰(Ξ)/sin 2θ`, `𝒱(Ξ)`;
* the angular moment splits, `FK (F_* + f) = FK F_* + FK f` (`L3RhsFKadd`);
* the two slots split, `D_θ(F_* + f) = D_θF_* + D_θf` and `D_z(F_* + f) = D_zF_* + D_zf`
  (additivity of `deriv` on the slices, from the interior smoothness of `F_*` and `f`).

Expanding the five terms of `N α (F_*+f) (Φs+Ef)` with these splits gives exactly the twenty
`nsP`-summands of `nsum`.  The second conjunct — the equality of the two `IP6`-pairings — is
`IP6_congr`, the congruence of the pairing in its first argument on the open quadrant.
-/


noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.H6Rows.Npair6SupAux

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-! ## Additivity of the partial derivatives over the split `F_* + f` -/

/-- The `θ`-slice of a function smooth on the open quadrant is differentiable at an interior
angle. -/
theorem nsplit6_difftheta {g : Fn} (hg : Work.FTS.EllipticEst.SmoothOpen g) {z θ : ℝ}
    (hz : 0 < z) (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    DifferentiableAt ℝ (fun θ' : ℝ => g z θ') θ :=
  (((hg.curry_θ hz).differentiableOn (by simp)).differentiableAt (isOpen_Ioo.mem_nhds hθ))

/-- The `z`-slice of a function smooth on the open quadrant is differentiable at `z > 0`. -/
theorem nsplit6_diffz {g : Fn} (hg : Work.FTS.EllipticEst.SmoothOpen g) {z θ : ℝ}
    (hz : 0 < z) (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    DifferentiableAt ℝ (fun z' : ℝ => g z' θ) z :=
  (((hg.curry_z hθ).differentiableOn (by simp)).differentiableAt (isOpen_Ioi.mem_nhds hz))

/-- `D_θ` is additive over the split `F_* + f`. -/
theorem nsplit6_dth_star_add {α : ℝ} {f : Fn} (hf : Work.FTS.EllipticEst.SmoothOpen f)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    Work.Spaces.Dth (fun z θ => Work.Construction.Fstar α z θ + f z θ) z θ
      = Work.Spaces.Dth (Work.Construction.Fstar α) z θ + Work.Spaces.Dth f z θ := by
  have h : Work.Spaces.pth (fun z θ => Work.Construction.Fstar α z θ + f z θ) z θ
      = Work.Spaces.pth (Work.Construction.Fstar α) z θ + Work.Spaces.pth f z θ :=
    Work.FTS.Nonlinear.Pieces.pth_add_of_diff
      (nsplit6_difftheta (Work.FTS.StrongPersist.H6Pair6Aux.smoothOpen_Fstar α) hz hθ)
      (nsplit6_difftheta hf hz hθ)
  have e1 : Work.Spaces.Dth (fun z θ => Work.Construction.Fstar α z θ + f z θ) z θ
      = Real.sin (2 * θ)
          * Work.Spaces.pth (fun z θ => Work.Construction.Fstar α z θ + f z θ) z θ := rfl
  have e2 : Work.Spaces.Dth (Work.Construction.Fstar α) z θ
      = Real.sin (2 * θ) * Work.Spaces.pth (Work.Construction.Fstar α) z θ := rfl
  have e3 : Work.Spaces.Dth f z θ = Real.sin (2 * θ) * Work.Spaces.pth f z θ := rfl
  rw [e1, e2, e3, h]
  ring

/-- `D_z` is additive over the split `F_* + f`. -/
theorem nsplit6_dz_star_add {α : ℝ} {f : Fn} (hf : Work.FTS.EllipticEst.SmoothOpen f)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2)) :
    Work.Spaces.Dz (fun z θ => Work.Construction.Fstar α z θ + f z θ) z θ
      = Work.Spaces.Dz (Work.Construction.Fstar α) z θ + Work.Spaces.Dz f z θ := by
  have h : Work.Spaces.pz (fun z θ => Work.Construction.Fstar α z θ + f z θ) z θ
      = Work.Spaces.pz (Work.Construction.Fstar α) z θ + Work.Spaces.pz f z θ :=
    Work.FTS.Nonlinear.Pieces.pz_add_of_diff
      (nsplit6_diffz (Work.FTS.StrongPersist.H6Pair6Aux.smoothOpen_Fstar α) hz hθ)
      (nsplit6_diffz hf hz hθ)
  have e1 : Work.Spaces.Dz (fun z θ => Work.Construction.Fstar α z θ + f z θ) z θ
      = z * Work.Spaces.pz (fun z θ => Work.Construction.Fstar α z θ + f z θ) z θ := rfl
  have e2 : Work.Spaces.Dz (Work.Construction.Fstar α) z θ
      = z * Work.Spaces.pz (Work.Construction.Fstar α) z θ := rfl
  have e3 : Work.Spaces.Dz f z θ = z * Work.Spaces.pz f z θ := rfl
  rw [e1, e2, e3, h]
  ring

/-! ## The pointwise identity -/

/-- **The twenty-piece splitting of the level-six `N`-row.**  On the open quadrant,
`N α (F_* + f) (Φs + Ef)` is the sum `nsum α f Ef Φs` of the twenty pieces of `NDefs`. -/
theorem nsplit6_pt {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {f Ef Φs : Fn}
    (hadm : Work.FTS.StrongPersist.H6Adm α f)
    (hEf : Work.FTS.EllipticEst.SmoothOpen Ef) (hΦs : Work.FTS.EllipticEst.SmoothOpen Φs) :
    ∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
      Work.Construction.N α (fun z θ => Work.Construction.Fstar α z θ + f z θ)
          (fun z θ => Φs z θ + Ef z θ) z θ
        = nsum α f Ef Φs z θ := by
  have hαIoc : α ∈ Set.Ioc 0 1 := ⟨hα, hα1⟩
  have hso : Work.FTS.EllipticEst.SmoothOpen f := hadm.reg.1
  obtain ⟨_hXi, hR, hU, hV⟩ := XiOpsplit hα hα1 hadm hEf hΦs
  intro z θ hzθ
  obtain ⟨hz, hθ0, hθ1⟩ := Work.FTS.EllipticEst.mem_Q0.mp hzθ
  have hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨hθ0, hθ1⟩
  have hN := Work.FTS.StrongPersist.H6Pair6Aux.NZeroAux.nzs_N_form α
    (fun z θ => Work.Construction.Fstar α z θ + f z θ)
    (fun z θ => Φs z θ + Ef z θ) z θ hzθ
  have hK : Work.Construction.FK (fun z θ => Work.Construction.Fstar α z θ + f z θ) z
      = Work.Construction.FK (Work.Construction.Fstar α) z + Work.Construction.FK f z := by
    have h := Work.FTS.StrongPersist.L3Rhs.L3RhsFKadd α hαIoc f hadm z hz
    have hftot : Work.Construction.Ftot α f
        = (fun z θ : ℝ => Work.Construction.Fstar α z θ + f z θ) := rfl
    rw [hftot] at h
    exact h
  have hT := nsplit6_dth_star_add (α := α) hso hz hθ
  have hZ := nsplit6_dz_star_add (α := α) hso hz hθ
  rw [hN, hR z θ hzθ, hU z θ hzθ, hV z θ hzθ, hK, hT, hZ]
  simp only [nsum, nsP0, nsP1, nsP2, nsP3, nsP4, nsP5, nsP6, nsP7, nsP8, nsP9, nsP10,
    nsP11, nsP12, nsP13, nsP14, nsP15, nsP16, nsP17, nsP18, nsP19,
    coefR1, coefR2, coefU1, coefU2, coefV1, coefV2, coefKs, coefKf,
    slotFs, slotTs, slotZs, slotTf, slotZf, angSin2]
  ring

theorem NSplit6 {α : ℝ} (hα : 0 < α) (hα1 : α ≤ 1) {f Ef Φs : Work.FTS.Galerkin.Fn}
    (hadm : Work.FTS.StrongPersist.H6Adm α f)
    (hEf : Work.FTS.EllipticEst.SmoothOpen Ef)
    (hΦs : Work.FTS.EllipticEst.SmoothOpen Φs) :
    (∀ z θ : ℝ, (z, θ) ∈ Work.Construction.Qd →
      Work.Construction.N α (fun z θ => Work.Construction.Fstar α z θ + f z θ)
          (fun z θ => Φs z θ + Ef z θ) z θ
        = Work.FTS.StrongPersist.H6Rows.Npair6SupAux.nsum α f Ef Φs z θ) ∧
    (∀ w : Work.FTS.Galerkin.Fn,
      Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1 α
          (Work.Construction.N α (fun z θ => Work.Construction.Fstar α z θ + f z θ)
            (fun z θ => Φs z θ + Ef z θ)) w
        = Work.FTS.StrongPersist.IP6 1 1 1 1 1 1 1 1 1 1 α
            (Work.FTS.StrongPersist.H6Rows.Npair6SupAux.nsum α f Ef Φs) w) := by
  have hmain := nsplit6_pt hα hα1 hadm hEf hΦs
  exact ⟨hmain, fun w =>
    Work.FTS.StrongPersist.IP6_congr 1 1 1 1 1 1 1 1 1 1 α hα hmain⟩

end Work.FTS.StrongPersist.H6Rows.Npair6SupAux
