import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.StrongEps.EpsRLX.MuBlockBase
import Submission.Work.FTS.NonlinRows.NRow1_7Aux
import Submission.Work.FTS.NonlinRows.NAux3
import Submission.Work.FTS.StrongPersist.H6Rows.AK6Row
import Submission.Work.FTS.OpenPkg.Basic
import Submission.Work.FTS.CoercivityFix.Assembly.RegQAux
import Submission.Work.FTS.LocData.HkMem_const_mul
import Submission.Work.FTS.EllipticEst.UopHk.hkMemDzPth_of_shifted
import Submission.Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0
import Submission.Work.FTS.PhiStar.CoreAux.EVDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.EpsRLX

open scoped Real Topology
open MeasureTheory Set Filter
open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-- **The difference of two modulation blocks is `C^∞` on the open quadrant and honestly in
`ℋ⁴`.**

Both modulation constants `μ`, `μ̄` of the block are *scalars* which depend on the profile only
through integrals, so the block is the linear combination

  `muBlock α Φs E W = -μ̄(W)·AK α - μ(W)·W - κ(W)·(D_z W)`,   `κ(W) = μ+λ+μλ`, `λ = lamfun μ`,

of the *fixed* profile `AK α` and of `W` and `D_z W`.  Hence

  `muBlock W₁ - muBlock W₂ = -(μ̄₁-μ̄₂)·AK α - μ₁·(W₁-W₂) - (μ₁-μ₂)·W₂
        - κ₁·(D_z(W₁-W₂)) - (κ₁-κ₂)·D_z W₂`

on the open quadrant, and each of the five summands is smooth / in `ℋ⁴` provided by the data of
the two class-`C` profiles (plus the universal datum `AK α`).

The statement is independent of `Φs` and `E`, precisely because those enter the block only
through the two scalars `μ̄(W)` and `μ(W)`. -/
theorem MuBlockDiffSmoothMem {α : ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn}
    {W₁ W₂ : Work.FTS.Galerkin.Fn}
    (hα : α ∈ Set.Ioc 0 1)
    (hW₁ : Work.FTS.ClassC.ClassC α W₁) (hW₂ : Work.FTS.ClassC.ClassC α W₂) :
    Work.FTS.EllipticEst.SmoothOpen (fun z θ =>
      Work.FTS.StrongEps.EpsRLX.muBlock α Φs E W₁ z θ
        - Work.FTS.StrongEps.EpsRLX.muBlock α Φs E W₂ z θ) ∧
    Work.Spaces.HkMem α 4 (fun z θ =>
      Work.FTS.StrongEps.EpsRLX.muBlock α Φs E W₁ z θ
        - Work.FTS.StrongEps.EpsRLX.muBlock α Φs E W₂ z θ) := by
  classical
  have hα0 : 0 < α := hα.1
  have hα1 : α ≤ 1 := hα.2
  -- ## the difference profile `h = W₁ - W₂` and the fields derived from it
  have hh_sm : Work.FTS.EllipticEst.SmoothOpen (fun z θ => W₁ z θ - W₂ z θ) :=
    Work.FTS.NonlinRows.smoothOpen_sub hW₁.reg hW₂.reg
  have hmem7h : Work.Spaces.HkMem α 7 (fun z θ => W₁ z θ - W₂ z θ) :=
    Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 (α := α) (k := 7)
      (u := fun z θ => W₁ z θ + (-1 : ℝ) * W₂ z θ)
      (v := fun z θ => W₁ z θ - W₂ z θ)
      (Work.FTS.CoercivityFix.Assembly.HkMem_add_open α 7 hW₁.reg
        (Work.FTS.NonlinRows.smoothOpen_const_mul (-1 : ℝ) hW₂.reg)
        hW₁.mem (Work.FTS.LocData.HkMem_const_mul α 7 (-1 : ℝ) hW₂.mem))
      (fun z _ θ _ => by ring)
  have hmem5h : Work.Spaces.HkMem α 5 (fun z θ => W₁ z θ - W₂ z θ) :=
    Work.FTS.OpenPkg.HkMem_mono_open hh_sm 5 (by norm_num) hmem7h
  have hmem4h : Work.Spaces.HkMem α 4 (fun z θ => W₁ z θ - W₂ z θ) :=
    Work.FTS.OpenPkg.HkMem_mono_open hh_sm 4 (by norm_num) hmem7h
  have hmem4₂ : Work.Spaces.HkMem α 4 W₂ :=
    Work.FTS.OpenPkg.HkMem_mono_open hW₂.reg 4 (by norm_num) hW₂.mem
  have hmem5₂ : Work.Spaces.HkMem α 5 W₂ :=
    Work.FTS.OpenPkg.HkMem_mono_open hW₂.reg 5 (by norm_num) hW₂.mem
  have hDzh_sm : Work.FTS.EllipticEst.SmoothOpen
      (Work.Spaces.Dz (fun z θ => W₁ z θ - W₂ z θ)) := hh_sm.Dz
  have hDzh_mem : Work.Spaces.HkMem α 4 (Work.Spaces.Dz (fun z θ => W₁ z θ - W₂ z θ)) :=
    Work.FTS.EllipticEst.UopHk.HkMem_Dz_of_smoothOpen α 4 hh_sm hmem5h
  have hDz₂_sm : Work.FTS.EllipticEst.SmoothOpen (Work.Spaces.Dz W₂) := hW₂.reg.Dz
  have hDz₂_mem : Work.Spaces.HkMem α 4 (Work.Spaces.Dz W₂) :=
    Work.FTS.EllipticEst.UopHk.HkMem_Dz_of_smoothOpen α 4 hW₂.reg hmem5₂
  -- ## the fixed datum `AK α`
  have hAK_sm : Work.FTS.EllipticEst.SmoothOpen (Work.Construction.AK α) :=
    Work.FTS.StrongPersist.AK_smoothO α
  have hAK_mem : Work.Spaces.HkMem α 4 (Work.Construction.AK α) :=
    Work.FTS.NonlinRows.HkMem_AK α hα0 hα1
  -- ## the four scalars of the two blocks
  set mb₁ : ℝ := mubarOf α Φs E W₁ with hmb₁
  set mb₂ : ℝ := mubarOf α Φs E W₂ with hmb₂
  set mu₁ : ℝ := muOf α Φs E W₁ with hmu₁
  set mu₂ : ℝ := muOf α Φs E W₂ with hmu₂
  set ka₁ : ℝ := mu₁ + Work.Construction.lamfun mu₁
    + mu₁ * Work.Construction.lamfun mu₁ with hka₁
  set ka₂ : ℝ := mu₂ + Work.Construction.lamfun mu₂
    + mu₂ * Work.Construction.lamfun mu₂ with hka₂
  -- ## the five summands of the telescoped block
  set f₁ : ℝ → ℝ → ℝ := fun z θ => (-(mb₁ - mb₂)) * Work.Construction.AK α z θ with hf₁
  set f₂ : ℝ → ℝ → ℝ := fun z θ => (-mu₁) * (W₁ z θ - W₂ z θ) with hf₂
  set f₃ : ℝ → ℝ → ℝ := fun z θ => (-(mu₁ - mu₂)) * W₂ z θ with hf₃
  set f₄ : ℝ → ℝ → ℝ :=
    fun z θ => (-ka₁) * Work.Spaces.Dz (fun z θ => W₁ z θ - W₂ z θ) z θ with hf₄
  set f₅ : ℝ → ℝ → ℝ := fun z θ => (-(ka₁ - ka₂)) * Work.Spaces.Dz W₂ z θ with hf₅
  have hf₁_sm : Work.FTS.EllipticEst.SmoothOpen f₁ := by
    rw [hf₁]; exact Work.FTS.NonlinRows.smoothOpen_const_mul _ hAK_sm
  have hf₂_sm : Work.FTS.EllipticEst.SmoothOpen f₂ := by
    rw [hf₂]; exact Work.FTS.NonlinRows.smoothOpen_const_mul _ hh_sm
  have hf₃_sm : Work.FTS.EllipticEst.SmoothOpen f₃ := by
    rw [hf₃]; exact Work.FTS.NonlinRows.smoothOpen_const_mul _ hW₂.reg
  have hf₄_sm : Work.FTS.EllipticEst.SmoothOpen f₄ := by
    rw [hf₄]; exact Work.FTS.NonlinRows.smoothOpen_const_mul _ hDzh_sm
  have hf₅_sm : Work.FTS.EllipticEst.SmoothOpen f₅ := by
    rw [hf₅]; exact Work.FTS.NonlinRows.smoothOpen_const_mul _ hDz₂_sm
  have hf₁_mem : Work.Spaces.HkMem α 4 f₁ := by
    rw [hf₁]; exact Work.FTS.LocData.HkMem_const_mul α 4 _ hAK_mem
  have hf₂_mem : Work.Spaces.HkMem α 4 f₂ := by
    rw [hf₂]; exact Work.FTS.LocData.HkMem_const_mul α 4 _ hmem4h
  have hf₃_mem : Work.Spaces.HkMem α 4 f₃ := by
    rw [hf₃]; exact Work.FTS.LocData.HkMem_const_mul α 4 _ hmem4₂
  have hf₄_mem : Work.Spaces.HkMem α 4 f₄ := by
    rw [hf₄]; exact Work.FTS.LocData.HkMem_const_mul α 4 _ hDzh_mem
  have hf₅_mem : Work.Spaces.HkMem α 4 f₅ := by
    rw [hf₅]; exact Work.FTS.LocData.HkMem_const_mul α 4 _ hDz₂_mem
  -- ## the telescoped block
  set u : ℝ → ℝ → ℝ := fun z θ =>
    (-(mb₁ - mb₂)) * Work.Construction.AK α z θ
      + (-mu₁) * (W₁ z θ - W₂ z θ)
      + (-(mu₁ - mu₂)) * W₂ z θ
      + (-ka₁) * Work.Spaces.Dz (fun z θ => W₁ z θ - W₂ z θ) z θ
      + (-(ka₁ - ka₂)) * Work.Spaces.Dz W₂ z θ with hu
  have hu_sm : Work.FTS.EllipticEst.SmoothOpen u := by
    rw [hu]
    exact Work.FTS.NonlinRows.smoothOpen_add
      (Work.FTS.NonlinRows.smoothOpen_add
        (Work.FTS.NonlinRows.smoothOpen_add
          (Work.FTS.NonlinRows.smoothOpen_add hf₁_sm hf₂_sm) hf₃_sm) hf₄_sm) hf₅_sm
  have hu_mem : Work.Spaces.HkMem α 4 u := by
    rw [hu]
    exact Work.FTS.CoercivityFix.Assembly.HkMem_add_open α 4
      (Work.FTS.NonlinRows.smoothOpen_add (Work.FTS.NonlinRows.smoothOpen_add
        (Work.FTS.NonlinRows.smoothOpen_add hf₁_sm hf₂_sm) hf₃_sm) hf₄_sm) hf₅_sm
      (Work.FTS.CoercivityFix.Assembly.HkMem_add_open α 4
        (Work.FTS.NonlinRows.smoothOpen_add (Work.FTS.NonlinRows.smoothOpen_add hf₁_sm hf₂_sm)
          hf₃_sm) hf₄_sm
        (Work.FTS.CoercivityFix.Assembly.HkMem_add_open α 4
          (Work.FTS.NonlinRows.smoothOpen_add hf₁_sm hf₂_sm) hf₃_sm
          (Work.FTS.CoercivityFix.Assembly.HkMem_add_open α 4 hf₁_sm hf₂_sm
            hf₁_mem hf₂_mem) hf₃_mem) hf₄_mem) hf₅_mem
  -- ## the pointwise telescoping identity on the open quadrant
  have key : ∀ z θ, 0 < z → 0 < θ → θ < Real.pi / 2 →
      u z θ = muBlock α Φs E W₁ z θ - muBlock α Φs E W₂ z θ := by
    intro z θ hz hθ0 hθ1
    have hDzlin : Work.Spaces.Dz (fun z θ => W₁ z θ - W₂ z θ) z θ
        = Work.Spaces.Dz W₁ z θ - Work.Spaces.Dz W₂ z θ := by
      have h := Dz_add_of_smoothOpen (f := W₁) (f' := fun z θ => W₁ z θ - W₂ z θ) (k := W₂)
        hh_sm hW₂.reg (fun z θ => by ring)
      have h' := h z θ hz hθ0 hθ1
      linarith
    rw [hu]
    simp only [hmb₁, hmb₂, hmu₁, hmu₂, hka₁, hka₂, muBlock_apply, Work.Construction.Nstar]
    rw [hDzlin]
    ring
  refine ⟨?_, ?_⟩
  · -- ## the `SmoothOpen` conjunct
    refine Work.FTS.PhiStar.CoreAux.SmoothOpen.congr hu_sm ?_
    intro z θ hz hθ0 hθ1
    exact key z θ hz hθ0 hθ1
  · -- ## the `HkMem` conjunct
    refine Work.FTS.EllipticEst.Cert.GbarSin.HkMem_congr_Q0 (α := α) (k := 4) hu_mem ?_
    intro z hz θ hθ
    exact key z θ hz hθ.1 hθ.2

end Work.FTS.StrongEps.EpsRLX
