import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.InnerProductSpace.Basic
import Submission.Work.FTS.StrongEps.PZeroScheme
import Submission.Work.FTS.StrongEps.ClassCRHS.SmoothOpenRHS
import Submission.Work.FTS.StrongEps.ScalarBounds
import Submission.Work.FTS.StrongEps.smoothOpen_dynRHS
import Submission.Work.FTS.StrongEps.smoothOpen_linPart

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Submission/Work/FTS/StrongEps/smoothOpen_epsWP.lean`

**Target.** `Work.FTS.StrongEps.smoothOpen_epsWP`: the pre-mollified right-hand side

  `epsWP α ρ ε Φs E g s = 𝓛_{Γ}^{T}(slice (JfamP ρ ε g) s) + gRHS(μ̄,λ, F_* + slice (JfamP ρ ε g) s,
   slice (PsiCan Φs E (JfamP ρ ε g)) s, slice (JfamP ρ ε g) s)`

of the `P₀`-corrected `ε`-scheme is `C^∞` on the open quadrant `(0,∞) × (0,π/2)`, for every
fake time `s ∈ [0,T]`, **assuming**

* `hC` : the projected slices `slice (JfamP ρ ε g) s` lie in the class `ClassC α` (i.e. they are
  open-quadrant smooth and `ℋ^{10}`-honest),
* `hEll` : the elliptic solution operator `E` returns an `EllPkgGo`-package at the class-`C`
  profiles,
* `hstar` : the star package `StarPkgo2 α Cs Φs` of the datum `Φs`.

## The proof

`epsWP = dynLin + dynRHS` definitionally, so it suffices to treat the two summands.

* **The linear part** `dynLin = -𝓛_Γ^T(w)`, `w := slice (JfamP ρ ε g) s`: the third conjunct of
  `ClassCRHS.SmoothOpenRHS` (the module that assembles the atoms of the right-hand side from the
  class-`C` data) is exactly `SmoothOpen (𝓛_Γ^T w)`.
* **The nonlinear part** `dynRHS`: here the useful general form is
  `smoothOpen_gRHS_gen`, whose hypotheses are the *atoms* of `gRHS` in exactly the shape in which
  `SmoothOpenRHS` delivers them: `F = F_* + w`, `Φ = Φs + E w = slice (PsiCan Φs E (JfamP …)) s`,
  the radial moments `L₁₂(w)`, `L₁₂(F)`, `FK(F)`, and the three transported coefficients
  `ℛ(Φ̃)`, `𝒰(Φ̃)`, `𝒱(Φ̃)` of the residual `Φ̃ = PhiTil α F Φ`.  The last three are produced here
  from `SmoothOpen (PhiTil α F Φ)` (which is `Φ - (1/(4α))·sin 2θ ·L₁₂(F)`) with
  `smoothOpen_Rop` / `EllipticEst.smoothOpen_Uop` / `smoothOpen_Vop`.

Everything is `SmoothOpen`-API plus definitional unfolding: `Ftau α (JfamP ρ ε g) s` and
`Ftot α (slice (JfamP ρ ε g) s)` are the same function, `slice (PsiCan Φs E (JfamP ρ ε g)) s` is
`fun z θ => Φs z θ + E (slice (JfamP ρ ε g) s) z θ`, and `gRHS`/`muDyn`/`lamDyn` unfold to the
`dynRHS` of `Work.FTS.Galerkin`.
-/

namespace Work.FTS.StrongEps

open Work.FTS.EllipticEst (SmoothOpen)

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

/-- **The nonlinear part of the `P₀`-corrected `ε`-scheme is `C^∞` on the open quadrant.**

This is `smoothOpen_gRHS_gen` at the profile `F = F_* + w` and the stream function
`Φs + E w`, where `w := slice (JfamP ρ ε g) s` is the projected slice at the fake time `s`; the
modulation constants `μ̄`, `λ` are irrelevant (they are numbers).  All atoms come from
`ClassCRHS.SmoothOpenRHS`; the coefficient atoms `ℛ`, `𝒰`, `𝒱` are built here from the
open-quadrant smoothness of the residual `PhiTil α F Φ`. -/
theorem smoothOpen_dynRHS_of_classC {α Ce Cs ε : ℝ} {ρ : ℝ × ℝ → ℝ}
    {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn}
    {g : Work.FTS.Galerkin.Fam} {s : ℝ}
    (hα0 : 0 < α) (hα1 : α ≤ 1)
    (hw : Work.FTS.ClassC.ClassC α
      (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ ε g) s))
    (hell : Work.FTS.VocabO.EllPkgGo α Ce
      (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ ε g) s)
      (E (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ ε g) s)))
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs) :
    SmoothOpen
      (Work.FTS.Galerkin.dynRHS α (Work.FTS.Nonlin.PsiCan Φs E (Work.FTS.StrongEps.JfamP ρ ε g))
        (Work.FTS.StrongEps.JfamP ρ ε g) s) := by
  -- ### the atoms of the right-hand side, in `SmoothOpen` normal form
  obtain ⟨hL12F, hFKF, hLG, hN0, hN⟩ :=
    Work.FTS.StrongEps.ClassCRHS.SmoothOpenRHS hα0 hα1 hw hell hstar
  -- the radial moment of the perturbation (`N₀` is evaluated at `w`, not at `F`)
  have hL12w : SmoothOpen (fun z _ => Work.Construction.L12
      (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ ε g) s) z) :=
    Work.FTS.NonlinRows.smoothOpen_L12_radial hα0 hell.smooth hell.V.1.1
  -- the full profile `F = F_* + w` and the stream function `Φs + E w`
  have hF : SmoothOpen
      (Work.Construction.Ftot α (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ ε g) s)) :=
    Work.FTS.NonlinRows.smoothOpen_add
      (Work.FTS.OpenPkg.smoothOpen_of_smoothQuad (Work.FTS.LocData.SmoothQuad_Fstar α)) hw.reg
  have hPhi : SmoothOpen
      (fun z θ => Φs z θ + E (Work.FTS.Galerkin.slice
        (Work.FTS.StrongEps.JfamP ρ ε g) s) z θ) :=
    Work.FTS.NonlinRows.smoothOpen_add hstar.smooth hell.smooth
  -- ### the residual `Φ̃ = Φ - Θ = Φ - (1/(4α))·sin 2θ·L₁₂(F)`
  have hTheta : SmoothOpen (fun z θ => (1 / (4 * α)) * Work.Construction.s2 θ
      * Work.Construction.L12 (Work.Construction.Ftot α
          (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ ε g) s)) z) :=
    Work.FTS.NonlinRows.smoothOpen_mul
      (Work.FTS.NonlinRows.smoothOpen_const_mul (1 / (4 * α))
        Work.FTS.GalFields.RHS.smoothOpen_sin_two) hL12F
  have hPsi : SmoothOpen (Work.Construction.PhiTil α (Work.Construction.Ftot α
      (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ ε g) s))
      (fun z θ => Φs z θ + E (Work.FTS.Galerkin.slice
        (Work.FTS.StrongEps.JfamP ρ ε g) s) z θ)) :=
    hPhi.sub hTheta
  -- ### the three transported coefficients `ℛ`, `𝒰`, `𝒱` of `Φ̃`
  have hR : SmoothOpen (Work.Construction.Rop α (Work.Construction.PhiTil α
      (Work.Construction.Ftot α (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ ε g) s))
      (fun z θ => Φs z θ + E (Work.FTS.Galerkin.slice
        (Work.FTS.StrongEps.JfamP ρ ε g) s) z θ))) :=
    Work.FTS.NonlinRows.smoothOpen_Rop hPsi
  have hU : SmoothOpen (Work.Construction.Uop α (Work.Construction.PhiTil α
      (Work.Construction.Ftot α (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ ε g) s))
      (fun z θ => Φs z θ + E (Work.FTS.Galerkin.slice
        (Work.FTS.StrongEps.JfamP ρ ε g) s) z θ))) :=
    Work.FTS.EllipticEst.smoothOpen_Uop hPsi
  have hV : SmoothOpen (Work.Construction.Vop (Work.Construction.PhiTil α
      (Work.Construction.Ftot α (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ ε g) s))
      (fun z θ => Φs z θ + E (Work.FTS.Galerkin.slice
        (Work.FTS.StrongEps.JfamP ρ ε g) s) z θ))) :=
    Work.FTS.NonlinRows.smoothOpen_Vop hPsi
  -- ### assembly: the general form of the right-hand side, at the modulation constants
  exact smoothOpen_gRHS_gen (α := α)
    (μ := Work.FTS.Galerkin.muDyn α
      (Work.FTS.Nonlin.PsiCan Φs E (Work.FTS.StrongEps.JfamP ρ ε g))
      (Work.FTS.StrongEps.JfamP ρ ε g) s)
    (lam := Work.FTS.Galerkin.lamDyn α
      (Work.FTS.Nonlin.PsiCan Φs E (Work.FTS.StrongEps.JfamP ρ ε g))
      (Work.FTS.StrongEps.JfamP ρ ε g) s)
    (F := Work.Construction.Ftot α (Work.FTS.Galerkin.slice
      (Work.FTS.StrongEps.JfamP ρ ε g) s))
    (Φ := fun z θ => Φs z θ + E (Work.FTS.Galerkin.slice
      (Work.FTS.StrongEps.JfamP ρ ε g) s) z θ)
    (gg := Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ ε g) s)
    hF hw.reg hL12w hFKF hR hU hV

theorem smoothOpen_epsWP {α C₀ Ce Cs T : ℝ} {ρ : ℝ × ℝ → ℝ}
    {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn}
    {g : Work.FTS.Galerkin.Fam} {ε : ℝ}
    (hα : α ∈ Set.Ioc 0 1)
    (hEll : ∀ u : Work.FTS.Galerkin.Fn, Work.FTS.ClassC.ClassC α u →
      Work.FTS.VocabO.EllPkgGo α Ce u (E u) ∧ Work.FTS.ClassC.EllPkgK α 6 Ce u (E u))
    (hstar : Work.FTS.VocabO2.StarPkgo2 α Cs Φs)
    (hC : ∀ s ∈ Set.Icc 0 T, Work.FTS.ClassC.ClassC α
      (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ ε g) s)) :
    ∀ s ∈ Set.Icc 0 T, Work.FTS.EllipticEst.SmoothOpen
      (Work.FTS.StrongEps.epsWP α ρ ε Φs E g s) := by
  intro s hs
  have hα0 : 0 < α := hα.1
  have hα1 : α ≤ 1 := hα.2
  -- the projected slice at the fake time `s` is in the class `C`, and `E` returns its package
  have hw : Work.FTS.ClassC.ClassC α
      (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ ε g) s) := hC s hs
  have hell : Work.FTS.VocabO.EllPkgGo α Ce
      (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ ε g) s)
      (E (Work.FTS.Galerkin.slice (Work.FTS.StrongEps.JfamP ρ ε g) s)) := (hEll _ hw).1
  -- the linear part `dynLin = -𝓛_Γ^T(w)`
  have hlin : SmoothOpen (Work.FTS.Galerkin.dynLin α (Work.FTS.StrongEps.JfamP ρ ε g) s) :=
    (Work.FTS.StrongEps.ClassCRHS.SmoothOpenRHS hα0 hα1 hw hell hstar).2.2.1.neg
  -- the nonlinear part `dynRHS`
  have hdyn : SmoothOpen (Work.FTS.Galerkin.dynRHS α
      (Work.FTS.Nonlin.PsiCan Φs E (Work.FTS.StrongEps.JfamP ρ ε g))
      (Work.FTS.StrongEps.JfamP ρ ε g) s) :=
    smoothOpen_dynRHS_of_classC hα0 hα1 hw hell hstar
  -- `epsWP` is definitionally the sum of the two
  exact Work.FTS.NonlinRows.smoothOpen_add hlin hdyn

end Work.FTS.StrongEps
