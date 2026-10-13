/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/GlueParts/Basic.lean` — the glue vocabulary of the `ε`-scheme

The continuation argument of the `ε`-scheme (`Work.FTS.StrongEps.EpsGlue`) restarts the local
existence (`hstep`) and *concatenates* the pieces at the junction times.  This module collects the
vocabulary those glue arguments need:

* `shiftFam H t` — the family `τ ↦ H (τ - t)` (the restart at a junction at absolute fake time
  `t` is used in this shifted form);
* `epsRHSu` — the right-hand side profile `-𝓛_Γ^T(W) + 𝓖(W)` of the scheme, as a function of
  `(z,θ)`, and its **congruence** `epsRHSu_congr` (with possibly different fake times) and its
  `Jeps`-companion `epsRHSu_Jeps_congr`, plus the junction form `epsRHSu_junction` (the two sides of
  the equation agree at a junction at which the profiles agree);
* the **component extraction** lemmas `hasFDerivWithinAt_apply_fst`/`_snd`/`_thd`: for a
  within-derivative on `ℝ × ℝ × ℝ`, the three coordinate directions are the corresponding partial
  derivatives (the `τ`-one only as a one-sided `HasDerivWithinAt`, since the fake-time interval is
  closed);
* monotonicity of `IsEpsSol`/`EpsReg` in the horizon, and the initial-value projection.

Everything rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.StrongGlobal.Defs
import Submission.Work.FTS.StrongEps.EpsODE

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps

open scoped Real Topology
open MeasureTheory Set Filter
open Work.FTS.Galerkin (Fn Fam slice dynLin dynRHS)

set_option autoImplicit false
set_option linter.unusedVariables false

open Work.FTS.StrongGlobal (P3)

/-! ## The shifted family and the scheme's right-hand side -/

/-- The fake-time shift of a family: `(shiftFam G t) z θ τ = G z θ (τ - t)`.  The restart at a
junction at absolute fake time `t` covers `[t, t + δ]` and is used in exactly this shifted form. -/
noncomputable def shiftFam (G : Fam) (t : ℝ) : Fam := fun z θ τ => G z θ (τ - t)

@[simp] theorem shiftFam_apply (G : Fam) (t z θ τ : ℝ) :
    shiftFam G t z θ τ = G z θ (τ - t) := rfl

@[simp] theorem slice_shiftFam (G : Fam) (t τ : ℝ) : slice (shiftFam G t) τ = slice G (τ - t) :=
  rfl

/-- `Ftau` depends on a family only through its slice, at possibly *different* fake times. -/
theorem Ftau_congr' {α : ℝ} {W W' : Fam} {τ τ' : ℝ} (h : slice W τ = slice W' τ') :
    Work.Construction.Ftau α W τ = Work.Construction.Ftau α W' τ' := by
  funext z θ
  have hzθ : W z θ τ = W' z θ τ' := congrFun (congrFun h z) θ
  simp only [Work.Construction.Ftau, hzθ]

/-- `PsiCan` depends on a family only through its slice, at possibly *different* fake times. -/
theorem slice_PsiCan_congr' {Φs : Fn} {E : Fn → Fn} {W W' : Fam} {τ τ' : ℝ}
    (h : slice W τ = slice W' τ') :
    slice (Work.FTS.Nonlin.PsiCan Φs E W) τ = slice (Work.FTS.Nonlin.PsiCan Φs E W') τ' := by
  funext z θ
  simp only [Work.FTS.Nonlin.PsiCan, slice]
  rw [h]

/-- `muDyn` depends on a family only through its slice, at possibly *different* fake times. -/
theorem muDyn_congr' {α : ℝ} {Φs : Fn} {E : Fn → Fn} {W W' : Fam} {τ τ' : ℝ}
    (h : slice W τ = slice W' τ') :
    Work.FTS.Galerkin.muDyn α (Work.FTS.Nonlin.PsiCan Φs E W) W τ
      = Work.FTS.Galerkin.muDyn α (Work.FTS.Nonlin.PsiCan Φs E W') W' τ' := by
  simp only [Work.FTS.Galerkin.muDyn, Ftau_congr' h, slice_PsiCan_congr' h, h]

/-- The right-hand side profile `-𝓛_Γ^T(W) + 𝓖(W)` of the `ε`-scheme at the fake time `τ`, as a
function of `(z,θ)`; `IsEpsSol` says `∂_τ g = J_ε (epsRHSu (J_ε g) τ)`. -/
noncomputable def epsRHSu (α : ℝ) (ρ : ℝ × ℝ → ℝ) (ε : ℝ) (Φs : Fn) (E : Fn → Fn)
    (W : Fam) (τ : ℝ) : Fn :=
  fun z θ => dynLin α W τ z θ + dynRHS α (Work.FTS.Nonlin.PsiCan Φs E W) W τ z θ

/-- **The right-hand side of the scheme depends on a family only through its slice** (and this at
possibly different fake times). -/
theorem epsRHSu_congr {α : ℝ} {ρ : ℝ × ℝ → ℝ} {ε : ℝ} {Φs : Fn} {E : Fn → Fn}
    {W W' : Fam} {τ τ' : ℝ} (h : slice W τ = slice W' τ') :
    epsRHSu α ρ ε Φs E W τ = epsRHSu α ρ ε Φs E W' τ' := by
  funext z θ
  simp only [epsRHSu, dynLin, dynRHS, Work.FTS.Galerkin.lamDyn,
    muDyn_congr' h, Ftau_congr' h, slice_PsiCan_congr' h, h]

/-- The `J_ε`-companion of `epsRHSu_congr`: the source term of the scheme is the same for two
families with the same slice, at possibly different fake times. -/
theorem epsRHSu_Jeps_congr {α : ℝ} {ρ : ℝ × ℝ → ℝ} {ε : ℝ} {Φs : Fn} {E : Fn → Fn}
    {W W' : Fam} {τ τ' : ℝ} (h : slice W τ = slice W' τ') :
    Jeps ρ ε (epsRHSu α ρ ε Φs E W τ) = Jeps ρ ε (epsRHSu α ρ ε Φs E W' τ') := by
  funext z θ
  refine Jeps_congr ρ ε (fun z θ => ?_) z θ
  exact congrFun (congrFun (epsRHSu_congr (α := α) (ρ := ρ) (ε := ε) (Φs := Φs) (E := E) h) z) θ

/-- The slices of the mollified families agree when the profiles do (at possibly different fake
times). -/
theorem slice_Jfam_eq_of {ρ : ℝ × ℝ → ℝ} {ε : ℝ} {G H : Fam} {t : ℝ}
    (h : ∀ z θ, G z θ t = H z θ 0) :
    slice (Jfam ρ ε G) t = slice (Jfam ρ ε H) 0 := by
  funext z θ
  simp only [slice_Jfam]
  rw [show slice G t = slice H 0 from funext fun z => funext (h z)]

/-- **The junction compatibility of the scheme's source term**: if two families agree at a junction
(`G (·,·,t) = H (·,·,0)`) then the right-hand sides acting on their mollified families agree. -/
theorem epsRHSu_junction {α : ℝ} {ρ : ℝ × ℝ → ℝ} {ε : ℝ} {Φs : Fn} {E : Fn → Fn}
    {G H : Fam} {t : ℝ} (h : ∀ z θ, G z θ t = H z θ 0) :
    epsRHSu α ρ ε Φs E (Jfam ρ ε G) t = epsRHSu α ρ ε Φs E (Jfam ρ ε H) 0 :=
  epsRHSu_congr (slice_Jfam_eq_of h)

/-! ## Component extraction for `HasFDerivWithinAt` on `ℝ × ℝ × ℝ`

For a within-derivative `c` of `f` at `x` on a set `S`, the three coordinate directions of `c` are
the corresponding partial derivatives along the coordinate curves; this is `HasFDerivWithinAt.comp`
with the affine curve (`HasDerivWithinAt`).  The `z`- and `θ`-directions give genuine (two-sided)
`deriv`s because those coordinates are interior to the relevant sets, while the `τ`-direction only
gives a `HasDerivWithinAt` (the fake time lives on a closed interval). -/

theorem hasFDerivWithinAt_apply_fst {f : P3 → ℝ} {c : P3 →L[ℝ] ℝ} {S : Set P3} {x : P3} {r : ℝ}
    (hr : 0 < r) (h : HasFDerivWithinAt f c S x)
    (hS : ∀ s ∈ Set.Ioo (x.1 - r) (x.1 + r), (s, x.2.1, x.2.2) ∈ S) :
    c ((1 : ℝ), 0, 0) = deriv (fun s => f (s, x.2.1, x.2.2)) x.1 := by
  have hcurve : HasDerivWithinAt (fun s : ℝ => (s, x.2.1, x.2.2))
      (((1 : ℝ), 0, 0) : P3) (Set.Ioo (x.1 - r) (x.1 + r)) x.1 :=
    (hasDerivWithinAt_id x.1 _).prodMk
      ((hasDerivWithinAt_const _ _ _).prodMk (hasDerivWithinAt_const _ _ _))
  have hcomp := h.comp_hasDerivWithinAt x.1 hcurve hS
  have hderiv : HasDerivAt (fun s : ℝ => f (s, x.2.1, x.2.2)) (c ((1 : ℝ), 0, 0)) x.1 :=
    hcomp.hasDerivAt (Ioo_mem_nhds (by linarith) (by linarith))
  exact hderiv.deriv.symm

theorem hasFDerivWithinAt_apply_snd {f : P3 → ℝ} {c : P3 →L[ℝ] ℝ} {S : Set P3} {x : P3} {r : ℝ}
    (hr : 0 < r) (h : HasFDerivWithinAt f c S x)
    (hS : ∀ s ∈ Set.Ioo (x.2.1 - r) (x.2.1 + r), (x.1, s, x.2.2) ∈ S) :
    c ((0 : ℝ), 1, 0) = deriv (fun s => f (x.1, s, x.2.2)) x.2.1 := by
  have hcurve : HasDerivWithinAt (fun s : ℝ => (x.1, s, x.2.2))
      (((0 : ℝ), 1, 0) : P3) (Set.Ioo (x.2.1 - r) (x.2.1 + r)) x.2.1 :=
    (hasDerivWithinAt_const _ _ _).prodMk
      ((hasDerivWithinAt_id x.2.1 _).prodMk (hasDerivWithinAt_const _ _ _))
  have hcomp := h.comp_hasDerivWithinAt x.2.1 hcurve hS
  have hderiv : HasDerivAt (fun s : ℝ => f (x.1, s, x.2.2)) (c ((0 : ℝ), 1, 0)) x.2.1 :=
    hcomp.hasDerivAt (Ioo_mem_nhds (by linarith) (by linarith))
  exact hderiv.deriv.symm

theorem hasFDerivWithinAt_apply_thd {f : P3 → ℝ} {c : P3 →L[ℝ] ℝ} {S : Set P3} {x : P3}
    {a b : ℝ} (h : HasFDerivWithinAt f c S x)
    (hS : ∀ s ∈ Set.Icc a b, (x.1, x.2.1, s) ∈ S) :
    HasDerivWithinAt (fun s => f (x.1, x.2.1, s)) (c ((0 : ℝ), 0, 1)) (Set.Icc a b) x.2.2 := by
  have hcurve : HasDerivWithinAt (fun s : ℝ => (x.1, x.2.1, s))
      (((0 : ℝ), 0, 1) : P3) (Set.Icc a b) x.2.2 :=
    (hasDerivWithinAt_const _ _ _).prodMk
      ((hasDerivWithinAt_const _ _ _).prodMk (hasDerivWithinAt_id x.2.2 _))
  exact h.comp_hasDerivWithinAt x.2.2 hcurve hS

/-! ## Monotonicity in the horizon and elementary consequences -/

/-- A solution on `[0,T']` is a solution on every shorter interval `[0,T]`. -/
theorem IsEpsSol.mono {α ε T T' : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Fn} {E : Fn → Fn} {g₀ : Fn}
    {g : Fam} (h : IsEpsSol α ρ ε T' Φs E g₀ g) (hTT' : T ≤ T') :
    IsEpsSol α ρ ε T Φs E g₀ g :=
  ⟨h.1, fun z θ τ hz hθ hτ =>
    (h.2 z θ τ hz hθ ⟨hτ.1, hτ.2.trans hTT'⟩).mono fun s hs => ⟨hs.1, hs.2.trans hTT'⟩⟩

/-- The fake-time zero slice of an `ε`-solution is its datum. -/
theorem IsEpsSol.slice_zero {α ε T : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Fn} {E : Fn → Fn} {g₀ : Fn}
    {g : Fam} (h : IsEpsSol α ρ ε T Φs E g₀ g) : slice g 0 = g₀ :=
  funext fun z => funext fun θ => h.1 z θ

/-- `EpsReg` is monotone in the horizon. -/
theorem EpsReg.mono {α ε T T' : ℝ} {ρ : ℝ × ℝ → ℝ} {g : Fam}
    (h : EpsReg α ρ ε T' g) (hTT' : T ≤ T') : EpsReg α ρ ε T g :=
  ⟨h.1.mono fun p hp => ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.trans hTT'⟩,
    fun τ hτ => h.2 τ ⟨hτ.1, hτ.2.trans hTT'⟩⟩

end Work.FTS.StrongEps
