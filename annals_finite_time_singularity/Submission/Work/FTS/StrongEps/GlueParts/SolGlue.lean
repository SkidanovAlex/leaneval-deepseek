/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/GlueParts/SolGlue.lean` — the concatenation of two `ε`-solutions

The continuation argument of the `ε`-scheme (`Work.FTS.StrongEps.EpsGlue`) restarts the local
existence at a junction time and *concatenates* the pieces.  This module proves that the
concatenation of an `ε`-solution on `[0,t]` with a *restarted* `ε`-solution on `[0,δ]` (the
restart being used in the shifted form `shiftFam H t`, i.e. `τ ↦ H (τ - t)`), taken at the
junction `t`, is an `ε`-solution on `[0, t + δ]` — the glue step `S5` of the strong route.

The whole content is the observation that the scheme `∂_τ g = J_ε (epsRHSu (J_ε g) τ)` depends on
the family only through its fake-time *slice* (`epsRHSu_congr`), so that at every `τ ∈ [0,t+δ]`
the right-hand side acting on the concatenation is the right-hand side of the piece that is
active at `τ`; the derivatives then glue by the elementary
`Work.FTS.Galerkin.Ode.hasDerivWithinAt_glue` (the `τ = t` junction being handled by the union
rule for `HasDerivWithinAt`, and the two one-sided values agreeing by `epsRHSu_junction`).

Everything rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.StrongEps.GlueParts.Basic
import Submission.Work.FTS.Galerkin.Ode.hasDerivWithinAt_glue

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.GlueParts

open scoped Real Topology
open Set Filter

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## Auxiliary facts -/

/-- The scheme's equation, with the right-hand side written through `epsRHSu`. -/
theorem isEpsSol_gdot_eq {α ε T : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Fn} {E : Fn → Fn} {g₀ : Fn}
    {g : Fam} (h : IsEpsSol α ρ ε T Φs E g₀ g) :
    ∀ z θ τ, 0 < z → θ ∈ Set.Ioo 0 (π / 2) → τ ∈ Set.Icc 0 T →
      HasDerivWithinAt (fun s => g z θ s)
        (Jeps ρ ε (epsRHSu α ρ ε Φs E (Jfam ρ ε g) τ) z θ) (Set.Icc 0 T) τ :=
  fun z θ τ hz hθ hτ => h.2 z θ τ hz hθ hτ

/-- Differentiation of a shifted function: `s ↦ f (s - a)` has the derivative of `f` at `s - a`,
on the shifted interval `[a, a+c]`. -/
theorem hasDerivWithinAt_comp_sub_Icc {f : ℝ → ℝ} {f' : ℝ} {x a c : ℝ}
    (h : HasDerivWithinAt f f' (Set.Icc 0 c) (x - a)) :
    HasDerivWithinAt (fun y : ℝ => f (y - a)) f' (Set.Icc a (a + c)) x := by
  have hg : HasDerivWithinAt (fun y : ℝ => y - a) 1 (Set.Icc a (a + c)) x :=
    ((hasDerivAt_id (x := x)).sub_const a).hasDerivWithinAt
  have hst : MapsTo (fun y : ℝ => y - a) (Set.Icc a (a + c)) (Set.Icc 0 c) :=
    fun y hy => ⟨by linarith [hy.1], by linarith [hy.2]⟩
  have hcomp := h.comp x hg hst
  have heq : (f ∘ fun y : ℝ => y - a) = (fun y : ℝ => f (y - a)) := funext fun y => rfl
  rw [heq, mul_one] at hcomp
  exact hcomp

/-- The slice of the mollified concatenation before the junction. -/
theorem slice_Jfam_concat_of_le {ρ : ℝ × ℝ → ℝ} {ε : ℝ} {G H : Fam} {t τ : ℝ}
    (h : τ ≤ t) :
    slice (Jfam ρ ε (Work.FTS.StrongGlobal.concat G (shiftFam H t) t)) τ
      = slice (Jfam ρ ε G) τ := by
  rw [slice_Jfam, slice_Jfam, Work.FTS.StrongGlobal.slice_concat_of_le h]

/-- The slice of the mollified concatenation after the junction. -/
theorem slice_Jfam_concat_of_gt {ρ : ℝ × ℝ → ℝ} {ε : ℝ} {G H : Fam} {t τ : ℝ}
    (h : t < τ) :
    slice (Jfam ρ ε (Work.FTS.StrongGlobal.concat G (shiftFam H t) t)) τ
      = slice (Jfam ρ ε H) (τ - t) := by
  rw [slice_Jfam, slice_Jfam, Work.FTS.StrongGlobal.slice_concat_of_gt h, slice_shiftFam]

/-- `epsRHSu` sees the mollified concatenation as the left piece before the junction. -/
theorem epsRHSu_concat_of_le {α ε : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Fn} {E : Fn → Fn}
    {G H : Fam} {t τ : ℝ} (h : τ ≤ t) :
    epsRHSu α ρ ε Φs E (Jfam ρ ε (Work.FTS.StrongGlobal.concat G (shiftFam H t) t)) τ
      = epsRHSu α ρ ε Φs E (Jfam ρ ε G) τ :=
  epsRHSu_congr (slice_Jfam_concat_of_le h)

/-- `epsRHSu` sees the mollified concatenation as the (shifted) right piece after the junction. -/
theorem epsRHSu_concat_of_gt {α ε : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Fn} {E : Fn → Fn}
    {G H : Fam} {t τ : ℝ} (h : t < τ) :
    epsRHSu α ρ ε Φs E (Jfam ρ ε (Work.FTS.StrongGlobal.concat G (shiftFam H t) t)) τ
      = epsRHSu α ρ ε Φs E (Jfam ρ ε H) (τ - t) :=
  epsRHSu_congr (slice_Jfam_concat_of_gt h)

/-! ## The glue -/

theorem SolGlue {α ε t δ : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Work.FTS.Galerkin.Fn} {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn} {g₀ : Work.FTS.Galerkin.Fn}
    {G H : Work.FTS.Galerkin.Fam} (ht : 0 ≤ t) (hδ : 0 < δ)
    (hG : Work.FTS.StrongEps.IsEpsSol α ρ ε t Φs E g₀ G)
    (hH : Work.FTS.StrongEps.IsEpsSol α ρ ε δ Φs E (Work.FTS.Galerkin.slice G t) H) :
    Work.FTS.StrongEps.IsEpsSol α ρ ε (t + δ) Φs E g₀
      (Work.FTS.StrongGlobal.concat G (Work.FTS.StrongEps.shiftFam H t) t) := by
  refine ⟨?_, ?_⟩
  · -- the datum
    intro z θ
    rw [Work.FTS.StrongGlobal.concat_apply_of_le (τ₀ := t) (τ := 0) ht]
    exact hG.1 z θ
  · -- the equation on `[0, t + δ]`
    intro z θ τ hz hθ hτ
    -- the two pieces agree at the junction
    have hjunc : Jeps ρ ε (epsRHSu α ρ ε Φs E (Jfam ρ ε G) t)
        = Jeps ρ ε (epsRHSu α ρ ε Φs E (Jfam ρ ε H) 0) := by
      rw [epsRHSu_junction (α := α) (ρ := ρ) (ε := ε) (Φs := Φs) (E := E) (G := G) (H := H)
        (t := t) (fun z θ => (hH.1 z θ).symm)]
    -- the value of the scheme on the concatenation, before/after the junction
    have hVle : ∀ x, x ≤ t →
        Jeps ρ ε (epsRHSu α ρ ε Φs E
            (Jfam ρ ε (Work.FTS.StrongGlobal.concat G (shiftFam H t) t)) x)
          = Jeps ρ ε (epsRHSu α ρ ε Φs E (Jfam ρ ε G) x) := by
      intro x hx
      rw [epsRHSu_concat_of_le (α := α) (ρ := ρ) (ε := ε) (Φs := Φs) (E := E) (G := G)
        (H := H) hx]
    have hVgt : ∀ x, t < x →
        Jeps ρ ε (epsRHSu α ρ ε Φs E
            (Jfam ρ ε (Work.FTS.StrongGlobal.concat G (shiftFam H t) t)) x)
          = Jeps ρ ε (epsRHSu α ρ ε Φs E (Jfam ρ ε H) (x - t)) := by
      intro x hx
      rw [epsRHSu_concat_of_gt (α := α) (ρ := ρ) (ε := ε) (Φs := Φs) (E := E) (G := G)
        (H := H) hx]
    -- the glue of the two one-sided statements
    have key : ∀ x ∈ Set.Icc (0 : ℝ) (t + δ),
        HasDerivWithinAt
          (fun s : ℝ => Work.FTS.StrongGlobal.concat G (shiftFam H t) t z θ s)
          (Jeps ρ ε (epsRHSu α ρ ε Φs E
            (Jfam ρ ε (Work.FTS.StrongGlobal.concat G (shiftFam H t) t)) x) z θ)
          (Set.Icc 0 (t + δ)) x := by
      have hglue := Work.FTS.Galerkin.Ode.hasDerivWithinAt_glue (E := ℝ)
        (f := fun y : ℝ => G z θ y) (g := fun y : ℝ => H z θ (y - t))
        (a := 0) (b := t) (c := t + δ) ht (by linarith)
        (by show G z θ t = H z θ (t - t); rw [sub_self]; exact (hH.1 z θ).symm)
        (v := fun x => Jeps ρ ε (epsRHSu α ρ ε Φs E
          (Jfam ρ ε (Work.FTS.StrongGlobal.concat G (shiftFam H t) t)) x) z θ)
        (fun x hx => by
          show HasDerivWithinAt (fun y : ℝ => G z θ y)
            (Jeps ρ ε (epsRHSu α ρ ε Φs E
              (Jfam ρ ε (Work.FTS.StrongGlobal.concat G (shiftFam H t) t)) x) z θ)
            (Set.Icc 0 t) x
          rw [hVle x hx.2]
          exact isEpsSol_gdot_eq hG z θ x hz hθ hx)
        (fun x hx => by
          show HasDerivWithinAt (fun y : ℝ => H z θ (y - t))
            (Jeps ρ ε (epsRHSu α ρ ε Φs E
              (Jfam ρ ε (Work.FTS.StrongGlobal.concat G (shiftFam H t) t)) x) z θ)
            (Set.Icc t (t + δ)) x
          have hx' : x - t ∈ Set.Icc (0 : ℝ) δ := ⟨by linarith [hx.1], by linarith [hx.2]⟩
          have hHd := isEpsSol_gdot_eq hH z θ (x - t) hz hθ hx'
          have hcomp := hasDerivWithinAt_comp_sub_Icc (a := t) (c := δ) (x := x) hHd
          have hval : Jeps ρ ε (epsRHSu α ρ ε Φs E (Jfam ρ ε H) (x - t))
              = Jeps ρ ε (epsRHSu α ρ ε Φs E
                  (Jfam ρ ε (Work.FTS.StrongGlobal.concat G (shiftFam H t) t)) x) := by
            rcases eq_or_lt_of_le hx.1 with hxt | hxt
            · subst hxt
              rw [sub_self]
              exact hjunc.symm.trans (hVle t le_rfl).symm
            · exact (hVgt x hxt).symm
          rw [hval] at hcomp
          exact hcomp)
      -- identify the glued function with the concatenation
      have hfun : (fun y : ℝ => if y ≤ t then G z θ y else H z θ (y - t))
          = fun s : ℝ => Work.FTS.StrongGlobal.concat G (shiftFam H t) t z θ s := by
        funext y
        simp only [Work.FTS.StrongGlobal.concat, shiftFam]
      intro x hx
      rw [← hfun]
      exact hglue x hx
    exact key τ hτ

end Work.FTS.StrongEps.GlueParts
