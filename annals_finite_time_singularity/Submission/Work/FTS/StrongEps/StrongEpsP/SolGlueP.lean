/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/StrongEpsP/SolGlueP.lean` — the concatenation of two
`P₀`-solutions

This is the `P₀`-corrected analogue of `Work.FTS.StrongEps.GlueParts.SolGlue`: the concatenation
of a `P₀`-solution `G` on `[0,t]` with a restarted `P₀`-solution `H` on `[0,δ]` (used in the
shifted form `shiftFam H t`) at the junction `t` is a `P₀`-solution on `[0, t + δ]`.

The proof is the same observation as for the unprojected scheme: the right-hand side
`epsRHSP α ρ ε Φs E g τ = Pz (Jeps ρ ε (epsWP α ρ ε Φs E g τ))` depends on the family `g` only
through its fake-time *slice* (`epsRHSP_congr`, proved in `Defs.lean` from `slice_JfamP_congr` and
`epsRHSu_congr`), so at every `τ ∈ [0, t+δ]` the right-hand side acting on the concatenation is
the right-hand side of the piece that is active at `τ`.  The derivatives glue by the elementary
`Work.FTS.Galerkin.Ode.hasDerivWithinAt_glue` (the junction `τ = t` being handled by the union
rule for `HasDerivWithinAt`, the two one-sided values agreeing by `epsRHSP_congr` at the
junction, where the two families have the same slice).

Everything rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.StrongEps.StrongEpsP.Defs
import Submission.Work.FTS.Galerkin.Ode.hasDerivWithinAt_glue

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.StrongEps.StrongEpsP

open scoped Real Topology
open Set Filter

open Work.FTS.Galerkin (Fn Fam slice)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## An elementary change of variables for one-sided derivatives -/

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

/-! ## The glue -/

theorem SolGlueP {α ε t δ : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Work.FTS.Galerkin.Fn}
    {E : Work.FTS.Galerkin.Fn → Work.FTS.Galerkin.Fn} {g₀ : Work.FTS.Galerkin.Fn}
    {G H : Work.FTS.Galerkin.Fam} (ht : 0 ≤ t) (hδ : 0 < δ)
    (hG : Work.FTS.StrongEps.IsEpsSolP α ρ ε t Φs E g₀ G)
    (hH : Work.FTS.StrongEps.IsEpsSolP α ρ ε δ Φs E (Work.FTS.Galerkin.slice G t) H) :
    Work.FTS.StrongEps.IsEpsSolP α ρ ε (t + δ) Φs E g₀
      (Work.FTS.StrongGlobal.concat G (Work.FTS.StrongEps.shiftFam H t) t) := by
  refine ⟨?_, ?_⟩
  · -- the datum
    intro z θ
    rw [Work.FTS.StrongGlobal.concat_apply_of_le (τ₀ := t) (τ := 0) ht]
    exact hG.1 z θ
  · -- the equation on `[0, t + δ]`
    intro z θ τ hz hθ hτ
    -- the two pieces agree at the junction (they have the same slice there)
    have hjunc : epsRHSP α ρ ε Φs E G t = epsRHSP α ρ ε Φs E H 0 :=
      epsRHSP_congr (Φs := Φs) (E := E) (W := G) (W' := H) (τ := t) (τ' := 0)
        (funext fun z => funext fun θ => (hH.1 z θ).symm)
    -- the value of the scheme on the concatenation, before/after the junction
    have hVle : ∀ x, x ≤ t →
        epsRHSP α ρ ε Φs E (Work.FTS.StrongGlobal.concat G (shiftFam H t) t) x
          = epsRHSP α ρ ε Φs E G x :=
      fun x hx => epsRHSP_congr (Φs := Φs) (E := E) (W := _) (W' := G) (τ := x) (τ' := x)
        (Work.FTS.StrongGlobal.slice_concat_of_le hx)
    have hVgt : ∀ x, t < x →
        epsRHSP α ρ ε Φs E (Work.FTS.StrongGlobal.concat G (shiftFam H t) t) x
          = epsRHSP α ρ ε Φs E H (x - t) :=
      fun x hx => epsRHSP_congr (Φs := Φs) (E := E) (W := _) (W' := H) (τ := x) (τ' := x - t)
        (Work.FTS.StrongGlobal.slice_concat_of_gt hx)
    -- the glue of the two one-sided statements
    have key : ∀ x ∈ Set.Icc (0 : ℝ) (t + δ),
        HasDerivWithinAt
          (fun s : ℝ => Work.FTS.StrongGlobal.concat G (shiftFam H t) t z θ s)
          (epsRHSP α ρ ε Φs E
            (Work.FTS.StrongGlobal.concat G (shiftFam H t) t) x z θ)
          (Set.Icc 0 (t + δ)) x := by
      have hglue := Work.FTS.Galerkin.Ode.hasDerivWithinAt_glue (E := ℝ)
        (f := fun y : ℝ => G z θ y) (g := fun y : ℝ => H z θ (y - t))
        (a := 0) (b := t) (c := t + δ) ht (by linarith)
        (by show G z θ t = H z θ (t - t); rw [sub_self]; exact (hH.1 z θ).symm)
        (v := fun x => epsRHSP α ρ ε Φs E
          (Work.FTS.StrongGlobal.concat G (shiftFam H t) t) x z θ)
        (fun x hx => by
          show HasDerivWithinAt (fun y : ℝ => G z θ y)
            (epsRHSP α ρ ε Φs E
              (Work.FTS.StrongGlobal.concat G (shiftFam H t) t) x z θ) (Set.Icc 0 t) x
          rw [hVle x hx.2]
          exact hG.2 z θ x hz hθ hx)
        (fun x hx => by
          show HasDerivWithinAt (fun y : ℝ => H z θ (y - t))
            (epsRHSP α ρ ε Φs E
              (Work.FTS.StrongGlobal.concat G (shiftFam H t) t) x z θ)
            (Set.Icc t (t + δ)) x
          have hx' : x - t ∈ Set.Icc (0 : ℝ) δ := ⟨by linarith [hx.1], by linarith [hx.2]⟩
          have hHd := hH.2 z θ (x - t) hz hθ hx'
          have hcomp := hasDerivWithinAt_comp_sub_Icc (a := t) (c := δ) (x := x) hHd
          have hval : epsRHSP α ρ ε Φs E H (x - t)
              = epsRHSP α ρ ε Φs E
                  (Work.FTS.StrongGlobal.concat G (shiftFam H t) t) x := by
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
        simp only [Work.FTS.StrongGlobal.concat, Work.FTS.StrongEps.shiftFam]
      intro x hx
      rw [← hfun]
      exact hglue x hx
    exact key τ hτ

end Work.FTS.StrongEps.StrongEpsP
