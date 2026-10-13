/-
Copyright: work module for the Elgindi finite-time singularity project.

# `Submission/Work/FTS/StrongEps/StrongEpsP/Defs.lean` — the shared interface of the
`P₀`-scheme's continuation

`Work.FTS.StrongEps.EpsGlue` proves the continuation (restart-and-concatenate) theorem for the
`ε`-scheme `IsEpsSol` of `EpsODE.lean`, through the abstract core
`Work.FTS.StrongEps.GlueParts.Induction.EpsGlue_of_glue` and the two junction glues
`GlueParts.SolGlue`/`GlueParts.RegGlue`.  Its proof never uses anything about the scheme beyond

* the scheme's right-hand side **depends on a family only through its fake-time slice**
  (`epsRHSu_congr`), and
* at a junction at which two families agree, the two one-sided right-hand sides agree
  (`epsRHSu_junction`).

The `P₀`-corrected scheme `IsEpsSolP` of `PZeroScheme.lean`,
`∂_τ g = P₀ J_ε [𝓛 + 𝓡](P₀ J_ε g)`, is the one the design's §(B) actually specifies (the
unprojected one has a *false* class-`C` clause; see `NOTES_Pzero.md`), and it enjoys the same two
properties.  This module records them, together with the elementary monotonicity/slice bookkeeping
that the copies of the three glue proofs need:

* `slice_JfamP_congr` / `slice_JfamP_eq_of` — the projected mollified family is slice-determined;
* `epsWP_eq_epsRHSu` — the projected right-hand side is the unprojected one at the projected family;
* `epsWP_congr`, `epsRHSP_congr` — slice-determination of the projected right-hand side;
* `epsRHSP_junction` — the junction compatibility;
* `IsEpsSolP.mono` / `IsEpsSolP.slice_zero` — horizon monotonicity and the initial slice;
* `slice_JfamP_concat_of_le/_gt`, `epsRHSP_concat_of_le/_gt` — the concatenation slices.

Everything here rests only on the definitions of `PZeroScheme.lean`/`EpsStructP.lean` and on the
already-proved glue vocabulary of `GlueParts/Basic.lean`.
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.StrongEps.GlueParts.Basic
import Submission.Work.FTS.StrongEps.PZeroScheme
import Submission.Work.FTS.StrongEps.EpsStructP

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongEps.StrongEpsP

open Work.FTS.Galerkin (Fn Fam slice)
open Work.FTS.StrongGlobal (Xn6 concat)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The projected right-hand side is the unprojected one at the projected family -/

/-- The right-hand side of the projected scheme is `epsRHSu` (the scheme's profile right-hand
side of `GlueParts/Basic.lean`) evaluated at the **projected** mollified family.  Definitional. -/
theorem epsWP_eq_epsRHSu (α : ℝ) (ρ : ℝ × ℝ → ℝ) (ε : ℝ) (Φs : Fn) (E : Fn → Fn) (g : Fam)
    (τ : ℝ) : epsWP α ρ ε Φs E g τ = epsRHSu α ρ ε Φs E (JfamP ρ ε g) τ := rfl

/-- The projected right-hand side, written through `epsRHSu`. -/
theorem epsRHSP_eq_Pz_Jeps_epsRHSu (α : ℝ) (ρ : ℝ × ℝ → ℝ) (ε : ℝ) (Φs : Fn) (E : Fn → Fn)
    (g : Fam) (τ : ℝ) :
    epsRHSP α ρ ε Φs E g τ
      = Pz (Jeps ρ ε (epsRHSu α ρ ε Φs E (JfamP ρ ε g) τ)) := rfl

/-! ## The projected family is slice-determined -/

/-- `JfamP` depends on a family only through its slice, at possibly different fake times. -/
theorem slice_JfamP_congr {ρ : ℝ × ℝ → ℝ} {ε : ℝ} {W W' : Fam} {τ τ' : ℝ}
    (h : slice W τ = slice W' τ') :
    slice (JfamP ρ ε W) τ = slice (JfamP ρ ε W') τ' := by
  simp only [slice_JfamP]
  rw [h]

/-- The junction form of `slice_JfamP_congr`: two families agreeing at a junction have the same
projected slice there. -/
theorem slice_JfamP_eq_of {ρ : ℝ × ℝ → ℝ} {ε : ℝ} {G H : Fam} {t : ℝ}
    (h : ∀ z θ, G z θ t = H z θ 0) :
    slice (JfamP ρ ε G) t = slice (JfamP ρ ε H) 0 :=
  slice_JfamP_congr (funext fun z => funext (h z))

/-! ## Slice-determination and junction compatibility of the projected right-hand side -/

/-- The projected profile right-hand side depends on a family only through its slice at the (same
or a different) fake time. -/
theorem epsWP_congr {α : ℝ} {ρ : ℝ × ℝ → ℝ} {ε : ℝ} {Φs : Fn} {E : Fn → Fn}
    {W W' : Fam} {τ τ' : ℝ} (h : slice W τ = slice W' τ') :
    epsWP α ρ ε Φs E W τ = epsWP α ρ ε Φs E W' τ' :=
  epsRHSu_congr (α := α) (ρ := ρ) (ε := ε) (Φs := Φs) (E := E)
    (W := JfamP ρ ε W) (W' := JfamP ρ ε W') (τ := τ) (τ' := τ') (slice_JfamP_congr h)

/-- The projected scheme's right-hand side depends on a family only through its slice. -/
theorem epsRHSP_congr {α : ℝ} {ρ : ℝ × ℝ → ℝ} {ε : ℝ} {Φs : Fn} {E : Fn → Fn}
    {W W' : Fam} {τ τ' : ℝ} (h : slice W τ = slice W' τ') :
    epsRHSP α ρ ε Φs E W τ = epsRHSP α ρ ε Φs E W' τ' := by
  simp only [epsRHSP]
  rw [epsWP_congr (Φs := Φs) (E := E) h]

/-- The projected scheme's right-hand side at a junction: if two families agree at a junction
(`G (·,·,t) = H (·,·,0)`) then the right-hand sides of the *projected scheme* acting on them agree.

This is the `P₀`-analogue of `GlueParts/Basic.epsRHSu_junction` for the **raw** families: the
scheme `IsEpsSolP`'s right-hand side is `epsRHSP … g τ` (the projection is applied *inside*
`epsRHSP`, at the argument of `epsRHSu`), so it is the raw families that must be compared. -/
theorem epsRHSP_junction {α : ℝ} {ρ : ℝ × ℝ → ℝ} {ε : ℝ} {Φs : Fn} {E : Fn → Fn}
    {G H : Fam} {t : ℝ} (h : ∀ z θ, G z θ t = H z θ 0) :
    epsRHSP α ρ ε Φs E G t = epsRHSP α ρ ε Φs E H 0 :=
  epsRHSP_congr (funext fun z => funext (h z))

/-- Variant of `epsRHSP_junction` at the *projected* mollified families (the form in which the
unprojected `epsRHSu_junction` is stated).  Kept for reuse; the consumers want the raw form. -/
theorem epsRHSP_junction_JfamP {α : ℝ} {ρ : ℝ × ℝ → ℝ} {ε : ℝ} {Φs : Fn} {E : Fn → Fn}
    {G H : Fam} {t : ℝ} (h : ∀ z θ, G z θ t = H z θ 0) :
    epsRHSP α ρ ε Φs E (JfamP ρ ε G) t = epsRHSP α ρ ε Φs E (JfamP ρ ε H) 0 :=
  epsRHSP_congr (slice_JfamP_eq_of h)

/-! ## Elementary consequences of the projected scheme -/

/-- A `P₀`-solution on `[0,T']` is one on every shorter interval `[0,T]`. -/
theorem IsEpsSolP.mono {α ε T T' : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Fn} {E : Fn → Fn} {g₀ : Fn}
    {g : Fam} (h : IsEpsSolP α ρ ε T' Φs E g₀ g) (hTT' : T ≤ T') :
    IsEpsSolP α ρ ε T Φs E g₀ g :=
  ⟨h.1, fun z θ τ hz hθ hτ =>
    (h.2 z θ τ hz hθ ⟨hτ.1, hτ.2.trans hTT'⟩).mono fun s hs => ⟨hs.1, hs.2.trans hTT'⟩⟩

/-- The fake-time zero slice of a `P₀`-solution is its datum. -/
theorem IsEpsSolP.slice_zero {α ε T : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Fn} {E : Fn → Fn} {g₀ : Fn}
    {g : Fam} (h : IsEpsSolP α ρ ε T Φs E g₀ g) : slice g 0 = g₀ :=
  funext fun z => funext fun θ => h.1 z θ

/-- The scheme's equation of a `P₀`-solution, with the right-hand side written through
`epsRHSP`. -/
theorem isEpsSolP_eq {α ε T : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Fn} {E : Fn → Fn} {g₀ : Fn} {g : Fam}
    (h : IsEpsSolP α ρ ε T Φs E g₀ g) :
    ∀ z θ τ, 0 < z → θ ∈ Set.Ioo 0 (π / 2) → τ ∈ Set.Icc 0 T →
      HasDerivWithinAt (fun s => g z θ s) (epsRHSP α ρ ε Φs E g τ z θ) (Set.Icc 0 T) τ :=
  fun z θ τ hz hθ hτ => h.2 z θ τ hz hθ hτ

/-! ## The slices of the projected mollified concatenation -/

/-- The projected slice of a concatenation before the junction. -/
theorem slice_JfamP_concat_of_le {ρ : ℝ × ℝ → ℝ} {ε : ℝ} {G H : Fam} {t τ : ℝ}
    (h : τ ≤ t) :
    slice (JfamP ρ ε (concat G (shiftFam H t) t)) τ = slice (JfamP ρ ε G) τ :=
  slice_JfamP_congr (Work.FTS.StrongGlobal.slice_concat_of_le h)

/-- The projected slice of a concatenation after the junction. -/
theorem slice_JfamP_concat_of_gt {ρ : ℝ × ℝ → ℝ} {ε : ℝ} {G H : Fam} {t τ : ℝ}
    (h : t < τ) :
    slice (JfamP ρ ε (concat G (shiftFam H t) t)) τ = slice (JfamP ρ ε H) (τ - t) :=
  slice_JfamP_congr (Work.FTS.StrongGlobal.slice_concat_of_gt h)

/-- `epsRHSP` sees the projected mollified concatenation as the left piece before the junction —
in the form the glue consumes: the scheme's right-hand side at the raw concatenation is the one at
the raw left piece. -/
theorem epsRHSP_concat_of_le {α ε : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Fn} {E : Fn → Fn}
    {G H : Fam} {t τ : ℝ} (h : τ ≤ t) :
    epsRHSP α ρ ε Φs E (concat G (shiftFam H t) t) τ = epsRHSP α ρ ε Φs E G τ :=
  epsRHSP_congr (Work.FTS.StrongGlobal.slice_concat_of_le h)

/-- `epsRHSP` sees the projected mollified concatenation as the (shifted) right piece after the
junction — in the form the glue consumes. -/
theorem epsRHSP_concat_of_gt {α ε : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Fn} {E : Fn → Fn}
    {G H : Fam} {t τ : ℝ} (h : t < τ) :
    epsRHSP α ρ ε Φs E (concat G (shiftFam H t) t) τ = epsRHSP α ρ ε Φs E H (τ - t) :=
  epsRHSP_congr (Work.FTS.StrongGlobal.slice_concat_of_gt h)

/-- The `JfamP`-prefixed variant of `epsRHSP_concat_of_le` (the form the unprojected
`epsRHSu_concat_of_le` takes). -/
theorem epsRHSP_concat_of_le_JfamP {α ε : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Fn} {E : Fn → Fn}
    {G H : Fam} {t τ : ℝ} (h : τ ≤ t) :
    epsRHSP α ρ ε Φs E (JfamP ρ ε (concat G (shiftFam H t) t)) τ
      = epsRHSP α ρ ε Φs E (JfamP ρ ε G) τ :=
  epsRHSP_congr (slice_JfamP_concat_of_le h)

/-- The `JfamP`-prefixed variant of `epsRHSP_concat_of_gt`. -/
theorem epsRHSP_concat_of_gt_JfamP {α ε : ℝ} {ρ : ℝ × ℝ → ℝ} {Φs : Fn} {E : Fn → Fn}
    {G H : Fam} {t τ : ℝ} (h : t < τ) :
    epsRHSP α ρ ε Φs E (JfamP ρ ε (concat G (shiftFam H t) t)) τ
      = epsRHSP α ρ ε Φs E (JfamP ρ ε H) (τ - t) :=
  epsRHSP_congr (slice_JfamP_concat_of_gt h)

end Work.FTS.StrongEps.StrongEpsP
