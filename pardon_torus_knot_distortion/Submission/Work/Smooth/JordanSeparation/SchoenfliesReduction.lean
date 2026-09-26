import Submission.Work.Smooth.JordanSeparation.planeSchoenflies_of_injective_extension
import Submission.Work.Smooth.JordanSeparation.Unconditional

/-!
# The Jordan–Schoenflies theorem reduces to the extension of an embedding of the circle

This file records the equivalence proved in `planeSchoenflies_of_injective_extension.lean` in the
packaged form in which the chapter is consumed:

> **the planar Jordan–Schoenflies theorem** (a simple closed plane curve spans an embedded disc
> whose image is the closure of its bounded side) **is equivalent to**
> **(E) every embedding `S¹ → ℂ` extends to a continuous injection `𝔻 → ℂ`.**

The forward direction is trivial (`e` itself is the extension).  The converse is
`planeSchoenflies_of_injective_extension`: from the index theory of the sibling chapter
(`|ind c z| = 1` on the bounded side) an injective extension `F` of `γ` automatically satisfies
`Set.range F = closure S.V` for the bounded side `S.V` of *any* separation `S` — no condition on the
image of `F` is needed beyond injectivity.

Consequently the whole of the planar classical input of the project
(`Work.Smooth.Jordan.ClassicalInput`, `Work.Smooth.SphereJordan.PlaneHypothesis`) is equivalent to
the single classical statement (E); see `SCHOENFLIES.md` §1.

## Main declarations

* `ExtensionInput` / `extensionInput` — (E) in the `SmoothPlaneCurve` form;
* `ContDiffExtensionInput` — (E) in the `PlaneCurve` + `ContDiff ℝ 1` form;
* `planeSchoenflies_of_contDiff_of_isSimple` — `PlaneSchoenflies` for a `C¹` `PlaneCurve`, from (E);
* `schoenfliesInput_of_extension`, `contDiffSchoenfliesInput_of_extension` — the sibling chapter's
  `SchoenfliesInput` shape;
* `planeJordanSchoenflies_of_extension` — the sibling chapter's **full** classical input
  `PlaneJordanSchoenflies`, from (E);
* `classicalInput_of_extension` — `Work.Smooth.Jordan.ClassicalInput` at `C¹` curves, from (E);
* `extension_of_planeSchoenflies` / `planeSchoenflies_iff_extension` — the converse, i.e. the
  *equivalence* of `PlaneSchoenflies` with (E).
-/

open Set
open Work.Smooth.Jordan

namespace Work.Smooth.JordanSeparation

noncomputable section

/-! ## The extension form of the theorem -/

/-- **(E), for `C¹` plane curves**: every `C¹` simple closed plane curve is the boundary circle of
an injective continuous map of the disc.  This is the Jordan–Schoenflies extension statement, in the
form in which it is the exact remaining input of this chapter. -/
def ExtensionInput : Prop :=
  ∀ c : SmoothPlaneCurve, c.toPlaneCurve.IsSimple →
    ∃ F : C(Disc, ℂ), Function.Injective F ∧ ∀ θ : ℝ, F (circlePoint θ) = c.γ θ

/-- **(E) for a bare `C¹` `PlaneCurve`** (no `SmoothPlaneCurve` wrapper). -/
def ContDiffExtensionInput : Prop :=
  ∀ c : PlaneCurve, ContDiff ℝ 1 c.γ → c.IsSimple →
    ∃ F : C(Disc, ℂ), Function.Injective F ∧ ∀ θ : ℝ, F (circlePoint θ) = c.γ θ

theorem contDiffExtensionInput_of_extension (h : ExtensionInput) : ContDiffExtensionInput :=
  fun c hdiff hs => h ⟨c, hdiff⟩ hs

theorem extension_of_contDiffExtensionInput (h : ContDiffExtensionInput) : ExtensionInput :=
  fun c hs => h c.toPlaneCurve c.contDiff hs

/-- The two forms of (E) are the same statement. -/
theorem extensionInput_iff_contDiff : ExtensionInput ↔ ContDiffExtensionInput :=
  ⟨contDiffExtensionInput_of_extension, extension_of_contDiffExtensionInput⟩

/-! ## Schoenflies from the extension -/

/-- **Jordan–Schoenflies for a `C¹` plane curve, from (E).** -/
theorem planeSchoenflies_of_contDiff_of_isSimple (h : ExtensionInput) (c : PlaneCurve)
    (hdiff : ContDiff ℝ 1 c.γ) (hs : c.IsSimple) : Nonempty (PlaneSchoenflies c) := by
  obtain ⟨F, hinj, hbd⟩ := h ⟨c, hdiff⟩ hs
  have hsep : Nonempty (PlaneSeparation c) :=
    planeSeparation_of_contDiff_of_isSimple c hdiff hs
  obtain ⟨S⟩ := hsep
  exact planeSchoenflies_of_injective_extension ⟨c, hdiff⟩ hs S F hinj hbd

/-- **`SchoenfliesInput` for a `C¹` curve, from (E)**: the sibling chapter's
`Work.Smooth.Jordan.SchoenfliesInput c`. -/
theorem schoenfliesInput_of_contDiff (h : ExtensionInput) (c : PlaneCurve)
    (hdiff : ContDiff ℝ 1 c.γ) : SchoenfliesInput c :=
  fun hs => planeSchoenflies_of_contDiff_of_isSimple h c hdiff hs

/-- **`SchoenfliesInput` for a smooth curve, from (E)** (the `SmoothPlaneCurve` form). -/
theorem nonempty_planeSchoenflies_of_extension (h : ExtensionInput) (c : SmoothPlaneCurve)
    (hs : c.toPlaneCurve.IsSimple) : Nonempty (PlaneSchoenflies c.toPlaneCurve) :=
  planeSchoenflies_of_contDiff_of_isSimple h c.toPlaneCurve c.contDiff hs

/-- **The full classical input of the sibling chapter at a `C¹` curve, from (E)**:
`Work.Smooth.Jordan.PlaneJordanSchoenflies c`. -/
def planeJordanSchoenflies_of_extension (h : ExtensionInput) (c : SmoothPlaneCurve)
    (hs : c.toPlaneCurve.IsSimple) : PlaneJordanSchoenflies c :=
  planeJordanSchoenflies_of_planeSchoenflies c hs (nonempty_planeSchoenflies_of_extension h c hs).some

/-- **`Work.Smooth.Jordan.ClassicalInput` for `C¹` curves, from (E).** -/
def ContDiffClassicalInput : Prop :=
  ∀ c : PlaneCurve, ContDiff ℝ 1 c.γ → c.IsSimple → Nonempty (PlaneSchoenflies c)

/-- **(E) implies the classical input at `C¹` curves.** -/
theorem contDiffClassicalInput_of_extension (h : ExtensionInput) : ContDiffClassicalInput :=
  fun c hdiff => schoenfliesInput_of_contDiff h c hdiff

/-- **The class of curves covered, in the `PlaneCurve` form** (the Schoenflies version of
`ContDiffSimpleInput`). -/
def ContDiffSchoenfliesInput : Prop := ContDiffClassicalInput

/-- (E) implies the packaged Schoenflies input. -/
theorem contDiffSchoenfliesInput_of_extension (h : ExtensionInput) : ContDiffSchoenfliesInput :=
  contDiffClassicalInput_of_extension h

/-! ## The converse: Schoenflies gives the extension -/

/-- **`PlaneSchoenflies` gives an injective extension of the curve**: the spanning embedding itself.
-/
theorem exists_injective_extension_of_planeSchoenflies {c : PlaneCurve}
    (h : PlaneSchoenflies c) :
    ∃ F : C(Disc, ℂ), Function.Injective F ∧ ∀ θ : ℝ, F (circlePoint θ) = c.γ θ :=
  ⟨h.e, h.inj, h.boundary⟩

/-- **The equivalence**: for a `C¹` simple closed curve, `PlaneSchoenflies` holds on the nose if and
only if (E) holds for it.  The forward direction is the spanning embedding; the converse is the
index-theoretic computation `planeSchoenflies_of_injective_extension`. -/
theorem planeSchoenflies_iff_extension (c : SmoothPlaneCurve) (hs : c.toPlaneCurve.IsSimple)
    (S : PlaneSeparation c.toPlaneCurve) :
    (∃ F : C(Disc, ℂ), Function.Injective F ∧
        (∀ θ : ℝ, F (circlePoint θ) = c.γ θ) ∧ Set.range F = closure S.V) ↔
      (∃ F : C(Disc, ℂ), Function.Injective F ∧ ∀ θ : ℝ, F (circlePoint θ) = c.γ θ) := by
  constructor
  · rintro ⟨F, hinj, hbd, _⟩; exact ⟨F, hinj, hbd⟩
  · rintro ⟨F, hinj, hbd⟩
    exact ⟨F, hinj, hbd,
      range_eq_closure_V_of_injective_extension c hs S F hinj hbd⟩

/-- **The global equivalence of the two forms of the classical input**: (E) for all `C¹` curves is
equivalent to `PlaneSchoenflies` for all `C¹` curves. -/
theorem extensionInput_iff_contDiffSchoenfliesInput :
    ExtensionInput ↔ ContDiffSchoenfliesInput :=
  ⟨contDiffSchoenfliesInput_of_extension, fun h c hs => by
    obtain ⟨hS⟩ := h c.toPlaneCurve c.contDiff hs
    exact exists_injective_extension_of_planeSchoenflies hS⟩

end

end Work.Smooth.JordanSeparation
