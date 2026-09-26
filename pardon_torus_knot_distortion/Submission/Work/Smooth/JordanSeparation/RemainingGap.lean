import Submission.Work.Smooth.JordanSeparation.SchoenfliesReduction
import Submission.Work.Smooth.JordanSeparation.discExtension_of_cylinder_chain

/-!
# The remaining gap of (E), as named propositions, and the last implication

`SCHOENFLIES.md` and `CUTTING.md` reduce the whole classical input of the plane to statement **(E)**
(`ExtensionInput`: every `C¹` simple closed plane curve extends to a continuous injection of the
disc).  This file names, *inside the tree*, the single missing construction and the interface lemma
that the exhaustion needs, and proves that the first of them is exactly one step away from (E):

* `ChainInput` — the cylinder chain of `discExtension_of_cylinder_chain` exists for every `C¹` simple
  closed curve (a chain of injective cylinders, disjoint shells, shrinking uniformly to a point);
* `PushIndexInput` — a push that never sweeps a point `x` does not change the index at `x` (the
  lemma that identifies the inside of a legal cut with the half-plane intersection);
* **`extensionInput_of_chainInput`** — `ChainInput` implies (E), by
  `ChainData.discExtension_of_chainData`;
* and hence `SchoenfliesInput`, `PlaneSchoenflies` and the `C¹` classical input follow from
  `ChainInput` by the already-proved transfer chain of `SchoenfliesReduction.lean`.

Nothing here is an axiom or a `sorry`: `ChainInput`/`PushIndexInput` are ordinary `Prop`-valued
definitions, and the implications *out of* them are theorems.  Thus
`Work.Smooth.JordanSeparation.ChainInput` is the exact remaining hypothesis of the chapter, with the
proved reduction `ChainInput → ExtensionInput → SchoenfliesInput → PlaneJordanSchoenflies`.
-/

open Set
open Work.Smooth.Jordan

namespace Work.Smooth.JordanSeparation

noncomputable section

/-- **The cylinder-chain construction** — the one missing piece of (E).  For every `C¹` `2π`-periodic
curve injective on one period there is a chain of injective cylinders `Φ k` glued consecutively,
with pairwise disjoint shells, shrinking uniformly to a point `p`
(exactly the data `ChainData`, consumed by `discExtension_of_cylinder_chain`). -/
def ChainInput : Prop :=
  ∀ (γ : ℝ → ℂ), Continuous γ → Function.Periodic γ (2 * Real.pi) → ContDiff ℝ 1 γ →
    Set.InjOn γ (Set.Ico 0 (2 * Real.pi)) →
    ∃ (Φ : ℕ → ℝ × ℝ → ℂ) (p : ℂ), ChainData γ Φ p

/-- **The index invariance under a push avoiding a point** — the interface lemma between the cutting
exhaustion (whose cut curves are only `C⁰` for the piecewise-linear profile) and the `C¹`
index/separation theory.  With `push_injective_iff_of_profile` one may cut with *smooth* profiles, so
this is the statement that the inside of a legal cut is the half-plane intersection of the regions. -/
def PushIndexInput : Prop :=
  ∀ (c c' : SmoothPlaneCurve) (ν : ℂ) (ψ : ℝ → ℝ) (x : ℂ),
    (∀ θ : ℝ, c'.γ θ = c.γ θ - ((ψ θ : ℝ) : ℂ) * ν) →
    (∀ θ s : ℝ, s ∈ Set.Icc (0:ℝ) 1 → c.γ θ - ((s * ψ θ : ℝ) : ℂ) * ν ≠ x) →
    ind c' x = ind c x

/-- **The last implication of (E).**  A cylinder chain for `γ` *is* an injective disc extension of
`γ`: this is `ChainData.discExtension_of_chainData`.  So `ChainInput` implies `ExtensionInput`, and
only the converse direction (the construction of the chain) is missing from the chapter. -/
theorem extensionInput_of_chainInput (h : ChainInput) : ExtensionInput := by
  intro c hs
  obtain ⟨Φ, p, hC⟩ := h c.γ c.cont c.periodic c.contDiff hs
  obtain ⟨F, hinj, hbd⟩ := hC.discExtension_of_chainData
  exact ⟨F, hinj, hbd⟩

/-- The sibling chapter's `SchoenfliesInput` at `C¹` curves, from the chain construction. -/
theorem schoenfliesInput_of_chainInput (h : ChainInput) (c : PlaneCurve)
    (hdiff : ContDiff ℝ 1 c.γ) : SchoenfliesInput c :=
  schoenfliesInput_of_contDiff (extensionInput_of_chainInput h) c hdiff

/-- `PlaneSchoenflies` at `C¹` curves, from the chain construction. -/
theorem planeSchoenflies_of_chainInput (h : ChainInput) (c : PlaneCurve)
    (hdiff : ContDiff ℝ 1 c.γ) (hs : c.IsSimple) : Nonempty (PlaneSchoenflies c) :=
  planeSchoenflies_of_contDiff_of_isSimple (extensionInput_of_chainInput h) c hdiff hs

/-- The `SmoothPlaneCurve` form of the same. -/
theorem nonempty_planeSchoenflies_of_chainInput (h : ChainInput) (c : SmoothPlaneCurve)
    (hs : c.toPlaneCurve.IsSimple) : Nonempty (PlaneSchoenflies c.toPlaneCurve) :=
  nonempty_planeSchoenflies_of_extension (extensionInput_of_chainInput h) c hs

end

end Work.Smooth.JordanSeparation
