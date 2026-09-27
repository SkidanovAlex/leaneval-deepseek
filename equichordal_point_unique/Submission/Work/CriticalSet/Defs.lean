import Submission.Work.Potential.Defs

/-!
# Regular level sets of a harmonic function: definitions

A *replacement for Sard's lemma* for harmonic functions on a Riemann surface.  The critical points
of a nonconstant harmonic function `u : X → ℝ` are isolated (its local holomorphic companion has an
analytic derivative with isolated zeros), so its critical values are countable and regular values
are plentiful.  This is all the uniformization argument needs; no Sard theorem is involved.

This module fixes the vocabulary.

## Main definitions

* `Work.CriticalSet.IsCriticalPointAt u x` — `u` has vanishing gradient at `x`.  Measured in the
  preferred chart at `x` by `fderiv ℝ (u ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x) = 0`; the notion is
  independent of the chart (`Work.CriticalSet.isCriticalPointAt_iff_chartAt`).
* `Work.CriticalSet.criticalSet u U` — the critical points of `u` lying in `U`.
* `Work.CriticalSet.IsRegularPointAt u U x` — `x ∈ U` is not a critical point of `u`.
* `Work.CriticalSet.IsRegularValueOn u U c` — no point of `U` with `u = c` is critical.
* `Work.CriticalSet.NotLocallyConstantOn u U` — `u` is not eventually constant near any point of
  `U`; equivalently `u` is nonconstant on every connected component of `U`.
* `Work.CriticalSet.IsLocalLevelGraphAt u x` — the level set of `u` through `x` is, in the preferred
  chart at `x` and after a real-linear change of coordinates, locally the graph of a `C¹` function of
  one real variable.
* `Work.CriticalSet.LevelSetIsLocallyGraphOn u U c` — every point of the level set `{u = c}` inside
  `U` has such a neighbourhood.
* `Work.CriticalSet.IsLocallyFiniteIn S U` / `Work.CriticalSet.IsDiscreteIn S U` — every point of
  `U` has a neighbourhood meeting `S` in a finite set, respectively at most in the point itself.

The conventions: the preferred chart at `x` is Mathlib's `chartAt ℂ x` of the `ChartedSpace ℂ X`
structure; derivatives of chart pullbacks are taken with respect to `ℝ` (`fderiv ℝ`) unless the
function is complex valued, in which case `deriv` is the complex derivative.
-/

open LeanEval.Geometry
open scoped Manifold ContDiff Topology

noncomputable section

open Filter Set
open Classical

namespace Work.CriticalSet

variable {X : Type*} [TopologicalSpace X] [ChartedSpace ℂ X]

/-- `x` is a critical point of `u : X → ℝ`: the derivative of the chart pullback of `u` at `x`
vanishes there.  The chart used is the preferred chart at `x`; chart independence is
`Work.CriticalSet.isCriticalPointAt_iff_chartAt`.

For a harmonic `u` the pullback is smooth, so this is the genuine vanishing of the gradient of `u`
at `x`.  (For a non-differentiable `u` the derivative is junk `0`, which is why the notion is only
used under differentiability hypotheses.) -/
def IsCriticalPointAt (u : X → ℝ) (x : X) : Prop :=
  fderiv ℝ (u ∘ (chartAt ℂ x).symm) ((chartAt ℂ x) x) = 0

/-- The set of critical points of `u` lying in `U`. -/
def criticalSet (u : X → ℝ) (U : Set X) : Set X := {x | x ∈ U ∧ IsCriticalPointAt u x}

@[simp]
theorem mem_criticalSet {u : X → ℝ} {U : Set X} {x : X} :
    x ∈ criticalSet u U ↔ x ∈ U ∧ IsCriticalPointAt u x := Iff.rfl

/-- `x ∈ U` is a regular point of `u` if `u` is not critical at `x`. -/
def IsRegularPointAt (u : X → ℝ) (U : Set X) (x : X) : Prop := x ∈ U ∧ ¬ IsCriticalPointAt u x

/-- `c` is a regular value of `u` on `U`: no point of `U` at which `u = c` is a critical point. -/
def IsRegularValueOn (u : X → ℝ) (U : Set X) (c : ℝ) : Prop :=
  ∀ x, x ∈ U → u x = c → ¬ IsCriticalPointAt u x

theorem IsRegularValueOn.not_critical {u : X → ℝ} {U : Set X} {c : ℝ}
    (h : IsRegularValueOn u U c) {x : X} (hx : x ∈ U) (hxc : u x = c) :
    ¬ IsCriticalPointAt u x := h x hx hxc

/-- `u` is nowhere locally constant on `U`: no point of `U` has a neighbourhood on which `u` is
constant.  For harmonic `u` on an open `U` this is equivalent to `u` being nonconstant on every
connected component of `U`. -/
def NotLocallyConstantOn (u : X → ℝ) (U : Set X) : Prop :=
  ∀ x ∈ U, ¬ ∀ᶠ y in 𝓝 x, u y = u x

theorem notLocallyConstantOn_iff {u : X → ℝ} {U : Set X} :
    NotLocallyConstantOn u U ↔ ∀ x ∈ U, ¬ ∀ᶠ y in 𝓝 x, u y = u x := Iff.rfl

/-- The punctured surface `X ∖ {z₀}`, the domain on which a Green function is harmonic. -/
def punctured (z₀ : X) : Set X := univ \ {z₀}

@[simp]
theorem mem_punctured {z₀ x : X} : x ∈ punctured z₀ ↔ x ≠ z₀ := by
  simp [punctured]

theorem isOpen_punctured [T1Space X] (z₀ : X) : IsOpen (punctured z₀) := by
  have h : punctured z₀ = {z₀}ᶜ := by ext x; simp [punctured]
  rw [h]; exact isOpen_compl_singleton

/-- `S` is locally finite in `U`: every point of `U` has a neighbourhood meeting `S` in a finite
set. -/
def IsLocallyFiniteIn (S U : Set X) : Prop := ∀ x ∈ U, ∃ V ∈ 𝓝 x, (S ∩ V).Finite

/-- `S` is discrete in `U`: every point of `U` has a neighbourhood meeting `S` at most in the point
itself. -/
def IsDiscreteIn (S U : Set X) : Prop := ∀ x ∈ U, ∃ V ∈ 𝓝 x, S ∩ V ⊆ {x}

theorem IsDiscreteIn.isLocallyFiniteIn {S U : Set X} (h : IsDiscreteIn S U) :
    IsLocallyFiniteIn S U := fun x hx => by
  obtain ⟨V, hV, hVsub⟩ := h x hx
  exact ⟨V, hV, (Set.finite_singleton x).subset hVsub⟩

/-- The level set of `u` through `x₀` is locally the graph of a `C¹` function of one real variable:
there is a real-linear isomorphism `e : ℂ ≃L[ℝ] ℝ × ℝ` such that, near `x₀`, a point `y` of the
preferred chart at `x₀` satisfies `u y = u x₀` exactly when the second coordinate of
`e ((chartAt ℂ x₀) y - (chartAt ℂ x₀) x₀)` is the value at the first coordinate of a `C¹` function
`g` with `g 0 = 0`.  In other words: in suitable real coordinates centred at `x₀`, the level set is
the graph of a `C¹` function of one variable. -/
def IsLocalLevelGraphAt (u : X → ℝ) (x₀ : X) : Prop :=
  ∃ (e : ℂ ≃L[ℝ] ℝ × ℝ) (ρ : ℝ) (g : ℝ → ℝ),
    0 < ρ ∧ ContDiffAt ℝ 1 g 0 ∧ g 0 = 0 ∧
      ∀ y ∈ (chartAt ℂ x₀).source,
        e ((chartAt ℂ x₀) y - (chartAt ℂ x₀) x₀) ∈ Metric.ball 0 ρ →
          (u y = u x₀ ↔ (e ((chartAt ℂ x₀) y - (chartAt ℂ x₀) x₀)).2
                          = g ((e ((chartAt ℂ x₀) y - (chartAt ℂ x₀) x₀)).1))

/-- Every point of the level set `{u = c}` lying in `U` has a neighbourhood on which the level set
is a `C¹` graph, in the sense of `Work.CriticalSet.IsLocalLevelGraphAt`. -/
def LevelSetIsLocallyGraphOn (u : X → ℝ) (U : Set X) (c : ℝ) : Prop :=
  ∀ x, x ∈ U → u x = c → IsLocalLevelGraphAt u x

/-- **A regular level of the Green function `E`.**  `ε > 0` is a regular value of `E` on the
punctured surface, the level set `{E = ε}` is locally a `C¹` graph at each of its points, and the
superlevel set `{E ≥ ε}` is compact.  This is the shape needed to build an exhaustion of `X ∖ {z₀}`
by compact sub-surfaces with smooth (`C¹`) boundary. -/
def IsRegularLevel (E : X → ℝ) (z₀ : X) (ε : ℝ) : Prop :=
  0 < ε ∧ IsRegularValueOn E (punctured z₀) ε ∧ LevelSetIsLocallyGraphOn E (punctured z₀) ε ∧
    IsCompact {x : X | ε ≤ E x}

end Work.CriticalSet
