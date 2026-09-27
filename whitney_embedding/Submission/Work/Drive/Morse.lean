import Mathlib

/-!
# Drive interfaces for the `n = 2` case: Morse functions (written by the project lead, 2026-09-23)

Surfaces only (model `ℝ²`). The compact `n = 2` case is attacked by Morse theory: a Morse function with distinct critical values,
its local normal form, products over regular intervals, and a handle-by-handle construction of the
embedding into `ℝ⁴`.  This file fixes the vocabulary.

* `IsCritical f x` : the differential of `f` at `x` vanishes;
* `NondegCrit f x` : critical, and the Hessian of the chart representative at the chart point is injective
  (as a linear map `E → (E →L[ℝ] ℝ)`), i.e. nondegenerate;
* `IsMorseDistinct f` : `f` is smooth, every critical point is nondegenerate, and distinct critical points have
  distinct values.
-/

namespace Work.Drive.Morse

open scoped Manifold ContDiff

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 2)) M]

/-- `x` is a critical point of `f`. -/
def IsCritical (f : M → ℝ) (x : M) : Prop :=
  mfderiv (𝓡 2) 𝓘(ℝ, ℝ) f x = 0

/-- `x` is a nondegenerate critical point of `f`: the Hessian of `f ∘ (extChartAt x).symm` at the chart point
is injective. -/
def NondegCrit (f : M → ℝ) (x : M) : Prop :=
  IsCritical f x ∧
    Function.Injective
      (fderiv ℝ (fderiv ℝ (f ∘ (extChartAt (𝓡 2) x).symm)) (extChartAt (𝓡 2) x x))

/-- A Morse function with distinct critical values. -/
def IsMorseDistinct (f : M → ℝ) : Prop :=
  ContMDiff (𝓡 2) 𝓘(ℝ, ℝ) ∞ f ∧
    (∀ x, IsCritical f x → NondegCrit f x) ∧
    (∀ x y, IsCritical f x → IsCritical f y → f x = f y → x = y)

/-- A smooth "level flow" over `[a, b]`: a smooth map `Φ : ℝ × M → M` with `Φ (0, x) = x` that raises `f` at unit
speed and composes like a flow while the values stay in `[a, b]`.  It is the flow of a vector field `X` with
`X f = 1` near `f⁻¹ [a, b]`, which exists when `f` has no critical point there and `M` is compact. -/
def HasLevelFlow (f : M → ℝ) (a b : ℝ) : Prop :=
  ∃ Φ : ℝ × M → M, ContMDiff (𝓘(ℝ, ℝ).prod (𝓡 2)) (𝓡 2) ∞ Φ ∧
    (∀ x, Φ (0, x) = x) ∧
    (∀ x t, f x ∈ Set.Icc a b → f x + t ∈ Set.Icc a b → f (Φ (t, x)) = f x + t) ∧
    (∀ x s t, f x ∈ Set.Icc a b → f x + t ∈ Set.Icc a b → f x + t + s ∈ Set.Icc a b →
      Φ (s, Φ (t, x)) = Φ (s + t, x))

end Work.Drive.Morse

namespace Work.Drive.Morse

/-- **The Morse lemma in the plane.**  A smooth `g : ℝ² → ℝ` with a nondegenerate critical point `x₀` is, in a
smooth local coordinate `φ` centred at `x₀`, equal to `g x₀ ± u² ± v²`. -/
def MorseLemma2 : Prop :=
  ∀ (g : EuclideanSpace ℝ (Fin 2) → ℝ) (x₀ : EuclideanSpace ℝ (Fin 2)),
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g → fderiv ℝ g x₀ = 0 →
    Function.Injective (fderiv ℝ (fderiv ℝ g) x₀) →
    ∃ (φ : OpenPartialHomeomorph (EuclideanSpace ℝ (Fin 2)) (EuclideanSpace ℝ (Fin 2)))
      (s₁ s₂ : ℝ),
      x₀ ∈ φ.source ∧ φ x₀ = 0 ∧
      ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ φ.source ∧
      ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) φ.symm φ.target ∧
      (s₁ = 1 ∨ s₁ = -1) ∧ (s₂ = 1 ∨ s₂ = -1) ∧
      ∀ y ∈ φ.source, g y = g x₀ + s₁ * (φ y 0) ^ 2 + s₂ * (φ y 1) ^ 2

end Work.Drive.Morse
