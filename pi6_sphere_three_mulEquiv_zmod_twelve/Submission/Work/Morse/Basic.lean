import Mathlib

set_option synthInstance.maxHeartbeats 400000

/-!
# Critical points of smooth functions on manifolds

For a smooth function `f : M → ℝ` on a smooth `n`-manifold `M` (charted over `ℝⁿ`) this file
defines

* `IsCritPoint f p` — the manifold derivative of `f` vanishes at `p`;
* `HasMorseThru f p` — the *strong* nondegeneracy condition provided by the Morse lemma: there is
  a chart at `p` in which `f - f p` is *exactly* a nondegenerate quadratic form.

`HasNondegHessian` is the same notion for an arbitrary model with corners (a chart in which the
second derivative is a nondegenerate bilinear form); `HasNondegHessian` implies `HasMorseThru` by
the Morse lemma (`Work.Morse.morse_lemma`), and `HasMorseThru f p → IsCritPoint f p`.

Note `HasMorseThru f p → IsCritPoint f p`, so the hypothesis "every critical point of `f` is
`HasMorseThru` and the only `HasMorseThru` points are `p` and `q`" says precisely that `f` is a
Morse function whose only critical points are `p` and `q`.
-/

open scoped Manifold ContDiff Topology

/-- `p` is a critical point of `f`: the manifold derivative of `f` vanishes at `p`. -/
def IsCritPoint {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (f : M → ℝ) (p : M) : Prop :=
  mfderiv (𝓡 n) 𝓘(ℝ, ℝ) f p = 0

/-- `p` is a nondegenerate critical point of `f`: in some chart at `p` centred at `0`,
`f x - f p` is exactly the quadratic form of a nondegenerate symmetric bilinear form `A`. -/
def HasMorseThru {n : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
    (f : M → ℝ) (p : M) : Prop :=
  ∃ e ∈ (contDiffGroupoid ∞ (𝓡 n)).maximalAtlas M,
    p ∈ e.source ∧ e p = 0 ∧
    ∃ A : EuclideanSpace ℝ (Fin n) →L[ℝ] EuclideanSpace ℝ (Fin n) →L[ℝ] ℝ,
      (∀ v, (∀ w, A v w = 0) → v = 0) ∧
      ∀ᶠ x in 𝓝 0, f (e.symm x) - f p = A x x

/-- `p` is a **nondegenerate** critical point of `f`, formulated for an arbitrary model with
corners: in some chart at `p` the derivative of `f` vanishes and the second derivative (computed in
the model space `E` via `I.symm`) is a nondegenerate bilinear form. -/
def HasNondegHessian {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {H : Type*}
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {n : ℕ∞ω}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I n M]
    (f : M → ℝ) (p : M) : Prop :=
  ∃ e ∈ (contDiffGroupoid n I).maximalAtlas M, p ∈ e.source ∧
    fderiv ℝ (fun x : E => f (e.symm (I.symm x))) (I (e p)) = 0 ∧
    ∀ v : E, (∀ w, (fderiv ℝ (fderiv ℝ (fun x : E => f (e.symm (I.symm x))))
      (I (e p))) v w = 0) → v = 0
