import Mathlib

open scoped Matrix
open InnerProductGeometry

/-!
# The cross product of two `C^n` functions into `EuclideanSpace ℝ (Fin 3)` is `C^n`

The cross product `⨯₃ : (Fin 3 → ℝ) × (Fin 3 → ℝ) → Fin 3 → ℝ` is
coordinatewise a polynomial (hence bilinear and `C∞`), and
`EuclideanSpace ℝ (Fin 3)` is `WithLp 2 (Fin 3 → ℝ)`.  This result packages
that fact so that the unit normal `N = e₀ × e₁` of a smooth immersion is
smooth whenever the tangent frame `e₀, e₁` is smooth.  It is used by the
formalization of Schwartz, "The optimal paper Moebius band" (the bend
foliation layer).

Suggested proof route (the prover may choose any correct route):
1. show the coordinate maps `x ↦ (u x) i` (`i : Fin 3`) are `C^n`
   (compose with the coordinate projection, which is linear and continuous
   through `WithLp.ofLp`),
2. use `ContDiffOn` closure under ring operations / `contDiffOn_congr`, or
   compose with a single `C∞` "cross product" function on the ambient space.
-/

noncomputable section
namespace Commons.Analysis.Calculus.ContDiff

/-- The cross product of two `C^n` maps into `EuclideanSpace ℝ (Fin 3)` is
`C^n`. -/
theorem crossProduct {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {s : Set E} {n : WithTop ℕ∞} {u v : E → EuclideanSpace ℝ (Fin 3)}
    (hu : ContDiffOn ℝ n u s) (hv : ContDiffOn ℝ n v s) :
    ContDiffOn ℝ n
      (fun x : E => WithLp.toLp 2 (WithLp.ofLp (u x) ⨯₃ WithLp.ofLp (v x))) s := by
  -- The coordinate functions of `u` and `v` (regarded as `Fin 3 → ℝ` via
  -- `WithLp.ofLp`) are `C^n`, by composing the smooth coordinate projection
  -- with the given `C^n` maps.
  have huc : ∀ i : Fin 3, ContDiffOn ℝ n (fun x : E => WithLp.ofLp (u x) i) s := by
    intro i
    fun_prop
  have hvc : ∀ i : Fin 3, ContDiffOn ℝ n (fun x : E => WithLp.ofLp (v x) i) s := by
    intro i
    fun_prop
  -- The cross product, as a function into the plain function space `Fin 3 → ℝ`,
  -- is `C^n`: coordinatewise it is a polynomial (difference of products) in the
  -- `C^n` coordinates above.
  have hcross : ContDiffOn ℝ n
      (fun x : E => WithLp.ofLp (u x) ⨯₃ WithLp.ofLp (v x)) s := by
    rw [contDiffOn_pi]
    intro i
    fin_cases i
    · simpa [cross_apply] using
        ContDiffOn.sub (ContDiffOn.mul (huc 1) (hvc 2)) (ContDiffOn.mul (huc 2) (hvc 1))
    · simpa [cross_apply] using
        ContDiffOn.sub (ContDiffOn.mul (huc 2) (hvc 0)) (ContDiffOn.mul (huc 0) (hvc 2))
    · simpa [cross_apply] using
        ContDiffOn.sub (ContDiffOn.mul (huc 0) (hvc 1)) (ContDiffOn.mul (huc 1) (hvc 0))
  -- Finally wrap the result back into `EuclideanSpace ℝ (Fin 3) = WithLp 2 _`
  -- through the smooth map `WithLp.toLp`.
  exact (PiLp.contDiff_toLp (p := 2) (𝕜 := ℝ) (E := fun _ : Fin 3 => ℝ)).comp_contDiffOn hcross

end Commons.Analysis.Calculus.ContDiff
