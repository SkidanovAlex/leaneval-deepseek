/-
# The Beurling transform for functions with values in a complex normed space

`beurlingV g` is the Beurling transform of `g : ℂ → E`, where `E` is a normed space over `ℂ`:
the same regularised singular integral as `Work.Beltrami.beurling`, with the complex scalars
acting on the values in `E`.

This is the form in which the commutation of the Beurling transform with the `∂`-operator (or
rather with the Fréchet derivative, i.e. `∂^j (B f) = B (∂^j f)`) can be iterated: at each step
the values of the `j`-th derivative live in the space `ℂ [×j]→L[ℝ] ℂ` of `j`-multilinear maps,
which is a normed space over `ℂ` (pointwise scalar multiplication in the codomain).
-/
import Mathlib
import Submission.Work.Beltrami.Cauchy
import Submission.Work.Beltrami.beurling_bounded

noncomputable section

namespace Work.Beltrami

open MeasureTheory

/-- The **Beurling transform** of a function `g : ℂ → E` with values in a complex normed space,
in the translated (convolution) form
`-(1/π) ∫ w, w⁻² • (g (z+w) - χ w • g z)`, where `χ = bumpC` is the standard cutoff. -/
def beurlingV {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (g : ℂ → E) (z : ℂ) : E :=
  (-(Real.pi)⁻¹ : ℝ) • ∫ w : ℂ, ((w ^ 2)⁻¹ : ℂ) • (g (z + w) - (bumpC w : ℂ) • g z)

/-- For scalar-valued functions `beurlingV` is the Beurling transform `beurling`. -/
theorem beurlingV_eq_beurling (g : ℂ → ℂ) (z : ℂ) : beurlingV g z = beurling g z := by
  rw [beurlingV, beurling_eq_translate]
  congr 1
  refine integral_congr_ae ?_
  filter_upwards with w
  simp only [smul_eq_mul]
  ring

/-- **The vector-valued Beurling transform commutes with complex linear continuous maps.**
For a continuous ℝ-linear `Θ : E →L[ℝ] F` which is complex linear and for which the regularised
kernel of `g` is integrable, `Θ ∘ (B g) = B (Θ ∘ g)`. -/
theorem map_beurlingV {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F] (Θ : E →L[ℝ] F)
    (hΘ : ∀ (c : ℂ) (x : E), Θ (c • x) = c • Θ x) (g : ℂ → E) (z : ℂ)
    (hint : Integrable
      (fun w : ℂ => ((w ^ 2)⁻¹ : ℂ) • (g (z + w) - (bumpC w : ℂ) • g z))) :
    Θ (beurlingV g z) = beurlingV (fun w => Θ (g w)) z := by
  have hK : ∀ w : ℂ, Θ (((w ^ 2)⁻¹ : ℂ) • (g (z + w) - (bumpC w : ℂ) • g z))
      = ((w ^ 2)⁻¹ : ℂ) • (Θ (g (z + w)) - (bumpC w : ℂ) • Θ (g z)) := by
    intro w
    rw [hΘ, map_sub, hΘ]
  simp only [beurlingV]
  rw [map_smul, ← ContinuousLinearMap.integral_comp_comm Θ hint]
  congr 1
  exact integral_congr_ae (Filter.Eventually.of_forall hK)


/-- A **uniform Schauder constant** for the Beurling transform: `IsSchauderBound α C` says that
`C > 0` and that for every function `f` bounded by `M`, globally `α`-Hölder with constant `K` and
supported in the ball of radius `R ≥ 0`, the Beurling transform `beurling f` is bounded by
`C (M + K) (1 + R)` and is globally `α`-Hölder with constant `C (M + K) (1 + R)`. -/
def IsSchauderBound (α C : ℝ) : Prop :=
  0 < C ∧ ∀ (M K R : ℝ) (f : ℂ → ℂ), 0 ≤ R → (∀ z : ℂ, ‖f z‖ ≤ M) →
    (∀ x y : ℂ, ‖f x - f y‖ ≤ K * ‖x - y‖ ^ α) → (∀ z : ℂ, R < ‖z‖ → f z = 0) →
    (∀ z : ℂ, ‖beurling f z‖ ≤ C * (M + K) * (1 + R)) ∧
    (∀ x y : ℂ, ‖beurling f x - beurling f y‖ ≤ C * (M + K) * (1 + R) * ‖x - y‖ ^ α)

end Work.Beltrami
