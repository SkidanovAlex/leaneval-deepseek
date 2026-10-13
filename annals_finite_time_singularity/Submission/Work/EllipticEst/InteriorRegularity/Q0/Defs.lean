/-
Interior regularity of the elliptic operator `bslOp α` of `Work.Elliptic` (Elgindi, Annals 194(3) 2021):
the vocabulary of the *transported* problem on `E2 = EuclideanSpace ℝ (Fin 2)` with coordinates
`s = (1/α) log z` (first coordinate) and `θ` (second coordinate).

For the weight `ω(z,θ) = z^((5-α)/α) cos θ` (the weight with respect to which `bslOp α` is
formally self-adjoint, see `Work.EllipticEst.InteriorRegularity.Q0`) and the unknown
`u := Ψ · ω`, the weak formulation

  `∫_{Q0} Ψ · (bslOp α φ) · ω = ∫_{Q0} F · φ · ω`

is, under the change of variables `z = exp (α s)` (Jacobian `α exp (α s)`), the statement

  `∫ V · Kop ψ = ∫ G · ψ`   on the strip `{0 < θ < π/2}`,

with `V (s,θ) = α exp (5s) cos θ · Ψ (exp (α s), θ)`, `G` the analogue for `F`, and
`Kop ψ = -∂_ss ψ - ∂_θθ ψ - 5 ∂_s ψ + tan θ · ∂_θ ψ + (tan²θ - 5) ψ` (`Strip.Kop`).

This module fixes that vocabulary.  The conventions of `Strip` are used (`E2`, `e0`, `e1`,
`stripE`, `Kop`, `coords`, `d0`, `d1`).
-/
import Mathlib.Analysis.Distribution.TemperedDistribution
import Submission.Work.EllipticEst.InteriorRegularity.Strip
import Submission.Work.Elliptic.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

set_option linter.unusedVariables false

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.EllipticEst.InteriorRegularity.Q0

/-- The transported weight `α exp (5 s) cos θ` (this is `α z · z^((5-α)/α) cos θ` with
`z = exp (α s)`, i.e. the Jacobian `α exp (α s)` times the weight `z^((5-α)/α) cos θ`). -/
def wt (α : ℝ) : E2 → ℝ := fun x => α * Real.exp (5 * x 0) * Real.cos (x 1)

/-- The transported unknown `V = wt α · Ψ ∘ chart`, zero off the strip. -/
def Vf (α : ℝ) (Ψ : ℝ → ℝ → ℝ) : E2 → ℝ :=
  stripE.indicator (fun x => wt α x * Ψ (Real.exp (α * x 0)) (x 1))

/-- The transported source `G = wt α · F ∘ chart`, zero off the strip. -/
def Gf (α : ℝ) (F : ℝ → ℝ → ℝ) : E2 → ℝ :=
  stripE.indicator (fun x => wt α x * F (Real.exp (α * x 0)) (x 1))

/-- **The weak identity on the strip**, complex form: for every smooth compactly supported test
function with topological support in the strip, `∫ V · Kop ψ = ∫ G · ψ`. -/
def StripWeakC (V G : E2 → ℂ) : Prop :=
  ∀ ψ : E2 → ℂ, (∀ n : ℕ, ContDiff ℝ n ψ) → HasCompactSupport ψ →
    tsupport ψ ⊆ stripE →
    ∫ x, V x * Kop ψ x = ∫ x, G x * ψ x

/-- **The weak identity on the strip**, for the transported pair `(V, G)` of real-valued
functions. -/
def StripWeakQ0 (α : ℝ) (V G : E2 → ℝ) : Prop :=
  StripWeakC (fun x => (V x : ℂ)) (fun x => (G x : ℂ))

/-- The pointwise ("uncurried") second-order operator `∂_00 + ∂_11` of a function on `E2`
(the Laplacian of `E2`, as a function-level operator). -/
def lapF (g : E2 → ℂ) : E2 → ℂ := fun x => d0 (d0 g) x + d1 (d1 g) x

/-- The transport of the quadrant `Q0 = (0,∞) × (0,π/2)` to `E2` (the `(z,θ)`-coordinates). -/
def QE : Set E2 := {x : E2 | 0 < x 0 ∧ 0 < x 1 ∧ x 1 < Real.pi / 2}

theorem mem_QE {x : E2} : x ∈ QE ↔ 0 < x 0 ∧ 0 < x 1 ∧ x 1 < Real.pi / 2 := Iff.rfl

/-- The transported weight as an explicit function of the strip coordinates. -/
theorem wt_apply (α : ℝ) (x : E2) :
    wt α x = α * Real.exp (5 * x 0) * Real.cos (x 1) := rfl

theorem wt_contDiff (α : ℝ) : ∀ n : ℕ, ContDiff ℝ n (wt α) := by
  intro n
  unfold wt
  fun_prop

theorem wt_continuous (α : ℝ) : Continuous (wt α) := (wt_contDiff α 0).continuous

/-- The weight is positive on the strip. -/
theorem wt_pos {α : ℝ} (hα : 0 < α) {x : E2} (hx : x ∈ stripE) : 0 < wt α x := by
  rw [wt_apply]
  have h1 : 0 < Real.exp (5 * x 0) := Real.exp_pos _
  have h2 : 0 < Real.cos (x 1) := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos, hx.1], hx.2⟩
  positivity

/-- The weight is nonzero on the strip. -/
theorem wt_ne_zero {α : ℝ} (hα : 0 < α) {x : E2} (hx : x ∈ stripE) : wt α x ≠ 0 :=
  ne_of_gt (wt_pos hα hx)

/-! ## Pairing predicates for the localized equation

The Sobolev tower works with the distributions `A = χ · U` (the localized unknown) and needs to
know that they pair against Schwartz functions as integrals of `χ · V`.  The two predicates
below record exactly that; they decouple the `L¹`/local-integrability bookkeeping (proved once,
from `U = distr (ρ · V)`) from the algebra of the localized equation. -/

/-- `Pair V χ A` says that the tempered distribution `A` pairs with Schwartz functions as the
integral of `ψ · (χ · V)`. -/
def Pair (V : E2 → ℂ) (χ : E2 → ℂ) (A : TemperedDistribution E2 ℂ) : Prop :=
  ∀ ψ : SchwartzMap E2 ℂ, A ψ = ∫ x, ψ x • (χ x * V x)

/-- **The localized integral identity** (the pairing form of the localized equation): this is
the identity proved by `Q0.localEq` from the weak formulation, transported to the level of the
concrete cut-offs.  It is stated separately so that the distributional algebra
(`Q0.distEq`) does not have to depend on the weak formulation. -/
def LocalId (V G : E2 → ℂ) (χ χ' σc tt : E2 → ℂ) : Prop :=
  ∀ φ : E2 → ℂ, (∀ n : ℕ, ContDiff ℝ n φ) → HasCompactSupport φ →
    (∫ x, (χ x * (d0 (d0 φ) x + d1 (d1 φ) x)) * V x)
      = - (∫ x, (χ x * d0 (fun y => (5 * σc y) * φ y) x) * V x)
        + (∫ x, (χ x * d1 (fun y => (σc y * tt y) * φ y) x) * V x)
        - (∫ x, (χ x * (6 * σc x) * φ x) * V x)
        + (∫ x,
            (χ' x * (((d0 (d0 χ) x + d1 (d1 χ) x) - 5 * d0 χ x + tt x * d1 χ x) * φ x)) * V x)
        - (∫ x, (χ' x * d0 (fun y => (2 * d0 χ y) * φ y) x) * V x)
        - (∫ x, (χ' x * d1 (fun y => (2 * d1 χ y) * φ y) x) * V x)
        - (∫ x, (χ x * φ x) * G x)

end Work.EllipticEst.InteriorRegularity.Q0
