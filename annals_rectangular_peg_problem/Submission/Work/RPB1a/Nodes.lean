import Mathlib
import Submission.Work.RPV.Defs
import Submission.Work.RPB1a.Defs
import Submission.Work.RPB1a.Geometry

/-!
# RPB1a: the node statements of the analytic route, as `Prop`s

The conformal-map route (`RECTPEG_B1_LEAD.md`) has six library-facing nodes, `N4`, `N4b`, `N5`,
`N6`, `N7`, `N8`.  Their proofs are **held** (the sibling subproject's `IMPORT_BLOCKER.md` shows that
the TauCeti library the design wanted for them is not importable in this fixed workspace), but their
*statements* cost nothing and are the interface the assembly `N10` is written against.  This file
curries them into named `Prop`s, one per node, in exactly the argument order of the design's
statements.  The two places the design wrote `TauCeti.IsJordanCurve` (`N4`'s conclusion and `N6`'s
hypothesis) use `Work.RPB1a.IsJordanCurveSet`, which is *definitionally* the same predicate
(`Nonempty (· ≃ₜ Circle)`, see `Geometry.lean`).

The assembly `Work.RPB1a.exists_curveIsotopy_of_nodes` (`Assembly.lean`) takes these six `Prop`s as
explicit hypotheses, so it is complete; the held node files (`Held.lean`) are the placeholder
instantiations that will be replaced one by one.
-/

set_option autoImplicit false

open Complex Set Metric
open scoped ContDiff Real

noncomputable section

namespace Work.RPB1a

/-- **N4** (`jordan_domain_of_loop`): a smooth loop bounds a Jordan domain `D` with
`frontier D = range v`, `Dᶜ` connected, and `range v` homeomorphic to the circle. -/
def JordanDomainNode : Prop :=
  ∀ v : ℝ → ℂ, IsSmoothLoop v →
    ∃ D : Set ℂ, IsOpen D ∧ IsConnected D ∧ Bornology.IsBounded D ∧ Disjoint D (range v) ∧
      frontier D = range v ∧ range v ⊆ closure (D ∪ range v)ᶜ ∧ IsConnected Dᶜ ∧
      IsJordanCurveSet (frontier D)

/-- **N4b** (`collar_side`): for a collar `Γ` of the boundary `range v` of `D`, exactly one of the
inner/outer halves of the collar lies in `D`. -/
def CollarSideNode : Prop :=
  ∀ (v : ℝ → ℂ) (D : Set ℂ), IsOpen D → frontier D = range v → Disjoint D (range v) →
    range v ⊆ closure (D ∪ range v)ᶜ →
    ∀ (Γ : ℂ → ℂ) (ρ : ℝ), 0 < ρ → ρ < 1 → ContinuousOn Γ (annulus ρ) → InjOn Γ (annulus ρ) →
      IsOpen (Γ '' annulus ρ) → (∀ t : ℝ, Γ (Complex.exp (t * I)) = v t) →
      (Γ '' (annulus ρ ∩ ball 0 1) ⊆ D ∧
          Disjoint (Γ '' (annulus ρ \ closedBall 0 1)) D) ∨
        (Γ '' (annulus ρ \ closedBall 0 1) ⊆ D ∧
          Disjoint (Γ '' (annulus ρ ∩ ball 0 1)) D)

/-- **N5** (`hasPrimitives_of_isConnected_compl`): on a bounded domain whose complement is
connected, every holomorphic function has a primitive. -/
def PrimitivesNode : Prop :=
  ∀ U : Set ℂ, IsOpen U → IsConnected U → Bornology.IsBounded U → IsConnected Uᶜ →
    ∀ f : ℂ → ℂ, DifferentiableOn ℂ f U →
      ∃ g : ℂ → ℂ, DifferentiableOn ℂ g U ∧ EqOn (deriv g) f U

/-- **N6** (`riemannMap_closedDisc`): the Riemann map of a Jordan domain, normalised so that its
derivative at `0` is a positive real. -/
def RiemannMapNode : Prop :=
  ∀ D : Set ℂ, IsOpen D → IsConnected D → Bornology.IsBounded D → IsJordanCurveSet (frontier D) →
    (∀ f : ℂ → ℂ, DifferentiableOn ℂ f D →
      ∃ g : ℂ → ℂ, DifferentiableOn ℂ g D ∧ EqOn (deriv g) f D) →
    ∃ Φ : ℂ → ℂ, ContinuousOn Φ (closedBall 0 1) ∧ DifferentiableOn ℂ Φ (ball 0 1) ∧
      InjOn Φ (closedBall 0 1) ∧ Φ '' ball 0 1 = D ∧ MapsTo Φ (sphere 0 1) (frontier D) ∧
      ∃ a : ℝ, 0 < a ∧ deriv Φ 0 = a

/-- **N7** (`analytic_extension_of_collar`): the Riemann map continues across the collar by
Schwarz reflection, to a locally biholomorphic `F` on a disc `|z| < R`, `R > 1`, whose boundary
values on `|z| = 1` are `v ∘ σ` for a smooth reparametrisation `σ`. -/
def ReflectionNode : Prop :=
  ∀ (v : ℝ → ℂ), IsSmoothLoop v → ∀ (D : Set ℂ), IsOpen D → frontier D = range v →
    Disjoint D (range v) →
    ∀ (Γ : ℂ → ℂ) (ρ : ℝ), 0 < ρ → ρ < 1 → DifferentiableOn ℂ Γ (annulus ρ) →
      InjOn Γ (annulus ρ) → (∀ w ∈ annulus ρ, deriv Γ w ≠ 0) →
      (∀ t : ℝ, Γ (Complex.exp (t * I)) = v t) →
      Γ '' (annulus ρ ∩ ball 0 1) ⊆ D → Disjoint (Γ '' (annulus ρ \ closedBall 0 1)) D →
      ∀ Φ : ℂ → ℂ, ContinuousOn Φ (closedBall 0 1) → DifferentiableOn ℂ Φ (ball 0 1) →
        InjOn Φ (closedBall 0 1) → Φ '' ball 0 1 = D → MapsTo Φ (sphere 0 1) (range v) →
        ∃ R : ℝ, 1 < R ∧ ∃ F : ℂ → ℂ, DifferentiableOn ℂ F (ball 0 R) ∧ InjOn F (ball 0 R) ∧
          (∀ z ∈ ball 0 R, deriv F z ≠ 0) ∧ EqOn F Φ (closedBall 0 1) ∧
          ∃ σ : ℝ → ℝ, ContDiff ℝ ∞ σ ∧ ∀ t : ℝ, F (Complex.exp (t * I)) = v (σ t)

/-- **N8** (`discLoopFamily`): the level circles of a locally biholomorphic map of a disc, from the
unit circle to `(F (e^{it}) - F 0)/a`, form a loop family. -/
def LevelCirclesNode : Prop :=
  ∀ (F : ℂ → ℂ) (R : ℝ), 1 < R → DifferentiableOn ℂ F (ball 0 R) → InjOn F (ball 0 R) →
    (∀ z ∈ ball 0 R, deriv F z ≠ 0) → ∀ a : ℝ, 0 < a → deriv F 0 = a →
    ∃ c : ℝ → ℝ → ℂ, IsLoopFamily c ∧ (∀ t : ℝ, c 0 t = Complex.exp (t * I)) ∧
      ∀ t : ℝ, c 1 t = (F (Complex.exp (t * I)) - F 0) / a

end Work.RPB1a

end
