import Mathlib
import Submission.Diff.Interfaces
import Submission.Work.Diff.C.Defs
import Submission.GlobalExp
import Submission.InjRadius
import Submission.CutTime
import Submission.HopfRinow2

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Area C: the vocabulary of the classical high-pinching sphere theorem

This module fixes the objects that the sub-lemmas of the classical endgame
(`Work.Diff.C.classical_end_v2`) are stated about.  Nothing here is a `sorry`.

* `fcos q = cos ∘ d(q,·)`, the basic building block;
* `gp F G x = ⟪∇F, ∇G⟫ + F·G`, the Gram pairing (the entries `A_ij` of the classical proof);
* `dirv e i = 0` for `i = 0` and `e (i-1)` otherwise, the `(n+1)` directions;
* `qpt hmet p e i = exp_p((π/2) • dirv e i)`: `q₀ = p`, `q_{i+1} = exp_p((π/2) eᵢ)`, the `(n+1)`
  points of the classical proof;
* `fFam hmet p e i = fcos (qpt ... i)`;
* `SmoothOnRegion c f`: `f` is smooth where `f > -1 + c`;
* `HessBoundRegion cov c ε f`: on that region, `Hess f = -f·g + E` with `|E| ≤ ε`.
-/

set_option linter.unusedSectionVars false

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.C

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

section Basic

variable [RiemannianBundle (fun x : M ↦ TangentSpace I x)]

/-- `cos` of the Riemannian distance to `p`. -/
noncomputable def fcos (p : M) : M → ℝ := fun x => Real.cos (rdist (I := I) p x)

/-- The Gram pairing `⟪∇F,∇G⟫ + F·G` of two functions on `M`. -/
noncomputable def gp (F G : M → ℝ) (x : M) : ℝ :=
  Inner.inner ℝ (rgrad (I := I) F x) (rgrad (I := I) G x) + F x * G x

/-- `f` is smooth on the region `{f > -1 + c}`. -/
def SmoothOnRegion (c : ℝ) (f : M → ℝ) : Prop :=
  ∀ x : M, -1 + c < f x → CMDiffAt ∞ f x

/-- On the region `{f > -1 + c}`, the Hessian of `f` is `-f·g + E` with `|E| ≤ ε` as a bilinear
form: `|Hess f (V,W) + f·⟪V,W⟫| ≤ ε·‖V‖·‖W‖`.  (This implies the quadratic-form version.) -/
-- ⚠️ CAUTION (endpoint `rdist = 0`).  For `f = fcos q` the region `{f > -1 + c}` contains the
-- centre `q` itself (`f q = cos 0 = 1`).  On the *real* side the Hessian bound below holds there
-- too (with error `0`, since `Hess (cos ∘ d)(q) = -g`), but the one-variable quantity
-- `cos d - sin d·√(1+η)·cot(√(1+η)d)` from the Hessian comparison evaluated at `d = 0` is `1`
-- in Lean (`Real.cot 0 = 0`, division by zero is `0`!), so *uniform hypotheses of the form
-- "max(… at d) ≤ ε for all `d ∈ [0, arccos(-1+c)]`" are only satisfiable for `ε ≥ 1`*.
-- Statements that feed this definition from the Hessian comparison must therefore either
-- (i) restrict the comparison hypothesis to `0 < d` and treat the centre separately
-- (at the centre the exact statement `Hess (cos ∘ d)(q) = -g` holds), or
-- (ii) exclude `x = q` from the region.  See the HANDOFF note in `classical_end_v2.lean`.
def HessBoundRegion (cov : CovariantDerivative I E (TangentSpace I (M := M))) (c ε : ℝ)
    (f : M → ℝ) : Prop :=
  ∀ (x : M) (V W : TangentSpace I x), -1 + c < f x →
    |rhess cov f x V W + f x * Inner.inner ℝ V W| ≤ ε * ‖V‖ * ‖W‖

/-- **The content of `Work.Diff.C.dist_eikonal2`** (area H286, live) as a hypothesis: the
distance function `rdist p ·` is smooth and its gradient is a unit vector on `0 < rdist p · < ρ`. -/
def EikonalInput (cov : CovariantDerivative I E (TangentSpace I (M := M))) (η : ℝ) : Prop :=
  ∀ (p : M) (y : M), 0 < rdist (I := I) p y →
    rdist (I := I) p y < Real.pi / Real.sqrt (1 + η) →
    CMDiffAt ∞ (fun z : M ↦ rdist (I := I) p z) y ∧
      Inner.inner ℝ (rgrad (I := I) (rdist (I := I) p) y)
        (rgrad (I := I) (rdist (I := I) p) y) = 1

/-- **The content of `Work.Diff.C.hess_upper`** (area H156, live) as a hypothesis: the upper
Hessian comparison for the distance function, under `sec > 1`. -/
def HessUpperInput (cov : CovariantDerivative I E (TangentSpace I (M := M))) : Prop :=
  ∀ (p : M) (x : M), CMDiffAt ∞ (fun z : M ↦ rdist (I := I) p z) x →
    Inner.inner ℝ (rgrad (I := I) (rdist (I := I) p) x)
      (rgrad (I := I) (rdist (I := I) p) x) = 1 →
    ∀ V : TangentSpace I x,
      rhess cov (rdist (I := I) p) x V V ≤ Real.cot (rdist (I := I) p x)
        * (Inner.inner ℝ V V - (Inner.inner ℝ (rgrad (I := I) (rdist (I := I) p) x) V) ^ 2)

/-- **The content of `Work.Diff.C.hess_lower`** (area H155, live) as a hypothesis: the lower
Hessian comparison for the distance function, under `sec ≤ 1 + η` and `√(1+η)·d < π`. -/
def HessLowerInput (cov : CovariantDerivative I E (TangentSpace I (M := M))) (η : ℝ) : Prop :=
  ∀ (p : M) (x : M), CMDiffAt ∞ (fun z : M ↦ rdist (I := I) p z) x →
    Inner.inner ℝ (rgrad (I := I) (rdist (I := I) p) x)
      (rgrad (I := I) (rdist (I := I) p) x) = 1 →
    Real.sqrt (1 + η) * rdist (I := I) p x < Real.pi →
    ∀ V : TangentSpace I x,
      Real.sqrt (1 + η) * Real.cot (Real.sqrt (1 + η) * rdist (I := I) p x)
          * (Inner.inner ℝ V V
              - (Inner.inner ℝ (rgrad (I := I) (rdist (I := I) p) x) V) ^ 2)
        ≤ rhess cov (rdist (I := I) p) x V V

/-- **The content of `Work.Diff.C.diffeo_of_local`** (area H153, live) as a hypothesis. -/
def DiffeoOfLocalInput : Prop :=
  2 ≤ Module.finrank ℝ E →
  ∀ G : M → SphereD E, IsLocalDiffeomorph I (𝓡 (Module.finrank ℝ E)) ∞ G →
    Nonempty (M ≃ₘ⟮I, 𝓡 (Module.finrank ℝ E)⟯ SphereD E)

end Basic

section Points

variable [I.Boundaryless] [Nontrivial E] [T2Space M] [CompactSpace M]
  {cov : CovariantDerivative I E (TangentSpace I (M := M))}
  [ContMDiffCovariantDerivative cov ∞]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

/-- The direction of the index `i ∈ Fin (n+1)`: the zero vector for `i = 0` and `e (i-1)`
otherwise. -/
noncomputable def dirv {n : ℕ} {p : M} (e : Fin n → TangentSpace I p) :
    Fin (n + 1) → TangentSpace I p :=
  fun i => Fin.cases (0 : TangentSpace I p) e i

/-- The point `qᵢ = exp_p((π/2)·dirᵢ)`: `q₀ = p` and `q_{i+1} = exp_p((π/2)·eᵢ)`. -/
noncomputable def qpt {n : ℕ} (hmet : IsMetricCompatible cov) (p : M)
    (e : Fin n → TangentSpace I p) (i : Fin (n + 1)) : M :=
  Submission.GlobalExp.GExp (cov := cov) hmet p ((Real.pi / 2) • dirv e i)

/-- The family `fᵢ = cos ∘ d(qᵢ, ·)`. -/
noncomputable def fFam {n : ℕ} (hmet : IsMetricCompatible cov) (p : M)
    (e : Fin n → TangentSpace I p) (i : Fin (n + 1)) : M → ℝ :=
  fcos (I := I) (M := M) (qpt (I := I) (M := M) hmet p e i)

end Points

section Data

variable [I.Boundaryless] [Nontrivial E] [T2Space M] [CompactSpace M]
  {cov : CovariantDerivative I E (TangentSpace I (M := M))}
  [ContMDiffCovariantDerivative cov ∞]
  [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]

/-- **The initial data of the classical construction** at the base point `p`, for an orthonormal
family `e : Fin n → T_pM`: `f₀(p) = 1`, `∇f₀(p) = 0`, and for `i ≥ 1`, `f_i(p) = 0`,
`∇f_i(p) = e i` (here `f_i = cos ∘ d(q_i,·)` with `q_i = exp_p((π/2)·e_i)`). -/
def InitData {n : ℕ} (hmet : IsMetricCompatible cov) (p : M)
    (e : Fin n → TangentSpace I p) : Prop :=
  fcos (I := I) (M := M) p p = 1 ∧
    rgrad (I := I) (M := M) (fcos (I := I) (M := M) p) p = 0 ∧
    ∀ i : Fin n,
      fcos (I := I) (M := M) (qpt (I := I) (M := M) (cov := cov) hmet p e (Fin.succ i)) p = 0 ∧
      rgrad (I := I) (M := M)
        (fcos (I := I) (M := M) (qpt (I := I) (M := M) (cov := cov) hmet p e (Fin.succ i))) p = e i

end Data

end Work.Diff.C
