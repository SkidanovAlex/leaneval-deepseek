import ChallengeDeps
import Submission.Diff.Alg

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Contracts for `sphere_theorem_differentiable` (lead-written; definitions and `Prop`s only)

Route (see HANDOFF.md): run the Ricci flow from the quarter-pinched metric only until the metric
is `(1+η)`-pinched (`FlowContract`), then apply a classical high-pinching differentiable sphere
theorem (`ClassicalEnd`). No convergence of the flow is needed.

A time-dependent metric is `G : ℝ → SMet I M` (Mathlib's `ContMDiffRiemannianMetric`), used with
EXPLICIT inner products `(G t).inner x u v`. A fixed metric is turned into the instance with
`letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩`.
-/

open LeanEval.Geometry.SphereTheorem Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Submission.Diff

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M]

variable (I M) in
/-- Smooth Riemannian metrics on `M`. -/
abbrev SMet := ContMDiffRiemannianMetric I ∞ E (fun x : M ↦ TangentSpace I x)

/-- The sphere target of the challenge. -/
abbrev SphereD (E : Type*) [NormedAddCommGroup E] [NormedSpace ℝ E] :=
  sphere (0 : EuclideanSpace ℝ (Fin (Module.finrank ℝ E + 1))) 1

/-- `(κ, Λ]`-pinching of `cov` w.r.t. the INSTANCE metric, phrased exactly like `QuarterPinched`. -/
def Pinched [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    (cov : CovariantDerivative I E (TangentSpace I (M := M))) (κ Λ : ℝ) : Prop :=
  ∀ (X Y : Π x : M, TangentSpace I x),
    CMDiff ∞ (T% X) → CMDiff ∞ (T% Y) →
    ∀ x : M,
      inner ℝ (X x) (X x) = (1 : ℝ) → inner ℝ (Y x) (Y x) = (1 : ℝ) →
      inner ℝ (X x) (Y x) = (0 : ℝ) →
      κ < inner ℝ (curv cov X Y Y x) (X x) ∧ inner ℝ (curv cov X Y Y x) (X x) ≤ Λ

variable (I M) in
/-- CONTRACT C (classical high-pinching differentiable sphere theorem): there is `η > 0` such that
every smooth metric on `M` whose Levi-Civita connection is `(κ, (1+η)κ]`-pinched makes `M`
diffeomorphic to the standard sphere. (Used with `M` compact, T2, boundaryless, simply connected.) -/
def ClassicalEnd : Prop :=
  ∃ η : ℝ, 0 < η ∧ ∀ g : SMet I M,
    letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
    ∀ cov : CovariantDerivative I E (TangentSpace I (M := M)),
      Nonempty (ContMDiffCovariantDerivative cov ∞) → cov.torsion = 0 → IsMetricCompatible cov →
      ∀ κ : ℝ, 0 < κ → Pinched cov κ ((1 + η) * κ) →
      Nonempty (M ≃ₘ⟮I, 𝓡 (Module.finrank ℝ E)⟯ SphereD E)

variable (I M) in
/-- CONTRACT FLOW: for every `η > 0` there is a smooth metric on `M` with a smooth Levi-Civita
connection that is `(κ, (1+η)κ]`-pinched. (Proved from a quarter-pinched metric via Ricci flow.) -/
def FlowContract : Prop :=
  ∀ η : ℝ, 0 < η → ∃ g : SMet I M,
    letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
    ∃ cov : CovariantDerivative I E (TangentSpace I (M := M)),
      Nonempty (ContMDiffCovariantDerivative cov ∞) ∧ cov.torsion = 0 ∧ IsMetricCompatible cov ∧
      ∃ κ : ℝ, 0 < κ ∧ Pinched cov κ ((1 + η) * κ)

/-! ## Pointwise tensors of a connection -/

/-- A smooth extension of `u ∈ TₓM` (chosen by `Classical.epsilon`; area T proves the spec). -/
noncomputable def smoothExt (x : M) (u : TangentSpace I x) : Π y : M, TangentSpace I y :=
  Classical.epsilon (fun X : Π y : M, TangentSpace I y => CMDiff ∞ (T% X) ∧ X x = u)

/-- Pointwise curvature `R(u,v)w` (tensorial for smooth torsion-free `cov`). -/
noncomputable def rmVec (cov : CovariantDerivative I E (TangentSpace I (M := M))) (x : M)
    (u v w : TangentSpace I x) : TangentSpace I x :=
  curv cov (smoothExt x u) (smoothExt x v) (smoothExt x w) x

/-- Ricci tensor `Ric(u,v) = tr (w ↦ R(w,u)v)` (trace in the basis `Module.finBasis ℝ E`). -/
noncomputable def ricAt (cov : CovariantDerivative I E (TangentSpace I (M := M))) (x : M)
    (u v : TangentSpace I x) : ℝ :=
  ∑ i, (Module.finBasis ℝ E).coord i
    (rmVec cov x ((Module.finBasis ℝ E i : E) : TangentSpace I x) u v)

/-- The Levi-Civita connection of an explicit smooth metric (Mathlib's Koszul construction). -/
noncomputable def lcOf (g : SMet I M) : CovariantDerivative I E (TangentSpace I (M := M)) :=
  letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
  CovariantDerivative.leviCivitaConnection I M

/-- `e` is a `g`-orthonormal frame of `TₓM`. -/
def IsONFrame (g : SMet I M) (x : M) (e : Fin (Module.finrank ℝ E) → TangentSpace I x) : Prop :=
  ∀ i j, g.inner x (e i) (e j) = if i = j then 1 else 0

/-- Curvature components of `g` in a frame: `R i j k l = g(R(eᵢ,eⱼ)eₗ, eₖ)`. -/
noncomputable def rmFrame (g : SMet I M) (x : M) (e : Fin (Module.finrank ℝ E) → TangentSpace I x) :
    Curv4 (Module.finrank ℝ E) := fun i j k l =>
  g.inner x (rmVec (lcOf g) x (e i) (e j) (e l)) (e k)

/-- The curvature of `g` lies in `F` at every point, in every orthonormal frame. -/
def CurvIn (g : SMet I M) (F : Set (Curv4 (Module.finrank ℝ E))) : Prop :=
  ∀ x (e : Fin (Module.finrank ℝ E) → TangentSpace I x), IsONFrame g x e → rmFrame g x e ∈ F

/-- All curvature components of `g` in orthonormal frames are bounded by `C`. -/
def CurvBound (g : SMet I M) (C : ℝ) : Prop :=
  ∀ x (e : Fin (Module.finrank ℝ E) → TangentSpace I x), IsONFrame g x e →
    ∀ i j k l, |rmFrame g x e i j k l| ≤ C

/-! ## Time-dependent metrics and the Ricci flow -/

/-- `(t, x) ↦ G t x` is jointly smooth on `J × M` (as a section of the bilinear-form bundle). -/
def JointSmooth (G : ℝ → SMet I M) (J : Set ℝ) : Prop :=
  ContMDiffOn (𝓘(ℝ, ℝ).prod I) (I.prod 𝓘(ℝ, E →L[ℝ] E →L[ℝ] ℝ)) ∞
    (fun p : ℝ × M ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
      (E := fun x : M ↦ TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) p.2 ((G p.1).inner p.2))
    (J ×ˢ univ)

/-- `G` is a smooth Ricci flow on `[0, T)`: `∂ₜ g = -2 Ric(g)`. -/
def IsRicciFlow (G : ℝ → SMet I M) (T : ℝ) : Prop :=
  JointSmooth G (Ico 0 T) ∧
    ∀ t ∈ Ico 0 T, ∀ (x : M) (u v : TangentSpace I x),
      HasDerivWithinAt (fun s ↦ (G s).inner x u v) (-2 * ricAt (lcOf (G t)) x u v) (Ico 0 T) t

variable (I M) in
/-- CONTRACT STE (short-time existence; analytic core P1+P2, DeTurck trick). -/
def ShortTimeExistence : Prop :=
  ∀ g₀ : SMet I M, ∃ T : ℝ, 0 < T ∧ ∃ G : ℝ → SMet I M, IsRicciFlow G T ∧ G 0 = g₀

variable (I M) in
/-- CONTRACT EXT (continuation): a Ricci flow with bounded curvature on `[0, T)` extends past `T`. -/
def Extension : Prop :=
  ∀ (G : ℝ → SMet I M) (T C : ℝ), 0 < T → IsRicciFlow G T →
    (∀ t ∈ Ico 0 T, CurvBound (G t) C) →
    ∃ T' : ℝ, T < T' ∧ ∃ G' : ℝ → SMet I M, IsRicciFlow G' T' ∧ ∀ t ∈ Ico 0 T, G' t = G t

variable (I M) in
/-- CONTRACT PP (Hamilton's maximum principle for the curvature; areas E + MP): time-dependent
invariant families of the ODE `R' = Q(R)` are preserved by the Ricci flow. (Static sets: take
`F t = F₀`; a static `IsInvariantSet` is an `IsInvariantFamily`.) -/
def PinchingPreserved : Prop :=
  ∀ F : ℝ → Set (Curv4 (Module.finrank ℝ E)), IsInvariantFamily F →
    ∀ (G : ℝ → SMet I M) (T : ℝ), IsRicciFlow G T → CurvIn (G 0) (F 0) →
      ∀ t ∈ Ico 0 T, CurvIn (G t) (F t)

variable (I M) in
/-- CONTRACT T1: the Levi-Civita connection of a smooth metric is a smooth, torsion-free,
metric-compatible (in the challenge's sense) covariant derivative. -/
def LCSmooth : Prop :=
  ∀ g : SMet I M,
    letI : RiemannianBundle (fun x : M ↦ TangentSpace I x) := ⟨g.toRiemannianMetric⟩
    Nonempty (ContMDiffCovariantDerivative (lcOf g) ∞) ∧ (lcOf g).torsion = 0 ∧
      IsMetricCompatible (lcOf g)

/-! ## First variation of the Levi-Civita connection (contract T2) -/

/-- `∂ₜ G` at `t₀`, pointwise. -/
noncomputable def dtMet (G : ℝ → SMet I M) (t₀ : ℝ) (y : M) (u v : TangentSpace I y) : ℝ :=
  deriv (fun t ↦ (G t).inner y u v) t₀

/-- `(∇_U h)(V, W)` at `x` for a pointwise bilinear form `h`, computed with smooth fields. -/
noncomputable def covDerivSym2 (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (h : Π y : M, TangentSpace I y → TangentSpace I y → ℝ)
    (U V W : Π y : M, TangentSpace I y) (x : M) : ℝ :=
  mvfderiv I (fun y : M ↦ h y (V y) (W y)) x (U x)
    - h x (cov V x (U x)) (W x) - h x (V x) (cov W x (U x))

variable (I M) in
/-- CONTRACT T2: `∂ₜ (∇_X Y) = A(X, Y)` with `g(A(X,Y), Z) = ½((∇_X h)(Y,Z) + (∇_Y h)(X,Z) - (∇_Z h)(X,Y))`,
`h = ∂ₜ g`, `∇ = ∇^{g(t₀)}`. -/
def LCVariation : Prop :=
  ∀ (G : ℝ → SMet I M) (J : Set ℝ), IsOpen J → JointSmooth G J → ∀ t₀ ∈ J,
    ∀ (X Y : Π x : M, TangentSpace I x), CMDiff ∞ (T% X) → CMDiff ∞ (T% Y) → ∀ x : M,
      ∃ A : TangentSpace I x,
        HasDerivAt (fun t ↦ ((lcOf (G t) Y x (X x) : TangentSpace I x) : E)) (A : E) t₀ ∧
        ∀ Z : Π x : M, TangentSpace I x, CMDiff ∞ (T% Z) →
          (G t₀).inner x A (Z x) =
            (1 / 2 : ℝ) * (covDerivSym2 (lcOf (G t₀)) (dtMet G t₀) X Y Z x
              + covDerivSym2 (lcOf (G t₀)) (dtMet G t₀) Y X Z x
              - covDerivSym2 (lcOf (G t₀)) (dtMet G t₀) Z X Y x)

end Submission.Diff
