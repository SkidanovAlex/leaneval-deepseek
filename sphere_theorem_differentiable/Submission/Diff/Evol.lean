import Submission.Diff.Grad

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Shared contracts: variation and evolution of the curvature (lead-written; one owner)
Consumers: PP (maximum principle), GE/EV1–EV3, EXT. Conventions as in Grad.lean:
`rmP g x a b c d = g(R(a,b)d, c)`, `rmFrame g x e i j k l = rmP g x (e i) (e j) (e k) (e l)`,
`covRm g x v a b c d = (∇_v Rm)(a,b,c,d)`.
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

/-- `(∇²_{v,w} Rm)(a,b,c,d) = (∇_v ∇Rm)(w,a,b,c,d)`, computed with smooth extensions. -/
noncomputable def cov2Rm (g : SMet I M) (x : M) (v w a b c d : TangentSpace I x) : ℝ :=
  mvfderiv I (fun y : M ↦ covRm g y (smoothExt x w y) (smoothExt x a y) (smoothExt x b y)
      (smoothExt x c y) (smoothExt x d y)) x v
    - covRm g x (lcOf g (smoothExt x w) x v) a b c d
    - covRm g x w (lcOf g (smoothExt x a) x v) b c d
    - covRm g x w a (lcOf g (smoothExt x b) x v) c d
    - covRm g x w a b (lcOf g (smoothExt x c) x v) d
    - covRm g x w a b c (lcOf g (smoothExt x d) x v)

/-- The rough Laplacian of `Rm` in a frame: `(ΔRm)ᵢⱼₖₗ = ∑ₘ (∇²_{eₘ,eₘ} Rm)(eᵢ,eⱼ,eₖ,eₗ)`. -/
noncomputable def lapRmFrame (g : SMet I M) (x : M) (e : Fin (Module.finrank ℝ E) → TangentSpace I x) :
    Curv4 (Module.finrank ℝ E) := fun i j k l =>
  ∑ m, cov2Rm g x (e m) (e m) (e i) (e j) (e k) (e l)

/-- `A(V,W)(y) = ∂ₜ|_{t₀} (∇^{G t}_V W)(y)` (first variation of the connection, as a field). -/
noncomputable def dLC (G : ℝ → SMet I M) (t₀ : ℝ) (V W : Π y : M, TangentSpace I y) (y : M) :
    TangentSpace I y :=
  deriv (fun t ↦ ((lcOf (G t) W y (V y) : TangentSpace I y) : E)) t₀

/-- `(∇_U A)(V,W)` at `x`, with `∇ = ∇^{G t₀}`. -/
noncomputable def covDLC (G : ℝ → SMet I M) (t₀ : ℝ) (U V W : Π y : M, TangentSpace I y) (x : M) :
    TangentSpace I x :=
  lcOf (G t₀) (dLC G t₀ V W) x (U x)
    - dLC G t₀ (fun y ↦ lcOf (G t₀) V y (U y)) W x
    - dLC G t₀ V (fun y ↦ lcOf (G t₀) W y (U y)) x

variable (I M) in
/-- CONTRACT CV (first variation of the curvature): `∂ₜ R(X,Y)Z = (∇_X A)(Y,Z) − (∇_Y A)(X,Z)`
for fixed smooth fields. -/
def CurvVariation : Prop :=
  ∀ (G : ℝ → SMet I M) (J : Set ℝ), IsOpen J → JointSmooth G J → ∀ t₀ ∈ J,
    ∀ (X Y Z : Π x : M, TangentSpace I x), CMDiff ∞ (T% X) → CMDiff ∞ (T% Y) → CMDiff ∞ (T% Z) →
    ∀ x : M, HasDerivAt (fun t ↦ ((curv (lcOf (G t)) X Y Z x : TangentSpace I x) : E))
      ((covDLC G t₀ X Y Z x - covDLC G t₀ Y X Z x : TangentSpace I x) : E) t₀

variable (I M) in
/-- CONTRACT CE (Hamilton's curvature evolution in an Uhlenbeck frame): along a Ricci flow, for a
family of `G s`-orthonormal frames at `x` with `∂ₛ eᵢ = ∑ⱼ Ric(eᵢ,eⱼ) eⱼ`, the components satisfy
`∂ₜ R = ΔR + Q(R)`. Sanity: round sphere, `R = K·Iso`, `K' = 2(n−1)K²`. -/
def CurvEvolution : Prop :=
  ∀ (G : ℝ → SMet I M) (T : ℝ), IsRicciFlow G T → ∀ t ∈ Ioo 0 T, ∀ (x : M)
    (e : ℝ → Fin (Module.finrank ℝ E) → TangentSpace I x),
    (∀ s ∈ Ioo 0 T, IsONFrame (G s) x (e s)) →
    (∀ i, HasDerivAt (fun s ↦ ((e s i : TangentSpace I x) : E))
        (((∑ j, ricAt (lcOf (G t)) x (e t i) (e t j) • e t j : TangentSpace I x)) : E) t) →
    HasDerivAt (fun s ↦ rmFrame (G s) x (e s))
      (lapRmFrame (G t) x (e t) + Q (rmFrame (G t) x (e t))) t

variable (I M) in
/-- CONTRACT LP (rough Laplacian via a parallel-at-`x` frame): every orthonormal frame at `x`
extends to a smooth frame field, orthonormal near `x`, for which the Laplacian at `x` of any linear
functional of the curvature components is that functional of `lapRmFrame`. (Radially parallel frames.)
This is the input of the maximum principle at a spatial maximum. -/
def LapRmFrameParallel : Prop :=
  ∀ (g : SMet I M) (x : M) (e : Fin (Module.finrank ℝ E) → TangentSpace I x), IsONFrame g x e →
    ∃ Ef : Fin (Module.finrank ℝ E) → Π y : M, TangentSpace I y,
      (∀ i, Ef i x = e i) ∧ (∀ i, CMDiff ∞ (T% (Ef i))) ∧
      (∀ᶠ y in 𝓝 x, IsONFrame g y (fun i ↦ Ef i y)) ∧
      ∀ ℓ : Curv4 (Module.finrank ℝ E) →L[ℝ] ℝ,
        laplAt g (fun y ↦ ℓ (rmFrame g y (fun i ↦ Ef i y))) x = ℓ (lapRmFrame g x e)

end Submission.Diff
