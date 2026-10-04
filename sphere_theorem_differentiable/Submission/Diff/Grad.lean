import Submission.Diff.Interfaces

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Contracts for Hamilton's gradient estimate (lead-written; definitions and `Prop`s only)

Design: FM3-DRIVE log / HANDOFF. For a Ricci flow whose curvature stays in a pinching set, and
`n ≥ 3`, `|∇Rm|² ≤ η |scal|³ + C(η)`. The proof is the maximum principle for
`Ψ = |∇Rm|² + N (scal + K₀) |Rm°|² − η (scal + K₀)³`.
All quantities are scalar functions computed in a (chosen) orthonormal frame; their values do not
depend on the frame.
-/

open LeanEval.Geometry.SphereTheorem Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Submission.Diff.Alg

variable {n : ℕ}

/-- `|R|²` (Frobenius). -/
noncomputable def frobSq (R : Curv4 n) : ℝ := ∑ i, ∑ j, ∑ k, ∑ l, R i j k l ^ 2

/-- `|Ric|²` with `Ricᵢⱼ = ∑ₖ Rₖᵢₖⱼ`. -/
noncomputable def ricSq (R : Curv4 n) : ℝ := ∑ i, ∑ j, (∑ k, R k i k j) ^ 2

/-- `⟪R, Q(R)⟫`. -/
noncomputable def qPair (R : Curv4 n) : ℝ := ∑ i, ∑ j, ∑ k, ∑ l, R i j k l * Q R i j k l

/-- `|R°|² = |R|² − 2 scal²/(n(n−1))`, the squared distance to the constant-curvature line. -/
noncomputable def frobSqTF (R : Curv4 n) : ℝ := frobSq R - 2 * scalAlg R ^ 2 / (n * (n - 1 : ℝ))

/-- CONTRACT PA (algebra). Consequences of a pinching set, plus the structure of the reaction term. -/
def PinchingAlgebra (n : ℕ) : Prop :=
  (∀ F : Set (Curv4 n), IsPinchingSet F →
      (∃ c C₀ : ℝ, 0 < c ∧ ∀ R ∈ F, Real.sqrt (frobSq R) ≤ c * scalAlg R + C₀) ∧
      (∀ δ : ℝ, 0 < δ → ∃ C : ℝ, ∀ R ∈ F, Real.sqrt (frobSqTF R) ≤ δ * Real.sqrt (frobSq R) + C)) ∧
  (∃ c : ℝ, ∀ R : Curv4 n, IsAlgCurv R →
      qPair R - 4 * scalAlg R / (n * (n - 1 : ℝ)) * ricSq R ≤ c * frobSqTF R * Real.sqrt (frobSq R)) ∧
  (∀ R : Curv4 n, IsAlgCurv R → scalAlg R ^ 2 ≤ n * ricSq R ∧ 0 ≤ frobSqTF R)

end Submission.Diff.Alg

namespace Submission.Diff

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M]

/-- A chosen `g`-orthonormal frame at `x`. -/
noncomputable def onFrame (g : SMet I M) (x : M) : Fin (Module.finrank ℝ E) → TangentSpace I x :=
  Classical.epsilon (IsONFrame g x)

/-- `Hess u (v, w)` at `x` for the Levi-Civita connection of `g`. -/
noncomputable def hessAt (g : SMet I M) (u : M → ℝ) (x : M) (v w : TangentSpace I x) : ℝ :=
  mvfderiv I (fun y : M ↦ mvfderiv I u y (smoothExt x w y)) x v
    - mvfderiv I u x (lcOf g (smoothExt x w) x v)

/-- `Δ_g u` at `x`. -/
noncomputable def laplAt (g : SMet I M) (u : M → ℝ) (x : M) : ℝ :=
  ∑ i, hessAt g u x (onFrame g x i) (onFrame g x i)

/-- `|∇u|²_g` at `x`. -/
noncomputable def gradSq (g : SMet I M) (u : M → ℝ) (x : M) : ℝ :=
  ∑ i, (mvfderiv I u x (onFrame g x i)) ^ 2

/-- Curvature components in the chosen frame. -/
noncomputable def rmC (g : SMet I M) (x : M) : Curv4 (Module.finrank ℝ E) := rmFrame g x (onFrame g x)

noncomputable def rmNormSq (g : SMet I M) (x : M) : ℝ := frobSq (rmC g x)
noncomputable def scalAt (g : SMet I M) (x : M) : ℝ := scalAlg (rmC g x)
noncomputable def ricNormSq (g : SMet I M) (x : M) : ℝ := ricSq (rmC g x)
noncomputable def qPairAt (g : SMet I M) (x : M) : ℝ := qPair (rmC g x)
noncomputable def rmoNormSq (g : SMet I M) (x : M) : ℝ := frobSqTF (rmC g x)

/-- `Rm(a,b,c,d) = g(R(a,b)d, c)` at a point. -/
noncomputable def rmP (g : SMet I M) (x : M) (a b c d : TangentSpace I x) : ℝ :=
  g.inner x (rmVec (lcOf g) x a b d) c

/-- `(∇_v Rm)(a,b,c,d)` computed with smooth extensions. -/
noncomputable def covRm (g : SMet I M) (x : M) (v a b c d : TangentSpace I x) : ℝ :=
  mvfderiv I (fun y : M ↦ rmP g y (smoothExt x a y) (smoothExt x b y) (smoothExt x c y)
      (smoothExt x d y)) x v
    - rmP g x (lcOf g (smoothExt x a) x v) b c d - rmP g x a (lcOf g (smoothExt x b) x v) c d
    - rmP g x a b (lcOf g (smoothExt x c) x v) d - rmP g x a b c (lcOf g (smoothExt x d) x v)

/-- `|∇Rm|²`. -/
noncomputable def dRmNormSq (g : SMet I M) (x : M) : ℝ :=
  let e := onFrame g x
  ∑ m, ∑ i, ∑ j, ∑ k, ∑ l, covRm g x (e m) (e i) (e j) (e k) (e l) ^ 2

/-- `|∇Rm°|² = |∇Rm|² − 2|∇scal|²/(n(n−1))`. -/
noncomputable def drmoNormSq (g : SMet I M) (x : M) : ℝ :=
  dRmNormSq g x - 2 * gradSq g (scalAt g) x /
    ((Module.finrank ℝ E : ℝ) * ((Module.finrank ℝ E : ℝ) - 1))

variable (I M) in
/-- CONTRACT EV1: `∂ₜ|Rm|² = Δ|Rm|² − 2|∇Rm|² + 2⟪Rm, Q(Rm)⟫` under Ricci flow. -/
def EvolRmNormSq : Prop :=
  ∀ (G : ℝ → SMet I M) (T : ℝ), IsRicciFlow G T → ∀ t ∈ Ico 0 T, ∀ x : M,
    HasDerivWithinAt (fun s ↦ rmNormSq (G s) x)
      (laplAt (G t) (rmNormSq (G t)) x - 2 * dRmNormSq (G t) x + 2 * qPairAt (G t) x) (Ico 0 T) t

variable (I M) in
/-- CONTRACT EV3: `∂ₜ scal = Δ scal + 2|Ric|²` under Ricci flow. -/
def EvolScal : Prop :=
  ∀ (G : ℝ → SMet I M) (T : ℝ), IsRicciFlow G T → ∀ t ∈ Ico 0 T, ∀ x : M,
    HasDerivWithinAt (fun s ↦ scalAt (G s) x)
      (laplAt (G t) (scalAt (G t)) x + 2 * ricNormSq (G t) x) (Ico 0 T) t

variable (I M) in
/-- CONTRACT EV2: `∂ₜ|∇Rm|² ≤ Δ|∇Rm|² + c |Rm| |∇Rm|²` under Ricci flow (the `−2|∇²Rm|²` is dropped). -/
def EvolDRmNormSq : Prop :=
  ∃ c : ℝ, 0 ≤ c ∧ ∀ (G : ℝ → SMet I M) (T : ℝ), IsRicciFlow G T → ∀ t ∈ Ico 0 T, ∀ x : M,
    ∃ D : ℝ, HasDerivWithinAt (fun s ↦ dRmNormSq (G s) x) D (Ico 0 T) t ∧
      D ≤ laplAt (G t) (dRmNormSq (G t)) x + c * Real.sqrt (rmNormSq (G t) x) * dRmNormSq (G t) x

variable (I M) in
/-- CONTRACT REG: the scalar curvature quantities of a Ricci flow are jointly smooth on `[0,T) × M`. -/
def NormsSmooth : Prop :=
  ∀ (G : ℝ → SMet I M) (T : ℝ), IsRicciFlow G T →
    ∀ u ∈ ({rmNormSq, dRmNormSq, scalAt} : Set (SMet I M → M → ℝ)),
      ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞ (fun p : ℝ × M ↦ u (G p.1) p.2) (Ico 0 T ×ˢ univ)

variable (I M) in
/-- CONTRACT BK (second Bianchi + Kato), `n ≥ 3`: `|∇scal|² ≤ K |∇Rm°|²` and
`|∇|Rm°|²|² ≤ 4 |Rm°|² |∇Rm°|²`. -/
def BianchiKato : Prop :=
  ∃ K : ℝ, 0 ≤ K ∧ ∀ (g : SMet I M) (x : M),
    gradSq g (scalAt g) x ≤ K * drmoNormSq g x ∧
      gradSq g (rmoNormSq g) x ≤ 4 * rmoNormSq g x * drmoNormSq g x

variable (I M) in
/-- CONTRACT SMP: the scalar maximum principle on a compact manifold along a family of metrics. -/
def ScalarMaxPrinciple : Prop :=
  ∀ (G : ℝ → SMet I M) (T : ℝ) (u d : ℝ → M → ℝ) (C₁ C₂ B : ℝ),
    JointSmooth G (Ico 0 T) → 0 ≤ C₁ → 0 ≤ C₂ →
    ContMDiffOn (𝓘(ℝ, ℝ).prod I) 𝓘(ℝ, ℝ) ∞ (fun p : ℝ × M ↦ u p.1 p.2) (Ico 0 T ×ˢ univ) →
    (∀ t ∈ Ico 0 T, ∀ x, HasDerivWithinAt (fun s ↦ u s x) (d t x) (Ico 0 T) t ∧
      d t x ≤ laplAt (G t) (u t) x + C₁ * max (u t x) 0 + C₂) →
    (∀ x, u 0 x ≤ B) →
    ∀ t ∈ Ico 0 T, ∀ x, u t x ≤ Real.exp (C₁ * t) * (max B 0 + C₂ * t)

variable (I M) in
/-- CONTRACT GE (Hamilton's gradient estimate on a pinched flow). -/
def GradientEstimate : Prop :=
  ∀ (G : ℝ → SMet I M) (T : ℝ) (F : Set (Curv4 (Module.finrank ℝ E))),
    0 < T → IsRicciFlow G T → IsPinchingSet F → (∀ t ∈ Ico 0 T, CurvIn (G t) F) →
    ∀ η : ℝ, 0 < η → ∃ C : ℝ, ∀ t ∈ Ico 0 T, ∀ x : M,
      dRmNormSq (G t) x ≤ η * |scalAt (G t) x| ^ 3 + C

end Submission.Diff
