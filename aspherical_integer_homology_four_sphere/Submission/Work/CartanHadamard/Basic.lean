/-
# Cartan–Hadamard: the basic interface

This file sets up the Cartan–Hadamard area (area `CH`): the variable block, the passage from a
non-positive curvature bound (`sec ≤ 0`) to the parametric upper bounds `CurvLe cov K` for every
`K > 0`, the local diffeomorphism/homeomorphism property of the exponential map, and the two
topological lemmas that the evenly-covered-neighbourhood argument uses (uniqueness of lifts of a
local homeomorphism on a preconnected space, and discreteness of the fibres).

The main deliverable of the area is `Submission/Work/CartanHadamard/Main.lean`.
-/
import Submission.Work.RiemLib.API
import Submission.Work.RiemLib.SecNonpos.All
import Submission.Work.RiemLib.UniformInj

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open LeanEval.Geometry.SphereTheorem

namespace Work.CartanHadamard

noncomputable section

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]
  [I.Boundaryless] [Nontrivial E] [CompactSpace M]
  {cov : CovariantDerivative I E (TangentSpace I (M := M))}
  [ContMDiffCovariantDerivative cov ∞]

/-! ## §1 `sec ≤ 0` gives every parametric upper bound -/

/-- **A non-positive sectional curvature bound gives `CurvLe cov K` for every `K > 0`.**

This is the curvature hypothesis of the whole area: the comparison theorems of the vendored
library are parametric in an upper bound `K`, and a non-positively curved manifold satisfies all
of them at once. -/
theorem curvLe_all
    (hK0 : ∀ x : M, ∀ u v : TangentSpace I x, ‖u‖ = 1 → ‖v‖ = 1 → inner ℝ u v = 0 →
      inner ℝ (Submission.CurvatureVec.curvVec cov x u v v) u ≤ 0) :
    ∀ K : ℝ, 0 < K → Submission.RauchK.CurvLe cov K :=
  fun K hK => Work.RiemLib.CurvLe_of_nonpos hK0 hK

/-! ## §2 The exponential map is a local diffeomorphism, hence a local homeomorphism -/

/-- **The exponential map at `p` is a local diffeomorphism at every point**, as soon as
`CurvLe cov K` holds for every `K > 0`.

Indeed, `Rauch`'s conjugate-radius bound says that `d GExp p` is invertible at every vector of
fibre norm `< π/√K`, and `π/√K` is unbounded in `K`. -/
theorem isLocalDiffeomorphAt_gexpMap
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    (hK : ∀ K : ℝ, 0 < K → Submission.RauchK.CurvLe cov K) (p : M) (u : E) :
    IsLocalDiffeomorphAt 𝓘(ℝ, E) I ∞ (Submission.XuLift.gexpMap (cov := cov) hmet p) u := by
  obtain ⟨K, hKpos, hKlt⟩ := Work.RiemLib.exists_lt_pi_div_sqrt ‖(show TangentSpace I p from u)‖
  exact Submission.XuLift.isLocalDiffeomorphAt_GExp (cov := cov) hmet p
    (Work.RiemLib.isInvertible_mfderiv_gexpMap_of_norm_lt_pi_div_sqrt
      (cov := cov) hmet htor hKpos (hK K hKpos) hKlt)

/-- `gexpMap` is a local diffeomorphism. -/
theorem isLocalDiffeomorph_gexpMap
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    (hK : ∀ K : ℝ, 0 < K → Submission.RauchK.CurvLe cov K) (p : M) :
    IsLocalDiffeomorph 𝓘(ℝ, E) I ∞ (Submission.XuLift.gexpMap (cov := cov) hmet p) :=
  fun u => isLocalDiffeomorphAt_gexpMap (cov := cov) hmet htor hK p u

/-- **`gexpMap` is a local homeomorphism** (deliverable of area `CH`). -/
theorem isLocalHomeomorph_gexpMap
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    (hK : ∀ K : ℝ, 0 < K → Submission.RauchK.CurvLe cov K) (p : M) :
    IsLocalHomeomorph (Submission.XuLift.gexpMap (cov := cov) hmet p) :=
  (isLocalDiffeomorph_gexpMap (cov := cov) hmet htor hK p).isLocalHomeomorph

/-- `GExp p` (with the tangent space at `p` as its domain) is a local homeomorphism. -/
theorem isLocalHomeomorph_GExp
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    (hK : ∀ K : ℝ, 0 < K → Submission.RauchK.CurvLe cov K) (p : M) :
    IsLocalHomeomorph (fun v : TangentSpace I p => Submission.GlobalExp.GExp (cov := cov) hmet p v) :=
  isLocalHomeomorph_gexpMap (cov := cov) hmet htor hK p

/-- `gexpMap` is an open map. -/
theorem isOpenMap_gexpMap
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    (hK : ∀ K : ℝ, 0 < K → Submission.RauchK.CurvLe cov K) (p : M) :
    IsOpenMap (Submission.XuLift.gexpMap (cov := cov) hmet p) :=
  (isLocalHomeomorph_gexpMap (cov := cov) hmet htor hK p).isOpenMap

/-- `GExp p` is an open map. -/
theorem isOpenMap_GExp
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    (hK : ∀ K : ℝ, 0 < K → Submission.RauchK.CurvLe cov K) (p : M) :
    IsOpenMap (fun v : TangentSpace I p => Submission.GlobalExp.GExp (cov := cov) hmet p v) :=
  (isLocalHomeomorph_GExp (cov := cov) hmet htor hK p).isOpenMap

/-! ## §2b The normal balls of the exponential map -/

/-- **The exponential image of a ball is open**: `GExp y` is an open map. -/
theorem isOpen_image_ball_GExp
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    (hK : ∀ K : ℝ, 0 < K → Submission.RauchK.CurvLe cov K) (y : M) (ρ : ℝ) :
    IsOpen ((fun w : TangentSpace I y => Submission.GlobalExp.GExp (cov := cov) hmet y w) ''
      Metric.ball (0 : TangentSpace I y) ρ) :=
  isOpenMap_GExp (cov := cov) hmet htor hK y _ Metric.isOpen_ball

/-- **`GExp y` is injective on the ball of the injectivity radius** (`InjAtLeast`, in the form of
`Metric.ball`). -/
theorem injOn_ball_GExp (hmet : IsMetricCompatible cov) {y : M} {ρ : ℝ}
    (hρ : Submission.InjRadius.InjAtLeast hmet y ρ) :
    Set.InjOn (fun w : TangentSpace I y => Submission.GlobalExp.GExp (cov := cov) hmet y w)
      (Metric.ball (0 : TangentSpace I y) ρ) := by
  intro u hu v hv huv
  refine hρ u v ?_ ?_ huv
  · rwa [Metric.mem_ball, dist_eq_norm, sub_zero] at hu
  · rwa [Metric.mem_ball, dist_eq_norm, sub_zero] at hv

/-! ## §3 Uniqueness of lifts of a local homeomorphism on a preconnected space -/

/-- **Two continuous lifts of the same map under a local homeomorphism, agreeing at one point of a
preconnected space, are equal.**  The set of agreement points is closed (the target is `T2`... the
domain is) and open (local injectivity of a local homeomorphism). -/
theorem lift_unique_of_isLocalHomeomorph {X Y A : Type*} [TopologicalSpace X] [T2Space X]
    [TopologicalSpace Y] [TopologicalSpace A] [PreconnectedSpace A] {F : X → Y}
    (hF : IsLocalHomeomorph F)
    {g₁ g₂ : A → X} (h₁ : Continuous g₁) (h₂ : Continuous g₂)
    (heq : ∀ a : A, F (g₁ a) = F (g₂ a)) {a₀ : A} (ha : g₁ a₀ = g₂ a₀) : g₁ = g₂ := by
  have hclosed : IsClosed {a : A | g₁ a = g₂ a} := isClosed_eq h₁ h₂
  have hopen : IsOpen {a : A | g₁ a = g₂ a} := by
    rw [isOpen_iff_mem_nhds]
    intro a ha
    obtain ⟨e, hae, heqe⟩ := hF (g₁ a)
    subst heqe
    have h1 : {b : A | g₁ b ∈ e.source} ∈ 𝓝 a :=
      h₁.continuousAt.preimage_mem_nhds (e.open_source.mem_nhds hae)
    have h2 : {b : A | g₂ b ∈ e.source} ∈ 𝓝 a :=
      h₂.continuousAt.preimage_mem_nhds (e.open_source.mem_nhds (ha ▸ hae))
    refine Filter.mem_of_superset (Filter.inter_mem h1 h2) ?_
    rintro b ⟨hb1, hb2⟩
    exact e.injOn hb1 hb2 (heq b)
  have hne : ({a : A | g₁ a = g₂ a}).Nonempty := ⟨a₀, ha⟩
  have huniv : {a : A | g₁ a = g₂ a} = Set.univ := IsClopen.eq_univ ⟨hclosed, hopen⟩ hne
  funext a
  have : a ∈ {a : A | g₁ a = g₂ a} := by rw [huniv]; trivial
  exact this

/-- **Uniqueness of lifts through the exponential map**: two continuous `W : A → T_pM` with
`GExp p ∘ W` equal and `W` equal at one point of a preconnected `A` coincide. -/
theorem lift_unique_GExp
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    (hK : ∀ K : ℝ, 0 < K → Submission.RauchK.CurvLe cov K) (p : M)
    {A : Type*} [TopologicalSpace A] [PreconnectedSpace A]
    {g₁ g₂ : A → TangentSpace I p} (h₁ : Continuous g₁) (h₂ : Continuous g₂)
    (heq : ∀ a : A, Submission.GlobalExp.GExp (cov := cov) hmet p (g₁ a)
      = Submission.GlobalExp.GExp (cov := cov) hmet p (g₂ a))
    {a₀ : A} (ha : g₁ a₀ = g₂ a₀) : g₁ = g₂ :=
  lift_unique_of_isLocalHomeomorph (isLocalHomeomorph_GExp (cov := cov) hmet htor hK p)
    h₁ h₂ heq ha

/-! ## §4 The fibres of a local homeomorphism are discrete -/

/-- **The fibre of a local homeomorphism is discrete.** -/
theorem discreteTopology_fiber_of_isLocalHomeomorph {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] (F : X → Y) (hF : IsLocalHomeomorph F) (y : Y) :
    DiscreteTopology (F ⁻¹' {y}) := by
  rw [discreteTopology_subtype_iff']
  intro x hx
  obtain ⟨e, hxe, heqe⟩ := hF x
  subst heqe
  refine ⟨e.source, e.open_source, ?_⟩
  ext u
  constructor
  · intro hu
    have hu1 : u ∈ e.source := hu.1
    have hu2 : e u = y := hu.2
    simp only [Set.mem_singleton_iff]
    exact e.injOn hu1 hxe (by rw [hu2, hx])
  · intro hu
    rw [Set.mem_singleton_iff] at hu
    subst hu
    exact ⟨hxe, hx⟩

/-- The fibre of `GExp p` over `y` is discrete. -/
theorem discreteTopology_fiber_GExp
    (hmet : IsMetricCompatible cov) (htor : cov.torsion = 0)
    (hK : ∀ K : ℝ, 0 < K → Submission.RauchK.CurvLe cov K) (p y : M) :
    DiscreteTopology ((fun v : TangentSpace I p => Submission.GlobalExp.GExp (cov := cov) hmet p v)
      ⁻¹' {y}) :=
  discreteTopology_fiber_of_isLocalHomeomorph _
    (isLocalHomeomorph_GExp (cov := cov) hmet htor hK p) y

end

end Work.CartanHadamard
