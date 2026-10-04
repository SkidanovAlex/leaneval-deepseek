import Mathlib
import Submission.Work.Diff.Dim2.Lib
import Submission.Work.Diff.Dim2.Azim
import Submission.Work.Diff.Dim2.transferSph

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.Dim2

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter Submission.Geodesic

theorem transferSph2
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    [RiemannianBundle (fun x : M ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)]
    [I.Boundaryless] [Nontrivial E] [CompactSpace M] [PathConnectedSpace M] [RegularSpace M]
    {N : Set M} (hN : IsOpen N)
    {V : (x : M) → TangentSpace I x}
    (hVsm : ContMDiff I (I.prod (modelWithCornersSelf ℝ E)) ∞
      (fun y : M => (⟨y, V y⟩ : Bundle.TotalSpace E (TangentSpace I))))
    {u v : M → EuclideanSpace ℝ (Fin 2)}
    (hu : ContMDiffOn I 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) ∞ u N)
    (hv : ContMDiffOn I 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) ∞ v N)
    (hu1 : ∀ x ∈ N, ‖u x‖ = 1) (hv1 : ∀ x ∈ N, ‖v x‖ = 1)
    (huV : ∀ x ∈ N, mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) u x (V x) = 0)
    (hvV : ∀ x ∈ N, mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) v x (V x) = 0)
    (huinj : ∀ x ∈ N, mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) u x ≠ 0)
    (hvinj : ∀ x ∈ N, mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) v x ≠ 0)
    (huv : ∀ x ∈ N, ∀ y ∈ N, u x = u y → v x = v y)
    (hvu : ∀ x ∈ N, ∀ y ∈ N, v x = v y → u x = u y)
    (husurj : ∀ z : EuclideanSpace ℝ (Fin 2), ‖z‖ = 1 → ∃ x ∈ N, u x = z) :
    ∃ (s : ℝ) (ρ : ℝ → ℝ), (s = 1 ∨ s = -1) ∧ ContDiff ℝ ∞ ρ ∧
      (∀ θ : ℝ, 0 < deriv ρ θ) ∧
      (∀ θ : ℝ, ρ (θ + 2 * Real.pi) = ρ θ + 2 * Real.pi) ∧
      (∀ x ∈ N, reflE s (v x) = rotE (ρ (argE (u x)) - argE (u x)) (u x)) := by
  classical
  have hsurj : ∀ θ : ℝ, ∃ x : M, x ∈ N ∧ u x = circPt θ :=
    fun θ => husurj (circPt θ) (norm_circPt θ)
  choose w hwN hwu using hsurj
  set κ : ℝ → EuclideanSpace ℝ (Fin 2) := fun θ => v (w θ) with hκ_eq
  have hκvd : ∀ θ : ℝ, κ θ = v (w θ) := fun θ => congrFun hκ_eq θ
  have hκper : ∀ θ : ℝ, κ (θ + 2 * Real.pi) = κ θ := by
    intro θ
    have h : u (w (θ + 2 * Real.pi)) = u (w θ) := by
      rw [hwu (θ + 2 * Real.pi), hwu θ]
      simpa using circPt_periodic θ (1 : ℤ)
    exact huv _ (hwN _) _ (hwN _) h
  have hκunit : ∀ θ : ℝ, ‖κ θ‖ = 1 := fun θ => hv1 (w θ) (hwN θ)
  have hκinj : Set.InjOn κ (Set.Ico 0 (2 * Real.pi)) := by
    intro θ hθ θ' hθ' heq
    have hu' : u (w θ) = u (w θ') := hvu _ (hwN θ) _ (hwN θ') heq
    rw [hwu θ, hwu θ'] at hu'
    exact circPt_injOn hθ hθ' hu'
  have hsm : ContDiff ℝ ∞ κ := by
    rw [contDiff_iff_contDiffAt]
    intro θ
    exact (kappa_local hN hu hu1 huinj hv hv1 hvinj huv hwN hwu hκvd θ).1
  have hang : ∀ θ : ℝ, angVel κ θ ≠ 0 := fun θ =>
    (kappa_local hN hu hu1 huinj hv hv1 hvinj huv hwN hwu hκvd θ).2
  obtain ⟨s, ρ, hs, hρsm, hρd, hρper, hρcs⟩ :=
    lift_monotone hsm hκper hκunit hκinj hang
  have hκevx : ∀ x ∈ N, κ (argE (u x)) = v x := by
    intro x hx
    have h : u (w (argE (u x))) = u x :=
      (hwu (argE (u x))).trans (circPt_argE (hu1 x hx))
    exact huv _ (hwN _) x hx h
  refine ⟨s, ρ, hs, hρsm, hρd, hρper, ?_⟩
  intro x hx
  exact transfer_convert (s := s) (ρ := ρ) (κ := κ) (ux := u x) (vx := v x)
    (hρcs (argE (u x))).1 (hρcs (argE (u x))).2 (hκevx x hx) (hu1 x hx)

end Work.Diff.Dim2
