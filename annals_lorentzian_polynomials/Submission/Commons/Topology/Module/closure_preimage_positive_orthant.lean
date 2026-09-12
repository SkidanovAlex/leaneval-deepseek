import Mathlib.Topology.Algebra.Module.ModuleTopology
import Mathlib.Topology.Algebra.Ring.Real

open Set Topology

namespace Commons.Topology.Module

theorem closure_preimage_positive_orthant
  {ι : Type*} [Fintype ι]
  {E : Type*} [AddCommGroup E] [Module ℝ E] [TopologicalSpace E] [IsModuleTopology ℝ E]
  (e : E ≃ₗ[ℝ] (ι → ℝ)) :
  closure {x : E | ∀ i, 0 < e x i} = {x : E | ∀ i, 0 ≤ e x i} := by
  have hcontE : ContinuousAdd E := IsModuleTopology.toContinuousAdd ℝ E
  let e' : E ≃L[ℝ] (ι → ℝ) :=
  { e with
    continuous_toFun := IsModuleTopology.continuous_of_linearMap e.toLinearMap
    continuous_invFun := @IsModuleTopology.continuous_of_linearMap ℝ _ _ (ι → ℝ) _ _ _ _ E _ _ _ hcontE _ e.symm.toLinearMap }
  let S : Set (ι → ℝ) := {f | ∀ i, 0 < f i}
  let T : Set (ι → ℝ) := {f | ∀ i, 0 ≤ f i}
  have hS : S = Set.pi Set.univ (fun i : ι => Set.Ioi (0 : ℝ)) := by
    ext f
    simp [S, Set.pi]
  have hT : T = Set.pi Set.univ (fun i : ι => Set.Ici (0 : ℝ)) := by
    ext f
    simp [T, Set.pi]
  have hclS : closure S = T := by
    rw [hS, hT, closure_pi_set]
    ext f
    simp [Set.pi, closure_Ioi]
  calc
    closure {x : E | ∀ i, 0 < e x i}
        = closure (e ⁻¹' S) := by
            ext x
            simp [S]
    _ = e ⁻¹' closure S := by
            change closure (e' ⁻¹' S) = e' ⁻¹' closure S
            exact (e'.preimage_closure S).symm
    _ = e ⁻¹' T := by rw [hclS]
    _ = {x : E | ∀ i, 0 ≤ e x i} := by
            ext x
            simp [T]

end Commons.Topology.Module