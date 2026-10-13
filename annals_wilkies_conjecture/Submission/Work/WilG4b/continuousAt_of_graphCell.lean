import Mathlib

namespace Work.WilG4b

open Filter Topology

/-- `Fin 1 → ℝ` is (topologically) `ℝ` via the `0`-th coordinate: the "diagonal"
embedding `t ↦ (fun _ => t)` is continuous. -/
theorem continuous_diag_fin1 : Continuous (fun t : ℝ => fun _ : Fin 1 => t) := by
  apply continuous_pi
  intro i
  exact continuous_id

theorem continuousAt_of_graphCell {C0 : Set (Fin 1 → ℝ)} {ψ : (Fin 1 → ℝ) → ℝ} {f : ℝ → ℝ} {x : ℝ}
    (hopen : IsOpen C0) (hcont : ContinuousOn ψ C0)
    (hmem : (fun _ : Fin 1 => x) ∈ C0)
    (hagree : ∀ p ∈ C0, ψ p = f (p 0)) : ContinuousAt f x := by
  -- The diagonal embedding `emb : ℝ → (Fin 1 → ℝ)`, `t ↦ (fun _ => t)`.
  have hemb : Continuous (fun t : ℝ => fun _ : Fin 1 => t) := continuous_diag_fin1
  -- `ψ` is continuous at the point `(fun _ => x)`, since `C0` is a neighbourhood of it.
  have hpsi : ContinuousAt (fun t : ℝ => ψ (fun _ : Fin 1 => t)) x := by
    have h1 : ContinuousAt ψ (fun _ : Fin 1 => x) :=
      hcont.continuousAt (IsOpen.mem_nhds hopen hmem)
    have h2 : ContinuousAt (fun t : ℝ => fun _ : Fin 1 => t) x := hemb.continuousAt
    exact h1.comp h2
  -- On the open neighbourhood `emb ⁻¹' C0` of `x`, the function `f` agrees with this
  -- continuous function, by the graph-cell agreement hypothesis.
  have heq : (fun t : ℝ => ψ (fun _ : Fin 1 => t)) =ᶠ[𝓝 x] f := by
    refine Set.EqOn.eventuallyEq_of_mem (s := (fun t : ℝ => fun _ : Fin 1 => t) ⁻¹' C0) ?_ ?_
    · intro t ht
      change ψ (fun _ : Fin 1 => t) = f t
      rw [hagree (fun _ : Fin 1 => t) ht]
    · exact IsOpen.mem_nhds (hopen.preimage hemb) (by simpa using hmem)
  exact hpsi.congr heq

end Work.WilG4b
