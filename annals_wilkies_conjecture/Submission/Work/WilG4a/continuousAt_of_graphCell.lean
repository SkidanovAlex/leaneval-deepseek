import Mathlib

namespace Work.WilG4a

open Filter Topology

/-- The "diagonal" embedding `ℝ → (Fin 1 → ℝ)`, `t ↦ (fun _ => t)`, is continuous. -/
theorem continuous_diag_fin1 : Continuous (fun t : ℝ => fun _ : Fin 1 => t) :=
  continuous_pi fun _ => continuous_id

/-- If `f : ℝ → ℝ` agrees, through the graph-cell map `p ↦ p 0`, with a function `ψ`
that is continuous on an open set `C0 ∋ (fun _ => x)`, then `f` is continuous at `x`.

Indeed the diagonal embedding `emb : t ↦ (fun _ => t)` is continuous, `emb ⁻¹' C0` is an
open neighbourhood of `x` on which `f = ψ ∘ emb`, and `ψ ∘ emb` is continuous at `x`. -/
theorem continuousAt_of_graphCell {C0 : Set (Fin 1 → ℝ)} {ψ : (Fin 1 → ℝ) → ℝ} {f : ℝ → ℝ} {x : ℝ}
    (hopen : IsOpen C0) (hcont : ContinuousOn ψ C0)
    (hmem : (fun _ : Fin 1 => x) ∈ C0)
    (hagree : ∀ p ∈ C0, ψ p = f (p 0)) : ContinuousAt f x := by
  -- The diagonal embedding `emb : ℝ → (Fin 1 → ℝ)`, `t ↦ (fun _ => t)`.
  let emb : ℝ → (Fin 1 → ℝ) := fun t => fun _ => t
  have hemb : Continuous emb := continuous_diag_fin1
  -- `C0` is a neighbourhood of the diagonal point `emb x`.
  have hC0 : C0 ∈ 𝓝 (emb x) := hopen.mem_nhds hmem
  -- `ψ` is continuous at that point, so `ψ ∘ emb` is continuous at `x`.
  have hψ : ContinuousAt ψ (emb x) := hcont.continuousAt hC0
  have hcomp : ContinuousAt (fun t => ψ (emb t)) x := hψ.comp hemb.continuousAt
  -- On the open neighbourhood `emb ⁻¹' C0` of `x`, `f` coincides with `ψ ∘ emb`.
  have hU : emb ⁻¹' C0 ∈ 𝓝 x := hemb.continuousAt.preimage_mem_nhds hC0
  have heq : (fun t => ψ (emb t)) =ᶠ[𝓝 x] f := by
    filter_upwards [hU] with t ht
    have h : ψ (emb t) = f ((emb t) 0) := hagree (emb t) ht
    rw [h]
  exact hcomp.congr heq

end Work.WilG4a
