import Mathlib
import Submission.Work.LT.lr_local_defs

/-! Orthogonality of the vertex operator `M₀` to layer-constant functions.

If `u : Vtx G → ℝ` has vanishing sum along every layer `(α,β,_)` and `k : Vtx G → ℝ` is
*constant on the `G`-coordinate* (`k w = c w.1 w.2.1`), then `∑_v u v * M₀ k v = 0`.

Indeed `M₀ k` is again constant on the `G`-coordinate: at `(α,β,g)` every A-neighbour lies in
layer `(flip α, β)` and every B-neighbour in layer `(α, flip β)`, so

  `M₀ k (α,β,g) = (Δ * c (flip α) β + Δ * c α (flip β)) / (2Δ)`,

independent of `g`; summing against `u` then fibres the sum over `(α,β)` and each `G`-fiber
contributes `∑_g u (α,β,g) = 0`. -/

set_option autoImplicit false

namespace Work.LT

open scoped BigOperators

theorem lr_M0_cross_const {G : Type} [Group G] [Fintype G] {Δ : ℕ} (A B : Fin Δ → G)
    (c : Fin 2 → Fin 2 → ℝ) (u : Vtx G → ℝ) (hu : ∀ α β : Fin 2, ∑ g : G, u (α, β, g) = 0) :
    (∑ v : Vtx G, u v * M0 A B (fun w => c w.1 w.2.1) v) = 0 := by
  -- `k := fun w => c w.1 w.2.1` depends only on the first two coordinates.
  -- Value of `k` at an A-neighbour of `(α,β,g)`: lives in layer `(flip α, β)`.
  have hnA : ∀ (α β : Fin 2) (g : G) (i : Fin Δ),
      (fun w : Vtx G => c w.1 w.2.1) (nA A (α,β,g) i) = c (if α = 0 then 1 else 0) β := by
    intro α β g i
    simp only [nA]
    split_ifs with h <;> simp
  -- Value of `k` at a B-neighbour of `(α,β,g)`: lives in layer `(α, flip β)`.
  have hnB : ∀ (α β : Fin 2) (g : G) (j : Fin Δ),
      (fun w : Vtx G => c w.1 w.2.1) (nB B (α,β,g) j) = c α (if β = 0 then 1 else 0) := by
    intro α β g j
    simp only [nB]
    split_ifs with h <;> simp
  -- `M₀ k` is constant along `G`.
  have hM : ∀ (α β : Fin 2) (g : G),
      M0 A B (fun w => c w.1 w.2.1) (α,β,g)
        = ((∑ i : Fin Δ, c (if α = 0 then 1 else 0) β)
            + (∑ j : Fin Δ, c α (if β = 0 then 1 else 0))) / (2*Δ) := by
    intro α β g
    simp only [M0]
    rw [show (∑ i : Fin Δ, (fun w : Vtx G => c w.1 w.2.1) (nA A (α,β,g) i))
          = ∑ i : Fin Δ, c (if α = 0 then 1 else 0) β from
            Finset.sum_congr rfl (fun i _ => hnA α β g i),
        show (∑ j : Fin Δ, (fun w : Vtx G => c w.1 w.2.1) (nB B (α,β,g) j))
          = ∑ j : Fin Δ, c α (if β = 0 then 1 else 0) from
            Finset.sum_congr rfl (fun j _ => hnB α β g j)]
  -- Fibre the vertex sum over the two `Fin 2` coordinates and `G`.
  have hsplit : (∑ v : Vtx G, u v * M0 A B (fun w => c w.1 w.2.1) v)
      = ∑ α : Fin 2, ∑ β : Fin 2, ∑ g : G,
          u (α,β,g) * M0 A B (fun w => c w.1 w.2.1) (α,β,g) := by
    simp [Vtx, Fintype.sum_prod_type]
  rw [hsplit]
  simp only [hM]
  apply Finset.sum_eq_zero
  intro α _
  apply Finset.sum_eq_zero
  intro β _
  rw [← Finset.sum_mul, hu α β, zero_mul]

end Work.LT
