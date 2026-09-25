import Mathlib
import Submission.Work.LT.lr_local_defs

/-!
# `lr_MA_form`: the `⟨1, M_A 1⟩` identity

The vertex operator `M_A` (average of `h` over the `Δ` A-neighbours) is symmetric, so its
quadratic form on the all-ones vector can be evaluated by grouping the vertices `(α,β,g)` in two
layers.  Writing the sum over `Vtx G = Fin 2 × Fin 2 × G` as a double layer sum, the layer `α = 1`
contribution is the layer `α = 0` contribution reindexed along the bijection `g ↦ A i * g` of the
group; hence the total is twice the layer `α = 0` contribution. -/

namespace Work.LT

open Classical
open scoped BigOperators

/-- Summation over `G` is invariant under left translation. -/
lemma lr_MA_sum_mulLeft {G : Type*} [Group G] [Fintype G] (a : G) (F : G → ℝ) :
    (∑ x, F (a * x)) = ∑ x, F x := Equiv.sum_comp (Equiv.mulLeft a) F

/-- The layer `α = 1` contribution to the quadratic form equals the layer `α = 0` contribution
for each fixed `β`: the substitution `g ↦ A i * g` turns `h (1,β,g) * h (0,β,(A i)⁻¹ * g)` into
`h (1,β,A i * g) * h (0,β,g)`. -/
lemma lr_MA_key_reindex {G : Type*} [Group G] [Fintype G] {Δ : ℕ} (A : Fin Δ → G)
    (h : Vtx G → ℝ) (β : Fin 2) :
    (∑ g : G, h (1, β, g) * ((∑ i : Fin Δ, h (0, β, (A i)⁻¹ * g)) / (Δ : ℝ)))
      = ∑ g : G, h (0, β, g) * ((∑ i : Fin Δ, h (1, β, A i * g)) / (Δ : ℝ)) := by
  calc (∑ g : G, h (1, β, g) * ((∑ i : Fin Δ, h (0, β, (A i)⁻¹ * g)) / (Δ : ℝ)))
      = ∑ g : G, h (1, β, g) * (∑ i : Fin Δ, h (0, β, (A i)⁻¹ * g) / (Δ : ℝ)) := by
        exact Finset.sum_congr rfl (fun g _ => by rw [Finset.sum_div])
    _ = ∑ g : G, ∑ i : Fin Δ, h (1, β, g) * (h (0, β, (A i)⁻¹ * g) / (Δ : ℝ)) := by
        exact Finset.sum_congr rfl (fun g _ => by rw [Finset.mul_sum])
    _ = ∑ g : G, ∑ i : Fin Δ, h (1, β, g) * h (0, β, (A i)⁻¹ * g) / (Δ : ℝ) := by
        exact Finset.sum_congr rfl
          (fun g _ => Finset.sum_congr rfl (fun i _ => by rw [← mul_div_assoc]))
    _ = ∑ i : Fin Δ, ∑ g : G, h (1, β, g) * h (0, β, (A i)⁻¹ * g) / (Δ : ℝ) := by
        rw [Finset.sum_comm]
    _ = ∑ i : Fin Δ, ∑ g : G, h (1, β, A i * g) * h (0, β, g) / (Δ : ℝ) := by
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [← lr_MA_sum_mulLeft (A i)
          (fun g => h (1, β, g) * h (0, β, (A i)⁻¹ * g) / (Δ : ℝ))]
        refine Finset.sum_congr rfl (fun g _ => ?_)
        simp only [inv_mul_cancel_left]
    _ = ∑ i : Fin Δ, ∑ g : G, h (0, β, g) * h (1, β, A i * g) / (Δ : ℝ) := by
        exact Finset.sum_congr rfl
          (fun i _ => Finset.sum_congr rfl (fun g _ => by rw [mul_comm]))
    _ = ∑ g : G, ∑ i : Fin Δ, h (0, β, g) * h (1, β, A i * g) / (Δ : ℝ) := by
        rw [Finset.sum_comm]
    _ = ∑ g : G, ∑ i : Fin Δ, h (0, β, g) * (h (1, β, A i * g) / (Δ : ℝ)) := by
        exact Finset.sum_congr rfl
          (fun g _ => Finset.sum_congr rfl (fun i _ => by rw [mul_div_assoc]))
    _ = ∑ g : G, h (0, β, g) * (∑ i : Fin Δ, h (1, β, A i * g) / (Δ : ℝ)) := by
        exact Finset.sum_congr rfl (fun g _ => by rw [Finset.mul_sum])
    _ = ∑ g : G, h (0, β, g) * ((∑ i : Fin Δ, h (1, β, A i * g)) / (Δ : ℝ)) := by
        exact Finset.sum_congr rfl (fun g _ => by rw [Finset.sum_div])

theorem lr_MA_form {G : Type} [Group G] [Fintype G] {Δ : ℕ} (A : Fin Δ → G) (h : Vtx G → ℝ) :
    (∑ v : Vtx G, h v * ((∑ i : Fin Δ, h (nA A v i)) / (Δ : ℝ)))
      = 2 * ∑ β : Fin 2, ∑ g : G,
          h (0, β, g) * ((∑ i : Fin Δ, h (1, β, A i * g)) / (Δ : ℝ)) := by
  -- Split the sum over `Vtx G = Fin 2 × Fin 2 × G` into its two layers `α = 0` and `α = 1`.
  have hdecomp : (∑ v : Vtx G, h v * ((∑ i : Fin Δ, h (nA A v i)) / (Δ : ℝ)))
      = (∑ β : Fin 2, ∑ g : G, h (0, β, g) * ((∑ i : Fin Δ, h (1, β, A i * g)) / (Δ : ℝ)))
       + (∑ β : Fin 2, ∑ g : G,
            h (1, β, g) * ((∑ i : Fin Δ, h (0, β, (A i)⁻¹ * g)) / (Δ : ℝ))) := by
    rw [Fintype.sum_prod_type]
    simp only [Fintype.sum_prod_type, Fin.sum_univ_two]
    congr 1
  -- The two layers agree, term by term in `β`.
  have hkey : (∑ β : Fin 2, ∑ g : G,
          h (1, β, g) * ((∑ i : Fin Δ, h (0, β, (A i)⁻¹ * g)) / (Δ : ℝ)))
      = ∑ β : Fin 2, ∑ g : G, h (0, β, g) * ((∑ i : Fin Δ, h (1, β, A i * g)) / (Δ : ℝ)) := by
    exact Finset.sum_congr rfl (fun β _ => lr_MA_key_reindex A h β)
  rw [hdecomp, hkey]
  ring

end Work.LT
