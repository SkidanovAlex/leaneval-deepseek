import Mathlib
import Submission.Work.LT.lr_local_defs

/-!
# The `A`-step layer constant of `M₀`

For a function `k : Vtx G → ℝ` that is constant along the group coordinate,
`k (α,β,g) = c α β`, the value of `∑ i, k (nA A v i)` at `v = (α,β,g)` does not depend on
`g` at all: an `A`-step only flips the first coordinate `α ↦ α + 1` and keeps the second
coordinate `β` fixed.  Hence

  `∑ i, k (nA A (α,β,g) i) = Δ * c (α + 1) β`

and summing over the `G`-coordinate contributes a factor `|G|` per layer `(α,β)`.  The four
layers give

  `∑_v c v.1 v.2.1 * ∑_i c (nA A v i).1 (nA A v i).2.1
     = |G| Δ (c 0 0 · c 1 0 + c 0 1 · c 1 1 + c 1 0 · c 0 0 + c 1 1 · c 0 1)`,

which is the stated constant.  This is the identity used to check that `M₀` has the correct
constant value on layer-constant functions (one-sidedness of `M₀` on `1^⊥`).
-/

set_option autoImplicit false

namespace Work.LT

open scoped BigOperators

/-- The value of a layer-constant function at an `A`-neighbour of `(α,β,g)` depends only on
`α + 1` and `β`. -/
lemma c_nA_val {G : Type} [Group G] {Δ : ℕ} (A : Fin Δ → G) (c : Fin 2 → Fin 2 → ℝ)
    (α β : Fin 2) (g : G) (i : Fin Δ) :
    c (nA A (α,β,g) i).1 (nA A (α,β,g) i).2.1 = c (α + 1) β := by
  fin_cases α <;> simp [nA]

theorem lr_M0_layerConst_A {G : Type} [Group G] [Fintype G] {Δ : ℕ} (A : Fin Δ → G)
    (c : Fin 2 → Fin 2 → ℝ) :
    (∑ v : Vtx G, c v.1 v.2.1 * (∑ i : Fin Δ, c (nA A v i).1 (nA A v i).2.1))
      = 2 * (Fintype.card G : ℝ) * (Δ : ℝ) * (c 0 0 * c 1 0 + c 0 1 * c 1 1) := by
  have hnAval : ∀ (α β : Fin 2) (g : G) (i : Fin Δ),
      c (nA A (α,β,g) i).1 (nA A (α,β,g) i).2.1 = c (α + 1) β :=
    fun α β g i => c_nA_val A c α β g i
  -- Fibre the vertex sum over the two `Fin 2` coordinates and over `G`.
  rw [show (∑ v : Vtx G, c v.1 v.2.1 * (∑ i : Fin Δ, c (nA A v i).1 (nA A v i).2.1))
      = ∑ α : Fin 2, ∑ β : Fin 2, ∑ g : G,
          c α β * (∑ i : Fin Δ, c (nA A (α,β,g) i).1 (nA A (α,β,g) i).2.1) from by
        simp [Vtx, Fintype.sum_prod_type]]
  simp only [hnAval]
  -- Each `(α,β)`-layer contributes `|G|` copies of `c α β * (Δ * c (α+1) β)`.
  trans ∑ α : Fin 2, ∑ β : Fin 2, (Fintype.card G : ℝ) * (c α β * ((Δ : ℝ) * c (α + 1) β))
  · refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun β _ => ?_
    simp [Finset.sum_const, Fintype.card_fin, nsmul_eq_mul]
  · simp only [Fin.sum_univ_two]
    norm_num
    ring

end Work.LT
