import Mathlib
import Submission.Work.LT.lr_local_defs
import Submission.Work.LT.lr_M0_layerConst_A
import Submission.Work.LT.lr_M0_layerConst_B

/-!
# The `M₀`-form of a layer-constant function is nonpositive

For a *layer-constant* function `f (α, β, g) = c α β` on the vertices `Vtx G = Fin 2 × Fin 2 × G`,
the quadratic form of the vertex operator `M₀ = ½(M_A + M_B)` is

`⟨f, M₀ f⟩ = |G| · (c₀₀ + c₁₁) · (c₀₁ + c₁₀)`.

The normalisation `∑_{α,β} c α β = 0` turns this into `-|G| · (c₀₁ + c₁₀)² ≤ 0`.

The two halves of the computation (the `A`-step and the `B`-step) are
`Work.LT.lr_M0_layerConst_A` and `Work.LT.lr_M0_layerConst_B`; the present file assembles them,
peels off the `1/(2Δ)` of `M₀` and finishes with the algebraic identity implied by `hc`.
-/

namespace Work.LT

open scoped BigOperators

/-- **The `M₀`-quadratic form of a layer-constant function.**  With `f v = c v.1 v.2.1` one has
`∑_v f v * M₀ f v = |G| · (c₀₀ + c₁₁) · (c₀₁ + c₁₀)`; combined with `∑ c α β = 0` this is
`-|G| (c₀₁ + c₁₀)² ≤ 0`. -/
theorem lr_M0_layerConst_form {G : Type} [Group G] [Fintype G] {Δ : ℕ} (A B : Fin Δ → G)
    (c : Fin 2 → Fin 2 → ℝ) (hc : ∑ α : Fin 2, ∑ β : Fin 2, c α β = 0) :
    (∑ v : Vtx G, c v.1 v.2.1 * M0 A B (fun v => c v.1 v.2.1) v) ≤ 0 := by
  set f : Vtx G → ℝ := fun w => c w.1 w.2.1 with hf
  have hgoal : (∑ v : Vtx G, c v.1 v.2.1 * M0 A B (fun v => c v.1 v.2.1) v)
      = (∑ v : Vtx G, f v * M0 A B f v) := rfl
  rw [hgoal]
  -- Peel off the `1/(2Δ)` of `M₀` and split the two edge families.
  have hsplit : (∑ v : Vtx G, f v * M0 A B f v)
      = (2 * (Δ : ℝ))⁻¹ *
          (∑ v : Vtx G, f v * ((∑ i : Fin Δ, f (nA A v i)) + (∑ j : Fin Δ, f (nB B v j)))) := by
    simp only [M0]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro v _
    rw [div_eq_mul_inv]
    ring
  -- The two halves of the computation.
  have hkey : (∑ v : Vtx G, f v * ((∑ i : Fin Δ, f (nA A v i)) + (∑ j : Fin Δ, f (nB B v j))))
      = 2 * (Fintype.card G : ℝ) * (Δ : ℝ) * ((c 0 0 + c 1 1) * (c 0 1 + c 1 0)) := by
    have hA := lr_M0_layerConst_A (G := G) A c
    have hB := lr_M0_layerConst_B (G := G) B c
    simp only [hf, mul_add, Finset.sum_add_distrib]
    rw [hA, hB]
    ring
  have hT : (∑ v : Vtx G, f v * M0 A B f v)
      = ((2 * (Δ : ℝ))⁻¹ * (2 * (Δ : ℝ))) *
          ((Fintype.card G : ℝ) * ((c 0 0 + c 1 1) * (c 0 1 + c 1 0))) := by
    rw [hsplit, hkey]
    ring
  rw [hT]
  -- `∑ c α β = 0` gives `c₀₀ + c₁₁ = -(c₀₁ + c₁₀)`.
  have hc' : c 0 0 + c 1 1 = -(c 0 1 + c 1 0) := by
    have h := hc
    simp only [Fin.sum_univ_two] at h
    linarith
  have hsq : (0 : ℝ) ≤ (c 0 1 + c 1 0) ^ 2 := sq_nonneg _
  have hk : 0 ≤ (2 * (Δ : ℝ))⁻¹ * (2 * (Δ : ℝ)) := by
    have h2 : (0 : ℝ) ≤ 2 * (Δ : ℝ) := by positivity
    exact mul_nonneg (inv_nonneg.mpr h2) h2
  have hcard : (0 : ℝ) ≤ (Fintype.card G : ℝ) := by positivity
  have hprod : 0 ≤ ((2 * (Δ : ℝ))⁻¹ * (2 * (Δ : ℝ))) *
      ((Fintype.card G : ℝ) * (c 0 1 + c 1 0) ^ 2) :=
    mul_nonneg hk (mul_nonneg hcard hsq)
  have heq : ((2 * (Δ : ℝ))⁻¹ * (2 * (Δ : ℝ))) *
        ((Fintype.card G : ℝ) * ((c 0 0 + c 1 1) * (c 0 1 + c 1 0)))
      = -(((2 * (Δ : ℝ))⁻¹ * (2 * (Δ : ℝ))) *
        ((Fintype.card G : ℝ) * (c 0 1 + c 1 0) ^ 2)) := by
    rw [hc']; ring
  rw [heq]
  linarith

end Work.LT
