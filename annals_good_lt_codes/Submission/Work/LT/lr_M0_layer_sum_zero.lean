import Mathlib
import Submission.Work.LT.lr_local_defs

/-!
# The layer sums of `M₀` vanish on mean-zero functions

`M₀` is the "average of a random A-step and a random B-step" operator
(`Work.LT.M0`).  Its A- (resp. B-) steps move the group coordinate by left (resp. right)
multiplication by `A i` (resp. `B j`), which is a bijection of `G`.  Hence if `h` has zero
mean on every layer `(γ,δ,·)`, so does `M₀ h`.

This is the elementary input used to propagate the "the walk kills the mean" property.
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Work.LT

open Classical
open scoped BigOperators

variable {G : Type*} [Group G] [Fintype G] {Δ : ℕ}

/-- Reindexing a sum over a group by left multiplication. -/
lemma sum_mul_left {M : Type*} [AddCommMonoid M] (a : G) (f : G → M) :
    (∑ g : G, f (a * g)) = ∑ g : G, f g :=
  Equiv.sum_comp (Equiv.mulLeft a) f

/-- Reindexing a sum over a group by right multiplication. -/
lemma sum_mul_right {M : Type*} [AddCommMonoid M] (a : G) (f : G → M) :
    (∑ g : G, f (g * a)) = ∑ g : G, f g :=
  Equiv.sum_comp (Equiv.mulRight a) f

/-- A single A-step of `M₀` preserves the vanishing of the layer sum. -/
lemma sum_nA_zero (A : Fin Δ → G) (h : Vtx G → ℝ)
    (hh : ∀ γ δ : Fin 2, ∑ g : G, h (γ, δ, g) = 0) (α β : Fin 2) (i : Fin Δ) :
    (∑ g : G, h (nA A (α, β, g) i)) = 0 := by
  calc ∑ g : G, h (nA A (α, β, g) i)
      = ∑ g : G, h (α + 1, β, (if α = 0 then A i else (A i)⁻¹) * g) := by
        refine Finset.sum_congr rfl fun g _ => ?_
        fin_cases α <;> simp [nA]
    _ = ∑ g : G, h (α + 1, β, g) :=
        sum_mul_left (if α = 0 then A i else (A i)⁻¹) (fun g => h (α + 1, β, g))
    _ = 0 := hh (α + 1) β

/-- A single B-step of `M₀` preserves the vanishing of the layer sum. -/
lemma sum_nB_zero (B : Fin Δ → G) (h : Vtx G → ℝ)
    (hh : ∀ γ δ : Fin 2, ∑ g : G, h (γ, δ, g) = 0) (α β : Fin 2) (j : Fin Δ) :
    (∑ g : G, h (nB B (α, β, g) j)) = 0 := by
  calc ∑ g : G, h (nB B (α, β, g) j)
      = ∑ g : G, h (α, β + 1, g * (if β = 0 then B j else (B j)⁻¹)) := by
        refine Finset.sum_congr rfl fun g _ => ?_
        fin_cases β <;> simp [nB]
    _ = ∑ g : G, h (α, β + 1, g) :=
        sum_mul_right (if β = 0 then B j else (B j)⁻¹) (fun g => h (α, β + 1, g))
    _ = 0 := hh α (β + 1)

theorem lr_M0_layer_sum_zero {G : Type} [Group G] [Fintype G] {Δ : ℕ} (A B : Fin Δ → G)
    (h : Vtx G → ℝ) (hh : ∀ α β : Fin 2, ∑ g : G, h (α, β, g) = 0) (α β : Fin 2) :
    (∑ g : G, M0 A B h (α, β, g)) = 0 := by
  have hA : (∑ g : G, ∑ i : Fin Δ, h (nA A (α, β, g) i)) = 0 := by
    rw [Finset.sum_comm]
    simp [sum_nA_zero A h hh]
  have hB : (∑ g : G, ∑ j : Fin Δ, h (nB B (α, β, g) j)) = 0 := by
    rw [Finset.sum_comm]
    simp [sum_nB_zero B h hh]
  have hnum : (∑ g : G, ((∑ i, h (nA A (α, β, g) i)) + (∑ j, h (nB B (α, β, g) j)))) = 0 := by
    rw [Finset.sum_add_distrib, hA, hB, add_zero]
  simp only [M0]
  rw [← Finset.sum_div, hnum, zero_div]

end Work.LT
