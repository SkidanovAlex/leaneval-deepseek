import Mathlib
import Submission.Work.LT.lr_local_defs

namespace Work.LT

set_option autoImplicit false

open scoped BigOperators

variable {G : Type} [Group G] [Fintype G] {Δ : ℕ}

/-- Value of `classOpA` at a vertex with first coordinate `0`: the average of the input over the
opposite layer, left-translated by the `A i`. -/
lemma classOpA_apply_zero (A : Fin Δ → G) (s : Fin 2 × G → ℝ) (g : G) :
    classOpA A s (0, g) = (∑ i, s (1, A i * g)) / Δ := by
  simp [classOpA]

/-- Value of `classOpA` at a vertex with first coordinate `1`. -/
lemma classOpA_apply_one (A : Fin Δ → G) (s : Fin 2 × G → ℝ) (g : G) :
    classOpA A s (1, g) = (∑ i, s (0, (A i)⁻¹ * g)) / Δ := by
  simp [classOpA]

/-- Sum of `classOpA A x` over the layer with first coordinate `0` is the total mass of `x` on the
layer with first coordinate `1`. -/
lemma classOpA_sum_zero (hΔ : 0 < Δ) (A : Fin Δ → G) (x : Fin 2 × G → ℝ) :
    (∑ g, classOpA A x (0, g)) = ∑ g, x (1, g) := by
  have key : ∀ i : Fin Δ, (∑ g, x (1, A i * g)) = ∑ g, x (1, g) := fun i =>
    Equiv.sum_comp (Equiv.mulLeft (A i)) (fun g => x (1, g))
  simp only [classOpA_apply_zero]
  rw [← Finset.sum_div, Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun i _ => key i)]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [mul_div_cancel_left₀]
  exact_mod_cast hΔ.ne'

/-- Sum of `classOpA A x` over the layer with first coordinate `1` is the total mass of `x` on the
layer with first coordinate `0`. -/
lemma classOpA_sum_one (hΔ : 0 < Δ) (A : Fin Δ → G) (x : Fin 2 × G → ℝ) :
    (∑ g, classOpA A x (1, g)) = ∑ g, x (0, g) := by
  have key : ∀ i : Fin Δ, (∑ g, x (0, (A i)⁻¹ * g)) = ∑ g, x (0, g) := fun i =>
    Equiv.sum_comp (Equiv.mulLeft ((A i)⁻¹)) (fun g => x (0, g))
  simp only [classOpA_apply_one]
  rw [← Finset.sum_div, Finset.sum_comm]
  rw [Finset.sum_congr rfl (fun i _ => key i)]
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [mul_div_cancel_left₀]
  exact_mod_cast hΔ.ne'

theorem lr_classOpA_basic {G : Type} [Group G] [Fintype G] {Δ : ℕ} (hΔ : 0 < Δ) (A : Fin Δ → G) :
    (∀ x y : Fin 2 × G → ℝ, classOpA A (x + y) = classOpA A x + classOpA A y) ∧
    (∀ (a : ℝ) (x : Fin 2 × G → ℝ), classOpA A (a • x) = a • classOpA A x) ∧
    (classOpA A (fun _ => (1 : ℝ)) = fun _ => (1 : ℝ)) ∧
    (∀ x : Fin 2 × G → ℝ, ∑ p, classOpA A x p = ∑ p, x p) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x y
    funext p
    obtain ⟨b, g⟩ := p
    fin_cases b <;> simp [classOpA, Pi.add_apply, Finset.sum_add_distrib, add_div]
  · intro a x
    funext p
    obtain ⟨b, g⟩ := p
    fin_cases b <;> simp [classOpA, Pi.smul_apply, ← Finset.mul_sum, mul_div_assoc]
  · funext p
    obtain ⟨b, g⟩ := p
    fin_cases b <;> simp [classOpA, Finset.sum_const, Fintype.card_fin, hΔ.ne']
  · intro x
    rw [Fintype.sum_prod_type, Fin.sum_univ_two]
    rw [classOpA_sum_zero hΔ A x, classOpA_sum_one hΔ A x]
    rw [Fintype.sum_prod_type, Fin.sum_univ_two]
    ring

end Work.LT
