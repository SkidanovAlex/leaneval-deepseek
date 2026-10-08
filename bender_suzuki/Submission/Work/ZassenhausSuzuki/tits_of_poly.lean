import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ZassenhausSuzuki

/-- Key algebraic consequence of the Tits-type condition, in characteristic two:
from the hypothesis one deduces `b * (b + 1) * (c + a ^ 2) = 0`. -/
private lemma tits_key {K : Type*} [Field K] [CharP K 2] (a b c : K)
    (hx : (1 + a ^ 2 * b) * (1 + b ^ 2 * c) = (1 + a * b) ^ 2 * (1 + b * c)) :
    b * (b + 1) * (c + a ^ 2) = 0 := by
  linear_combination (norm := (ring_nf; simp [CharTwo.two_eq_zero])) hx

theorem tits_of_poly {K : Type*} [Field K] [CharP K 2] (θ : K ≃+* K)
    (h : ∀ ν : K, ν ≠ 0 → ν ≠ 1 →
      (1 + ν ^ 2 * θ ν) * (1 + (θ ν) ^ 2 * θ (θ ν))
        = (1 + ν * θ ν) ^ 2 * (1 + θ ν * θ (θ ν))) :
    ∀ x : K, θ (θ x) = x ^ 2 := by
  intro x
  by_cases hx0 : x = 0
  · subst hx0; simp
  by_cases hx1 : x = 1
  · subst hx1; simp
  · have hb0 : θ x ≠ 0 := by
      intro hc
      exact hx0 (θ.injective (by rw [hc, map_zero]))
    have hb1 : θ x ≠ 1 := by
      intro hc
      exact hx1 (θ.injective (by rw [hc, map_one]))
    have hx := h x hx0 hx1
    have key : θ x * (θ x + 1) * (θ (θ x) + x ^ 2) = 0 :=
      tits_key x (θ x) (θ (θ x)) hx
    rcases mul_eq_zero.mp key with h1 | h1
    · rcases mul_eq_zero.mp h1 with h2 | h2
      · exact absurd h2 hb0
      · have hb : θ x = 1 := by
          calc θ x = θ x + 0 := (add_zero _).symm
            _ = θ x + (1 + 1) := by rw [CharTwo.add_self_eq_zero]
            _ = (θ x + 1) + 1 := by rw [add_assoc]
            _ = 0 + 1 := by rw [h2]
            _ = 1 := by rw [zero_add]
        exact absurd hb hb1
    · calc θ (θ x) = θ (θ x) + 0 := (add_zero _).symm
        _ = θ (θ x) + (x ^ 2 + x ^ 2) := by rw [CharTwo.add_self_eq_zero]
        _ = (θ (θ x) + x ^ 2) + x ^ 2 := by rw [add_assoc]
        _ = 0 + x ^ 2 := by rw [h1]
        _ = x ^ 2 := by rw [zero_add]

end Work.ZassenhausSuzuki
