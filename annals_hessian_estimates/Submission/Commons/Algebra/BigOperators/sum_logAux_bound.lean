import Mathlib.Algebra.BigOperators.Field
import Mathlib.Algebra.Order.Star.Real

open scoped BigOperators

namespace Commons.Algebra.BigOperators

theorem sum_logAux_bound {n : ℕ} (f c lam xc A G L2 : Fin n → ℝ) {q Z hh s1 δ uC : ℝ}
    (hq : 0 < q) (hZ : 0 < Z) (hδ : 0 < δ) (huC : 0 ≤ uC) (hh_eq : hh = 2 * δ * uC)
    (hf : ∀ i, 0 < f i) (hL2 : ∀ i, L2 i ≤ 0)
    (hL2exp : ∀ i, L2 i = A i / q + G i / q - 2 * (c i * lam i) ^ 2 / q ^ 2
        + hh * lam i + 2 * δ * (c i) ^ 2 - 2 / Z - 4 * (xc i) ^ 2 / Z ^ 2)
    (hAnn : 0 ≤ ∑ i, f i * A i)
    (hG : (∑ i, f i * G i) = 0) (hlam : (∑ i, f i * lam i) = 2) (hfs : (∑ i, f i) = 3 * s1)
    (hS2 : (∑ i, f i * (c i * lam i) ^ 2) = q ^ 2 * (4 * (∑ i, f i * (xc i) ^ 2) / Z ^ 2
        - 4 * hh * (∑ i, f i * c i * xc i) / Z + hh ^ 2 * (∑ i, f i * (c i) ^ 2))) :
    (2 * δ - 2 * hh ^ 2) * (∑ i, f i * (c i) ^ 2) + 8 * hh * (∑ i, f i * c i * xc i) / Z
        - 6 * s1 / Z - 12 * (∑ i, f i * (xc i) ^ 2) / Z ^ 2 ≤ 0 := by
  have hS_nonpos : ∑ i, f i * L2 i ≤ 0 := by
    apply Finset.sum_nonpos
    intro i _
    exact mul_nonpos_of_nonneg_of_nonpos (le_of_lt (hf i)) (hL2 i)
  have hexp : ∑ i, f i * L2 i
      = (∑ i, f i * A i) / q + (∑ i, f i * G i) / q
        - (2 * ∑ i, f i * (c i * lam i) ^ 2) / q ^ 2
        + hh * (∑ i, f i * lam i) + (2 * δ) * (∑ i, f i * (c i) ^ 2)
        - (2 * (∑ i, f i)) / Z - (4 * (∑ i, f i * (xc i) ^ 2)) / Z ^ 2 := by
    have h1 : ∑ i, f i * L2 i
        = ∑ i, (f i * A i / q + f i * G i / q - 2 * (f i * (c i * lam i) ^ 2) / q ^ 2
            + hh * (f i * lam i) + 2 * δ * (f i * (c i) ^ 2) - 2 * f i / Z
            - 4 * (f i * (xc i) ^ 2) / Z ^ 2) :=
      Finset.sum_congr rfl (fun i _ => by rw [hL2exp i]; ring)
    rw [h1]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib]
    simp only [← Finset.sum_div]
    simp only [← Finset.mul_sum]
  have hFA : 0 ≤ (∑ i, f i * A i) / q := div_nonneg hAnn (le_of_lt hq)
  have hhh : 0 ≤ 2 * hh := by rw [hh_eq]; nlinarith [hδ, huC]
  have hSe : ∑ i, f i * L2 i
      = (∑ i, f i * A i) / q + 2 * hh
        + ((2 * δ - 2 * hh ^ 2) * (∑ i, f i * (c i) ^ 2)
            + 8 * hh * (∑ i, f i * c i * xc i) / Z
            - 6 * s1 / Z - 12 * (∑ i, f i * (xc i) ^ 2) / Z ^ 2) := by
    rw [hexp, hG, hlam, hfs, hS2]
    field_simp
    ring
  linarith [hS_nonpos, hFA, hhh, hSe]

end Commons.Algebra.BigOperators