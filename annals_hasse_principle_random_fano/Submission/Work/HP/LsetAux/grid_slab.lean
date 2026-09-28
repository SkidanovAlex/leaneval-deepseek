import Mathlib
import Submission.Work.HP.LsetAux.GridDefs

/-!
# Volume of the slab-type set attached to a grid point

The slab hypothesis `hslab` is applied at the unit vector `gw n N z`: the coordinate condition
`1/(n+1) ≤ |gw n N z i|` comes from `exists_coord_ge_one_div`, the norm condition from
`rNorm_gw`, and `A = 1` kills the `A ^ (NN d n - n - 1)` factor.
-/

set_option autoImplicit false
noncomputable section
open Classical Finset MvPolynomial MeasureTheory
open scoped BigOperators ENNReal

namespace Work.HP.LsetAux

theorem grid_slab (d n N : ℕ) {K C1 C2 : ℝ} (hK : 0 < K) (hC1 : 0 ≤ C1) (hC2 : 0 ≤ C2)
    (hslab : ∀ (x : Fin (n + 1) → ℝ) (i : Fin (n + 1)) (A ε δ : ℝ),
      1 / ((n : ℝ) + 1) ≤ |x i| → rNorm x ≤ 2 → 0 ≤ A → 0 ≤ ε → 0 ≤ δ →
      MeasureTheory.volume {a : Mon d n → ℝ | rNorm a ≤ A ∧ |formEvalR d n a x| ≤ ε ∧
          (∀ j : Fin (n + 1), |gradVec d n a x j| ≤ δ)}
        ≤ ENNReal.ofReal (K * ε * δ ^ n * A ^ (NN d n - n - 1)))
    (hN : N ≠ 0) {z : Fin (n + 1) → ℤ} (hz : z ≠ 0) :
    MeasureTheory.volume (gS d n N C1 C2 z)
      ≤ ENNReal.ofReal (K * gEps n N C2 * (gDel n N C1) ^ n) := by
  obtain ⟨i, hi⟩ := exists_coord_ge_one_div n (rNorm_gw hN hz)
  have hw : rNorm (gw n N z) = 1 := rNorm_gw hN hz
  have hw2 : rNorm (gw n N z) ≤ 2 := by rw [hw]; norm_num
  have hε : 0 ≤ gEps n N C2 := by
    rw [gEps]; apply div_nonneg <;> positivity
  have hδ : 0 ≤ gDel n N C1 := by
    rw [gDel]; apply div_nonneg <;> positivity
  have hkey := hslab (gw n N z) i 1 (gEps n N C2) (gDel n N C1) hi hw2
    (by norm_num) hε hδ
  have h1 : (1 : ℝ) ^ (NN d n - n - 1) = 1 := one_pow _
  rw [h1, mul_one] at hkey
  exact hkey

end Work.HP.LsetAux
