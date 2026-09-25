import Mathlib

namespace Work.BourgainPlan.Maximal

/-- Auxiliary: for a polynomial `q` of positive degree, if for all `u ≥ U` (with `U ≥ 1`) one has
`c * u ^ (deg - 1) ≤ q'(u)` and `q(u) ≤ C₀ * u ^ deg`, then at every such `u` with `q(u) > 0`
the weighted derivative inequality `1 ≤ q'(u) * (C₀ ^ ((deg-1)/deg) / c) * q(u) ^ (1/deg - 1)`
holds. -/
theorem deriv_weight_ge_one (q : Polynomial ℝ) {U c C₀ : ℝ} (hU : 1 ≤ U) (hc : 0 < c)
    (hC₀ : 0 < C₀) (hd : 0 < q.natDegree)
    (hderiv : ∀ u : ℝ, U ≤ u → c * u ^ (q.natDegree - 1) ≤ q.derivative.eval u)
    (hupper : ∀ u : ℝ, U ≤ u → q.eval u ≤ C₀ * u ^ q.natDegree)
    {u : ℝ} (hu : U ≤ u) (hqu : 0 < q.eval u) :
    1 ≤ q.derivative.eval u * (C₀ ^ (((q.natDegree : ℝ) - 1) / (q.natDegree : ℝ)) / c)
          * (q.eval u) ^ ((q.natDegree : ℝ)⁻¹ - 1) := by
  set Q : ℝ := q.eval u with hQdef
  set A : ℝ := q.derivative.eval u with hAdef
  set B : ℝ := Q ^ ((q.natDegree : ℝ)⁻¹) with hBdef
  have hn1 : 1 ≤ q.natDegree := by omega
  have hnc : q.natDegree ≠ 0 := by omega
  have hupos : 0 < u := by
    have hU0 : 0 < U := lt_of_lt_of_le zero_lt_one hU
    linarith
  have hQpos : 0 < Q := hqu
  have hBpos : 0 < B := by
    rw [hBdef]; exact Real.rpow_pos_of_pos hQpos _
  have hQle : Q ≤ C₀ * u ^ q.natDegree := hupper u hu
  have hexpnn : (0:ℝ) ≤ (q.natDegree : ℝ)⁻¹ := inv_nonneg.mpr (Nat.cast_nonneg _)
  have hBle : B ≤ C₀ ^ ((q.natDegree : ℝ)⁻¹) * u := by
    rw [hBdef]
    calc Q ^ ((q.natDegree : ℝ)⁻¹)
        ≤ (C₀ * u ^ q.natDegree) ^ ((q.natDegree : ℝ)⁻¹) :=
          Real.rpow_le_rpow (le_of_lt hQpos) hQle hexpnn
      _ = C₀ ^ ((q.natDegree : ℝ)⁻¹) * (u ^ q.natDegree) ^ ((q.natDegree : ℝ)⁻¹) :=
          Real.mul_rpow (le_of_lt hC₀) (pow_nonneg (le_of_lt hupos) _)
      _ = C₀ ^ ((q.natDegree : ℝ)⁻¹) * u := by
          rw [Real.pow_rpow_inv_natCast (le_of_lt hupos) hnc]
  have hBpow : B ^ (q.natDegree - 1)
      ≤ C₀ ^ (((q.natDegree : ℝ) - 1) / (q.natDegree : ℝ)) * u ^ (q.natDegree - 1) := by
    calc B ^ (q.natDegree - 1)
        ≤ (C₀ ^ ((q.natDegree : ℝ)⁻¹) * u) ^ (q.natDegree - 1) :=
          pow_le_pow_left₀ (le_of_lt hBpos) hBle _
      _ = (C₀ ^ ((q.natDegree : ℝ)⁻¹)) ^ (q.natDegree - 1) * u ^ (q.natDegree - 1) := by
          rw [mul_pow]
      _ = C₀ ^ (((q.natDegree : ℝ)⁻¹) * ((q.natDegree - 1 : ℕ) : ℝ)) * u ^ (q.natDegree - 1) := by
          rw [Real.rpow_mul_natCast (le_of_lt hC₀)]
      _ = C₀ ^ (((q.natDegree : ℝ) - 1) / (q.natDegree : ℝ)) * u ^ (q.natDegree - 1) := by
          have hex : ((q.natDegree : ℝ)⁻¹) * ((q.natDegree - 1 : ℕ) : ℝ)
              = ((q.natDegree : ℝ) - 1) / (q.natDegree : ℝ) := by
            rw [Nat.cast_sub hn1, Nat.cast_one, div_eq_mul_inv]
            ring
          rw [hex]
  have hupow : u ^ (q.natDegree - 1) ≤ A / c := by
    rw [le_div_iff₀ hc, mul_comm]
    exact hderiv u hu
  have hC0nn : 0 ≤ C₀ ^ (((q.natDegree : ℝ) - 1) / (q.natDegree : ℝ)) :=
    Real.rpow_nonneg (le_of_lt hC₀) _
  have hcomb : B ^ (q.natDegree - 1)
      ≤ A / c * C₀ ^ (((q.natDegree : ℝ) - 1) / (q.natDegree : ℝ)) := by
    calc B ^ (q.natDegree - 1)
        ≤ C₀ ^ (((q.natDegree : ℝ) - 1) / (q.natDegree : ℝ)) * u ^ (q.natDegree - 1) := hBpow
      _ ≤ C₀ ^ (((q.natDegree : ℝ) - 1) / (q.natDegree : ℝ)) * (A / c) :=
          mul_le_mul_of_nonneg_left hupow hC0nn
      _ = A / c * C₀ ^ (((q.natDegree : ℝ) - 1) / (q.natDegree : ℝ)) := by ring
  have hQexp : Q ^ ((q.natDegree : ℝ)⁻¹ - 1) = B / Q := by
    have h := Real.rpow_sub_natCast (ne_of_gt hQpos) ((q.natDegree : ℝ)⁻¹) 1
    simp only [Nat.cast_one, pow_one] at h
    rw [h, hBdef]
  have hBpowQ : B ^ q.natDegree = Q := by
    rw [hBdef]
    exact Real.rpow_inv_natCast_pow (le_of_lt hQpos) hnc
  have hsplit : B ^ (q.natDegree - 1) * B = B ^ q.natDegree := by
    rw [← pow_succ, Nat.sub_add_cancel hn1]
  rw [hQexp]
  have hX : A * (C₀ ^ (((q.natDegree : ℝ) - 1) / (q.natDegree : ℝ)) / c)
      = A / c * C₀ ^ (((q.natDegree : ℝ) - 1) / (q.natDegree : ℝ)) := by ring
  rw [hX, ← mul_div_assoc, le_div_iff₀ hQpos, one_mul]
  rw [← hBpowQ, ← hsplit]
  exact mul_le_mul_of_nonneg_right hcomb (le_of_lt hBpos)

end Work.BourgainPlan.Maximal
