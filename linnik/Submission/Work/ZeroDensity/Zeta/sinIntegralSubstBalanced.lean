import Mathlib

namespace Work.ZeroDensity.Zeta

open MeasureTheory
open scoped Pointwise

/-- **Substitution `u = v / c` on a half-line.**

For `c > 0` and any complex-valued `f`,
`∫_{u > N} f (c * u) du = c⁻¹ · ∫_{v > c * N} f v dv`.

This is the change of variables `v = c * u` for an integral over `Set.Ioi`,
a direct corollary of `MeasureTheory.Measure.setIntegral_comp_smul_of_pos`. -/
private lemma setIntegral_comp_mul_Ioi {f : ℝ → ℂ} {c N : ℝ} (hc : 0 < c) :
    ∫ u in Set.Ioi N, f (c * u) = (c⁻¹ : ℝ) • ∫ v in Set.Ioi (c * N), f v := by
  have h := MeasureTheory.Measure.setIntegral_comp_smul_of_pos (μ := volume) f
    (s := Set.Ioi N) hc
  simp only [Module.finrank_self, pow_one] at h
  have hset : c • (Set.Ioi N) = Set.Ioi (c * N) := by
    rw [← Set.image_mul_left_Ioi hc]
    ext x; constructor <;> rintro ⟨y, hy, rfl⟩ <;> exact ⟨y, hy, rfl⟩
  rw [show (∫ u in Set.Ioi N, f (c * u)) = ∫ x in Set.Ioi N, f (c • x) by
    simp only [smul_eq_mul]] at *
  rw [h, hset]

/-- **Balanced substitution for the oscillatory integral `∫ sin(cu) u^{-s-1}`.**

Substituting `v = 2πk u` turns `∫_{u > N} sin(2πk u) u^{-s-1} du` into
`(2πk)^s ∫_{v > 2πk N} sin v · v^{-s-1} dv`: the powers balance because the
Jacobi factor `c⁻¹` cancels the factor `c^{s+1}` produced by the algebra
`(c u)^{-s-1} = c^{-s-1} u^{-s-1}`. -/
theorem sinIntegralSubstBalanced {s : ℂ} (hs0 : 0 < s.re) (N : ℕ) (hN : 1 ≤ N) {k : ℕ} (hk : 1 ≤ k) :
    ∫ u in Set.Ioi (N : ℝ), ((Real.sin (2 * Real.pi * (k : ℝ) * u) : ℝ) : ℂ) * (u : ℂ) ^ (-s - 1)
      = (2 * Real.pi * (k : ℝ) : ℂ) ^ s *
          ∫ v in Set.Ioi (2 * Real.pi * (k : ℝ) * (N : ℝ)),
            ((Real.sin v : ℝ) : ℂ) * (v : ℂ) ^ (-s - 1) := by
  -- Abbreviate `c = 2πk`; keep it an opaque variable so that rewriting is stable.
  generalize hc_def : (2 * Real.pi * (k : ℝ)) = c
  have hkpos : (0 : ℝ) < (k : ℝ) := by
    exact_mod_cast (Nat.lt_of_lt_of_le Nat.zero_lt_one hk)
  have hcp : (0 : ℝ) < c := by rw [← hc_def]; positivity
  have hcne : (c : ℂ) ≠ 0 := by exact_mod_cast hcp.ne'
  -- The target writes the base of `^s` as a product of complex coercions.
  have hcb : (2 : ℂ) * (Real.pi : ℂ) * ((k : ℝ) : ℂ) = (c : ℂ) := by
    rw [← hc_def]; push_cast; ring
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  -- Pointwise identity `sin(cu) u^{-s-1} = c^s · (c · (sin(cu) (cu)^{-s-1}))`.
  have hpt : ∀ u ∈ Set.Ioi (N : ℝ),
      ((Real.sin (c * u) : ℝ) : ℂ) * (u : ℂ) ^ (-s - 1)
        = (c : ℂ) ^ s *
            ((c : ℂ) * (((Real.sin (c * u) : ℝ) : ℂ) * ((c * u : ℝ) : ℂ) ^ (-s - 1))) := by
    intro u hu
    have hu0 : (0 : ℝ) < u := lt_of_lt_of_le (lt_of_lt_of_le zero_lt_one hN1) hu.le
    have hz : (c : ℂ)^s * (c : ℂ) * (c : ℂ)^(-s - 1) = 1 := by
      have h2 : (c : ℂ)^(s + 1) * (c : ℂ)^(-s - 1) = 1 := by
        rw [← Complex.cpow_add (s + 1) (-s - 1) hcne]
        rw [show (s + 1) + (-s - 1) = 0 by ring, Complex.cpow_zero]
      have hA : (c : ℂ)^s * (c : ℂ) = (c : ℂ)^(s + 1) := by
        nth_rewrite 2 [← Complex.cpow_one (c : ℂ)]
        rw [← Complex.cpow_add s 1 hcne]
      rw [hA, h2]
    rw [Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg hcp.le hu0.le]
    rw [show (c : ℂ) ^ s * ((c : ℂ) * (((Real.sin (c * u) : ℝ) : ℂ) *
            ((c : ℂ) ^ (-s - 1) * (u : ℂ) ^ (-s - 1))))
        = ((Real.sin (c * u) : ℝ) : ℂ) * (u : ℂ)^(-s-1) *
            ((c : ℂ)^s * (c : ℂ) * (c : ℂ)^(-s - 1)) by ring]
    rw [hz, mul_one]
  rw [MeasureTheory.setIntegral_congr_fun measurableSet_Ioi hpt]
  -- Pull the two constants out of the integral.
  rw [MeasureTheory.integral_const_mul]
  rw [MeasureTheory.integral_const_mul]
  -- Change of variables `v = c u`.
  have hsub : ∫ u in Set.Ioi (N : ℝ), ((Real.sin (c * u) : ℝ) : ℂ) * ((c * u : ℝ) : ℂ) ^ (-s - 1)
      = (c⁻¹ : ℝ) • ∫ v in Set.Ioi (c * (N : ℝ)),
          ((Real.sin v : ℝ) : ℂ) * (v : ℂ) ^ (-s - 1) := by
    simpa using setIntegral_comp_mul_Ioi (f := fun v => ((Real.sin v : ℝ) : ℂ) * (v : ℂ) ^ (-s - 1))
      (c := c) (N := (N : ℝ)) hcp
  rw [hsub, hcb]
  -- The Jacobi factor `c⁻¹` cancels the extra `c`.
  congr 1
  rw [Complex.real_smul, Complex.ofReal_inv, ← mul_assoc, mul_inv_cancel₀ hcne, one_mul]

end Work.ZeroDensity.Zeta
