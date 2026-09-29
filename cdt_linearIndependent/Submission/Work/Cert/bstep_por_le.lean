import Mathlib
import Submission.Work.Cert.ThetaDefs

namespace Work.Cert

/-- **Odd-power step of the `B` accumulator.**  From an enclosure `‖cx a b - z^(2k+1)‖ ≤ 16/S`
of the odd power `z^(2k+1)` (`z = qc qr qi`), the rounded product
`cx (cmr a b q2r q2i) (cmi a b q2r q2i)` with the rounded square `q2 = cx (cmr qr qi qr qi) (cmi qr qi qr qi)`
of the centre `z` encloses `z^(2(k+1)+1) = z^(2k+3)` again within `16/S`.

The two roundings cost `3/S` each (`hcxmul`), the Lipschitz factor of `w ↦ w·z²` is `‖z‖² ≤ μ²`
and `‖z^(2k+1)‖ ≤ μ`, so the accumulated error is at most
`3/S + (μ + 16/S)·(3/S) + μ²·(16/S) ≤ (3 + 3μ + 16μ²)/S + 48/S² ≤ 16/S`
for `μ ≤ 79/100` and `S ≥ 100`. -/
theorem bstep_por_le
    (hcxmul : ∀ a b c d : ℤ, ‖cx (cmr a b c d) (cmi a b c d) - cx a b * cx c d‖ ≤ 3 / ((S : ℝ)))
    (qr qi m : ℤ) {a b : ℤ} {k : ℕ}
    (hμ : mub m ≤ 79/100) (hz : ‖qc qr qi‖ ≤ mub m)
    (h : ‖cx a b - (qc qr qi) ^ (2*k+1)‖ ≤ 16 / ((S:ℝ))) :
    ‖cx (cmr a b (cmr qr qi qr qi) (cmi qr qi qr qi)) (cmi a b (cmr qr qi qr qi) (cmi qr qi qr qi))
        - (qc qr qi) ^ (2*(k+1)+1)‖ ≤ 16 / ((S:ℝ)) := by
  have hS : (0 : ℝ) < (S : ℝ) := thS_pos
  have hS100 : (100 : ℝ) ≤ (S : ℝ) := by
    have h : (100 : ℤ) ≤ S := by norm_num [S]
    exact_mod_cast h
  set z : ℂ := qc qr qi with hzdef
  set A : ℂ := cx a b with hAdef
  set Z2 : ℂ := cx (cmr qr qi qr qi) (cmi qr qi qr qi) with hZ2def
  set W : ℂ := cx (cmr a b (cmr qr qi qr qi) (cmi qr qi qr qi))
    (cmi a b (cmr qr qi qr qi) (cmi qr qi qr qi)) with hWdef
  set μ : ℝ := mub m with hμdef
  -- the two rounding errors
  have h1 : ‖Z2 - z * z‖ ≤ 3/(S:ℝ) := by
    have hh := hcxmul qr qi qr qi
    simp only [qc] at hh hzdef
    rw [← hZ2def, ← hzdef] at hh
    exact hh
  have h2 : ‖W - A * Z2‖ ≤ 3/(S:ℝ) := by
    have hh := hcxmul a b (cmr qr qi qr qi) (cmi qr qi qr qi)
    rw [← hWdef, ← hAdef, ← hZ2def] at hh
    exact hh
  have hA0 : ‖A - z ^ (2*k+1)‖ ≤ 16/(S:ℝ) := h
  -- size of `z` and of `A`
  have hznonneg : 0 ≤ ‖z‖ := norm_nonneg z
  have hμnn : 0 ≤ μ := le_trans hznonneg hz
  have hμ1 : μ ≤ 1 := by linarith
  have hzp : ‖z‖ ^ (2*k+1) ≤ μ := by
    have hle : ‖z‖ ^ (2*k+1) ≤ μ ^ (2*k+1) := pow_le_pow_left₀ hznonneg hz _
    have hle2 : μ ^ (2*k+1) ≤ μ := pow_le_of_le_one hμnn hμ1 (by omega)
    linarith
  have hAnorm : ‖A‖ ≤ μ + 16/(S:ℝ) := by
    have htri : ‖A‖ - ‖z ^ (2*k+1)‖ ≤ ‖A - z ^ (2*k+1)‖ := norm_sub_norm_le _ _
    rw [norm_pow] at htri
    linarith
  have hzsq : ‖z * z‖ ≤ μ ^ 2 := by
    rw [norm_mul]
    nlinarith [hz, hμnn, hznonneg]
  -- telescoping identity
  have hkey : W - z ^ (2*(k+1)+1) = (W - A*Z2) + A*(Z2 - z*z) + (A - z^(2*k+1))*(z*z) := by
    have he : 2*(k+1)+1 = 2*k+1+2 := by omega
    rw [he, pow_add]
    ring
  have e2 : ‖A*(Z2 - z*z)‖ ≤ ‖A‖ * (3/(S:ℝ)) :=
    le_trans (norm_mul_le _ _) (mul_le_mul_of_nonneg_left h1 (norm_nonneg A))
  have e3 : ‖(A - z^(2*k+1))*(z*z)‖ ≤ (16/(S:ℝ)) * ‖z*z‖ :=
    le_trans (norm_mul_le _ _) (mul_le_mul_of_nonneg_right hA0 (norm_nonneg _))
  have step1 : ‖W - z^(2*(k+1)+1)‖ ≤ 3/(S:ℝ) + ‖A‖*(3/(S:ℝ)) + (16/(S:ℝ))*‖z*z‖ := by
    rw [hkey]
    calc ‖(W - A*Z2) + A*(Z2 - z*z) + (A - z^(2*k+1))*(z*z)‖
        ≤ ‖W - A*Z2‖ + ‖A*(Z2 - z*z)‖ + ‖(A - z^(2*k+1))*(z*z)‖ := norm_add₃_le
      _ ≤ 3/(S:ℝ) + ‖A‖*(3/(S:ℝ)) + (16/(S:ℝ))*‖z*z‖ := by linarith
  have step2 : 3/(S:ℝ) + ‖A‖*(3/(S:ℝ)) + (16/(S:ℝ))*‖z*z‖
      ≤ 3/(S:ℝ) + (μ + 16/(S:ℝ))*(3/(S:ℝ)) + (16/(S:ℝ))*μ^2 := by
    have h3 : (0:ℝ) ≤ 3/(S:ℝ) := by positivity
    have h16 : (0:ℝ) ≤ 16/(S:ℝ) := by positivity
    nlinarith [hAnorm, hzsq, h3, h16, mul_le_mul_of_nonneg_right hAnorm h3,
      mul_le_mul_of_nonneg_left hzsq h16]
  have hfinal : 3/(S:ℝ) + (μ + 16/(S:ℝ))*(3/(S:ℝ)) + (16/(S:ℝ))*μ^2 ≤ 16/(S:ℝ) := by
    have hnum : 3 + 3*μ + 16*μ^2 + 48/(S:ℝ) ≤ 16 := by
      have hμ2 : μ^2 ≤ (79/100)^2 := by nlinarith [hμ, hμnn]
      have h48 : 48/(S:ℝ) ≤ 48/100 := by
        rw [div_le_div_iff₀ hS (by norm_num : (0:ℝ) < 100)]
        linarith [hS100]
      nlinarith [hμ, hμnn, hμ2, h48]
    have heq : 3/(S:ℝ) + (μ + 16/(S:ℝ))*(3/(S:ℝ)) + (16/(S:ℝ))*μ^2
        = (3 + 3*μ + 16*μ^2 + 48/(S:ℝ))/(S:ℝ) := by
      field_simp
      ring
    rw [heq]
    exact div_le_div_of_nonneg_right hnum (le_of_lt hS)
  linarith

end Work.Cert
