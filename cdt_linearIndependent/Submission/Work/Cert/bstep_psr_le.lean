import Mathlib
import Submission.Work.Cert.ThetaDefs

namespace Work.Cert

/-! # The `psr` combination step of the `b`-loop

`bStep` (in `Defs.lean`) combines the "power square" approximant `psr + i psi` (which tracks
`q^{k²}`) with the "power" approximant `por + i poi` (which tracks `q^{2k+1}`) into the new square
`cmr psr psi por poi + i·cmi psr psi por poi`, which tracks `q^{(k+1)²} = q^{k²}·q^{2k+1}`.

This file proves the error propagation for that step.  The rounded product loses at most
`3/S` (`cx_mul_le`), and the two factors are correct up to `16/S` and `8k²/S`, so the total
is bounded by the numerical core `bstep_psr_num`. -/

/-- Numerical core of `bstep_psr_le`: the accumulated error budget
`3/S + (1 + 8k²/S)·(16/S) + 8k²/S` fits into the step tolerance `8(k+1)²/S`
for `1 ≤ k ≤ 11` (there is a lot of slack: `k² ≤ 121` and `S = 2^40·10^8`). -/
lemma bstep_psr_num (k : ℕ) (hk : 1 ≤ k) (hkK : k ≤ 11) :
    3/((S:ℝ)) + ((1 + 8*((k*k:ℕ):ℝ)/(S:ℝ))*(16/(S:ℝ)) + 8*((k*k:ℕ):ℝ)/(S:ℝ))
      ≤ 8*(((k+1)*(k+1):ℕ):ℝ)/((S:ℝ)) := by
  have hS : (0:ℝ) < (S:ℝ) := thS_pos
  have hkk : ((k*k:ℕ):ℝ) = (k:ℝ)*(k:ℝ) := by push_cast; ring
  have hK : (((k+1)*(k+1):ℕ):ℝ) = ((k:ℝ)+1)*((k:ℝ)+1) := by push_cast; ring
  have hkR : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
  have hkR11 : (k:ℝ) ≤ 11 := by exact_mod_cast hkK
  have hSbig : (15488:ℝ) ≤ (S:ℝ) := by norm_num [S]
  have hsmall : 128 * ((k*k:ℕ):ℝ) / (S:ℝ) ≤ 1 := by
    rw [div_le_one hS, hkk]
    nlinarith [hkR, hkR11, hSbig]
  rw [hkk, hK] at *
  rw [le_div_iff₀ hS]
  field_simp
  nlinarith [hsmall, hkR, hS]

theorem bstep_psr_le
    (hcxmul : ∀ a b c d : ℤ, ‖cx (cmr a b c d) (cmi a b c d) - cx a b * cx c d‖ ≤ 3 / ((S : ℝ)))
    (qr qi m : ℤ) {a b c d : ℤ} {k : ℕ} (hk : 1 ≤ k) (hkK : k ≤ 11)
    (hμ : mub m ≤ 79/100) (hz : ‖qc qr qi‖ ≤ mub m)
    (ha : ‖cx a b - (qc qr qi) ^ (2*k+1)‖ ≤ 16 / ((S:ℝ)))
    (hb : ‖cx c d - (qc qr qi) ^ (k*k)‖ ≤ 8 * ((k*k : ℕ) : ℝ) / ((S:ℝ))) :
    ‖cx (cmr c d a b) (cmi c d a b) - (qc qr qi) ^ ((k+1)*(k+1))‖
      ≤ 8 * ((((k+1)*(k+1) : ℕ)) : ℝ) / ((S:ℝ)) := by
  have hS : (0:ℝ) < (S:ℝ) := thS_pos
  set q : ℂ := qc qr qi with hq
  -- the centre sits strictly inside the unit disc, so all its powers have norm ≤ 1
  have hq1 : ‖q‖ ≤ 1 := by
    have h1 : ‖q‖ ≤ mub m := hz
    have h2 : mub m ≤ (79:ℝ)/100 := hμ
    linarith
  have hqpow : ∀ n : ℕ, ‖q‖ ^ n ≤ 1 := fun n => pow_le_one₀ (norm_nonneg q) hq1 (n := n)
  have hqnorm : ∀ n : ℕ, ‖q ^ n‖ ≤ 1 := fun n => by rw [norm_pow]; exact hqpow n
  have hnn : (0:ℝ) ≤ 8 * ((k*k:ℕ):ℝ) := mul_nonneg (by norm_num) (Nat.cast_nonneg _)
  -- `‖cx c d‖ ≤ ‖q^{k²}‖ + 8k²/S ≤ 1 + 8k²/S`
  have hcd : ‖cx c d‖ ≤ 1 + 8 * ((k*k:ℕ):ℝ) / (S:ℝ) := by
    have e : (cx c d - q ^ (k*k)) + q ^ (k*k) = cx c d := by ring
    calc ‖cx c d‖ = ‖(cx c d - q ^ (k*k)) + q ^ (k*k)‖ := by rw [e]
      _ ≤ ‖cx c d - q ^ (k*k)‖ + ‖q ^ (k*k)‖ := norm_add_le _ _
      _ ≤ 8 * ((k*k:ℕ):ℝ) / (S:ℝ) + 1 := add_le_add hb (hqnorm (k*k))
      _ = 1 + 8 * ((k*k:ℕ):ℝ) / (S:ℝ) := by ring
  -- split the error into the rounding error and the two factor errors
  have hdecomp : cx (cmr c d a b) (cmi c d a b) - q ^ ((k+1)*(k+1))
      = (cx (cmr c d a b) (cmi c d a b) - cx c d * cx a b)
        + (cx c d * (cx a b - q ^ (2*k+1)) + (cx c d - q ^ (k*k)) * q ^ (2*k+1)) := by
    have hp : q ^ (k*k) * q ^ (2*k+1) = q ^ ((k+1)*(k+1)) := by
      rw [← pow_add]
      congr 1
      ring
    rw [← hp]
    ring
  rw [hdecomp]
  calc ‖(cx (cmr c d a b) (cmi c d a b) - cx c d * cx a b)
        + (cx c d * (cx a b - q ^ (2*k+1)) + (cx c d - q ^ (k*k)) * q ^ (2*k+1))‖
      ≤ ‖cx (cmr c d a b) (cmi c d a b) - cx c d * cx a b‖
        + ‖cx c d * (cx a b - q ^ (2*k+1)) + (cx c d - q ^ (k*k)) * q ^ (2*k+1)‖ := norm_add_le _ _
    _ ≤ 3/(S:ℝ) + (‖cx c d‖ * (16/(S:ℝ)) + (8 * ((k*k:ℕ):ℝ)/(S:ℝ)) * ‖q‖^(2*k+1)) := by
        apply add_le_add (hcxmul c d a b)
        calc ‖cx c d * (cx a b - q ^ (2*k+1)) + (cx c d - q ^ (k*k)) * q ^ (2*k+1)‖
            ≤ ‖cx c d * (cx a b - q ^ (2*k+1))‖ + ‖(cx c d - q ^ (k*k)) * q ^ (2*k+1)‖ := norm_add_le _ _
          _ = ‖cx c d‖ * ‖cx a b - q ^ (2*k+1)‖ + ‖cx c d - q ^ (k*k)‖ * ‖q ^ (2*k+1)‖ := by rw [norm_mul, norm_mul]
          _ ≤ ‖cx c d‖ * (16/(S:ℝ)) + (8 * ((k*k:ℕ):ℝ)/(S:ℝ)) * ‖q‖^(2*k+1) := by
              rw [norm_pow]
              exact add_le_add (mul_le_mul_of_nonneg_left ha (norm_nonneg _))
                (mul_le_mul_of_nonneg_right hb (pow_nonneg (norm_nonneg q) _))
    _ ≤ 3/(S:ℝ) + ((1 + 8 * ((k*k:ℕ):ℝ)/(S:ℝ)) * (16/(S:ℝ)) + (8 * ((k*k:ℕ):ℝ)/(S:ℝ)) * 1) := by
        have h1 : ‖cx c d‖ * (16/(S:ℝ)) ≤ (1 + 8 * ((k*k:ℕ):ℝ)/(S:ℝ)) * (16/(S:ℝ)) :=
          mul_le_mul_of_nonneg_right hcd (div_nonneg (by norm_num) (le_of_lt hS))
        have h2 : (8 * ((k*k:ℕ):ℝ)/(S:ℝ)) * ‖q‖^(2*k+1) ≤ (8 * ((k*k:ℕ):ℝ)/(S:ℝ)) * 1 :=
          mul_le_mul_of_nonneg_left (hqpow (2*k+1)) (div_nonneg hnn (le_of_lt hS))
        linarith
    _ = 3/(S:ℝ) + ((1 + 8 * ((k*k:ℕ):ℝ)/(S:ℝ)) * (16/(S:ℝ)) + 8 * ((k*k:ℕ):ℝ)/(S:ℝ)) := by ring
    _ ≤ 8 * ((((k+1)*(k+1) : ℕ)) : ℝ) / ((S:ℝ)) := bstep_psr_num k hk hkK

end Work.Cert
