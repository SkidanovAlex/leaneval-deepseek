import Mathlib
import Submission.Work.Cert.ThetaDefs

/-! # Base case of the `B`-loop invariant

`Work.Cert.binv_base1`: after the *first* step of the `B` accumulator loop (the one that computes the
partial sums of `1 + 2·Σ (-1)^{n+1} q^{n²}`), started from the loop's initial state
`⟨qr, qi, S, 0, S, 0, m, S, 0⟩` (i.e. `por + i·poi = q`, `psr + i·psi = 1`, `Br + i·Bi = 1`,
`mo = m`, `ms = S`, `dB = 0`), the invariant `Work.Cert.BInv` holds at index `1`.

Because the first step is `1` and the initial mantissas are exact multiples of `S`, the roundings
`md S x = x`, `mu S x = x` are exact there: the new state is

* `por + i·poi = ⌊q·q²⌋` (i.e. `q³` up to the product roundings),
* `psr + i·psi = q` (exactly — no rounding at all),
* `ms = m + 1`, `mo = mu m (mu m m + 1) + 1`,
* `Br + i·Bi = 1 - 2q` (exactly),
* `dB = 2·mu (dvu (m+1) m) rq + 17`.

The only genuinely analytic ingredient is `hcxmul` (the one-ulp product bound), combined with
`‖q‖ ≤ 79/100`; the remaining obligations are the integer inequalities
`mu (dvu (m+1) m) rq ≥ rq` and `mu m (mu m m + 1) + 1 ≥ m³/S²`, from `thmu_ge`/`thdvu_ge`.
-/

namespace Work.Cert

noncomputable section

open Complex

/-- `md 0 b = 0`. -/
lemma binv_md_zero (b : ℤ) : md 0 b = 0 := by
  rw [md, fdiv, Int.zero_mul]; decide

/-- Multiplying an exact mantissa by `S` on the left is exact. -/
lemma binv_cmr_S0 (a b : ℤ) : cmr S 0 a b = a := by
  rw [cmr, md_S, binv_md_zero]; ring

/-- Multiplying an exact mantissa by `S` on the left is exact (imaginary part). -/
lemma binv_cmi_S0 (a b : ℤ) : cmi S 0 a b = b := by
  rw [cmi, md_S, binv_md_zero]; ring

theorem binv_base1
    (hcxmul : ∀ a b c d : ℤ, ‖cx (cmr a b c d) (cmi a b c d) - cx a b * cx c d‖ ≤ 3 / ((S : ℝ)))
    (qr qi rq m : ℤ) (hm : 1 ≤ m) (hrq : 0 ≤ rq) (hμ : mub m ≤ 79 / 100)
    (hz : ‖qc qr qi‖ ≤ mub m) :
    BInv qr qi rq m 1 (bStep (cmr qr qi qr qi) (cmi qr qi qr qi) rq m 1 ⟨qr, qi, S, 0, S, 0, m, S, 0⟩) := by
  simp only [BInv, bStep, Nat.reduceMod, if_true]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `por + i·poi`: the rounded triple product of `q`
    have h1 := hcxmul qr qi (cmr qr qi qr qi) (cmi qr qi qr qi)
    have h2 := hcxmul qr qi qr qi
    have h1' : ‖cx (cmr qr qi (cmr qr qi qr qi) (cmi qr qi qr qi))
            (cmi qr qi (cmr qr qi qr qi) (cmi qr qi qr qi))
          - qc qr qi * cx (cmr qr qi qr qi) (cmi qr qi qr qi)‖ ≤ 3 / (S : ℝ) := by
      simpa only [qc] using h1
    have h2' : ‖cx (cmr qr qi qr qi) (cmi qr qi qr qi) - qc qr qi * qc qr qi‖ ≤ 3 / (S : ℝ) := by
      simpa only [qc] using h2
    have hQ : ‖qc qr qi‖ ≤ 79 / 100 := le_trans hz hμ
    have key : cx (cmr qr qi (cmr qr qi qr qi) (cmi qr qi qr qi))
            (cmi qr qi (cmr qr qi qr qi) (cmi qr qi qr qi))
          - qc qr qi ^ (2 * 1 + 1)
        = (cx (cmr qr qi (cmr qr qi qr qi) (cmi qr qi qr qi))
              (cmi qr qi (cmr qr qi qr qi) (cmi qr qi qr qi))
            - qc qr qi * cx (cmr qr qi qr qi) (cmi qr qi qr qi))
          + qc qr qi * (cx (cmr qr qi qr qi) (cmi qr qi qr qi) - qc qr qi * qc qr qi) := by
      rw [show (2 * 1 + 1 : ℕ) = 3 from rfl]; ring
    rw [key]
    have hstep : ‖cx (cmr qr qi (cmr qr qi qr qi) (cmi qr qi qr qi))
              (cmi qr qi (cmr qr qi qr qi) (cmi qr qi qr qi))
            - qc qr qi * cx (cmr qr qi qr qi) (cmi qr qi qr qi)‖
          + ‖qc qr qi‖ * ‖cx (cmr qr qi qr qi) (cmi qr qi qr qi) - qc qr qi * qc qr qi‖
          ≤ 3 / (S : ℝ) + (79 / 100) * (3 / (S : ℝ)) := by
      have hmul := mul_le_mul hQ h2' (norm_nonneg _) (by norm_num : (0:ℝ) ≤ 79 / 100)
      linarith [add_le_add h1' hmul]
    have hfin : (3:ℝ) / (S : ℝ) + (79 / 100) * (3 / (S : ℝ)) ≤ 16 / (S : ℝ) := by
      rw [show (79 / 100 : ℝ) * (3 / (S : ℝ)) = (79 / 100 * 3) / (S : ℝ) by ring, ← add_div]
      apply div_le_div_of_nonneg_right _ (le_of_lt thS_pos)
      norm_num
    calc ‖cx (cmr qr qi (cmr qr qi qr qi) (cmi qr qi qr qi))
              (cmi qr qi (cmr qr qi qr qi) (cmi qr qi qr qi))
            - qc qr qi * cx (cmr qr qi qr qi) (cmi qr qi qr qi)
          + qc qr qi * (cx (cmr qr qi qr qi) (cmi qr qi qr qi) - qc qr qi * qc qr qi)‖
        ≤ ‖cx (cmr qr qi (cmr qr qi qr qi) (cmi qr qi qr qi))
              (cmi qr qi (cmr qr qi qr qi) (cmi qr qi qr qi))
            - qc qr qi * cx (cmr qr qi qr qi) (cmi qr qi qr qi)‖
          + ‖qc qr qi * (cx (cmr qr qi qr qi) (cmi qr qi qr qi) - qc qr qi * qc qr qi)‖ :=
        norm_add_le _ _
      _ = ‖cx (cmr qr qi (cmr qr qi qr qi) (cmi qr qi qr qi))
              (cmi qr qi (cmr qr qi qr qi) (cmi qr qi qr qi))
            - qc qr qi * cx (cmr qr qi qr qi) (cmi qr qi qr qi)‖
          + ‖qc qr qi‖ * ‖cx (cmr qr qi qr qi) (cmi qr qi qr qi) - qc qr qi * qc qr qi‖ := by
        rw [norm_mul]
      _ ≤ 3 / (S : ℝ) + (79 / 100) * (3 / (S : ℝ)) := hstep
      _ ≤ 16 / (S : ℝ) := hfin
  · -- `psr + i·psi = q` exactly
    rw [binv_cmr_S0, binv_cmi_S0]
    have h : qc qr qi ^ (1 * 1 : ℕ) = cx qr qi := by simp [qc]
    rw [h, sub_self, norm_zero]
    norm_num
    exact div_nonneg (by norm_num) (le_of_lt thS_pos)
  · -- `ms = m + 1 ≥ μ`
    rw [show (1 * 1 : ℕ) = 1 from rfl, pow_one, mub, mu_S]
    have h : (m : ℝ) ≤ ((m + 1 : ℤ) : ℝ) := by push_cast; linarith
    exact div_le_div_of_nonneg_right h (le_of_lt thS_pos)
  · -- `mo = mu m (mu m m + 1) + 1 ≥ μ³`
    have hS := thS_pos
    have hm0 : (0 : ℝ) ≤ (m : ℝ) := by exact_mod_cast (le_trans zero_le_one hm)
    have hμ0 : 0 ≤ mub m := by rw [mub]; exact div_nonneg hm0 (le_of_lt hS)
    have h1 : (mub m) * (mub m) ≤ ((mu m m : ℤ) : ℝ) / (S : ℝ) := by
      have := thmu_ge m m
      simpa only [mub] using this
    have h2 : (mub m) * ((((mu m m + 1 : ℤ)) : ℝ) / (S : ℝ)) ≤
        ((mu m (mu m m + 1) : ℤ) : ℝ) / (S : ℝ) := by
      have := thmu_ge m (mu m m + 1)
      simpa only [mub] using this
    have h1S : (mub m) * (mub m) * (S : ℝ) ≤ ((mu m m : ℤ) : ℝ) := (le_div_iff₀ hS).mp h1
    have h2S : (mub m) * (((mu m m : ℤ) : ℝ) + 1) ≤ ((mu m (mu m m + 1) : ℤ) : ℝ) := by
      have h := (le_div_iff₀ hS).mp h2
      have e : (mub m) * ((((mu m m + 1 : ℤ)) : ℝ) / (S : ℝ)) * (S : ℝ)
          = (mub m) * (((mu m m : ℤ) : ℝ) + 1) := by
        have e1 : (((mu m m + 1 : ℤ)) : ℝ) = ((mu m m : ℤ) : ℝ) + 1 := by push_cast; ring
        rw [e1]; field_simp
      rwa [e] at h
    have step1 : (mub m) ^ 3 * (S : ℝ) ≤ ((mu m m : ℤ) : ℝ) * (mub m) := by
      calc (mub m) ^ 3 * (S : ℝ) = ((mub m) * (mub m) * (S : ℝ)) * (mub m) := by ring
        _ ≤ ((mu m m : ℤ) : ℝ) * (mub m) := mul_le_mul_of_nonneg_right h1S hμ0
    have h3 : (mub m) ^ 3 * (S : ℝ) ≤ ((mu m (mu m m + 1) : ℤ) : ℝ) + 1 := by linarith
    rw [show (2 * 1 + 1 : ℕ) = 3 from rfl, le_div_iff₀ hS]
    push_cast
    linarith
  · -- `dB = 2·mu (dvu (m+1) m) rq + 17 ≥ Bd2 1 + BdM2 m rq 1 = 17 + 2rq`
    have hBd2 : Bd2 1 = 17 := by norm_num [Bd2, Finset.sum_range_one]
    have hBdM2 : BdM2 m rq 1 = 2 * (rq : ℝ) := by simp [BdM2]
    have hms : mu S m + 1 = m + 1 := by rw [mu_S]
    rw [hBd2, hBdM2, hms]
    have key : (rq : ℝ) ≤ ((mu (dvu (m + 1) m) rq : ℤ) : ℝ) := by
      have hS := thS_pos
      have hm' : (0 : ℤ) < m := by omega
      have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm'
      have hrqR : (0 : ℝ) ≤ (rq : ℝ) := by exact_mod_cast hrq
      have h3 := thdvu_ge (m + 1) m hm'
      have hmul := mul_le_mul_of_nonneg_right h3 (div_nonneg hrqR (le_of_lt hS))
      have h2 := thmu_ge (dvu (m + 1) m) rq
      have hm1 : (1 : ℝ) ≤ (((m + 1 : ℤ)) : ℝ) / (m : ℝ) := by
        rw [le_div_iff₀ hmR]; push_cast; linarith
      have hle : (rq : ℝ) / (S : ℝ)
          ≤ (((m + 1 : ℤ)) : ℝ) / (m : ℝ) * ((rq : ℝ) / (S : ℝ)) := by
        simpa using mul_le_mul_of_nonneg_right hm1 (div_nonneg hrqR (le_of_lt hS))
      have hchain : (rq : ℝ) / (S : ℝ) ≤ ((mu (dvu (m + 1) m) rq : ℤ) : ℝ) / (S : ℝ) :=
        le_trans hle (le_trans hmul h2)
      rwa [div_le_div_iff_of_pos_right hS] at hchain
    have hcast : ((0 + 2 * mu (Int.ofNat 1 * Int.ofNat 1 * dvu (m + 1) m) rq
          + 16 * Int.ofNat 1 * Int.ofNat 1 + 1 : ℤ) : ℝ)
        = 2 * ((mu (dvu (m + 1) m) rq : ℤ) : ℝ) + 17 := by norm_num; ring
    rw [hcast]
    linarith
  · -- `Br + i·Bi = 1 - 2q` exactly
    have hBsum : Bsum (qc qr qi) 1 = 1 - 2 * qc qr qi := by
      simp [Bsum]
      ring
    rw [binv_cmr_S0, binv_cmi_S0, hBsum]
    have hcx : cx (S + 2 * -1 * qr) (0 + 2 * -1 * qi) = 1 - 2 * qc qr qi := by
      have hSc : ((S : ℤ) : ℂ) ≠ 0 := by
        have : (S : ℤ) ≠ 0 := by norm_num [S]
        exact_mod_cast this
      simp only [cx, qc]
      push_cast
      field_simp
      ring
    rw [hcx, sub_self, norm_zero]
    have hBd2 : Bd2 1 = 17 := by norm_num [Bd2, Finset.sum_range_one]
    rw [hBd2]
    exact div_nonneg (by norm_num) (le_of_lt thS_pos)

end

end Work.Cert
