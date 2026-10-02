import Submission.Work.ConeSwitch.MathlibNoHG
import Submission.Work.Deep.Nibble.r2_num_basic
import Submission.Work.Deep.Nibble.log_one_sub_bound

/-!
# The "sparse regime" numerical side conditions of round 2

This file proves `Work.Deep.Nibble.r2_num_sparse`: in the regime
`n ≥ nThresh r θ δ D = 10^6 r D / (δ^2 θ^4)` (i.e. `n` large compared with `D`),
the four asymptotic side conditions needed by the second round of the nibble
hold, for all sufficiently large `D ≤ n`.

The proof rests on `r2_num_basic`, which (for all large `D`) supplies
`8 * qV r ε' θ D ≤ δ^2 θ^4 / (4096 r D)`, and on the elementary lower bound
`θ - θ exp(-θ) ≥ θ^2/2` for `0 < θ ≤ 1`.
-/

namespace Work.Deep.Nibble

/-- If `0 ≤ a`, `0 < b` and `C^2 * a < b^2`, then `C * √a < b`. -/
lemma r2ns_mul_sqrt_lt {a b C : ℝ} (ha : 0 ≤ a) (hb : 0 < b) (h : C^2 * a < b^2) :
    C * Real.sqrt a < b := by
  by_contra hcon
  push Not at hcon
  have hle := mul_self_le_mul_self hb.le hcon
  have hsq : (C * Real.sqrt a) * (C * Real.sqrt a) = C^2 * a := by
    rw [← pow_two, mul_pow, Real.sq_sqrt ha]
  rw [hsq] at hle
  rw [pow_two] at h
  linarith

theorem r2_num_sparse {r : ℕ} (hr : 2 ≤ r) {θ δ ε' ε : ℝ}
    (hθ0 : 0 < θ) (hθ1 : θ ≤ 1 / 100) (hδ0 : 0 < δ) (hδ1 : δ ≤ θ / 100)
    (hε'0 : 0 < ε') (hε'1 : ε' ≤ 1 / 2) (hε'2 : 100 * (ε + ε * (r : ℝ) * θ) ≤ ε')
    (hε0 : 0 < ε) (hε1 : ε ≤ θ / 100) (hεδ : 4 * ε ≤ δ) :
    ∃ N : ℕ, ∀ (D n : ℕ), N ≤ D → D ≤ n → Work.Deep.Nibble.nThresh r θ δ D ≤ (n:ℝ) →
      (50 * Real.sqrt (2 * (D:ℝ) * (n:ℝ) / (r:ℝ)) < δ * θ * (n:ℝ) / (2 * (r:ℝ)))
      ∧ (100 * (r:ℝ) * Real.sqrt (2 * (D:ℝ) * (n:ℝ) / (r:ℝ))
          < (δ / 2) * (θ - θ * Real.exp (-θ)) * (n:ℝ))
      ∧ (8 * Work.Deep.Nibble.qV r ε' θ D * (n:ℝ) + Real.log 48 ≤ δ^2 * θ^2 * (n:ℝ) / (128 * (r:ℝ) * (D:ℝ)))
      ∧ (8 * Work.Deep.Nibble.qV r ε' θ D * (n:ℝ) + Real.log 48 ≤ δ^2 * θ^4 * (n:ℝ) / (2048 * (r:ℝ) * (D:ℝ))) := by
  obtain ⟨N₀, hN₀⟩ := r2_num_basic hr hθ0 hθ1 hδ0 hδ1 hε'0 hε'1 hε'2 hε0 hε1 hεδ
  refine ⟨N₀, fun D n hND hDn hnT => ?_⟩
  obtain ⟨hD1n, -, -, -, -, -, -, -, hqV9, -⟩ := hN₀ D hND
  rw [nThresh] at hnT
  -- basic sign and cast facts
  have hr1 : 1 ≤ r := by omega
  have hrpos : (0:ℝ) < (r:ℝ) := by exact_mod_cast (by omega : 0 < r)
  have hD1 : 1 ≤ D := hD1n
  have hDpos : (0:ℝ) < (D:ℝ) := by exact_mod_cast (by omega : 0 < D)
  have hn1 : 1 ≤ n := le_trans hD1 hDn
  have hnpos : (0:ℝ) < (n:ℝ) := by exact_mod_cast (by omega : 0 < n)
  -- the master lower bound on `n`
  have hkey : (10:ℝ)^6 * (r:ℝ) * (D:ℝ) ≤ δ^2*θ^4*(n:ℝ) := by
    have h1 := (div_le_iff₀ (show 0 < δ^2*θ^4 by positivity)).mp hnT
    calc (10:ℝ)^6 * (r:ℝ) * (D:ℝ) ≤ (n:ℝ)*(δ^2*θ^4) := h1
      _ = δ^2*θ^4*(n:ℝ) := by ring
  -- θ^2 ≤ 10^{-4}
  have hθsq : θ^2 ≤ 1/(10:ℝ)^4 := by
    have h1 : θ*θ ≤ (1/100)*(1/100) := mul_le_mul hθ1 hθ1 hθ0.le (by norm_num)
    have h2 : θ^2 = θ*θ := pow_two θ
    have h3 : (1/100)*(1/100) = 1/((10:ℝ)^4) := by norm_num
    rw [h3] at h1
    rwa [h2]
  have hθ16 : θ^2 ≤ 16 := by nlinarith [hθ0, hθ1]
  -- `20000 θ^2 ≤ 2`
  have hupper : 20000 * θ^2 ≤ 2 := by
    have h1 : 20000 * θ^2 ≤ 20000 * (1/(10:ℝ)^4) :=
      mul_le_mul_of_nonneg_left hθsq (by norm_num)
    norm_num at h1 ⊢
    linarith
  -- `20000 D r < δ^2 θ^2 n`
  have hN1 : 20000*(D:ℝ)*(r:ℝ) < δ^2*θ^2*(n:ℝ) := by
    have h2 : 20000*(D:ℝ)*(r:ℝ)*θ^2 ≤ 2*(D:ℝ)*(r:ℝ) := by
      have h3 := mul_le_mul_of_nonneg_right hupper (mul_nonneg hDpos.le hrpos.le)
      nlinarith [h3]
    have h4 : 2*(D:ℝ)*(r:ℝ) < δ^2*θ^4*(n:ℝ) := by
      have h5 : 2*(D:ℝ)*(r:ℝ) < (10:ℝ)^6*(r:ℝ)*(D:ℝ) := by
        have h6 : (2:ℝ) < (10:ℝ)^6 := by norm_num
        have h7 := mul_lt_mul_of_pos_right h6 (mul_pos hDpos hrpos)
        nlinarith [h7, hkey]
      linarith [h5, hkey]
    have h1 : (20000*(D:ℝ)*(r:ℝ))*θ^2 < (δ^2*θ^2*(n:ℝ))*θ^2 := by
      have h8 : δ^2*θ^4*(n:ℝ) = (δ^2*θ^2*(n:ℝ))*θ^2 := by ring
      nlinarith [h2, h4, h8]
    have hθ2pos : 0 < θ^2 := by positivity
    by_contra hc
    push Not at hc
    have h9 := mul_le_mul_of_nonneg_right hc hθ2pos.le
    linarith
  -- `320000 D r < δ^2 θ^4 n`
  have hF2 : 320000*(D:ℝ)*(r:ℝ) < δ^2*θ^4*(n:ℝ) := by
    have h5 : 320000*(D:ℝ)*(r:ℝ) < (10:ℝ)^6*(r:ℝ)*(D:ℝ) := by
      have h6 : (320000:ℝ) < (10:ℝ)^6 := by norm_num
      have h7 := mul_lt_mul_of_pos_right h6 (mul_pos hDpos hrpos)
      nlinarith [h7, hkey]
    linarith [h5, hkey]
  -- the lower bound `θ^2/2 ≤ θ - θ exp(-θ)`
  have hTlow : θ^2/2 ≤ θ - θ*Real.exp (-θ) := by
    have hx0 : 0 ≤ θ/2 := by linarith
    have hx1 : θ/2 ≤ 1/2 := by linarith
    have hlog := log_one_sub_bound hx0 hx1
    have hlog' : -θ ≤ Real.log (1 - θ/2) := by linarith
    have h1p : 0 < 1 - θ/2 := by linarith
    have hexp : Real.exp (-θ) ≤ 1 - θ/2 := by
      have h := Real.exp_le_exp.mpr hlog'
      rwa [Real.exp_log h1p] at h
    have hm := mul_le_mul_of_nonneg_left hexp hθ0.le
    nlinarith [hm]
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- (A) 50 √(2Dn/r) < δ θ n /(2r)
    have ha : 0 ≤ 2*(D:ℝ)*(n:ℝ)/(r:ℝ) := by positivity
    have hb : 0 < δ*θ*(n:ℝ)/(2*(r:ℝ)) := by positivity
    refine r2ns_mul_sqrt_lt ha hb ?_
    have hN1n : 20000*(D:ℝ)*(r:ℝ)*(n:ℝ) < δ^2*θ^2*(n:ℝ)*(n:ℝ) :=
      mul_lt_mul_of_pos_right hN1 hnpos
    field_simp
    nlinarith [hN1n]
  · -- (B) 100 r √(2Dn/r) < (δ/2)(θ - θ e^{-θ}) n
    have hRHSmono : (δ/2)*(θ^2/2)*(n:ℝ) ≤ (δ/2)*(θ - θ*Real.exp (-θ))*(n:ℝ) := by
      have h1 : (δ/2)*(θ^2/2) ≤ (δ/2)*(θ - θ*Real.exp (-θ)) :=
        mul_le_mul_of_nonneg_left hTlow (by positivity)
      exact mul_le_mul_of_nonneg_right h1 hnpos.le
    have hBsmall : 100*(r:ℝ)*Real.sqrt (2*(D:ℝ)*(n:ℝ)/(r:ℝ)) < (δ/2)*(θ^2/2)*(n:ℝ) := by
      have ha : 0 ≤ 2*(D:ℝ)*(n:ℝ)/(r:ℝ) := by positivity
      have hb : 0 < (δ/2)*(θ^2/2)*(n:ℝ) := by positivity
      refine r2ns_mul_sqrt_lt ha hb ?_
      have hF2n : 320000*(D:ℝ)*(r:ℝ)*(n:ℝ) < δ^2*θ^4*(n:ℝ)*(n:ℝ) :=
        mul_lt_mul_of_pos_right hF2 hnpos
      field_simp
      nlinarith [hF2n]
    exact lt_of_lt_of_le hBsmall hRHSmono
  · -- (C) 8 qV n + log 48 ≤ δ^2 θ^2 n /(128 r D)
    have hC1 : 8*qV r ε' θ D*(n:ℝ) ≤ δ^2*θ^4*(n:ℝ)/(4096*(r:ℝ)*(D:ℝ)) := by
      have h := mul_le_mul_of_nonneg_right hqV9 hnpos.le
      rwa [div_mul_eq_mul_div] at h
    have hC2 : Real.log 48 ≤ δ^2*θ^4*(n:ℝ)/(4096*(r:ℝ)*(D:ℝ)) := by
      have h1 : (10:ℝ)^6*(r:ℝ)*(D:ℝ)/(4096*(r:ℝ)*(D:ℝ))
          ≤ δ^2*θ^4*(n:ℝ)/(4096*(r:ℝ)*(D:ℝ)) :=
        div_le_div_of_nonneg_right hkey (by positivity)
      have h2 : (10:ℝ)^6*(r:ℝ)*(D:ℝ)/(4096*(r:ℝ)*(D:ℝ)) = (10:ℝ)^6/4096 := by
        field_simp
      have h3 : (48:ℝ) ≤ (10:ℝ)^6/4096 := by
        rw [le_div_iff₀ (by norm_num : (0:ℝ) < 4096)]
        norm_num
      have h4 : Real.log 48 ≤ 48 := Real.log_le_self (by norm_num)
      linarith
    have hC3 : 2*(δ^2*θ^4*(n:ℝ)/(4096*(r:ℝ)*(D:ℝ)))
        ≤ δ^2*θ^2*(n:ℝ)/(128*(r:ℝ)*(D:ℝ)) := by
      field_simp
      nlinarith [hθ16]
    linarith [hC1, hC2, hC3]
  · -- (D) 8 qV n + log 48 ≤ δ^2 θ^4 n /(2048 r D)
    have hC1 : 8*qV r ε' θ D*(n:ℝ) ≤ δ^2*θ^4*(n:ℝ)/(4096*(r:ℝ)*(D:ℝ)) := by
      have h := mul_le_mul_of_nonneg_right hqV9 hnpos.le
      rwa [div_mul_eq_mul_div] at h
    have hC2 : Real.log 48 ≤ δ^2*θ^4*(n:ℝ)/(4096*(r:ℝ)*(D:ℝ)) := by
      have h1 : (10:ℝ)^6*(r:ℝ)*(D:ℝ)/(4096*(r:ℝ)*(D:ℝ))
          ≤ δ^2*θ^4*(n:ℝ)/(4096*(r:ℝ)*(D:ℝ)) :=
        div_le_div_of_nonneg_right hkey (by positivity)
      have h2 : (10:ℝ)^6*(r:ℝ)*(D:ℝ)/(4096*(r:ℝ)*(D:ℝ)) = (10:ℝ)^6/4096 := by
        field_simp
      have h3 : (48:ℝ) ≤ (10:ℝ)^6/4096 := by
        rw [le_div_iff₀ (by norm_num : (0:ℝ) < 4096)]
        norm_num
      have h4 : Real.log 48 ≤ 48 := Real.log_le_self (by norm_num)
      linarith
    have hD3 : 2*(δ^2*θ^4*(n:ℝ)/(4096*(r:ℝ)*(D:ℝ)))
        = δ^2*θ^4*(n:ℝ)/(2048*(r:ℝ)*(D:ℝ)) := by
      field_simp
      ring
    linarith [hC1, hC2, hD3]

end Work.Deep.Nibble
