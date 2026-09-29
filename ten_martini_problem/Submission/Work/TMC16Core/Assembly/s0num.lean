import Mathlib
import Submission.Work.TMC16Core.Defs

open Filter Topology

namespace Work.TMC16Core.Assembly

/-! ## Helper lemmas: `(y+1) * exp(-c*y) → 0`, hence `poly ≪ exp` along `ℕ`

The only genuinely analytic ingredient of `s0num` is that a linear function of `K`
is eventually dominated by `exp (c * K)` for any positive `c`.  We obtain it from
`tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero`. -/

lemma sm_tendsto_mul_exp_neg (c : ℝ) (hc : 0 < c) :
    Tendsto (fun y : ℝ => (y + 1) * Real.exp (-(c * y))) atTop (nhds 0) := by
  have hA : Tendsto (fun y : ℝ => y ^ (1:ℝ) * Real.exp (-(c * y))) atTop (nhds 0) := by
    simpa only [neg_mul] using tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 c hc
  have hB : Tendsto (fun y : ℝ => y ^ (0:ℝ) * Real.exp (-(c * y))) atTop (nhds 0) := by
    simpa only [neg_mul] using tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 0 c hc
  have hAB : Tendsto (fun y : ℝ =>
      y ^ (1:ℝ) * Real.exp (-(c * y)) + y ^ (0:ℝ) * Real.exp (-(c * y))) atTop (nhds (0+0)) :=
    hA.add hB
  have h0 : (0:ℝ) + 0 = 0 := by norm_num
  rw [h0] at hAB
  refine hAB.congr' (Eventually.of_forall fun y => ?_)
  simp only [Real.rpow_one, Real.rpow_zero, one_mul]
  ring

lemma sm_exp_eventually_gt {a c : ℝ} (hc : 0 < c) :
    ∀ᶠ K : ℕ in atTop, a * ((K : ℝ) + 1) < Real.exp (c * (K : ℝ)) := by
  have h1 : Tendsto (fun y : ℝ => (y + 1) * Real.exp (-(c * y))) atTop (nhds 0) :=
    sm_tendsto_mul_exp_neg c hc
  have h2 : Tendsto (fun y : ℝ => a * ((y + 1) * Real.exp (-(c * y)))) atTop (nhds (a * 0)) :=
    h1.const_mul a
  rw [mul_zero] at h2
  have hreal : ∀ᶠ y : ℝ in atTop, a * (y + 1) < Real.exp (c * y) := by
    have hev : ∀ᶠ y : ℝ in atTop, a * ((y + 1) * Real.exp (-(c * y))) < 1 :=
      (tendsto_order.1 h2).2 1 zero_lt_one
    refine hev.mono fun y hy => ?_
    have hpos : 0 < Real.exp (c * y) := Real.exp_pos _
    have h2' := mul_lt_mul_of_pos_right hy hpos
    have heq : Real.exp (-(c * y)) * Real.exp (c * y) = 1 := by
      rw [Real.exp_neg, inv_mul_cancel₀ (Real.exp_ne_zero _)]
    calc a * (y + 1)
        = a * (y + 1) * (Real.exp (-(c * y)) * Real.exp (c * y)) := by rw [heq, mul_one]
      _ = (a * ((y + 1) * Real.exp (-(c * y)))) * Real.exp (c * y) := by ring
      _ < 1 * Real.exp (c * y) := h2'
      _ = Real.exp (c * y) := by ring
  exact tendsto_natCast_atTop_atTop.eventually hreal

/-- The numerical assembly lemma `s0num`: all the elementary estimates that the
S0 separation argument needs, valid for all sufficiently large `K`.

With `m = min (L/1000) (κ/8)` and `A_K = (L/4) * (1/40 + 1/K) - m`, the key
facts are `0 < m`, `m ≤ L/1000`, `0 < A_K`, `m < A_K`, `L/1000 < A_K`, the
linear estimate `(L+m)(K-1-K/40) - (K+1)(L-A_K) + (7L/10)(K/40) < 0`,
`A_K ≤ L`, and the exponential estimate `4(K+1) exp(L - A_K) < exp(K (A_K - L/1000))`. -/
theorem s0num {L κ : ℝ} (hL : 0 < L) (hκ : 0 < κ) :
    ∃ K₀ : ℕ, ∀ K : ℕ, K₀ ≤ K →
      0 < min (L / 1000) (κ / 8) ∧
      min (L / 1000) (κ / 8) ≤ L / 1000 ∧
      0 < (L / 4) * (1 / 40 + 1 / (K : ℝ)) - min (L / 1000) (κ / 8) ∧
      min (L / 1000) (κ / 8) < (L / 4) * (1 / 40 + 1 / (K : ℝ)) - min (L / 1000) (κ / 8) ∧
      L / 1000 < (L / 4) * (1 / 40 + 1 / (K : ℝ)) - min (L / 1000) (κ / 8) ∧
      0 < 7 * L / 10 ∧
      7 * L / 10 ≤ L + min (L / 1000) (κ / 8) ∧
      (L + min (L / 1000) (κ / 8)) * ((K : ℝ) - 1 - (K : ℝ) / 40)
        - ((K : ℝ) + 1) * (L - ((L / 4) * (1 / 40 + 1 / (K : ℝ)) - min (L / 1000) (κ / 8)))
        + (7 * L / 10) * ((K : ℝ) / 40) < 0 ∧
      4 * ((K : ℝ) + 1) *
          Real.exp (L - ((L / 4) * (1 / 40 + 1 / (K : ℝ)) - min (L / 1000) (κ / 8)))
        < Real.exp ((K : ℝ) *
            (((L / 4) * (1 / 40 + 1 / (K : ℝ)) - min (L / 1000) (κ / 8)) - L / 1000)) ∧
      (1 : ℝ) / 40 ≤ 1 / 40 + 1 / (K : ℝ) ∧
      1 / 40 + 1 / (K : ℝ) ≤ 1 / 2 ∧
      1 ≤ (K : ℝ) * ((1 / 40 + 1 / (K : ℝ)) - 1 / 40) ∧
      L / 4 ≤ L ∧
      (L / 4) * (1 / 40 + 1 / (K : ℝ)) - min (L / 1000) (κ / 8) ≤ L := by
  obtain ⟨K₁, hK₁⟩ := Filter.eventually_atTop.mp
    (sm_exp_eventually_gt (a := 4 * Real.exp L) (c := 17 * L / 4000) (by positivity))
  refine ⟨max K₁ 3, fun K hK => ?_⟩
  have hKc1 : K₁ ≤ K := le_trans (le_max_left _ _) hK
  have hKc3 : 3 ≤ K := le_trans (le_max_right _ _) hK
  have hKge1 : 1 ≤ K := by omega
  have hKpos : (0:ℝ) < (K:ℝ) := by exact_mod_cast (by omega : 0 < K)
  have hKne : (K:ℝ) ≠ 0 := ne_of_gt hKpos
  have hK1r : (1:ℝ) ≤ (K:ℝ) := by exact_mod_cast hKge1
  have hK3r : (3:ℝ) ≤ (K:ℝ) := by exact_mod_cast hKc3
  set m := min (L / 1000) (κ / 8) with hm
  have hm_pos : 0 < m := by rw [hm]; exact lt_min (by positivity) (by positivity)
  have hm_le : m ≤ L / 1000 := by rw [hm]; exact min_le_left _ _
  set A := (L/4)*(1/40 + 1/(K:ℝ)) - m with hA
  have hA_eq : A = L/160 + L/(4*(K:ℝ)) - m := by rw [hA]; ring
  have h4K : (0:ℝ) ≤ L/(4*(K:ℝ)) := div_nonneg hL.le (by positivity)
  have hsmall : L/(4*(K:ℝ)) ≤ L/4 := by
    apply div_le_div_of_nonneg_left hL.le (by norm_num)
    linarith [hK1r]
  have hA_pos : 0 < A := by
    rw [hA_eq]
    have h2 : (21:ℝ) * L / 4000 ≤ L/160 - m := by linarith [hm_le]
    linarith [h4K, h2, hL]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hm_pos
  · exact hm_le
  · exact hA_pos
  · rw [hA_eq]
    have h2 : (17:ℝ) * L / 4000 ≤ L/160 - 2*m := by linarith [hm_le]
    linarith [h4K, h2, hL]
  · rw [hA_eq]
    have h2 : (17:ℝ) * L / 4000 ≤ L/160 - m - L/1000 := by linarith [hm_le]
    linarith [h4K, h2, hL]
  · linarith [hL]
  · linarith [hm_pos]
  · have hmain : (L+m)*((K:ℝ) - 1 - (K:ℝ)/40) - ((K:ℝ)+1)*(L - A) + (7*L/10)*((K:ℝ)/40)
        = -(K:ℝ)*L/800 - (K:ℝ)*m/40 - 279*L/160 - 2*m + L/(4*(K:ℝ)) := by
      rw [hA_eq]; field_simp; ring
    rw [hmain]
    have h1 : (0:ℝ) ≤ (K:ℝ)*L/800 := by positivity
    have h2 : (0:ℝ) ≤ (K:ℝ)*m/40 := by positivity
    linarith [h1, h2, hsmall, hL, hm_pos]
  · have hLmA : L - A ≤ L := by linarith [hA_pos]
    have heLmA : Real.exp (L - A) ≤ Real.exp L := Real.exp_le_exp.mpr hLmA
    have hc_le : 17*L/4000 ≤ A - L/1000 := by
      rw [hA_eq]
      have h2 : (21:ℝ)*L/4000 ≤ L/160 - m := by linarith [hm_le]
      linarith [h4K, h2, hL]
    have hKc : Real.exp ((K:ℝ) * (17*L/4000)) ≤ Real.exp ((K:ℝ) * (A - L/1000)) :=
      Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hc_le (Nat.cast_nonneg K))
    have hmul : (0:ℝ) ≤ 4*((K:ℝ)+1) := by positivity
    have hLHS : 4*((K:ℝ)+1)*Real.exp (L - A) ≤ 4*Real.exp L*((K:ℝ)+1) := by
      have hh := mul_le_mul_of_nonneg_left heLmA hmul
      calc 4*((K:ℝ)+1)*Real.exp (L - A) = (4*((K:ℝ)+1))*Real.exp (L-A) := by ring
        _ ≤ (4*((K:ℝ)+1))*Real.exp L := hh
        _ = 4*Real.exp L*((K:ℝ)+1) := by ring
    have hK1e := hK₁ K hKc1
    rw [mul_comm (17*L/4000) (K:ℝ)] at hK1e
    calc 4*((K:ℝ)+1)*Real.exp (L - A) ≤ 4*Real.exp L*((K:ℝ)+1) := hLHS
      _ < Real.exp ((K:ℝ) * (17*L/4000)) := hK1e
      _ ≤ Real.exp ((K:ℝ) * (A - L/1000)) := hKc
  · have h1 : (0:ℝ) ≤ 1/(K:ℝ) := by positivity
    linarith
  · have h3 : 1/(K:ℝ) ≤ 1/3 := one_div_le_one_div_of_le (by norm_num) hK3r
    linarith
  · have he : (1/40 + 1/(K:ℝ)) - 1/40 = 1/(K:ℝ) := by ring
    rw [he, mul_one_div, div_self hKne]
  · linarith [hL]
  · rw [hA_eq]
    linarith [hsmall, hL, hm_pos]

end Work.TMC16Core.Assembly
