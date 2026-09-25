import Mathlib

namespace Work.NN.Newton

/-- Pure real arithmetic for the constants of `Work.NN.Newton.newtonCorrection`: with
`N := N1 + N2` and `C` large enough (roughly
`C1 * 2^N1 * (n:ℝ) * (1/2 + C2 * 2^N2 * (n:ℝ)^2 * C3) + C2 * 2^N2 * (n:ℝ)^2 * C3 + 1`),
both inequalities below hold for every `δ ∈ (0, 1/8]` and `a ∈ [0,1]`.

Hints: `(δ/2)^N = δ^N / 2^N` (`div_pow`, `mul_pow`), `a ^ 2 ≤ a` (`pow_le_one₀`, `pow_two`),
`δ ^ k ≤ 1` and `1 ≤ 1 / δ ^ k` for `k ≥ 0` (`pow_le_one₀`, `one_le_div`), and
`(δ/2)/(1-δ/2) ≥ δ/2` because `1 - δ/2 ≤ 1` (so `1 / d₁ ^ N1 ≤ 2^N1 / δ^N1`).
`0 ≤ (n:ℝ)` comes from `hn`. -/
theorem newtonCorrectionArith {n : ℕ} (hn : 0 < n) {C1 C2 C3 : ℝ} (h1 : 0 < C1) (h2 : 0 < C2)
    (h3 : 0 < C3) (N1 N2 : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∃ N : ℕ, ∀ δ a : ℝ, 0 < δ → δ ≤ 1 / 8 → 0 ≤ a → a ≤ 1 →
      C1 / ((δ / 2) / (1 - δ / 2)) ^ N1
          * ((n : ℝ) * (a / 2 + C2 / (δ / 2) ^ N2 * ((n : ℝ) ^ 2 * C3 * a ^ 2)))
        ≤ C / δ ^ N * a ∧
      C2 / (δ / 2) ^ N2 * ((n : ℝ) ^ 2 * C3 * a ^ 2) ≤ C / δ ^ N * a ^ 2 := by
  have hnpos : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
  refine ⟨C1 * (2:ℝ)^N1 * (n:ℝ) / 2 + C1 * C2 * C3 * (2:ℝ)^(N1+N2) * (n:ℝ)^3
      + C2 * (2:ℝ)^N2 * (n:ℝ)^2 * C3 + 1, ?_, N1+N2, ?_⟩
  · positivity
  set W : ℝ := C1 * (2:ℝ)^N1 * (n:ℝ) / 2 + C1 * C2 * C3 * (2:ℝ)^(N1+N2) * (n:ℝ)^3
      + C2 * (2:ℝ)^N2 * (n:ℝ)^2 * C3 + 1 with hW
  intro δ a hδ hδ8 ha0 ha1
  -- basic size facts about `δ`
  have hδ1 : δ ≤ 1 := by linarith
  have hhalfpos : 0 < δ/2 := by linarith
  have hone : 0 < 1 - δ/2 := by linarith
  have ha2 : a^2 ≤ a := by nlinarith [mul_nonneg ha0 (by linarith : (0:ℝ) ≤ 1 - a)]
  have hd1ppos : 0 < δ^N1 := pow_pos hδ N1
  have hd2ppos : 0 < δ^N2 := pow_pos hδ N2
  have hdNpos : 0 < δ^(N1+N2) := pow_pos hδ _
  have hd1ple : δ^N1 ≤ 1 := pow_le_one₀ (n := N1) hδ.le hδ1
  have hd2ple : δ^N2 ≤ 1 := pow_le_one₀ (n := N2) hδ.le hδ1
  have hdNle1 : δ^(N1+N2) ≤ δ^N1 := by
    rw [pow_add]; exact mul_le_of_le_one_right hd1ppos.le hd2ple
  have hdNle2 : δ^(N1+N2) ≤ δ^N2 := by
    rw [pow_add]; nlinarith [mul_le_mul_of_nonneg_right hd1ple hd2ppos.le]
  -- reciprocal bounds: `1/d₁^N1 ≤ 2^N1/δ^N1` and `1/(δ/2)^N2 ≤ 2^N2/δ^N2`
  have hP : 1 / ((δ/2)/(1-δ/2))^N1 ≤ (2:ℝ)^N1/δ^N1 := by
    have hge : δ/2 ≤ (δ/2)/(1-δ/2) := by
      rw [le_div_iff₀ hone]
      exact mul_le_of_le_one_right hhalfpos.le (by linarith : 1 - δ/2 ≤ 1)
    have hpow : (δ/2)^N1 ≤ ((δ/2)/(1-δ/2))^N1 := pow_le_pow_left₀ hhalfpos.le hge N1
    have hh : 1 / ((δ/2)/(1-δ/2))^N1 ≤ 1 / (δ/2)^N1 :=
      one_div_le_one_div_of_le (show 0 < (δ/2)^N1 by positivity) hpow
    have hS : 1 / (δ/2)^N1 = (2:ℝ)^N1 / δ^N1 := by rw [div_pow, one_div_div]
    rwa [hS] at hh
  have hQ : 1 / (δ/2)^N2 ≤ (2:ℝ)^N2 / δ^N2 := by rw [div_pow, one_div_div]
  have hC2S : C2 / (δ/2)^N2 ≤ C2 * ((2:ℝ)^N2/δ^N2) := by
    rw [div_eq_mul_one_div]
    exact mul_le_mul_of_nonneg_left hQ h2.le
  have hP' : C1 / ((δ/2)/(1-δ/2))^N1 ≤ C1 * ((2:ℝ)^N1/δ^N1) := by
    rw [div_eq_mul_one_div]
    exact mul_le_mul_of_nonneg_left hP h1.le
  have hInner : a/2 + C2/(δ/2)^N2*((n:ℝ)^2*C3*a^2)
      ≤ a/2 + C2*((2:ℝ)^N2/δ^N2)*((n:ℝ)^2*C3*a^2) := by
    have := mul_le_mul_of_nonneg_right hC2S (by positivity : (0:ℝ) ≤ (n:ℝ)^2*C3*a^2)
    linarith
  have hR : (n:ℝ)*(a/2 + C2/(δ/2)^N2*((n:ℝ)^2*C3*a^2))
      ≤ (n:ℝ)*(a/2 + C2*((2:ℝ)^N2/δ^N2)*((n:ℝ)^2*C3*a^2)) :=
    mul_le_mul_of_nonneg_left hInner hnpos.le
  have hstep1 : C1 / ((δ/2)/(1-δ/2))^N1 * ((n:ℝ)*(a/2 + C2/(δ/2)^N2*((n:ℝ)^2*C3*a^2)))
      ≤ C1 * ((2:ℝ)^N1/δ^N1) * ((n:ℝ)*(a/2 + C2*((2:ℝ)^N2/δ^N2)*((n:ℝ)^2*C3*a^2))) := by
    apply mul_le_mul hP' hR
    · positivity
    · positivity
  have hE : C1 * ((2:ℝ)^N1/δ^N1) * ((n:ℝ)*(a/2 + C2*((2:ℝ)^N2/δ^N2)*((n:ℝ)^2*C3*a^2)))
      = a * (C1*(2:ℝ)^N1*(n:ℝ)/2)/δ^N1
        + a^2*(C1*C2*C3*(2:ℝ)^(N1+N2)*(n:ℝ)^3)/δ^(N1+N2) := by
    have h2p : (2:ℝ)^(N1+N2) = (2:ℝ)^N1 * (2:ℝ)^N2 := by rw [pow_add]
    have hδp : δ^(N1+N2) = δ^N1 * δ^N2 := pow_add δ N1 N2
    rw [h2p, hδp]
    ring_nf
  have hMsum : C1*(2:ℝ)^N1*(n:ℝ)/2 + C1*C2*C3*(2:ℝ)^(N1+N2)*(n:ℝ)^3 ≤ W := by
    rw [hW]
    nlinarith [show (0:ℝ) ≤ C2*(2:ℝ)^N2*(n:ℝ)^2*C3 + 1 by positivity]
  have hM3le : C2*(2:ℝ)^N2*(n:ℝ)^2*C3 ≤ W := by
    rw [hW]
    nlinarith [show (0:ℝ) ≤ C1*(2:ℝ)^N1*(n:ℝ)/2 + C1*C2*C3*(2:ℝ)^(N1+N2)*(n:ℝ)^3 + 1 by positivity]
  have key1 : C1 / ((δ/2)/(1-δ/2))^N1 * ((n:ℝ)*(a/2 + C2/(δ/2)^N2*((n:ℝ)^2*C3*a^2)))
      ≤ a * W / δ^(N1+N2) := by
    calc
      _ ≤ C1 * ((2:ℝ)^N1/δ^N1) * ((n:ℝ)*(a/2 + C2*((2:ℝ)^N2/δ^N2)*((n:ℝ)^2*C3*a^2))) := hstep1
      _ = a * (C1*(2:ℝ)^N1*(n:ℝ)/2)/δ^N1
          + a^2*(C1*C2*C3*(2:ℝ)^(N1+N2)*(n:ℝ)^3)/δ^(N1+N2) := hE
      _ ≤ a * (C1*(2:ℝ)^N1*(n:ℝ)/2)/δ^N1
          + a*(C1*C2*C3*(2:ℝ)^(N1+N2)*(n:ℝ)^3)/δ^(N1+N2) := by
            gcongr
      _ ≤ a * (C1*(2:ℝ)^N1*(n:ℝ)/2)/δ^(N1+N2)
          + a*(C1*C2*C3*(2:ℝ)^(N1+N2)*(n:ℝ)^3)/δ^(N1+N2) := by
            gcongr
      _ = a * (C1*(2:ℝ)^N1*(n:ℝ)/2 + C1*C2*C3*(2:ℝ)^(N1+N2)*(n:ℝ)^3)/δ^(N1+N2) := by ring
      _ ≤ a * W / δ^(N1+N2) := by
            gcongr
  have hE2 : C2 * ((2:ℝ)^N2/δ^N2) * ((n:ℝ)^2*C3*a^2) = a^2*(C2*(2:ℝ)^N2*(n:ℝ)^2*C3)/δ^N2 := by ring_nf
  have key2 : C2 / (δ/2)^N2 * ((n:ℝ)^2*C3*a^2) ≤ W / δ^(N1+N2) * a^2 := by
    calc
      _ ≤ C2 * ((2:ℝ)^N2/δ^N2) * ((n:ℝ)^2*C3*a^2) := mul_le_mul_of_nonneg_right hC2S (by positivity)
      _ = a^2*(C2*(2:ℝ)^N2*(n:ℝ)^2*C3)/δ^N2 := hE2
      _ ≤ a^2*(C2*(2:ℝ)^N2*(n:ℝ)^2*C3)/δ^(N1+N2) := by gcongr
      _ ≤ a^2*W/δ^(N1+N2) := by gcongr
      _ = W/δ^(N1+N2)*a^2 := by ring
  exact ⟨key1.trans (le_of_eq (by ring : a * W / δ^(N1+N2) = W / δ^(N1+N2) * a)), key2⟩

end Work.NN.Newton
