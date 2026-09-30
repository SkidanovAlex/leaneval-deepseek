import Mathlib
import Submission.Work.BMF.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF

/-- Eventually, any fixed power of `log P` is dominated by `K * P^{1/2}`.

This is the analytic input to `n4_num_sqrt_bound`: it says that for `P` large enough
(how large depending only on the two constants and the exponent) the quantity
`a * (log P)^n` is at most `K * P^{1/2}`.  It is a direct consequence of the
little-o statement `log^n =o P^{1/2}` at `+∞`. -/
lemma log_pow_le_rpow_half (n : ℕ) (a K : ℝ) (ha : 0 < a) (hK : 0 < K) :
    ∃ P₀ : ℝ, ∀ P : ℝ, P₀ ≤ P → a * Real.log P ^ n ≤ K * P ^ ((1:ℝ)/2) := by
  have hlit : (fun x : ℝ => Real.log x ^ (n : ℝ)) =o[Filter.atTop]
      (fun x : ℝ => x ^ ((1:ℝ)/2)) :=
    isLittleO_log_rpow_rpow_atTop (n:ℝ) (by norm_num)
  rw [Asymptotics.isLittleO_iff] at hlit
  have hc : 0 < K / a := div_pos hK ha
  obtain ⟨P₀, hP₀⟩ := Filter.eventually_atTop.mp (hlit hc)
  refine ⟨max P₀ 1, fun P hP => ?_⟩
  have hP1 : (1:ℝ) ≤ P := le_trans (le_max_right _ _) hP
  have hPP : P₀ ≤ P := le_trans (le_max_left _ _) hP
  have hkey := hP₀ P hPP
  have hlog : 0 ≤ Real.log P := Real.log_nonneg hP1
  have h1 : ‖Real.log P ^ (n:ℝ)‖ = Real.log P ^ (n:ℝ) :=
    Real.norm_of_nonneg (Real.rpow_nonneg hlog n)
  have h2 : ‖P ^ ((1:ℝ)/2)‖ = P ^ ((1:ℝ)/2) :=
    Real.norm_of_nonneg (Real.rpow_nonneg (by linarith) _)
  rw [h1, h2] at hkey
  have h3 : Real.log P ^ n = Real.log P ^ (n:ℝ) := (Real.rpow_natCast _ _).symm
  rw [h3]
  calc a * Real.log P ^ (n:ℝ) ≤ a * ((K/a) * P ^ ((1:ℝ)/2)) :=
        mul_le_mul_of_nonneg_left hkey ha.le
    _ = K * P ^ ((1:ℝ)/2) := by field_simp

/-- The "square-root" numerical bound of the MRT/MRTTZ pipeline (node `n4`).

For every `ℓ ≥ 2` and every pair of constants `C₁, K > 0` there is a threshold `P₀` such
that whenever `P ≥ P₀`, `N ≥ 3` with `N ≤ P^{ℓ-1}`, `C₀ ≥ 1/log P` and `r ≤ P^{1/2}`, one has

`(C₁ π₀(P))^ℓ · (ℓ+1)^ℓ · r ≤ K C₀ π₀(P)^{2ℓ} / N · 1/log N`,

where `π₀(P) = P / log P`.

This is the estimate that lets one throw away the factor `r = X/N` (which is at most
`P^{1/2}`) against the gain `π₀(P)^ℓ` produced by the MRT counting, at the cost of a
constant `C₀` and a factor `1/log N`.  The whole content is that for `P → ∞` the ratio
`P^{1/2} / (log P)^{ℓ+2}` tends to `∞`, i.e. elementary asymptotics. -/
lemma n4_num_sqrt_bound (ℓ : ℕ) (hℓ : 2 ≤ ℓ) (C₁ K : ℝ) (hC₁ : 0 < C₁) (hK : 0 < K) :
    ∃ P₀ : ℝ, ∀ (P N C₀ r : ℝ), P₀ ≤ P → 3 ≤ N → N ≤ P ^ (ℓ - 1) → 1 / Real.log P ≤ C₀ →
      r ≤ P ^ ((1 : ℝ) / 2) →
      (C₁ * pi0 P) ^ ℓ * ((ℓ + 1 : ℕ) : ℝ) ^ ℓ * r ≤
        K * C₀ * pi0 P ^ (2 * ℓ) / N * (1 / Real.log N) := by
  have hℓ1 : 1 ≤ ℓ := by omega
  have hm1pos : (0:ℝ) < ((ℓ - 1 : ℕ) : ℝ) := by
    have : 0 < ℓ - 1 := by omega
    exact_mod_cast this
  set a : ℝ := C₁^ℓ * ((ℓ+1:ℕ):ℝ)^ℓ * ((ℓ-1:ℕ):ℝ) with ha_def
  have ha_pos : 0 < a := by
    rw [ha_def]
    exact mul_pos (mul_pos (pow_pos hC₁ ℓ) (pow_pos (by positivity) ℓ)) hm1pos
  obtain ⟨Q, hQ⟩ := log_pow_le_rpow_half (ℓ+2) a K ha_pos hK
  refine ⟨max Q 3, fun P N C₀ r hP hN3 hNle hC0 hr => ?_⟩
  have hP3 : (3:ℝ) ≤ P := le_trans (le_max_right _ _) hP
  have hQP : Q ≤ P := le_trans (le_max_left _ _) hP
  have hP1 : (1:ℝ) < P := by linarith
  have hPpos : 0 < P := by linarith
  have hLp : 0 < Real.log P := Real.log_pos hP1
  have hNpos : 0 < N := by linarith
  have hN1 : (1:ℝ) < N := by linarith
  have hLn : 0 < Real.log N := Real.log_pos hN1
  have hπpos : 0 < pi0 P := by rw [pi0]; positivity
  have hana : a * (Real.log P)^(ℓ+2) ≤ K * P^((1:ℝ)/2) := hQ P hQP
  have hsq : P^((1:ℝ)/2) * P^((1:ℝ)/2) = P := by
    rw [← Real.rpow_add hPpos]; norm_num
  have hpoweq : P * P^(ℓ-1) = P^ℓ := by
    rw [← pow_succ' P (ℓ-1), Nat.sub_add_cancel hℓ1]
  have hLnle : Real.log N ≤ ((ℓ-1:ℕ):ℝ) * Real.log P := by
    calc Real.log N ≤ Real.log (P^(ℓ-1)) := Real.log_le_log hNpos hNle
      _ = ((ℓ-1:ℕ):ℝ) * Real.log P := Real.log_pow P (ℓ-1)
  have hNLn : N * Real.log N ≤ P^(ℓ-1) * (((ℓ-1:ℕ):ℝ) * Real.log P) :=
    mul_le_mul hNle hLnle (le_of_lt hLn) (by positivity)
  have hG3 : C₁^ℓ * ((ℓ+1:ℕ):ℝ)^ℓ * P^((1:ℝ)/2) * (N * Real.log N) *
      (Real.log P)^(ℓ+1) ≤ K * P^ℓ := by
    have hii : C₁^ℓ * ((ℓ+1:ℕ):ℝ)^ℓ * P^((1:ℝ)/2) * (N * Real.log N) * (Real.log P)^(ℓ+1)
        ≤ C₁^ℓ * ((ℓ+1:ℕ):ℝ)^ℓ * P^((1:ℝ)/2) *
            (P^(ℓ-1) * (((ℓ-1:ℕ):ℝ) * Real.log P)) * (Real.log P)^(ℓ+1) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hNLn (by positivity)) (by positivity)
    have hiii : C₁^ℓ * ((ℓ+1:ℕ):ℝ)^ℓ * P^((1:ℝ)/2) *
            (P^(ℓ-1) * (((ℓ-1:ℕ):ℝ) * Real.log P)) * (Real.log P)^(ℓ+1)
        = a * (P^((1:ℝ)/2) * P^(ℓ-1)) * (Real.log P)^(ℓ+2) := by
      have hpow2 : Real.log P * (Real.log P)^(ℓ+1) = (Real.log P)^(ℓ+2) := by
        rw [mul_comm, ← pow_succ]
      rw [ha_def, ← hpow2]
      ring
    have hiv : a * (P^((1:ℝ)/2) * P^(ℓ-1)) * (Real.log P)^(ℓ+2)
        ≤ K * (P^((1:ℝ)/2) * P^(ℓ-1)) * P^((1:ℝ)/2) := by
      have h := mul_le_mul_of_nonneg_right hana (by positivity : 0 ≤ P^((1:ℝ)/2) * P^(ℓ-1))
      calc a * (P^((1:ℝ)/2) * P^(ℓ-1)) * (Real.log P)^(ℓ+2)
          = (a * (Real.log P)^(ℓ+2)) * (P^((1:ℝ)/2) * P^(ℓ-1)) := by ring
        _ ≤ (K * P^((1:ℝ)/2)) * (P^((1:ℝ)/2) * P^(ℓ-1)) := h
        _ = K * (P^((1:ℝ)/2) * P^(ℓ-1)) * P^((1:ℝ)/2) := by ring
    have hv : K * (P^((1:ℝ)/2) * P^(ℓ-1)) * P^((1:ℝ)/2) = K * P^ℓ := by
      calc K * (P^((1:ℝ)/2) * P^(ℓ-1)) * P^((1:ℝ)/2)
          = K * ((P^((1:ℝ)/2) * P^((1:ℝ)/2)) * P^(ℓ-1)) := by ring
        _ = K * (P * P^(ℓ-1)) := by rw [hsq]
        _ = K * P^ℓ := by rw [hpoweq]
    exact le_trans (le_trans hii (le_of_eq hiii)) (le_trans hiv (le_of_eq hv))
  have hG2 : C₁^ℓ * ((ℓ+1:ℕ):ℝ)^ℓ * P^((1:ℝ)/2) * (N * Real.log N) * (Real.log P)^ℓ
      ≤ K * C₀ * P^ℓ := by
    have h1 : C₁^ℓ * ((ℓ+1:ℕ):ℝ)^ℓ * P^((1:ℝ)/2) * (N * Real.log N) * (Real.log P)^ℓ
        ≤ K * P^ℓ / Real.log P :=
      (le_div_iff₀ hLp).mpr (by rw [mul_assoc, ← pow_succ]; exact hG3)
    have h2 : K * P^ℓ / Real.log P ≤ K * C₀ * P^ℓ := by
      rw [show K * P^ℓ / Real.log P = K * (1 / Real.log P) * P^ℓ from by ring]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hC0 (le_of_lt hK)) (by positivity)
    exact le_trans h1 h2
  have hπpow : (pi0 P)^ℓ = P^ℓ / (Real.log P)^ℓ := by
    rw [pi0, div_pow]
  have hle1 : C₁^ℓ * ((ℓ+1:ℕ):ℝ)^ℓ * P^((1:ℝ)/2) * (N * Real.log N) ≤ K * C₀ * (pi0 P)^ℓ := by
    rw [hπpow]
    rw [show K * C₀ * (P^ℓ / (Real.log P)^ℓ) = K * C₀ * P^ℓ / (Real.log P)^ℓ from by ring]
    rw [le_div_iff₀ (pow_pos hLp ℓ)]
    exact hG2
  have hcore : C₁^ℓ * ((ℓ+1:ℕ):ℝ)^ℓ * P^((1:ℝ)/2) ≤ K * C₀ * (pi0 P)^ℓ / (N * Real.log N) :=
    (le_div_iff₀ (by positivity : 0 < N * Real.log N)).mpr hle1
  have hfnn : 0 ≤ (C₁ * pi0 P)^ℓ * ((ℓ+1:ℕ):ℝ)^ℓ :=
    mul_nonneg (pow_nonneg (le_of_lt (mul_pos hC₁ hπpos)) ℓ) (pow_nonneg (by positivity) ℓ)
  calc (C₁ * pi0 P)^ℓ * ((ℓ+1:ℕ):ℝ)^ℓ * r
      ≤ (C₁ * pi0 P)^ℓ * ((ℓ+1:ℕ):ℝ)^ℓ * P^((1:ℝ)/2) :=
        mul_le_mul_of_nonneg_left hr hfnn
    _ = (pi0 P)^ℓ * (C₁^ℓ * ((ℓ+1:ℕ):ℝ)^ℓ * P^((1:ℝ)/2)) := by rw [mul_pow]; ring
    _ ≤ (pi0 P)^ℓ * (K * C₀ * (pi0 P)^ℓ / (N * Real.log N)) :=
        mul_le_mul_of_nonneg_left hcore (pow_nonneg (le_of_lt hπpos) ℓ)
    _ = K * C₀ * (pi0 P)^(2 * ℓ) / N * (1 / Real.log N) := by
        rw [show 2 * ℓ = ℓ + ℓ by omega, pow_add]; ring

end Work.BMF
