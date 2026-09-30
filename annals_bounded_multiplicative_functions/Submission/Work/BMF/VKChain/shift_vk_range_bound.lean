import Mathlib
import Submission.Work.BMF.VKGrowth
import Submission.Work.BMF.VKGrowthDefs
import Submission.Commons.Analysis.Complex.conj_cpow_ofReal_of_nonneg

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The Vinogradov–Korobov range bound for the shift-difference series

We bound `∑_{K₀ < m ≤ Nt} shiftTerm a m (σ + i t)`, where `Nt ≤ |t| + 1` and `K₀` lies in the
Vinogradov–Korobov range `log K₀ ≥ (log(|t|+3)/cvk)^{6/7}`, by `2 Cvk e^{1/2} Ab`, where `Ab`
dominates `(1 + log(|t|+3)/log 2) exp(-θ)`, `θ` being the VK saving exponent at the threshold
`log K = (log(|t|+3)/cvk)^{6/7}`.

The range `(K₀, Nt]` is split into `≤ 1 + log(|t|+3)/log 2` dyadic blocks; on each block the VK
saving `γ(K) log K ≥ θ` beats the loss `(1-σ) log K ≤ 1/2`.
-/

namespace Work.BMF.VKChain

open Finset
open scoped BigOperators

noncomputable section

set_option linter.unusedVariables false

/-! ## Dyadic summation -/

/-- Dyadic summation: if every block `(K,R]` inside `(K₀,M]` with `R ≤ 2K` is bounded by `B`,
then `(K₀,M]` is bounded by `(J+1)B`, where `K₀ 2^J ≤ M ≤ K₀ 2^{J+1}`. -/
theorem dyadic_ioc_le {f : ℕ → ℂ} {K₀ : ℕ} (hK₀ : 1 ≤ K₀) {B : ℝ} (hB : 0 ≤ B) :
    ∀ (J M : ℕ), K₀ * 2 ^ J ≤ M → M ≤ K₀ * 2 ^ (J + 1) →
      (∀ K R : ℕ, K₀ ≤ K → K ≤ R → R ≤ 2 * K → R ≤ M →
        ‖∑ n ∈ Finset.Ioc K R, f n‖ ≤ B) →
      ‖∑ n ∈ Finset.Ioc K₀ M, f n‖ ≤ ((J : ℝ) + 1) * B := by
  intro J
  induction J with
  | zero =>
    intro M hM hM' hblock
    have h := hblock K₀ M le_rfl (by simpa using hM) (by simpa [mul_comm] using hM') le_rfl
    simpa using h
  | succ J ih =>
    intro M hM hM' hblock
    set A : ℕ := K₀ * 2 ^ (J + 1) with hA
    have hKA : K₀ ≤ A := by
      rw [hA]
      calc K₀ = K₀ * 1 := (mul_one _).symm
        _ ≤ K₀ * 2 ^ (J + 1) := Nat.mul_le_mul_left _ Nat.one_le_two_pow
    have hA1 : K₀ * 2 ^ J ≤ A := by
      rw [hA]
      exact Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) (by omega))
    have hAA : A ≤ K₀ * 2 ^ (J + 1) := le_of_eq hA
    have h1 : ‖∑ n ∈ Finset.Ioc K₀ A, f n‖ ≤ ((J : ℝ) + 1) * B := by
      refine ih A hA1 hAA ?_
      intro K R hK hKR hR2K hRM
      exact hblock K R hK hKR hR2K (le_trans hRM hM)
    have hMA : M ≤ 2 * A := by
      have h2 : K₀ * 2 ^ (J + 1 + 1) = 2 * A := by rw [hA]; ring
      calc M ≤ K₀ * 2 ^ (J + 1 + 1) := hM'
        _ = 2 * A := h2
    have h2 : ‖∑ n ∈ Finset.Ioc A M, f n‖ ≤ B :=
      hblock A M hKA hM hMA le_rfl
    rw [Work.BMF.sum_Ioc_split hKA hM]
    have h3 : ‖(∑ n ∈ Finset.Ioc K₀ A, f n) + ∑ n ∈ Finset.Ioc A M, f n‖ ≤
        ((J : ℝ) + 1) * B + B :=
      le_trans (norm_add_le _ _) (add_le_add h1 h2)
    have h4 : ((J : ℝ) + 1) * B + B ≤ ((↑(J + 1) : ℝ) + 1) * B := by
      have : (↑(J+1) : ℝ) = (J:ℝ) + 1 := by push_cast; ring
      rw [this]; ring_nf; exact le_refl _
    exact le_trans h3 h4

/-- The number of dyadic blocks up to `Nt` is at most `1 + log(t+3)/log 2`. -/
theorem dyadic_block_count {K₀ Nt J : ℕ} {t : ℝ} (hK₀1 : 1 ≤ K₀) (hJ : K₀ * 2 ^ J ≤ Nt)
    (hNt : (Nt : ℝ) ≤ t + 1) (ht : 3 ≤ t) :
    (J : ℝ) + 1 ≤ 1 + Real.log (t + 3) / Real.log 2 := by
  have hpow : (2:ℕ)^J ≤ Nt := le_trans (Nat.le_mul_of_pos_left _ (by omega)) hJ
  have hcast : (2:ℝ)^J ≤ t + 3 := by
    have h1 : ((2:ℕ)^J : ℝ) ≤ (Nt:ℝ) := by exact_mod_cast hpow
    have h2 : ((2:ℕ)^J : ℝ) = (2:ℝ)^J := by push_cast; ring
    rw [h2] at h1; linarith
  have hpos : (0:ℝ) < (2:ℝ)^J := by positivity
  have hlog : (J:ℝ) * Real.log 2 ≤ Real.log (t+3) := by
    have h := Real.log_le_log hpos hcast
    rwa [Real.log_pow] at h
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hJle : (J:ℝ) ≤ Real.log (t+3) / Real.log 2 := by
    rw [le_div_iff₀ hlog2]; linarith
  linarith

/-! ## `Real.rpow` and `log` bookkeeping -/

/-- `L / (L/cvk)^{6/7} = cvk^{6/7} L^{1/7}`. -/
theorem vk_shift_theta_log_arg {cvk L : ℝ} (hcvk0 : 0 < cvk) (hL0 : 0 < L) :
    L / (L / cvk) ^ (6 / 7 : ℝ) = cvk ^ (6 / 7 : ℝ) * L ^ (1 / 7 : ℝ) := by
  have h1 : (L / cvk) ^ (6/7:ℝ) = L ^ (6/7:ℝ) / cvk ^ (6/7:ℝ) :=
    Real.div_rpow hL0.le hcvk0.le _
  rw [h1]
  have h2 : L / (L ^ (6/7:ℝ) / cvk ^ (6/7:ℝ)) = (L / L ^ (6/7:ℝ)) * cvk ^ (6/7:ℝ) := by
    field_simp
  rw [h2]
  have h3 : L / L ^ (6/7:ℝ) = L ^ (1/7:ℝ) := by
    have h4 : L ^ (1:ℝ) / L ^ (6/7:ℝ) = L ^ (1/7:ℝ) := by
      rw [← Real.rpow_sub hL0 (1:ℝ) (6/7:ℝ)]
      norm_num
    rwa [Real.rpow_one] at h4
  rw [h3]; ring

/-- Replacing `log(t+3)` by `log t` in `u³/(L² log(L/u+2))` decreases it. -/
theorem vk_shift_gamma_lower {cvk t u : ℝ} (hcvk0 : 0 < cvk) (ht : 3 ≤ t) (hu0 : 0 < u)
    (hut : u ≤ Real.log t) :
    cvk * u ^ 3 / (Real.log (t + 3) ^ 2 * Real.log (Real.log (t + 3) / u + 2)) ≤
      cvk * (u / Real.log t) ^ 2 / Real.log (Real.log t / u + 2) * u := by
  have ht0 : 0 < t := by linarith
  have hlogt : 0 < Real.log t := Real.log_pos (by linarith)
  have hlogt3 : 0 < Real.log (t + 3) := Real.log_pos (by linarith)
  have hle : Real.log t ≤ Real.log (t + 3) := Real.log_le_log ht0 (by linarith)
  have hdiv : Real.log t / u ≤ Real.log (t + 3) / u := div_le_div_of_nonneg_right hle hu0.le
  have hr : 1 ≤ Real.log t / u := by rw [le_div_iff₀ hu0]; linarith
  have harg : 1 < Real.log t / u + 2 := by linarith
  have hB : 0 < (Real.log t) ^ 2 * Real.log (Real.log t / u + 2) := by
    have : 0 < Real.log (Real.log t / u + 2) := Real.log_pos harg
    positivity
  have hBA : (Real.log t) ^ 2 * Real.log (Real.log t / u + 2) ≤
      Real.log (t + 3) ^ 2 * Real.log (Real.log (t + 3) / u + 2) := by
    have h1 : (Real.log t)^2 ≤ Real.log (t+3)^2 := by nlinarith
    have h2 : Real.log (Real.log t / u + 2) ≤ Real.log (Real.log (t+3) / u + 2) :=
      Real.log_le_log (by linarith) (by linarith)
    exact mul_le_mul h1 h2 (Real.log_nonneg (by linarith)) (by positivity)
  have key : cvk * u ^ 3 / (Real.log (t + 3) ^ 2 * Real.log (Real.log (t + 3) / u + 2)) ≤
      cvk * u ^ 3 / ((Real.log t) ^ 2 * Real.log (Real.log t / u + 2)) :=
    div_le_div_of_nonneg_left (by positivity) hB hBA
  have heq : cvk * u ^ 3 / ((Real.log t) ^ 2 * Real.log (Real.log t / u + 2)) =
      cvk * (u / Real.log t) ^ 2 / Real.log (Real.log t / u + 2) * u := by
    field_simp
  linarith [key, heq.le, heq.ge]

/-- `cvk * X ^ 2 = cvk^{-5/7} L^{12/7}` for `X = (L/cvk)^{6/7}`. -/
theorem vk_shift_X_sq {cvk L X : ℝ} (hcvk0 : 0 < cvk) (hL0 : 0 < L)
    (hX : X = (L/cvk)^(6/7:ℝ)) :
    cvk * X ^ 2 = cvk ^ (-(5/7):ℝ) * L ^ (12/7:ℝ) := by
  have hcp : (0:ℝ) < L / cvk := by positivity
  have hconv : X ^ 2 = X ^ (2:ℝ) := (Real.rpow_natCast X 2).symm
  rw [hconv, hX, ← Real.rpow_mul hcp.le (6/7) (2:ℝ)]
  norm_num
  rw [Real.div_rpow hL0.le hcvk0.le, div_eq_mul_inv]
  have hmm : cvk * (L ^ (12/7:ℝ) * (cvk ^ (12/7:ℝ))⁻¹) =
      cvk * (cvk ^ (12/7:ℝ))⁻¹ * L ^ (12/7:ℝ) := by ring
  rw [hmm]
  have h1 : cvk * (cvk ^ (12/7:ℝ))⁻¹ = cvk ^ (-(5/7):ℝ) := by
    rw [← Real.rpow_neg hcvk0.le (12/7:ℝ)]
    nth_rewrite 1 [← Real.rpow_one cvk]
    rw [← Real.rpow_add hcvk0]
    norm_num
  rw [h1]

/-- `cvk^{11/7} log (cvk^{6/7} L^{1/7} + 2) ≤ 6 L^{4/7}`. -/
theorem vk_shift_log_bound {cvk L : ℝ} (hcvk0 : 0 < cvk) (hcvk1 : cvk ≤ 1) (hL1 : 1 ≤ L)
    (hL0 : 0 < L) :
    cvk ^ (11/7:ℝ) * Real.log (cvk ^ (6/7:ℝ) * L ^ (1/7:ℝ) + 2) ≤ 6 * L ^ (4/7:ℝ) := by
  have hcvk67 : cvk ^ (6/7:ℝ) ≤ 1 := Real.rpow_le_one hcvk0.le hcvk1 (by norm_num)
  have hL17pos : 0 < L ^ (1/7:ℝ) := Real.rpow_pos_of_pos hL0 _
  have hL17one : 1 ≤ L ^ (1/7:ℝ) := Real.one_le_rpow hL1 (by norm_num)
  have hargpos : 0 < cvk ^ (6/7:ℝ) * L ^ (1/7:ℝ) + 2 := by positivity
  have hargnn : 0 ≤ cvk ^ (6/7:ℝ) * L ^ (1/7:ℝ) := by positivity
  have h11 : cvk ^ (6/7:ℝ) * L ^ (1/7:ℝ) + 2 ≤ L ^ (1/7:ℝ) + 2 := by
    have := mul_le_of_le_one_left hL17pos.le hcvk67
    linarith
  have h22 : Real.log (cvk ^ (6/7:ℝ) * L ^ (1/7:ℝ) + 2) ≤ Real.log (L ^ (1/7:ℝ) + 2) :=
    Real.log_le_log hargpos h11
  have h33 : Real.log (L ^ (1/7:ℝ) + 2) ≤ L ^ (1/7:ℝ) + 1 := by
    have := Real.log_le_sub_one_of_pos (show (0:ℝ) < L ^ (1/7:ℝ) + 2 by linarith)
    linarith
  have h44 : L ^ (1/7:ℝ) + 1 ≤ 2 * L ^ (1/7:ℝ) := by linarith
  have h55 : 2 * L ^ (1/7:ℝ) ≤ 6 * L ^ (4/7:ℝ) := by
    have h6 : L ^ (1/7:ℝ) ≤ L ^ (4/7:ℝ) := Real.rpow_le_rpow_of_exponent_le hL1 (by norm_num)
    linarith
  have h77 : cvk ^ (11/7:ℝ) ≤ 1 := Real.rpow_le_one hcvk0.le hcvk1 (by norm_num)
  have h99 : 0 ≤ Real.log (cvk ^ (6/7:ℝ) * L ^ (1/7:ℝ) + 2) := Real.log_nonneg (by linarith)
  have h88 : cvk ^ (11/7:ℝ) * Real.log (cvk ^ (6/7:ℝ) * L ^ (1/7:ℝ) + 2) ≤
      1 * Real.log (L ^ (1/7:ℝ) + 2) := mul_le_mul h77 h22 h99 (by norm_num)
  linarith

/-! ## The elementary real-variable core -/

/-- The elementary real-variable core: with `X = (L/cvk)^{6/7}` (the threshold of the VK range
condition) and `A = max (1-σ) 0`, one has `A u ≤ 1/2 + f(u) - f(X)` where
`f(u) = cvk u³/(L² log(L/u+2))`, for every `u ≥ X`. -/
theorem vk_shift_Au_bound {cvk σ L u : ℝ} (hcvk0 : 0 < cvk) (hcvk1 : cvk ≤ 1) (hL1 : 1 ≤ L)
    (hσ : 1 - σ ≤ cvk ^ (6 / 7 : ℝ) / 2 * L ^ (-(6 / 7 : ℝ)))
    (hu : (L / cvk) ^ (6 / 7 : ℝ) ≤ u) :
    max (1 - σ) 0 * u ≤ 1 / 2 + cvk * u ^ 3 / (L ^ 2 * Real.log (L / u + 2)) -
      cvk * ((L / cvk) ^ (6 / 7 : ℝ)) ^ 3 /
        (L ^ 2 * Real.log (L / (L / cvk) ^ (6 / 7 : ℝ) + 2)) := by
  have hL0 : 0 < L := by linarith
  set X : ℝ := (L / cvk) ^ (6 / 7 : ℝ) with hX
  have hXpos : 0 < X := by rw [hX]; exact Real.rpow_pos_of_pos (by positivity) _
  have hXu : X ≤ u := by rw [hX]; exact hu
  have hAle : max (1 - σ) 0 ≤ cvk ^ (6 / 7 : ℝ) / 2 * L ^ (-(6 / 7 : ℝ)) := by
    rcases le_or_gt (0:ℝ) (1-σ) with h | h
    · rw [max_eq_left h]; exact hσ
    · rw [max_eq_right (le_of_lt h)]; positivity
  have hAX : max (1 - σ) 0 * X ≤ 1 / 2 := by
    have hXid : cvk ^ (6/7:ℝ) * X = L ^ (6/7:ℝ) := by
      rw [hX, ← Real.mul_rpow hcvk0.le (show (0:ℝ) ≤ L/cvk by positivity)]
      congr 1
      field_simp
    have hLpow : L ^ (6/7:ℝ) * L ^ (-(6/7):ℝ) = 1 := by
      rw [← Real.rpow_add hL0]; norm_num
    have h1 := mul_le_mul_of_nonneg_right hAle hXpos.le
    have h2 : (cvk ^ (6/7:ℝ)/2 * L^(-(6/7):ℝ)) * X = 1/2 := by
      have h3 : (cvk ^ (6/7:ℝ)/2 * L^(-(6/7):ℝ)) * X =
          (1/2) * (cvk^(6/7:ℝ)*X) * L^(-(6/7):ℝ) := by ring
      rw [h3, hXid]
      have h4 : (1/2:ℝ) * L^(6/7:ℝ) * L^(-(6/7):ℝ) =
          (1/2) * (L^(6/7:ℝ)*L^(-(6/7):ℝ)) := by ring
      rw [h4, hLpow]; norm_num
    linarith
  have hE2b := vk_shift_log_bound hcvk0 hcvk1 hL1 hL0
  have hlogarg : L / X = cvk ^ (6/7:ℝ) * L ^ (1/7:ℝ) := by
    rw [hX]; exact vk_shift_theta_log_arg hcvk0 hL0
  have hlogpos : 0 < Real.log (L / X + 2) := by
    apply Real.log_pos
    have : 0 < L / X := div_pos hL0 hXpos
    linarith
  have hDpos : 0 < L ^ 2 * Real.log (L/X+2) := by positivity
  have hXsq : cvk * X ^ 2 = cvk^(-(5/7):ℝ) * L^(12/7:ℝ) :=
    vk_shift_X_sq hcvk0 hL0 hX
  have hsplit : cvk ^ (6/7:ℝ) = cvk ^ (11/7:ℝ) * cvk ^ (-(5/7):ℝ) := by
    rw [← Real.rpow_add hcvk0]; norm_num
  have hLsum : L ^ (8/7:ℝ) * L ^ (4/7:ℝ) = L ^ (12/7:ℝ) := by
    rw [← Real.rpow_add hL0]; norm_num
  have hE2 : max (1 - σ) 0 ≤ 3 * cvk * X ^ 2 / (L ^ 2 * Real.log (L / X + 2)) := by
    refine le_trans hAle ?_
    rw [le_div_iff₀ hDpos]
    have hLpow : L ^ (-(6/7):ℝ) * L ^ 2 = L ^ (8/7:ℝ) := by
      have hc : L ^ 2 = L ^ (2:ℝ) := (Real.rpow_natCast L 2).symm
      rw [hc, ← Real.rpow_add hL0]; norm_num
    have hE1 : (cvk ^ (6/7:ℝ)/2 * L^(-(6/7):ℝ)) * (L^2 * Real.log (L/X+2)) =
        (1/2) * cvk ^ (6/7:ℝ) * L ^ (8/7:ℝ) *
          Real.log (cvk ^ (6/7:ℝ) * L ^ (1/7:ℝ) + 2) := by
      rw [hlogarg]
      have h5 : (cvk ^ (6/7:ℝ)/2 * L^(-(6/7):ℝ)) *
          (L^2 * Real.log (cvk ^ (6/7:ℝ) * L ^ (1/7:ℝ) + 2))
          = (1/2) * cvk ^ (6/7:ℝ) * (L ^ (-(6/7):ℝ) * L^2) *
              Real.log (cvk ^ (6/7:ℝ) * L ^ (1/7:ℝ) + 2) := by ring
      rw [h5, hLpow]
    calc (cvk ^ (6/7:ℝ)/2 * L^(-(6/7):ℝ)) * (L^2 * Real.log (L/X+2))
        = (1/2) * cvk ^ (6/7:ℝ) * L ^ (8/7:ℝ) *
            Real.log (cvk ^ (6/7:ℝ) * L ^ (1/7:ℝ) + 2) := hE1
      _ = (1/2) * (cvk ^ (-(5/7):ℝ) * L ^ (8/7:ℝ)) *
            (cvk ^ (11/7:ℝ) * Real.log (cvk ^ (6/7:ℝ) * L ^ (1/7:ℝ) + 2)) := by
            rw [hsplit]; ring
      _ ≤ (1/2) * (cvk ^ (-(5/7):ℝ) * L ^ (8/7:ℝ)) * (6 * L ^ (4/7:ℝ)) := by
            apply mul_le_mul_of_nonneg_left hE2b; positivity
      _ = 3 * (cvk ^ (-(5/7):ℝ) * L ^ (12/7:ℝ)) := by rw [← hLsum]; ring
      _ = 3 * (cvk * X ^ 2) := by rw [hXsq]
      _ = 3 * cvk * X ^ 2 := by ring
  have hstep : max (1 - σ) 0 * (u - X) ≤
      cvk * u ^ 3 / (L ^ 2 * Real.log (L / u + 2)) -
        cvk * X ^ 3 / (L ^ 2 * Real.log (L / X + 2)) := by
    have huX : 0 ≤ u - X := sub_nonneg.mpr hXu
    have hupos : 0 < u := lt_of_lt_of_le hXpos hXu
    have hlu : L / u ≤ L / X := div_le_div_of_nonneg_left hL0.le hXpos hXu
    have hlogmono : Real.log (L / u + 2) ≤ Real.log (L / X + 2) :=
      Real.log_le_log (by positivity) (by linarith)
    have hDupos : 0 < L ^ 2 * Real.log (L / u + 2) := by
      have h2 : 0 < Real.log (L / u + 2) := by
        apply Real.log_pos
        have : 0 < L/u := div_pos hL0 hupos
        linarith
      positivity
    have hcube : 3 * X^2 * (u - X) ≤ u^3 - X^3 := by
      have h2 : 3 * X^2 ≤ u^2 + u*X + X^2 := by
        have hh : 0 ≤ (u - X) * (u + 2*X) := mul_nonneg huX (by linarith)
        nlinarith [hh]
      have h3 : 3 * X^2 * (u - X) ≤ (u^2 + u*X + X^2) * (u - X) :=
        mul_le_mul_of_nonneg_right h2 huX
      nlinarith [h3]
    have hmul : max (1 - σ) 0 * (u - X) ≤
        (3 * cvk * X ^ 2 / (L ^ 2 * Real.log (L / X + 2))) * (u - X) :=
      mul_le_mul_of_nonneg_right hE2 huX
    have hA : cvk * u ^ 3 / (L ^ 2 * Real.log (L / X + 2)) ≤
        cvk * u ^ 3 / (L ^ 2 * Real.log (L / u + 2)) :=
      div_le_div_of_nonneg_left (by positivity) hDupos
        (mul_le_mul_of_nonneg_left hlogmono (by positivity))
    have hB : 3 * cvk * X^2 * (u - X) / (L ^ 2 * Real.log (L / X + 2)) ≤
        cvk * (u^3 - X^3) / (L^2 * Real.log (L / X + 2)) :=
      div_le_div_of_nonneg_right (by nlinarith [hcube]) hDpos.le
    have hC : (3 * cvk * X ^ 2 / (L ^ 2 * Real.log (L / X + 2))) * (u - X) =
        3 * cvk * X^2 * (u - X) / (L^2 * Real.log (L / X + 2)) := by ring
    have hD : cvk * u^3 / (L^2 * Real.log (L/X+2)) - cvk * X^3 / (L^2 * Real.log (L/X+2)) =
        cvk * (u^3 - X^3) / (L^2 * Real.log (L/X+2)) := by ring
    linarith [hmul, hA, hB, hC.le, hC.ge, hD.le, hD.ge]
  calc max (1 - σ) 0 * u = max (1 - σ) 0 * X + max (1 - σ) 0 * (u - X) := by ring
    _ ≤ 1 / 2 + (cvk * u ^ 3 / (L ^ 2 * Real.log (L / u + 2)) -
        cvk * X ^ 3 / (L ^ 2 * Real.log (L / X + 2))) := add_le_add hAX hstep
    _ = 1 / 2 + cvk * u ^ 3 / (L ^ 2 * Real.log (L / u + 2)) -
        cvk * ((L / cvk) ^ (6 / 7 : ℝ)) ^ 3 /
          (L ^ 2 * Real.log (L / (L / cvk) ^ (6 / 7 : ℝ) + 2)) := by rw [hX]; ring

/-! ## The VK block bound for the shift-difference series -/

/-- A single dyadic block of the shift-difference series, bounded by the VK saving.  The summand
`shiftTerm a n s = (n+a)^{-s} - (n+1)^{-s}` splits into two sums, each handled by
`Work.BMF.vk_block_bound` (with shift parameter `u = a` respectively `u = 1`). -/
theorem shift_block_vk {Cvk cvk a σ t : ℝ} (hVK : Work.BMF.VKExpInput Cvk cvk)
    (ha : 0 < a) (ha1 : a ≤ 1) (hσ0 : 0 < σ) (ht : 3 ≤ t)
    {K R : ℕ} (hK2 : 2 ≤ K) (hKR : K ≤ R) (hR2K : (R : ℝ) ≤ 2 * K) (hKt : (K : ℝ) ≤ t)
    (hrange : Real.log t ≤ cvk * Real.log (K : ℝ) ^ (7 / 6 : ℝ)) :
    ‖∑ n ∈ Finset.Ioc K R, Work.BMF.shiftTerm a n ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      2 * Cvk * (K : ℝ) ^ (1 - σ - cvk * (Real.log (K : ℝ) / Real.log t) ^ 2 /
        Real.log (Real.log t / Real.log (K : ℝ) + 2)) := by
  have hCvk : 0 < Cvk := hVK.1
  rcases eq_or_lt_of_le hKR with h | h
  · subst h
    rw [Finset.Ioc_self, Finset.sum_empty, norm_zero]
    exact le_of_lt (by positivity)
  · have hKpos : (0:ℝ) < (K:ℝ) := by exact_mod_cast (by omega : 0 < K)
    have h1 := Work.BMF.vk_block_bound (Cvk := Cvk) (cvk := cvk) hVK ha ha1 ht hσ0 h
      hR2K hKt hK2 hrange
    have h2 := Work.BMF.vk_block_bound (Cvk := Cvk) (cvk := cvk) hVK
      (by norm_num : (0:ℝ) < 1) (by norm_num : (1:ℝ) ≤ 1) ht hσ0 h hR2K hKt hK2 hrange
    have hdecomp : (∑ n ∈ Finset.Ioc K R,
          Work.BMF.shiftTerm a n ((σ:ℂ) + (t:ℂ) * Complex.I))
        = (∑ n ∈ Finset.Ioc K R, ((((n:ℝ)+a:ℝ)):ℂ)^(-((σ:ℂ)+(t:ℂ)*Complex.I)))
          - (∑ n ∈ Finset.Ioc K R, ((((n:ℝ)+1:ℝ)):ℂ)^(-((σ:ℂ)+(t:ℂ)*Complex.I))) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun n hn => ?_)
      simp only [Work.BMF.shiftTerm]
      push_cast
      ring
    rw [hdecomp]
    have hKpow : (K:ℝ)^(-σ) * (K:ℝ)^(1 - cvk * (Real.log (K:ℝ) / Real.log t)^2 /
        Real.log (Real.log t / Real.log (K:ℝ) + 2))
        = (K:ℝ)^(1 - σ - cvk * (Real.log (K:ℝ) / Real.log t)^2 /
            Real.log (Real.log t / Real.log (K:ℝ) + 2)) := by
      rw [← Real.rpow_add hKpos]
      congr 1
      ring
    calc ‖(∑ n ∈ Finset.Ioc K R, ((((n:ℝ)+a:ℝ)):ℂ)^(-((σ:ℂ)+(t:ℂ)*Complex.I)))
            - (∑ n ∈ Finset.Ioc K R, ((((n:ℝ)+1:ℝ)):ℂ)^(-((σ:ℂ)+(t:ℂ)*Complex.I)))‖
        ≤ ‖∑ n ∈ Finset.Ioc K R, ((((n:ℝ)+a:ℝ)):ℂ)^(-((σ:ℂ)+(t:ℂ)*Complex.I))‖
          + ‖∑ n ∈ Finset.Ioc K R, ((((n:ℝ)+1:ℝ)):ℂ)^(-((σ:ℂ)+(t:ℂ)*Complex.I))‖ :=
          norm_sub_le _ _
      _ ≤ Cvk * (K:ℝ)^(-σ) * ((K:ℝ)^(1 - cvk * (Real.log (K:ℝ) / Real.log t)^2 /
              Real.log (Real.log t / Real.log (K:ℝ) + 2)))
          + Cvk * (K:ℝ)^(-σ) * ((K:ℝ)^(1 - cvk * (Real.log (K:ℝ) / Real.log t)^2 /
              Real.log (Real.log t / Real.log (K:ℝ) + 2))) := add_le_add h1 h2
      _ = 2 * Cvk * (K:ℝ)^(1 - σ - cvk * (Real.log (K:ℝ) / Real.log t)^2 /
            Real.log (Real.log t / Real.log (K:ℝ) + 2)) := by
          have hKpow2 : Cvk * (K:ℝ)^(-σ) * (K:ℝ)^(1 - cvk * (Real.log (K:ℝ) / Real.log t)^2 /
              Real.log (Real.log t / Real.log (K:ℝ) + 2))
              = Cvk * (K:ℝ)^(1 - σ - cvk * (Real.log (K:ℝ) / Real.log t)^2 /
                  Real.log (Real.log t / Real.log (K:ℝ) + 2)) := by
            rw [mul_assoc, hKpow]
          rw [hKpow2]
          ring

/-! ## Conjugation -/

/-- `‖conj z‖ = ‖z‖` for the ring-endomorphism version of conjugation. -/
private lemma norm_starRingEnd (z : ℂ) : ‖(starRingEnd ℂ) z‖ = ‖z‖ := by
  simpa using norm_star z

/-- `shiftTerm a m (conj s) = conj (shiftTerm a m s)` for `0 < a`. -/
lemma shiftTerm_conj {a : ℝ} (ha : 0 < a) (m : ℕ) (s : ℂ) :
    Work.BMF.shiftTerm a m ((starRingEnd ℂ) s) = (starRingEnd ℂ) (Work.BMF.shiftTerm a m s) := by
  simp only [Work.BMF.shiftTerm, map_sub]
  rw [Commons.Analysis.Complex.conj_cpow_ofReal_of_nonneg (show (0:ℝ) ≤ (m:ℝ)+a by positivity) (-s),
      Commons.Analysis.Complex.conj_cpow_ofReal_of_nonneg (show (0:ℝ) ≤ ((m+1:ℕ):ℝ) by positivity) (-s),
      map_neg]

/-! ## The range bound -/

/-- The range bound with `|t|` replaced by a positive parameter `T ≥ 3` (the case of the main
theorem that carries all the content). -/
private theorem shift_vk_range_bound_aux {Cvk cvk Ab a σ T : ℝ}
    (hVK : Work.BMF.VKExpInput Cvk cvk)
    (hcvk0 : 0 < cvk) (hcvk1 : cvk ≤ 1) (ha : 0 < a) (ha1 : a ≤ 1) (hT : 3 ≤ T)
    (hσ0 : 0 < σ) (hσ2 : σ ≤ 2)
    (hσδ : 1 - σ ≤ cvk ^ (6 / 7 : ℝ) / 2 * Real.log (T + 3) ^ (-(6 / 7 : ℝ)))
    {K₀ Nt : ℕ} (hK₀2 : 2 ≤ K₀) (hNt : (Nt : ℝ) ≤ T + 1) (hK₀Nt : K₀ ≤ Nt)
    (hlogK₀ : (Real.log (T + 3) / cvk) ^ (6 / 7 : ℝ) ≤ Real.log (K₀ : ℝ))
    (hAb : (1 + Real.log (T + 3) / Real.log 2) *
        Real.exp (-(cvk * ((Real.log (T + 3) / cvk) ^ (6 / 7 : ℝ)) ^ 3 /
          (Real.log (T + 3) ^ 2 * Real.log (cvk ^ (6 / 7 : ℝ) * Real.log (T + 3) ^ (1 / 7 : ℝ) + 2)))) ≤ Ab) :
    ‖∑ m ∈ Finset.Ioc K₀ Nt, Work.BMF.shiftTerm a m ((σ : ℂ) + (T : ℂ) * Complex.I)‖ ≤
      2 * Cvk * Real.exp (1 / 2) * Ab := by
  have hCvk : 0 < Cvk := hVK.1
  have hcvkpos : 0 < cvk := hVK.2.1
  have hT0 : 0 < T := by linarith
  have hL0 : 0 < Real.log (T + 3) := Real.log_pos (by linarith)
  have hL1 : 1 ≤ Real.log (T + 3) := by
    have he : (1:ℝ) ≤ Real.log 6 := by
      have h2 : Real.exp 1 < 6 := lt_trans Real.exp_one_lt_three (by norm_num)
      have h3 : Real.log (Real.exp 1) < Real.log 6 := Real.log_lt_log (Real.exp_pos 1) h2
      rw [Real.log_exp] at h3
      linarith
    exact le_trans he (Real.log_le_log (by norm_num) (by linarith))
  set X : ℝ := (Real.log (T + 3) / cvk) ^ (6 / 7 : ℝ) with hXdef
  have hXpos : 0 < X := by rw [hXdef]; exact Real.rpow_pos_of_pos (by positivity) _
  set θ : ℝ := cvk * ((Real.log (T + 3) / cvk) ^ (6 / 7 : ℝ)) ^ 3 /
      (Real.log (T + 3) ^ 2 * Real.log (cvk ^ (6 / 7 : ℝ) * Real.log (T + 3) ^ (1 / 7 : ℝ) + 2))
    with hθdef
  have hAb' : (1 + Real.log (T + 3) / Real.log 2) * Real.exp (-θ) ≤ Ab := by
    rw [hθdef]; exact hAb
  have hK₀1 : 1 ≤ K₀ := by omega
  set J : ℕ := Nat.log 2 (Nt / K₀) with hJdef
  have hq0 : Nt / K₀ ≠ 0 := Nat.pos_iff_ne_zero.mp (Nat.div_pos hK₀Nt (by omega))
  have hJ1 : K₀ * 2 ^ J ≤ Nt := by
    have hq : 2 ^ J ≤ Nt / K₀ := by
      rw [hJdef]; exact Nat.pow_log_le_self 2 hq0
    calc K₀ * 2 ^ J ≤ K₀ * (Nt / K₀) := Nat.mul_le_mul_left _ hq
      _ = (Nt / K₀) * K₀ := Nat.mul_comm _ _
      _ ≤ Nt := Nat.div_mul_le_self Nt K₀
  have hJ2 : Nt ≤ K₀ * 2 ^ (J + 1) := by
    have hq : Nt / K₀ < 2 ^ (J + 1) := by
      have := Nat.lt_pow_succ_log_self (by norm_num : 1 < 2) (Nt / K₀)
      rwa [← hJdef] at this
    have hr : Nt % K₀ < K₀ := Nat.mod_lt _ (by omega)
    have hdm : K₀ * (Nt / K₀) + Nt % K₀ = Nt := Nat.div_add_mod Nt K₀
    have hbase : K₀ * (Nt / K₀) + K₀ ≤ K₀ * 2 ^ (J + 1) := by
      have := Nat.mul_le_mul_left K₀ (Nat.succ_le_of_lt hq)
      rwa [Nat.succ_eq_add_one, Nat.mul_add, Nat.mul_one] at this
    omega
  have hXpow : cvk * X ^ (7 / 6 : ℝ) = Real.log (T + 3) := by
    rw [hXdef]
    have h3 : (((Real.log (T + 3)) / cvk) ^ (6 / 7 : ℝ)) ^ (7 / 6 : ℝ)
        = (Real.log (T + 3)) / cvk := by
      rw [← Real.rpow_mul (by positivity : (0:ℝ) ≤ Real.log (T + 3) / cvk) (6/7) (7/6)]
      norm_num
    rw [h3]
    field_simp
  have hblock : ∀ K R : ℕ, K₀ ≤ K → K ≤ R → R ≤ 2 * K → R ≤ Nt →
      ‖∑ n ∈ Finset.Ioc K R, Work.BMF.shiftTerm a n ((σ : ℂ) + (T : ℂ) * Complex.I)‖
        ≤ 2 * Cvk * Real.exp (1 / 2) * Real.exp (-θ) := by
    intro K R hK₀K hKR hR2K hRNt
    rcases eq_or_lt_of_le hKR with h | hlt
    · subst h
      rw [Finset.Ioc_self, Finset.sum_empty, norm_zero]
      have : 0 < 2 * Cvk * Real.exp (1/2) * Real.exp (-θ) := by positivity
      linarith
    · have hK2 : 2 ≤ K := le_trans hK₀2 hK₀K
      have hKpos : (0:ℝ) < (K:ℝ) := by exact_mod_cast (by omega : 0 < K)
      have hKt : (K:ℝ) ≤ T := by
        have h1 : K + 1 ≤ Nt := by omega
        have h2 : ((K:ℕ):ℝ) + 1 ≤ (Nt:ℝ) := by exact_mod_cast h1
        push_cast at h2 ⊢
        linarith
      have hlogKge : X ≤ Real.log (K:ℝ) := by
        refine le_trans hlogK₀ (Real.log_le_log (by exact_mod_cast (by omega : 0 < K₀)) ?_)
        exact_mod_cast hK₀K
      have hrange : Real.log T ≤ cvk * Real.log (K:ℝ) ^ (7 / 6 : ℝ) := by
        have h1 : Real.log T ≤ Real.log (T + 3) := Real.log_le_log hT0 (by linarith)
        have h2 : X ^ (7/6:ℝ) ≤ (Real.log (K:ℝ)) ^ (7/6:ℝ) :=
          Real.rpow_le_rpow hXpos.le hlogKge (by norm_num)
        calc Real.log T ≤ Real.log (T + 3) := h1
          _ = cvk * X ^ (7/6:ℝ) := hXpow.symm
          _ ≤ cvk * (Real.log (K:ℝ)) ^ (7/6:ℝ) := mul_le_mul_of_nonneg_left h2 hcvkpos.le
      have hb := shift_block_vk (Cvk := Cvk) (cvk := cvk) hVK ha ha1 hσ0 hT hK2
        (le_of_lt hlt) (by exact_mod_cast hR2K) hKt hrange
      have hlogKpos : 0 < Real.log (K:ℝ) :=
        Real.log_pos (by exact_mod_cast (by omega : 1 < K))
      have hlogKle : Real.log (K:ℝ) ≤ Real.log T := Real.log_le_log hKpos hKt
      have hAu := vk_shift_Au_bound (cvk := cvk) (σ := σ) (L := Real.log (T+3))
        (u := Real.log (K:ℝ)) hcvkpos hcvk1 hL1 hσδ hlogKge
      have hgam := vk_shift_gamma_lower (cvk := cvk) (t := T) (u := Real.log (K:ℝ))
        hcvkpos hT hlogKpos hlogKle
      have hθX : cvk * X ^ 3 /
          (Real.log (T + 3) ^ 2 * Real.log (Real.log (T + 3) / X + 2)) = θ := by
        rw [hθdef, hXdef]
        have hlogarg := vk_shift_theta_log_arg (cvk := cvk) (L := Real.log (T+3)) hcvkpos hL0
        rw [hlogarg]
      have hexp : (1 - σ - cvk * (Real.log (K:ℝ) / Real.log T) ^ 2 /
            Real.log (Real.log T / Real.log (K:ℝ) + 2)) * Real.log (K:ℝ) ≤ 1/2 - θ := by
        have h1 : (1-σ) * Real.log (K:ℝ) ≤ max (1-σ) 0 * Real.log (K:ℝ) := by
          rcases le_or_gt 0 (1-σ) with hh | hh
          · rw [max_eq_left hh]
          · rw [max_eq_right (le_of_lt hh)]
            nlinarith [hlogKpos]
        linarith [hAu, hgam, hθX.le, hθX.ge]
      have hKpow : (K:ℝ)^(1 - σ - cvk * (Real.log (K:ℝ) / Real.log T)^2 /
            Real.log (Real.log T / Real.log (K:ℝ) + 2)) ≤
          Real.exp (1/2) * Real.exp (-θ) := by
        rw [Real.rpow_def_of_pos hKpos, ← Real.exp_add]
        apply Real.exp_le_exp.mpr
        rw [mul_comm]
        exact hexp
      calc ‖∑ n ∈ Finset.Ioc K R, Work.BMF.shiftTerm a n ((σ:ℂ) + (T:ℂ)*Complex.I)‖
          ≤ 2 * Cvk * (K:ℝ)^(1 - σ - cvk * (Real.log (K:ℝ) / Real.log T)^2 /
              Real.log (Real.log T / Real.log (K:ℝ) + 2)) := hb
        _ ≤ 2 * Cvk * (Real.exp (1/2) * Real.exp (-θ)) :=
            mul_le_mul_of_nonneg_left hKpow (by positivity)
        _ = 2 * Cvk * Real.exp (1/2) * Real.exp (-θ) := by ring
  have hdy := dyadic_ioc_le (f := fun n => Work.BMF.shiftTerm a n ((σ:ℂ) + (T:ℂ)*Complex.I))
    hK₀1 (B := 2 * Cvk * Real.exp (1/2) * Real.exp (-θ)) (by positivity) J Nt hJ1 hJ2 hblock
  have hcount := dyadic_block_count (K₀ := K₀) (Nt := Nt) (J := J) (t := T) hK₀1 hJ1 hNt hT
  calc ‖∑ m ∈ Finset.Ioc K₀ Nt, Work.BMF.shiftTerm a m ((σ:ℂ) + (T:ℂ)*Complex.I)‖
      ≤ ((J:ℝ) + 1) * (2 * Cvk * Real.exp (1/2) * Real.exp (-θ)) := hdy
    _ ≤ (1 + Real.log (T + 3) / Real.log 2) * (2 * Cvk * Real.exp (1/2) * Real.exp (-θ)) := by
        apply mul_le_mul_of_nonneg_right hcount
        positivity
    _ = 2 * Cvk * Real.exp (1/2) * ((1 + Real.log (T + 3) / Real.log 2) * Real.exp (-θ)) := by
        ring
    _ ≤ 2 * Cvk * Real.exp (1/2) * Ab :=
        mul_le_mul_of_nonneg_left hAb' (by positivity)
    _ = 2 * Cvk * Real.exp (1 / 2) * Ab := by ring

/-- **The Vinogradov–Korobov range bound for the shift-difference series.** -/
theorem shift_vk_range_bound {Cvk cvk Ab a σ t : ℝ} (hVK : Work.BMF.VKExpInput Cvk cvk)
    (hcvk0 : 0 < cvk) (hcvk1 : cvk ≤ 1) (ha : 0 < a) (ha1 : a ≤ 1) (ht : 3 ≤ |t|)
    (hσ0 : 0 < σ) (hσ2 : σ ≤ 2)
    (hσδ : 1 - σ ≤ cvk ^ (6 / 7 : ℝ) / 2 * Real.log (|t| + 3) ^ (-(6 / 7 : ℝ)))
    {K₀ Nt : ℕ} (hK₀2 : 2 ≤ K₀) (hNt : (Nt : ℝ) ≤ |t| + 1) (hK₀Nt : K₀ ≤ Nt)
    (hlogK₀ : (Real.log (|t| + 3) / cvk) ^ (6 / 7 : ℝ) ≤ Real.log (K₀ : ℝ))
    (hAb : (1 + Real.log (|t| + 3) / Real.log 2) *
        Real.exp (-(cvk * ((Real.log (|t| + 3) / cvk) ^ (6 / 7 : ℝ)) ^ 3 /
          (Real.log (|t| + 3) ^ 2 * Real.log (cvk ^ (6 / 7 : ℝ) * Real.log (|t| + 3) ^ (1 / 7 : ℝ) + 2)))) ≤ Ab) :
    ‖∑ m ∈ Finset.Ioc K₀ Nt, Work.BMF.shiftTerm a m ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      2 * Cvk * Real.exp (1 / 2) * Ab := by
  have hmain := shift_vk_range_bound_aux (T := |t|) hVK hcvk0 hcvk1 ha ha1 ht hσ0 hσ2 hσδ
    hK₀2 hNt hK₀Nt hlogK₀ hAb
  rcases le_or_gt (0:ℝ) t with hpos | hneg
  · rwa [abs_of_nonneg hpos] at hmain
  · have habs : |t| = -t := abs_of_neg hneg
    have hs : ((σ:ℂ) + (t:ℂ) * Complex.I)
        = (starRingEnd ℂ) (((σ:ℝ):ℂ) + (((|t|:ℝ):ℂ)) * Complex.I) := by
      have h1 : (starRingEnd ℂ) (((σ:ℝ):ℂ) + (((|t|:ℝ):ℂ)) * Complex.I)
          = ((σ:ℝ):ℂ) + (-((|t|:ℝ):ℂ)) * Complex.I := by
        simp only [map_add, map_mul, Complex.conj_ofReal, Complex.conj_I]
        ring
      rw [h1, habs]
      push_cast
      ring
    have hsum : (∑ m ∈ Finset.Ioc K₀ Nt, Work.BMF.shiftTerm a m ((σ:ℂ) + (t:ℂ)*Complex.I))
        = (starRingEnd ℂ) (∑ m ∈ Finset.Ioc K₀ Nt,
            Work.BMF.shiftTerm a m (((σ:ℝ):ℂ) + (((|t|:ℝ):ℂ))*Complex.I)) := by
      rw [map_sum]
      refine Finset.sum_congr rfl (fun m hm => ?_)
      rw [hs, shiftTerm_conj ha]
    rw [hsum, norm_starRingEnd]
    exact hmain

end

end Work.BMF.VKChain
