import Mathlib
import Submission.Work.GM.S3.tail_defs
import Submission.Work.GM.S3.hhat_decay
import Submission.Work.GM.Trace.hhat_norm_le_Azero

namespace Work.GM.S3

/-- Arithmetic core of the pointwise majorant: for `0 ≤ b ≤ a` with `a > 0` and `2 ≤ j`,
the `j`-th power quotient is dominated by the square quotient. This is what allows the decay
`(T/(|m|N))^j` of `hhat` to be reduced to the `j = 2` power, since `|m| > T/N` makes the base
at most `1`. -/
private lemma pow_div_pow_le_sq_div_sq {a b : ℝ} (ha : 0 < a) (hb : 0 ≤ b) (hba : b ≤ a)
    {j : ℕ} (hj : 2 ≤ j) : b ^ j / a ^ j ≤ b ^ 2 / a ^ 2 := by
  have h0 : 0 ≤ b / a := div_nonneg hb ha.le
  have h1 : b / a ≤ 1 := (div_le_one ha).mpr hba
  have hpow : (b / a) ^ j ≤ (b / a) ^ 2 := pow_le_pow_of_le_one h0 h1 hj
  rwa [div_pow, div_pow] at hpow

/-- Pointwise majorant for `‖ĥ_t(mN)‖` when `|t| ≤ T`, `T ≥ 1`, `N ≥ 1`: with `L = T/N` the
value is bounded by `Azero = ∫w²` for `|m| ≤ L` and by `C_j·2^j·L²/m²` for `|m| > L`, using the
decay `‖ĥ_t(ξ)‖ ≤ C_j(1+|t|)^j/|ξ|^j` with `j ≥ 2` and `1+|t| ≤ 1+T ≤ 2T` (so the ratio
`(T/N)/|m| < 1` may be raised from the `j`-th to the `2`-nd power). -/
theorem hhat_le_phiMaj (j : ℕ) (hj : 2 ≤ j) (Cj : ℝ) (hCj : 0 ≤ Cj)
    (hdec : ∀ t ξ : ℝ, ξ ≠ 0 → ‖Submission.GM.hhat t ξ‖ ≤ Cj * (1 + |t|) ^ j / |ξ| ^ j)
    (hAz : ∀ t ξ : ℝ, ‖Submission.GM.hhat t ξ‖ ≤ Work.GM.Trace.Azero)
    {N : ℕ} (hN : 1 ≤ N) {T : ℝ} (hT : 1 ≤ T) {t : ℝ} (ht : |t| ≤ T) (m : ℤ) :
    ‖Submission.GM.hhat t ((m : ℝ) * N)‖ ≤
      Work.GM.S3.phiMaj (T / N) Work.GM.Trace.Azero (Cj * 2 ^ j * (T / N) ^ 2) m := by
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  have hNne : (N : ℝ) ≠ 0 := ne_of_gt hNpos
  have hTpos : (0 : ℝ) < T := by linarith
  have hLnn : (0 : ℝ) ≤ T / N := div_nonneg hTpos.le hNpos.le
  unfold Work.GM.S3.phiMaj
  split_ifs with hm
  · -- `|m| ≤ T/N`: the trivial uniform bound suffices.
    exact hAz t ((m : ℝ) * N)
  · -- `|m| > T/N`: use the decay, `1 + |t| ≤ 2T`, `|mN|^j ≥ (|m|N)^j` and `T ≤ |m|N`.
    have hLlt : T / (N : ℝ) < |(m : ℝ)| := not_le.mp hm
    have hmp : 0 < |(m : ℝ)| := lt_of_le_of_lt hLnn hLlt
    have hmne : (m : ℝ) ≠ 0 := by
      intro h
      rw [h] at hmp
      simp at hmp
    have hξ : (m : ℝ) * (N : ℝ) ≠ 0 := mul_ne_zero hmne hNne
    have ha : 0 < |(m : ℝ)| * (N : ℝ) := mul_pos hmp hNpos
    have hb : 0 ≤ T := hTpos.le
    have hba : T ≤ |(m : ℝ)| * (N : ℝ) := (div_le_iff₀ hNpos).mp hLlt.le
    have ht2 : 1 + |t| ≤ 2 * T := by linarith [abs_nonneg t]
    have hnum : Cj * (1 + |t|) ^ j ≤ Cj * (2 * T) ^ j :=
      mul_le_mul_of_nonneg_left
        (pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ 1 + |t|) ht2 j) hCj
    have habs : |(m : ℝ) * (N : ℝ)| = |(m : ℝ)| * (N : ℝ) := by rw [abs_mul, Nat.abs_cast]
    have heq : T ^ 2 / (|(m : ℝ)| * (N : ℝ)) ^ 2 = (T / N) ^ 2 / (m : ℝ) ^ 2 := by
      rw [mul_pow, sq_abs, div_pow, div_div, mul_comm ((m : ℝ) ^ 2) ((N : ℝ) ^ 2)]
    have hcore := pow_div_pow_le_sq_div_sq ha hb hba hj
    have hCj2 : (0 : ℝ) ≤ Cj * 2 ^ j := by positivity
    have hstep : Cj * 2 ^ j * (T ^ j / (|(m : ℝ)| * (N : ℝ)) ^ j)
        ≤ Cj * 2 ^ j * (T ^ 2 / (|(m : ℝ)| * (N : ℝ)) ^ 2) :=
      mul_le_mul_of_nonneg_left hcore hCj2
    refine (hdec t _ hξ).trans ?_
    rw [habs]
    refine (div_le_div_of_nonneg_right hnum (pow_pos ha j).le).trans ?_
    calc Cj * (2 * T) ^ j / (|(m : ℝ)| * (N : ℝ)) ^ j
        = Cj * 2 ^ j * (T ^ j / (|(m : ℝ)| * (N : ℝ)) ^ j) := by rw [mul_pow]; ring
      _ ≤ Cj * 2 ^ j * (T ^ 2 / (|(m : ℝ)| * (N : ℝ)) ^ 2) := hstep
      _ = Cj * 2 ^ j * (T / N) ^ 2 / (m : ℝ) ^ 2 := by rw [heq]; ring

end Work.GM.S3
