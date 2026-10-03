import Mathlib
import Submission.Work.Analysis.IonescuWainger.Basic

/-!
# Growth bound for the Ionescu–Wainger quantity `Q_0^{(l)}`

`Q_0^{(l)} = (N_0^{(l)}!)^{D_ρ}`, where `N_0^{(l)} = ⌊2^{ρ l/2}⌋ + 1` and `D_ρ = ⌊2/ρ⌋ + 1`.
Since `N_0^{(l)} ≤ 2 · 2^{ρ l/2}`, we get

  `log Q_0^{(l)} = D_ρ log(N_0^{(l)}!) ≤ D_ρ N_0 log N_0 ≤ 4 D_ρ 2^{ρ l}`,

whence `Q_0^{(l)} ≤ 2^{(4 D_ρ / log 2) 2^{ρ l}}`: the quantity `Q_0^{(l)}` is of size `2^{O(2^{ρl})}`.
This is the bound used in Appendix A of Krause–Mirek–Tao to control the number of tolerable
(modulus) denominators at height `≤ 2^l`.
-/

set_option autoImplicit false

namespace Work.KMTAreas

open Work.Analysis.IonescuWainger

/-- **Logarithmic growth of `Q_0^{(l)}`.** `log Q_0^{(l)} ≤ 4 D_ρ 2^{ρ l}`. -/
theorem log_iwQ0_le (ρ : ℝ) (hρ : 0 < ρ) (l : ℕ) :
    Real.log ((iwQ0 ρ l : ℕ) : ℝ) ≤ 4 * (iwD ρ : ℝ) * (2 : ℝ) ^ (ρ * (l : ℝ)) := by
  set t : ℝ := (2 : ℝ) ^ (ρ * (l : ℝ) / 2) with htdef
  set S : ℝ := (2 : ℝ) ^ (ρ * (l : ℝ)) with hSdef
  have htpos : 0 < t := by rw [htdef]; positivity
  have ht1 : 1 ≤ t := by
    rw [htdef]
    exact Real.one_le_rpow (by norm_num : (1 : ℝ) ≤ 2) (by positivity)
  have htt : t * t = S := by
    rw [htdef, hSdef, ← Real.rpow_add (by norm_num : (0 : ℝ) < 2)]
    congr 1
    ring
  have hNpos : 0 < ((iwN0 ρ l : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < iwN0 ρ l by rw [iwN0]; exact Nat.succ_pos _)
  have hN1 : (1 : ℝ) ≤ ((iwN0 ρ l : ℕ) : ℝ) := by
    exact_mod_cast (show 1 ≤ iwN0 ρ l by rw [iwN0]; exact Nat.le_add_left 1 _)
  have hNle : ((iwN0 ρ l : ℕ) : ℝ) ≤ 2 * t := by
    have hfl : ((⌊t⌋₊ : ℕ) : ℝ) ≤ t := Nat.floor_le (le_of_lt htpos)
    have heq : ((iwN0 ρ l : ℕ) : ℝ) = ((⌊t⌋₊ : ℕ) : ℝ) + 1 := by
      rw [iwN0, ← htdef, Nat.cast_add, Nat.cast_one]
    rw [heq]; linarith [ht1]
  have h2tpos : 0 < 2 * t := by linarith
  have hlogN : Real.log ((iwN0 ρ l : ℕ) : ℝ) ≤ 2 * t := by
    have h1 : Real.log ((iwN0 ρ l : ℕ) : ℝ) ≤ Real.log (2 * t) := Real.log_le_log hNpos hNle
    have h2 : Real.log (2 * t) ≤ 2 * t - 1 := Real.log_le_sub_one_of_pos h2tpos
    linarith
  have hfact : Real.log (((iwN0 ρ l).factorial : ℕ) : ℝ) ≤ 4 * S := by
    have h := Nat.factorial_le_pow (iwN0 ρ l)
    have hR : (((iwN0 ρ l).factorial : ℕ) : ℝ) ≤ (((iwN0 ρ l) ^ (iwN0 ρ l) : ℕ) : ℝ) := by
      exact_mod_cast h
    have hp : 0 < (((iwN0 ρ l).factorial : ℕ) : ℝ) := by
      exact_mod_cast Nat.factorial_pos _
    have h2 := Real.log_le_log hp hR
    rw [Nat.cast_pow, Real.log_pow] at h2
    have h3 : ((iwN0 ρ l : ℕ) : ℝ) * Real.log ((iwN0 ρ l : ℕ) : ℝ) ≤ (2 * t) * (2 * t) :=
      mul_le_mul hNle hlogN (Real.log_nonneg hN1) (by linarith)
    nlinarith [h2, h3, htt]
  have hDnn : (0 : ℝ) ≤ (iwD ρ : ℝ) := by positivity
  rw [iwQ0, Nat.cast_pow, Real.log_pow]
  have h4 := mul_le_mul_of_nonneg_left hfact hDnn
  nlinarith [h4]

/-- **The growth bound `Q_0^{(l)} ≤ 2^{C 2^{ρl}}`** (Appendix A of Krause–Mirek–Tao): the number
of admissible IW denominators at height `2^l` is at most `2^{C 2^{ρl}}`. -/
theorem iwQ0_le (ρ : ℝ) (hρ : 0 < ρ) :
    ∃ C : ℝ, 0 < C ∧ ∀ l : ℕ,
      ((Work.Analysis.IonescuWainger.iwQ0 ρ l : ℕ) : ℝ) ≤
        (2 : ℝ) ^ (C * (2 : ℝ) ^ (ρ * (l : ℝ))) := by
  set K : ℝ := 4 * (iwD ρ : ℝ) with hKdef
  have hD1 : 1 ≤ (iwD ρ : ℝ) := by
    exact_mod_cast (show 1 ≤ iwD ρ by rw [iwD]; exact Nat.le_add_left 1 _)
  have hKpos : 0 < K := by rw [hKdef]; linarith
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨K / Real.log 2, div_pos hKpos hlog2pos, ?_⟩
  intro l
  set S : ℝ := (2 : ℝ) ^ (ρ * (l : ℝ)) with hSdef
  have hx : 0 < ((iwQ0 ρ l : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < iwQ0 ρ l by rw [iwQ0]; exact pow_pos (Nat.factorial_pos _) _)
  have hlog : Real.log ((iwQ0 ρ l : ℕ) : ℝ) ≤ K * S := by
    rw [hKdef, hSdef]
    exact log_iwQ0_le ρ hρ l
  have h1 : Real.logb 2 ((iwQ0 ρ l : ℕ) : ℝ) ≤ K * S / Real.log 2 := by
    rw [Real.logb]
    exact div_le_div_of_nonneg_right hlog hlog2pos.le
  rw [← div_mul_eq_mul_div K (Real.log 2) S] at h1
  exact (Real.logb_le_iff_le_rpow (by norm_num : (1 : ℝ) < 2) hx).mp h1

end Work.KMTAreas
