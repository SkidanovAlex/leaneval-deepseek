import Mathlib
import Submission.Work.Analysis.IonescuWainger.Basic

/-!
# The logarithmic growth bound for `Q_0^{(l)}` used in Appendix A

`Q_0^{(l)} = (N_0^{(l)}!)^{D_ρ}` with `N_0^{(l)} = ⌊2^{ρ l/2}⌋ + 1 ≤ 2·2^{ρ l/2}` and
`D_ρ = ⌊2/ρ⌋ + 1`.  Since `log(N!) ≤ N log N` and `log N_0^{(l)} ≤ (1 + ρ l/2) log 2`, we get

  `logb 2 (Q_0^{(l)}) = log Q_0^{(l)} / log 2 ≤ D_ρ (2 + ρ l) 2^{ρ l/2}
     ≤ D_ρ (2 + ρ) (l + 1) 2^{ρ l/2}`,

which is the estimate `Q_0^{(l)} ≤ 2^{D_ρ (2+ρ)(l+1) 2^{ρl/2}}` quoted in the proof of the
Ionescu–Wainger decomposition (Krause–Mirek–Tao, Appendix A).
-/

set_option autoImplicit false

namespace Work.KMTAreas

open Work.Analysis.IonescuWainger

/-- **Logarithmic growth of `Q_0^{(l)}`.** -/
theorem logb_iwQ0_le (ρ : ℝ) (hρ : 0 < ρ) (l : ℕ) :
    Real.logb 2 ((Work.Analysis.IonescuWainger.iwQ0 ρ l : ℕ) : ℝ) ≤
      ((Work.Analysis.IonescuWainger.iwD ρ : ℕ) : ℝ) * (2 + ρ) * ((l : ℝ) + 1) *
        (2 : ℝ) ^ (ρ * (l : ℝ) / 2) := by
  set t : ℝ := (2 : ℝ) ^ (ρ * (l : ℝ) / 2) with ht
  have htpos : 0 < t := by rw [ht]; positivity
  have ht1 : 1 ≤ t := by
    rw [ht]
    exact Real.one_le_rpow (by norm_num : (1 : ℝ) ≤ 2) (by positivity)
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hNpos : 0 < (((iwN0 ρ l : ℕ) : ℝ)) := by
    exact_mod_cast (show 0 < iwN0 ρ l by rw [iwN0]; exact Nat.succ_pos _)
  have hN1 : (1 : ℝ) ≤ ((iwN0 ρ l : ℕ) : ℝ) := by
    exact_mod_cast (show 1 ≤ iwN0 ρ l by rw [iwN0]; exact Nat.le_add_left 1 _)
  have hNle : ((iwN0 ρ l : ℕ) : ℝ) ≤ 2 * t := by
    have hfl : ((⌊t⌋₊ : ℕ) : ℝ) ≤ t := Nat.floor_le (le_of_lt htpos)
    have heq : ((iwN0 ρ l : ℕ) : ℝ) = ((⌊t⌋₊ : ℕ) : ℝ) + 1 := by
      rw [iwN0, ← ht, Nat.cast_add, Nat.cast_one]
    rw [heq]; linarith [ht1]
  have hlogN : Real.log ((iwN0 ρ l : ℕ) : ℝ) ≤ (1 + ρ * (l : ℝ) / 2) * Real.log 2 := by
    have hle : ((iwN0 ρ l : ℕ) : ℝ) ≤ (2 : ℝ) ^ (1 + ρ * (l : ℝ) / 2) := by
      calc ((iwN0 ρ l : ℕ) : ℝ) ≤ 2 * t := hNle
        _ = (2 : ℝ) ^ (1 : ℝ) * (2 : ℝ) ^ (ρ * (l : ℝ) / 2) := by
              rw [ht, Real.rpow_one]
        _ = (2 : ℝ) ^ (1 + ρ * (l : ℝ) / 2) :=
              (Real.rpow_add (by norm_num) 1 _).symm
    calc Real.log ((iwN0 ρ l : ℕ) : ℝ)
        ≤ Real.log ((2 : ℝ) ^ (1 + ρ * (l : ℝ) / 2)) := Real.log_le_log hNpos hle
      _ = (1 + ρ * (l : ℝ) / 2) * Real.log 2 := Real.log_rpow (by norm_num) _
  have hfact : Real.log ((((iwN0 ρ l).factorial : ℕ) : ℝ))
      ≤ ((iwN0 ρ l : ℕ) : ℝ) * Real.log ((iwN0 ρ l : ℕ) : ℝ) := by
    have hle : ((((iwN0 ρ l).factorial : ℕ) : ℝ))
        ≤ (((iwN0 ρ l) ^ (iwN0 ρ l) : ℕ) : ℝ) := by
      exact_mod_cast Nat.factorial_le_pow (iwN0 ρ l)
    have hpos : 0 < ((((iwN0 ρ l).factorial : ℕ) : ℝ)) := by
      exact_mod_cast Nat.factorial_pos _
    have h := Real.log_le_log hpos hle
    rw [Nat.cast_pow, Real.log_pow] at h
    exact h
  have h1 : ((iwN0 ρ l : ℕ) : ℝ) * Real.log ((iwN0 ρ l : ℕ) : ℝ)
      ≤ (2 * t) * ((1 + ρ * (l : ℝ) / 2) * Real.log 2) :=
    mul_le_mul hNle hlogN (Real.log_nonneg hN1) (by linarith [htpos])
  have hle2 : (2 + ρ * (l : ℝ)) ≤ (2 + ρ) * ((l : ℝ) + 1) := by
    have hl : (0 : ℝ) ≤ (l : ℝ) := Nat.cast_nonneg l
    nlinarith [hρ.le, hl]
  have hkey : Real.log ((((iwN0 ρ l).factorial : ℕ) : ℝ))
      ≤ (2 + ρ) * ((l : ℝ) + 1) * t * Real.log 2 := by
    calc Real.log ((((iwN0 ρ l).factorial : ℕ) : ℝ))
        ≤ ((iwN0 ρ l : ℕ) : ℝ) * Real.log ((iwN0 ρ l : ℕ) : ℝ) := hfact
      _ ≤ (2 * t) * ((1 + ρ * (l : ℝ) / 2) * Real.log 2) := h1
      _ = (2 + ρ * (l : ℝ)) * (t * Real.log 2) := by ring
      _ ≤ ((2 + ρ) * ((l : ℝ) + 1)) * (t * Real.log 2) :=
            mul_le_mul_of_nonneg_right hle2 (mul_nonneg htpos.le hlog2pos.le)
      _ = (2 + ρ) * ((l : ℝ) + 1) * t * Real.log 2 := by ring
  have hlogQ : Real.log ((iwQ0 ρ l : ℕ) : ℝ) =
      (iwD ρ : ℝ) * Real.log ((((iwN0 ρ l).factorial : ℕ) : ℝ)) := by
    rw [iwQ0, Nat.cast_pow, Real.log_pow]
  have hDnn : (0 : ℝ) ≤ (iwD ρ : ℝ) := by positivity
  rw [Real.logb, hlogQ, div_le_iff₀ hlog2pos]
  have hDkey := mul_le_mul_of_nonneg_left hkey hDnn
  calc (iwD ρ : ℝ) * Real.log ((((iwN0 ρ l).factorial : ℕ) : ℝ))
      ≤ (iwD ρ : ℝ) * ((2 + ρ) * ((l : ℝ) + 1) * t * Real.log 2) := hDkey
    _ = ((iwD ρ : ℝ) * (2 + ρ) * ((l : ℝ) + 1) * t) * Real.log 2 := by ring

end Work.KMTAreas
