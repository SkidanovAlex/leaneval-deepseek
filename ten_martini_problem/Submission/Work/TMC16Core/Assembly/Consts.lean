import Mathlib
import Submission.Work.TMC16Core.Defs
import Submission.Work.TMC16Core.Core.geom

/-!
# The numerical constants of the non-resonant branch of AJ §9

With `L = log λ > 0` the non-resonant branch of `Assembly` uses

* `csing L = 99 L/100`: the singularity parameter (`m_sing = L/100` is fixed, so `0` is
  `(m_sing, K)`-singular for all large `K`);
* `epsA L εu = max εu (csing L/40) + L/1000`: the `A`-exponent deficit, where `εu` is the
  uniformity rate of `NrFinal.nr_uniform`; the `max` makes `δ ≥ 1/40` free;
* `cdelta L εu = (epsA L εu + L/10000)/csing L`: the window parameter `δ`, so that
  `csing · δ - L/10000 = epsA` — the exact hypothesis of `Core.nr_ablock`;
* `cL1 L = L/4`: the uniform decay rate `L₁`;
* `eps2 L = L/100`: the Furman slack used in the `hbd` hypothesis.

The single numerical hypothesis on the uniformity rate is `εu ≤ L/8 + L/100`.
-/

namespace Work.TMC16Core.Assembly

open Work.TMC16Core
open Work.TMC16Core.Core

noncomputable section

/-- The singularity rate `m_sing = L/100`. -/
def msing (L : ℝ) : ℝ := L / 100

/-- The singularity parameter `εsing = L - m_sing = 99 L/100`. -/
def csing (L : ℝ) : ℝ := L - L / 100

/-- The Furman slack. -/
def eps2 (L : ℝ) : ℝ := L / 100

/-- The Lemma 9.2 slack. -/
def epss (L : ℝ) : ℝ := L / 10000

/-- The `A`-exponent deficit `εA`. -/
def epsA (L εu : ℝ) : ℝ := max εu (csing L / 40) + L / 1000

/-- The window parameter `δ`. -/
def cdelta (L εu : ℝ) : ℝ := (epsA L εu + eps2 L) / csing L

/-- The uniform decay rate `L₁`. -/
def cL1 (L : ℝ) : ℝ := L / 4

/-- The uniformity rate of `NrFinal.nr_uniform`. -/
def rateNR1 (q : ℕ → ℕ) (n s : ℕ) (c : ℝ) : ℝ :=
  2 * Real.log ((q n : ℝ) / (s : ℝ)) / (q (n - 1) : ℝ)
    + 200 * Real.log (q (n - 1) : ℝ) / (q (n - 1) : ℝ)
    + 2 * Real.log (1 / c) / ((s : ℝ) * (q (n - 1) : ℝ))
    + 200 / (q (n - 1) : ℝ)

/-! ## Elementary bounds -/

theorem csing_pos {L : ℝ} (hL : 0 < L) : 0 < csing L := by
  simp only [csing]; linarith

theorem msing_pos {L : ℝ} (hL : 0 < L) : 0 < msing L := by
  simp only [msing]; linarith

theorem csing_lt_L {L : ℝ} (hL : 0 < L) : csing L < L := by
  simp only [csing]; linarith

theorem eps2_pos {L : ℝ} (hL : 0 < L) : 0 < eps2 L := by
  simp only [eps2]; linarith

theorem epss_pos {L : ℝ} (hL : 0 < L) : 0 < epss L := by
  simp only [epss]; linarith

theorem epsA_gt {L εu : ℝ} (hL : 0 < L) : εu < epsA L εu := by
  have : εu ≤ max εu (csing L / 40) := le_max_left _ _
  simp only [epsA]; linarith

theorem epsA_sub {L εu : ℝ} : L / 1000 ≤ epsA L εu - εu := by
  simp only [epsA]
  rcases le_total εu (csing L / 40) with h | h
  · rw [max_eq_right h]; linarith
  · rw [max_eq_left h]; linarith

theorem epsA_le {L εu : ℝ} (hL : 0 < L) (hεu : εu ≤ L / 8 + L / 100) :
    epsA L εu ≤ L / 8 + L / 100 + L / 1000 := by
  have h1 : csing L / 40 ≤ L / 8 + L / 100 := by
    simp only [csing]; linarith
  simp only [epsA]
  rcases le_total εu (csing L / 40) with h | h
  · rw [max_eq_right h]; linarith
  · rw [max_eq_left h]; linarith

/-- The central constant inequality `εA + (3/4) ε₂ + L₁/4 ≤ L/4`. -/
theorem epsA_hkey {L εu : ℝ} (hL : 0 < L) (hεu : εu ≤ L / 8 + L / 100) :
    epsA L εu + (3 / 4) * eps2 L + cL1 L / 4 ≤ L / 4 := by
  have h := epsA_le hL hεu
  simp only [eps2, cL1]
  linarith

theorem epsA_le_L {L εu : ℝ} (hL : 0 < L) (hεu : εu ≤ L / 8 + L / 100) :
    epsA L εu ≤ L := by
  have h := epsA_le hL hεu
  linarith

theorem cL1_pos {L : ℝ} (hL : 0 < L) : 0 < cL1 L := by
  simp only [cL1]; linarith

theorem cL1_le_L {L : ℝ} (hL : 0 < L) : cL1 L ≤ L := by
  simp only [cL1]; linarith

/-- `csing · δ - ε₂ = εA`: the exact hypothesis of `Core.nr_ablock`. -/
theorem cdelta_spec {L εu : ℝ} (h : csing L ≠ 0) :
    csing L * cdelta L εu - eps2 L = epsA L εu := by
  simp only [cdelta]
  rw [mul_div_cancel₀ _ h]
  ring

theorem cdelta_spec' {L εu : ℝ} (h : csing L ≠ 0) :
    csing L * cdelta L εu = epsA L εu + eps2 L := by
  simp only [cdelta]
  rw [mul_div_cancel₀ _ h]

/-- The window parameter lies in `[1/40, 1/4 - 1/(4s)]`. -/
theorem cdelta_bounds {L εu : ℝ} {s : ℕ} (hL : 0 < L) (hεu : εu ≤ L / 8 + L / 100)
    (hs : 3 ≤ s) :
    1 / 40 ≤ cdelta L εu ∧ cdelta L εu ≤ 1 / 4 - 1 / (4 * (s : ℝ)) := by
  have h1 : 0 < csing L := csing_pos hL
  have hεA := epsA_le hL hεu
  have hsR : (3 : ℝ) ≤ (s : ℝ) := by exact_mod_cast hs
  have hlow : (1 / 40) * csing L ≤ epsA L εu + eps2 L := by
    have h2 : csing L / 40 ≤ epsA L εu := by
      simp only [epsA]
      linarith [le_max_right εu (csing L / 40), show (0:ℝ) < L / 1000 by linarith]
    have h3 : 0 < eps2 L := eps2_pos hL
    linarith
  have hsu : (1 : ℝ) / 4 - 1 / (4 * (s : ℝ)) ≥ 1 / 6 := by
    have h4s : (0 : ℝ) < 4 * (s : ℝ) := by linarith
    have h12 : (1 : ℝ) / (4 * (s : ℝ)) ≤ 1 / 12 := by
      rw [div_le_div_iff₀ h4s (by norm_num : (0 : ℝ) < 12)]
      linarith
    linarith
  have hhigh : epsA L εu + eps2 L ≤ csing L * (1 / 4 - 1 / (4 * (s : ℝ))) := by
    have h6 : epsA L εu + eps2 L ≤ csing L * (1 / 6) := by
      simp only [csing] at hεA ⊢
      simp only [eps2]
      linarith
    nlinarith [csing_pos hL, hsu]
  constructor
  · rw [cdelta, le_div_iff₀ h1]; linarith
  · rw [cdelta, div_le_iff₀ h1]; linarith

theorem rateNR1_pos {q : ℕ → ℕ} {n s : ℕ} {c : ℝ}
    (hL : 1 ≤ q (n - 1)) (hqn : s ≤ q n) (hs : 1 ≤ s) (hc : 0 < c) (hc1 : c ≤ 1) :
    0 < rateNR1 q n s c := by
  rw [rateNR1]
  have h1 : (0 : ℝ) < (q (n - 1) : ℝ) := by exact_mod_cast (by omega : 0 < q (n - 1))
  have h2 : (0 : ℝ) < (s : ℝ) := by exact_mod_cast (by omega : 0 < s)
  have h3 : (0 : ℝ) < (q n : ℝ) := lt_of_lt_of_le h2 (by exact_mod_cast hqn)
  have hlog : 0 ≤ Real.log ((q n : ℝ) / (s : ℝ)) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ h2, one_mul]
    exact_mod_cast hqn
  have hlog2 : 0 ≤ Real.log (q (n - 1) : ℝ) := Real.log_nonneg (by exact_mod_cast hL)
  have hlog3 : 0 ≤ Real.log (1 / c) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ hc, one_mul]; linarith
  have ht1 : 0 ≤ 2 * Real.log ((q n : ℝ) / (s : ℝ)) / (q (n - 1) : ℝ) :=
    div_nonneg (by linarith) (le_of_lt h1)
  have ht2 : 0 ≤ 200 * Real.log (q (n - 1) : ℝ) / (q (n - 1) : ℝ) :=
    div_nonneg (by linarith) (le_of_lt h1)
  have ht3 : 0 ≤ 2 * Real.log (1 / c) / ((s : ℝ) * (q (n - 1) : ℝ)) :=
    div_nonneg (by linarith) (by positivity)
  have ht4 : 0 < 200 / (q (n - 1) : ℝ) := by positivity
  linarith

end

end Work.TMC16Core.Assembly
