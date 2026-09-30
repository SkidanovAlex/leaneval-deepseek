import Mathlib
import Submission.Work.BMF.adi_all_defs
import Submission.Work.BMF.adi_count
import Submission.Work.BMF.primesIn_card_le_pi0

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Chebyshev-type bound for the primes in `[P/2, P]`, valid for all `P ≥ 2`

`Work.BMF.primesIn_half_card_le` (in `adi_count`) gives `#(primesIn (P/2) P) ≤ C π₀ P` only
for `P` above a threshold `P₀`.  Here we upgrade it to *all* `P ≥ 2`, at the price of a larger
constant: below the threshold `B = max P₀ 2` the number of primes in `[P/2, P]` is at most the
number of integers in that interval, i.e. at most `⌊B⌋₊ + 1`, while `π₀ P = P / log P ≥ 2 / log B`
is bounded below on `[2, B]`.
-/

namespace Work.BMF

/-- Crude bound: the primes of `[P/2, P]` are integers of `[⌈P/2⌉₊, ⌊P⌋₊]`, hence number at
most `⌊P⌋₊ + 1`. -/
theorem primesIn_half_card_le_floor (P : ℝ) :
    (Work.BMF.primesIn (P / 2) P).card ≤ ⌊P⌋₊ + 1 := by
  have hsub : Work.BMF.primesIn (P / 2) P ⊆ Finset.Icc ⌈P / 2⌉₊ ⌊P⌋₊ := by
    intro p hp
    rw [Work.BMF.primesIn, Work.BMF.natIcc, Finset.mem_filter] at hp
    exact hp.1
  calc (Work.BMF.primesIn (P / 2) P).card ≤ (Finset.Icc ⌈P / 2⌉₊ ⌊P⌋₊).card :=
        Finset.card_le_card hsub
    _ = ⌊P⌋₊ + 1 - ⌈P / 2⌉₊ := Nat.card_Icc _ _
    _ ≤ ⌊P⌋₊ + 1 := Nat.sub_le _ _

/-- `π₀` is bounded below on `[2, B]`: for `2 ≤ P ≤ B` one has `2 / log B ≤ π₀ P`. -/
theorem two_div_log_le_pi0 {P B : ℝ} (hP : 2 ≤ P) (hPB : P ≤ B) :
    2 / Real.log B ≤ pi0 P := by
  have hP0 : 0 < P := by linarith
  have hlogP : 0 < Real.log P := Real.log_pos (by linarith)
  have h1 : 2 / Real.log B ≤ 2 / Real.log P :=
    div_le_div_of_nonneg_left (by norm_num) hlogP (Real.log_le_log hP0 hPB)
  have h2 : 2 / Real.log P ≤ P / Real.log P :=
    div_le_div_of_nonneg_right hP hlogP.le
  rw [pi0]
  linarith

theorem primesIn_half_card_le_all :
    ∃ C : ℝ, 0 < C ∧ ∀ P : ℝ, 2 ≤ P →
      ((Work.BMF.primesIn (P / 2) P).card : ℝ) ≤ C * Work.BMF.pi0 P := by
  obtain ⟨C₀, P₀, hC₀, hbound⟩ := primesIn_half_card_le
  set B : ℝ := max P₀ 2 with hBdef
  have hB2 : 2 ≤ B := le_max_right _ _
  have hBP₀ : P₀ ≤ B := le_max_left _ _
  have hlogB : 0 < Real.log B := Real.log_pos (by linarith)
  have hDnonneg : (0 : ℝ) ≤ ((⌊B⌋₊ + 1 : ℕ) : ℝ) := by positivity
  refine ⟨C₀ + ((⌊B⌋₊ + 1 : ℕ) : ℝ) * Real.log B / 2, ?_, ?_⟩
  · have hterm : 0 ≤ ((⌊B⌋₊ + 1 : ℕ) : ℝ) * Real.log B / 2 := by positivity
    linarith
  · intro P hP
    have hlogP : 0 < Real.log P := Real.log_pos (by linarith)
    have hpi0 : 0 ≤ pi0 P := by rw [pi0]; positivity
    set C : ℝ := C₀ + ((⌊B⌋₊ + 1 : ℕ) : ℝ) * Real.log B / 2 with hCdef
    have hCge : C₀ ≤ C := by
      have hterm : 0 ≤ ((⌊B⌋₊ + 1 : ℕ) : ℝ) * Real.log B / 2 := by positivity
      rw [hCdef]; linarith
    -- the elementary bound at the threshold: `⌊B⌋₊ + 1 ≤ C * (2 / log B)`
    have hDle : ((⌊B⌋₊ + 1 : ℕ) : ℝ) ≤ C * (2 / Real.log B) := by
      have hstep : ((⌊B⌋₊ + 1 : ℕ) : ℝ) * (Real.log B / 2) ≤ C := by
        have hterm : ((⌊B⌋₊ + 1 : ℕ) : ℝ) * Real.log B / 2 =
            ((⌊B⌋₊ + 1 : ℕ) : ℝ) * (Real.log B / 2) := by ring
        rw [hCdef, hterm]
        linarith
      have hfac : 0 ≤ 2 / Real.log B := by positivity
      calc ((⌊B⌋₊ + 1 : ℕ) : ℝ)
          = ((⌊B⌋₊ + 1 : ℕ) : ℝ) * (Real.log B / 2) * (2 / Real.log B) := by
            field_simp
        _ ≤ C * (2 / Real.log B) := mul_le_mul_of_nonneg_right hstep hfac
    rcases le_or_gt B P with hPB | hPB
    · -- large range: the threshold version applies
      calc ((Work.BMF.primesIn (P / 2) P).card : ℝ) ≤ C₀ * pi0 P := hbound P (le_trans hBP₀ hPB)
        _ ≤ C * pi0 P := mul_le_mul_of_nonneg_right hCge hpi0
    · -- small range: crude counting plus the lower bound for `π₀`
      have hcard : ((Work.BMF.primesIn (P / 2) P).card : ℝ) ≤
          ((⌊B⌋₊ + 1 : ℕ) : ℝ) := by
        have h1 : (Work.BMF.primesIn (P / 2) P).card ≤ ⌊P⌋₊ + 1 :=
          primesIn_half_card_le_floor P
        have h2 : ⌊P⌋₊ ≤ ⌊B⌋₊ := Nat.floor_mono hPB.le
        have h3 : (Work.BMF.primesIn (P / 2) P).card ≤ ⌊B⌋₊ + 1 :=
          le_trans h1 (Nat.add_le_add_right h2 1)
        exact_mod_cast h3
      have hpi0ge : 2 / Real.log B ≤ pi0 P := two_div_log_le_pi0 hP hPB.le
      have hCnonneg : 0 ≤ C := le_trans hC₀.le hCge
      calc ((Work.BMF.primesIn (P / 2) P).card : ℝ)
          ≤ ((⌊B⌋₊ + 1 : ℕ) : ℝ) := hcard
        _ ≤ C * (2 / Real.log B) := hDle
        _ ≤ C * pi0 P := mul_le_mul_of_nonneg_left hpi0ge hCnonneg

end Work.BMF
