/-
# Continued-fraction data: the core estimates

For an irrational `β ∈ (0,1)` this file proves the standard facts about the convergents
`cfP β n / cfQ β n` built in `CFDefs`.
-/
import Mathlib
import Submission.Work.TMC16Core.Defs
import Submission.Work.TMC16Core.Basic.CFDefs

namespace Work.TMC16Core.Basic

open Work.TMC16Core

/-! ## Tails and partial quotients -/

theorem cfX_spec {β : ℝ} (h0 : 0 < β) (h1 : β < 1) (hirr : Irrational β) (n : ℕ) :
    0 < cfX β n ∧ cfX β n < 1 ∧ Irrational (cfX β n) := by
  induction n with
  | zero => exact ⟨h0, h1, hirr⟩
  | succ n ih =>
    obtain ⟨hpos, hlt, hi⟩ := ih
    have hinv : Irrational ((cfX β n)⁻¹) := hi.inv
    have hfl : (cfX β n)⁻¹ ≠ (⌊((cfX β n)⁻¹)⌋ : ℝ) := hinv.ne_int _
    rw [cfX_succ]
    exact ⟨Int.fract_pos.mpr hfl, Int.fract_lt_one _, hinv.sub_intCast ⌊((cfX β n)⁻¹)⌋⟩

theorem cfX_pos {β : ℝ} (h0 : 0 < β) (h1 : β < 1) (hirr : Irrational β) (n : ℕ) :
    0 < cfX β n := (cfX_spec h0 h1 hirr n).1

theorem cfX_lt_one {β : ℝ} (h0 : 0 < β) (h1 : β < 1) (hirr : Irrational β) (n : ℕ) :
    cfX β n < 1 := (cfX_spec h0 h1 hirr n).2.1

theorem cfX_irrational {β : ℝ} (h0 : 0 < β) (h1 : β < 1) (hirr : Irrational β) (n : ℕ) :
    Irrational (cfX β n) := (cfX_spec h0 h1 hirr n).2.2

theorem cfX_ne_zero {β : ℝ} (h0 : 0 < β) (h1 : β < 1) (hirr : Irrational β) (n : ℕ) :
    cfX β n ≠ 0 := ne_of_gt (cfX_pos h0 h1 hirr n)

theorem cfX_succ_nonneg (β : ℝ) (n : ℕ) : 0 ≤ cfX β (n + 1) := by
  rw [cfX_succ]; exact Int.fract_nonneg _

theorem cfA_one_le {β : ℝ} (h0 : 0 < β) (h1 : β < 1) (hirr : Irrational β) (n : ℕ) :
    1 ≤ cfA β n := by
  obtain ⟨hpos, hlt, _⟩ := cfX_spec h0 h1 hirr n
  rw [cfA_apply, Int.le_floor]
  push_cast
  rw [one_le_inv₀ hpos]
  exact hlt.le

/-- The basic relation `1/(cfX β n) = cfA β n + cfX β (n+1)`. -/
theorem cfX_inv_eq (β : ℝ) (n : ℕ) :
    (cfX β n)⁻¹ = (cfA β n : ℝ) + cfX β (n + 1) := by
  rw [cfA_apply, cfX_succ]
  have h := Int.fract_add_floor ((cfX β n)⁻¹)
  linarith

theorem cfX_mul_inv_eq {β : ℝ} (h0 : 0 < β) (h1 : β < 1) (hirr : Irrational β) (n : ℕ) :
    cfX β (n + 1) * ((cfA β (n + 1) : ℝ) + cfX β (n + 2)) = 1 := by
  have hne : cfX β (n + 1) ≠ 0 := cfX_ne_zero h0 h1 hirr (n + 1)
  rw [mul_comm, ← cfX_inv_eq β (n + 1)]
  exact inv_mul_cancel₀ hne

/-! ## Denominators -/

theorem cfQ_one_le {β : ℝ} (h0 : 0 < β) (h1 : β < 1) (hirr : Irrational β) (n : ℕ) :
    1 ≤ cfQ β n := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one => simpa [cfQ_one] using cfA_one_le h0 h1 hirr 0
  | more n ih ih1 =>
    rw [cfQ_add_two]
    have ha : 1 ≤ cfA β (n + 1) := cfA_one_le h0 h1 hirr (n + 1)
    nlinarith [ih, ih1]

theorem cfQ_pos {β : ℝ} (h0 : 0 < β) (h1 : β < 1) (hirr : Irrational β) (n : ℕ) :
    0 < cfQ β n := lt_of_lt_of_le zero_lt_one (cfQ_one_le h0 h1 hirr n)

theorem cfQ_lt_succ {β : ℝ} (h0 : 0 < β) (h1 : β < 1) (hirr : Irrational β) {n : ℕ}
    (hn : 1 ≤ n) : cfQ β n < cfQ β (n + 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  rw [cfQ_add_two]
  have ha : 1 ≤ cfA β (m + 1) := cfA_one_le h0 h1 hirr (m + 1)
  have hq : 1 ≤ cfQ β (m + 1) := cfQ_one_le h0 h1 hirr (m + 1)
  have hqm : 1 ≤ cfQ β m := cfQ_one_le h0 h1 hirr m
  nlinarith

theorem cfQ_strictMono {β : ℝ} (h0 : 0 < β) (h1 : β < 1) (hirr : Irrational β) :
    StrictMono (fun m => cfQ β (m + 1)) := by
  apply strictMono_nat_of_lt_succ
  intro m
  exact cfQ_lt_succ h0 h1 hirr (n := m + 1) (by omega)

/-- From index `2` on, the denominators are at least `2`. -/
theorem cfQ_two_le {β : ℝ} (h0 : 0 < β) (h1 : β < 1) (hirr : Irrational β) {n : ℕ}
    (hn : 2 ≤ n) : 2 ≤ cfQ β n := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  rw [cfQ_add_two]
  have ha : 1 ≤ cfA β (m + 1) := cfA_one_le h0 h1 hirr (m + 1)
  have hq : 1 ≤ cfQ β (m + 1) := cfQ_one_le h0 h1 hirr (m + 1)
  have hqm : 1 ≤ cfQ β m := cfQ_one_le h0 h1 hirr m
  nlinarith

/-! ## Determinant, identity and error formula -/

theorem cf_det (β : ℝ) (n : ℕ) :
    cfQ β n * cfP β (n + 1) - cfP β n * cfQ β (n + 1) = (-1) ^ n := by
  induction n using Nat.twoStepInduction with
  | zero => simp
  | one =>
    have hP2 : cfP β 2 = cfA β 1 := by rw [cfP_add_two β 0]; simp
    have hQ2 : cfQ β 2 = cfA β 1 * cfA β 0 + 1 := by rw [cfQ_add_two β 0]; simp
    rw [cfQ_one, cfP_one, hP2, hQ2]
    ring
  | more n ih ih1 =>
    rw [cfP_add_two (n := n + 1), cfQ_add_two (n := n + 1)]
    have hcast : ((-1 : ℤ) ^ (n + 2)) = -((-1 : ℤ) ^ (n + 1)) := by ring
    rw [hcast, ← ih1]
    ring

theorem cf_identity {β : ℝ} (h0 : 0 < β) (h1 : β < 1) (hirr : Irrational β) (n : ℕ) :
    β * ((cfQ β (n + 1) : ℝ) + (cfQ β n : ℝ) * cfX β (n + 1))
      = (cfP β (n + 1) : ℝ) + (cfP β n : ℝ) * cfX β (n + 1) := by
  induction n with
  | zero =>
    have h := cfX_inv_eq β 0
    rw [cfX_zero] at h
    have hne : β ≠ 0 := ne_of_gt h0
    have hg : β * ((cfA β 0 : ℝ) + cfX β 1) = 1 := by
      rw [← h, mul_inv_cancel₀ hne]
    simpa [cfQ_one, cfQ_zero, cfP_one, cfP_zero] using hg
  | succ n ih =>
    have hx := cfX_mul_inv_eq h0 h1 hirr n
    have hxne : cfX β (n + 1) ≠ 0 := cfX_ne_zero h0 h1 hirr (n + 1)
    have hQ : ((cfQ β (n + 2) : ℝ) + (cfQ β (n + 1) : ℝ) * cfX β (n + 2)) * cfX β (n + 1)
        = (cfQ β (n + 1) : ℝ) + (cfQ β n : ℝ) * cfX β (n + 1) := by
      have expand : ((cfQ β (n + 2) : ℝ) + (cfQ β (n + 1) : ℝ) * cfX β (n + 2)) * cfX β (n + 1)
          = (cfQ β (n + 1) : ℝ) * (cfX β (n + 1) * ((cfA β (n + 1) : ℝ) + cfX β (n + 2)))
            + (cfQ β n : ℝ) * cfX β (n + 1) := by
        rw [cfQ_add_two]
        push_cast
        ring
      rw [expand, hx]
      ring
    have hP : ((cfP β (n + 2) : ℝ) + (cfP β (n + 1) : ℝ) * cfX β (n + 2)) * cfX β (n + 1)
        = (cfP β (n + 1) : ℝ) + (cfP β n : ℝ) * cfX β (n + 1) := by
      have expand : ((cfP β (n + 2) : ℝ) + (cfP β (n + 1) : ℝ) * cfX β (n + 2)) * cfX β (n + 1)
          = (cfP β (n + 1) : ℝ) * (cfX β (n + 1) * ((cfA β (n + 1) : ℝ) + cfX β (n + 2)))
            + (cfP β n : ℝ) * cfX β (n + 1) := by
        rw [cfP_add_two]
        push_cast
        ring
      rw [expand, hx]
      ring
    refine mul_right_cancel₀ hxne ?_
    rw [mul_assoc, hQ, ih, ← hP]

theorem cfMpos {β : ℝ} (h0 : 0 < β) (h1 : β < 1) (hirr : Irrational β) (n : ℕ) :
    0 < (cfQ β (n + 1) : ℝ) + (cfQ β n : ℝ) * cfX β (n + 1) := by
  have hQ1 : (1 : ℝ) ≤ (cfQ β (n + 1) : ℝ) := by
    exact_mod_cast cfQ_one_le h0 h1 hirr (n + 1)
  have hQ0 : (0 : ℝ) ≤ (cfQ β n : ℝ) := by
    have h := cfQ_one_le h0 h1 hirr n
    have hz : (0 : ℤ) ≤ cfQ β n := by omega
    exact_mod_cast hz
  have hxn : 0 ≤ cfX β (n + 1) := cfX_succ_nonneg β n
  nlinarith [mul_nonneg hQ0 hxn]

theorem cf_error {β : ℝ} (h0 : 0 < β) (h1 : β < 1) (hirr : Irrational β) (n : ℕ) :
    (cfQ β n : ℝ) * β - (cfP β n : ℝ)
      = (-1 : ℝ) ^ n / ((cfQ β (n + 1) : ℝ) + (cfQ β n : ℝ) * cfX β (n + 1)) := by
  have hid := cf_identity h0 h1 hirr n
  have hdetR : (cfQ β n : ℝ) * (cfP β (n + 1) : ℝ) - (cfP β n : ℝ) * (cfQ β (n + 1) : ℝ)
      = (-1 : ℝ) ^ n := by
    have h := cf_det β n
    exact_mod_cast h
  have hMpos := cfMpos h0 h1 hirr n
  have key : ((cfQ β n : ℝ) * β - (cfP β n : ℝ))
      * ((cfQ β (n + 1) : ℝ) + (cfQ β n : ℝ) * cfX β (n + 1)) = (-1 : ℝ) ^ n := by
    have expand : ((cfQ β n : ℝ) * β - (cfP β n : ℝ))
        * ((cfQ β (n + 1) : ℝ) + (cfQ β n : ℝ) * cfX β (n + 1))
        = (cfQ β n : ℝ) * (β * ((cfQ β (n + 1) : ℝ) + (cfQ β n : ℝ) * cfX β (n + 1)))
          - (cfP β n : ℝ) * ((cfQ β (n + 1) : ℝ) + (cfQ β n : ℝ) * cfX β (n + 1)) := by ring
    rw [expand, hid]
    linear_combination hdetR
  rw [eq_div_iff hMpos.ne']
  exact key

/-! ## The quantities `cfDelta β n` -/

/-- `cfDelta β n = 1/(cfQ β (n+1) + cfQ β n * cfX β (n+1))`, the exact value of
`|cfQ β n * β - cfP β n|` for `n ≥ 1`. -/
noncomputable def cfDelta (β : ℝ) (n : ℕ) : ℝ :=
  1 / ((cfQ β (n + 1) : ℝ) + (cfQ β n : ℝ) * cfX β (n + 1))

theorem cfDelta_pos {β : ℝ} (h0 : 0 < β) (h1 : β < 1) (hirr : Irrational β) (n : ℕ) :
    0 < cfDelta β n := by
  rw [cfDelta]
  exact one_div_pos.mpr (cfMpos h0 h1 hirr n)

theorem cfDelta_lt {β : ℝ} (h0 : 0 < β) (h1 : β < 1) (hirr : Irrational β) (n : ℕ) :
    cfDelta β n < 1 / (cfQ β (n + 1) : ℝ) := by
  have hQp : (0 : ℝ) < (cfQ β (n + 1) : ℝ) := by
    have h := cfQ_one_le h0 h1 hirr (n + 1)
    have hz : (0 : ℤ) < cfQ β (n + 1) := by omega
    exact_mod_cast hz
  rw [cfDelta, one_div_lt_one_div (cfMpos h0 h1 hirr n) hQp]
  have hx : 0 < cfX β (n + 1) := cfX_pos h0 h1 hirr (n + 1)
  have hq : 0 < (cfQ β n : ℝ) := by
    have h := cfQ_one_le h0 h1 hirr n
    have hz : (0 : ℤ) < cfQ β n := by omega
    exact_mod_cast hz
  nlinarith [mul_pos hq hx]

theorem cfDelta_gt {β : ℝ} (h0 : 0 < β) (h1 : β < 1) (hirr : Irrational β) (n : ℕ) :
    1 / ((cfQ β (n + 1) : ℝ) + (cfQ β n : ℝ)) < cfDelta β n := by
  have hQp : (1 : ℝ) ≤ (cfQ β (n + 1) : ℝ) := by
    exact_mod_cast cfQ_one_le h0 h1 hirr (n + 1)
  have hQn : (0 : ℝ) ≤ (cfQ β n : ℝ) := by
    have h := cfQ_one_le h0 h1 hirr n
    have hz : (0 : ℤ) ≤ cfQ β n := by omega
    exact_mod_cast hz
  have hDpos : 0 < (cfQ β (n + 1) : ℝ) + (cfQ β n : ℝ) := by linarith
  rw [cfDelta, one_div_lt_one_div hDpos (cfMpos h0 h1 hirr n)]
  have hx : cfX β (n + 1) < 1 := cfX_lt_one h0 h1 hirr (n + 1)
  have hq : 0 < (cfQ β n : ℝ) := by
    have h := cfQ_one_le h0 h1 hirr n
    have hz : (0 : ℤ) < cfQ β n := by omega
    exact_mod_cast hz
  nlinarith

theorem cf_fracDist_eq_cfDelta {β : ℝ} (h0 : 0 < β) (h1 : β < 1) (hirr : Irrational β)
    {n : ℕ} (hn : 1 ≤ n) : fracDist ((cfQ β n : ℝ) * β) = cfDelta β n := by
  have herr := cf_error h0 h1 hirr n
  have habs : |(cfQ β n : ℝ) * β - (cfP β n : ℝ)| = cfDelta β n := by
    rw [herr, cfDelta, abs_div, abs_neg_one_pow, abs_of_pos (cfMpos h0 h1 hirr n)]
  have hlt1 := cfDelta_lt h0 h1 hirr n
  have hQ2 : (2 : ℝ) ≤ (cfQ β (n + 1) : ℝ) := by
    have h2 : 2 ≤ cfQ β (n + 1) := cfQ_two_le h0 h1 hirr (by omega)
    exact_mod_cast h2
  have hQp : (0 : ℝ) < (cfQ β (n + 1) : ℝ) := by
    have h := cfQ_one_le h0 h1 hirr (n + 1)
    have hz : (0 : ℤ) < cfQ β (n + 1) := by omega
    exact_mod_cast hz
  have hlt : cfDelta β n < 1 / 2 := by
    refine lt_of_lt_of_le hlt1 ?_
    rw [one_div_le_one_div hQp (by norm_num : (0 : ℝ) < 2)]
    exact hQ2
  have habslt : |(cfQ β n : ℝ) * β - (cfP β n : ℝ)| < 1 / 2 := by rw [habs]; exact hlt
  have hround : round ((cfQ β n : ℝ) * β) = cfP β n := by
    rw [round_eq_iff, Set.mem_Ico]
    obtain ⟨hl, hr⟩ := abs_lt.mp habslt
    exact ⟨by linarith, by linarith⟩
  simp only [Work.TMC16Core.fracDist, hround]
  exact habs

end Work.TMC16Core.Basic
