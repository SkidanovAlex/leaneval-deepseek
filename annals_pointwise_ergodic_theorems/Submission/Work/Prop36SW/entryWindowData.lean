import Mathlib
import Submission.Work.Prop36SW.roundToNextDefs
import Submission.Work.Peluse.P1Aux.card_ge_two_mul_cD

namespace Work.Prop36SW

theorem entryWindowData (D : Work.Peluse.UControl.IdxDatum) (d : ℕ) (c : ℤ) (A₀ : ℝ) (b : ℤ)
    (s : ℕ) (hA₀ : 1 ≤ A₀) (hd : 2 ≤ d) (hb : 0 ≤ b) :
    ∃ Cw : ℝ, 0 < Cw ∧ 1 ≤ Cw ∧
      ∀ (N H : ℕ) (η : ℝ), 1 ≤ N → 1 ≤ H → 0 < η → η ≤ 1 →
        ((H : ℝ) + 1) ^ d ≤ A₀ * (N : ℝ) →
        ∃ N₀ N₂ : ℕ,
          N ≤ N₀ ∧ N₀ ≤ N₂ ∧
          ((H : ℝ) + 1) * ((H : ℝ) + 1) ≤ (N₀ : ℝ) ∧
          b * ((H : ℤ) + 1) ^ d ≤ (N₀ : ℤ) ∧
          Work.Prop36SW.ambK D d c * ((H : ℝ) + 1) ^ d ≤ (N₂ : ℝ) ∧
          (N₂ : ℝ) ≤ Cw * (N : ℝ) ∧
          (((2 : ℝ) ^ s) * (2 * Cw + 1))⁻¹ * η ≤
            ((((Work.Peluse.symIcc N).card : ℝ) / ((Work.Peluse.symIcc N₀).card : ℝ)) * η
                / (2 : ℝ) ^ s)
              * (((Work.Peluse.symIcc N₀).card : ℝ) / ((Work.Peluse.symIcc N₂).card : ℝ)) := by
  -- The window data is chosen by rounding up.  Concretely, for a given `(N,H,η)` we pick
  -- `N₀ := max N ⌈(H+1)^2⌉ ⌈b(H+1)^d⌉` and `N₂ := max N₀ ⌈ambK·(H+1)^d⌉`, and we take the
  -- constant `Cw := A₀·(b+1) + A₀·ambK + 3`, large enough that `N₂ ≤ Cw·N` for every datum
  -- satisfying `(H+1)^d ≤ A₀N`.  The last inequality then only needs the crude bound
  -- `|symIcc N₂| ≤ (2Cw+1)|symIcc N|`.
  have hbR : (0 : ℝ) ≤ (b : ℝ) := by exact_mod_cast hb
  have hK1 : 1 ≤ Work.Prop36SW.ambK D d c := Work.Prop36SW.one_le_ambK D d c
  set Cw : ℝ := A₀ * ((b : ℝ) + 1) + A₀ * Work.Prop36SW.ambK D d c + 3 with hCwdef
  have hCwpos : 0 < Cw := by rw [hCwdef]; nlinarith
  have hCw1 : 1 ≤ Cw := by rw [hCwdef]; nlinarith
  refine ⟨Cw, hCwpos, hCw1, ?_⟩
  intro N H η hN hH hη _hη1 hHd
  have hK0 : 0 ≤ Work.Prop36SW.ambK D d c := le_trans zero_le_one hK1
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hH1 : (1 : ℝ) ≤ (H : ℝ) + 1 := by
    have := Nat.cast_nonneg (α := ℝ) H; linarith
  have hX1 : (1 : ℝ) ≤ ((H : ℝ) + 1) ^ d := one_le_pow₀ hH1
  have hX0 : 0 ≤ ((H : ℝ) + 1) ^ d := le_trans zero_le_one hX1
  have hX2d : ((H : ℝ) + 1) ^ 2 ≤ ((H : ℝ) + 1) ^ d := pow_le_pow_right₀ hH1 hd
  have hXA : ((H : ℝ) + 1) ^ d ≤ A₀ * (N : ℝ) := hHd
  set n₀ : ℕ := max N (max ⌈((H : ℝ) + 1) ^ 2⌉₊ ⌈(b : ℝ) * ((H : ℝ) + 1) ^ d⌉₊) with hn₀def
  set n₂ : ℕ := max n₀ ⌈(Work.Prop36SW.ambK D d c) * ((H : ℝ) + 1) ^ d⌉₊ with hn₂def
  have hmax1 : (n₀ : ℝ) ≤ (b : ℝ) * A₀ * (N : ℝ) + A₀ * (N : ℝ) + 1 := by
    rw [hn₀def]; push_cast
    refine max_le ?_ (max_le ?_ ?_)
    · nlinarith [hN1, hA₀, hbR, hX0]
    · have h : ((⌈((H : ℝ) + 1) ^ 2⌉₊ : ℕ) : ℝ) ≤ ((H : ℝ) + 1) ^ 2 + 1 :=
        le_of_lt (Nat.ceil_lt_add_one (by positivity))
      nlinarith [h, hX2d, hXA, hbR]
    · have h : ((⌈(b : ℝ) * ((H : ℝ) + 1) ^ d⌉₊ : ℕ) : ℝ) ≤ (b : ℝ) * ((H : ℝ) + 1) ^ d + 1 :=
        le_of_lt (Nat.ceil_lt_add_one (mul_nonneg hbR hX0))
      nlinarith [h, hXA, hbR]
  have hmax2 : (n₂ : ℝ)
      ≤ (Work.Prop36SW.ambK D d c) * A₀ * (N : ℝ) + (b : ℝ) * A₀ * (N : ℝ)
          + A₀ * (N : ℝ) + 2 := by
    rw [hn₂def]; push_cast
    refine max_le ?_ ?_
    · nlinarith [hmax1, hK0, hA₀, hN1]
    · have h : ((⌈(Work.Prop36SW.ambK D d c) * ((H : ℝ) + 1) ^ d⌉₊ : ℕ) : ℝ)
          ≤ (Work.Prop36SW.ambK D d c) * ((H : ℝ) + 1) ^ d + 1 :=
        le_of_lt (Nat.ceil_lt_add_one (mul_nonneg hK0 hX0))
      nlinarith [h, hXA]
  have hfinal6 : (n₂ : ℝ) ≤ Cw * (N : ℝ) := by
    rw [hCwdef]; nlinarith [hmax2, hN1, hbR]
  refine ⟨n₀, n₂, ?_, ?_, ?_, ?_, ?_, hfinal6, ?_⟩
  · rw [hn₀def]; exact le_max_left _ _
  · rw [hn₂def]; exact le_max_left _ _
  · have h3a : ((H : ℝ) + 1) ^ 2 ≤ (⌈((H : ℝ) + 1) ^ 2⌉₊ : ℝ) := Nat.le_ceil _
    have h3b : (⌈((H : ℝ) + 1) ^ 2⌉₊ : ℝ) ≤ (n₀ : ℝ) := by
      have h : ⌈((H : ℝ) + 1) ^ 2⌉₊ ≤ n₀ := by
        rw [hn₀def]; exact le_trans (le_max_left _ _) (le_max_right _ _)
      exact_mod_cast h
    linarith
  · have h4a : (b : ℝ) * ((H : ℝ) + 1) ^ d ≤ (⌈(b : ℝ) * ((H : ℝ) + 1) ^ d⌉₊ : ℝ) :=
      Nat.le_ceil _
    have h4b : (⌈(b : ℝ) * ((H : ℝ) + 1) ^ d⌉₊ : ℝ) ≤ (n₀ : ℝ) := by
      have h : ⌈(b : ℝ) * ((H : ℝ) + 1) ^ d⌉₊ ≤ n₀ := by
        rw [hn₀def]; exact le_trans (le_max_right _ _) (le_max_right _ _)
      exact_mod_cast h
    have h4c : ((b * ((H : ℤ) + 1) ^ d : ℤ) : ℝ) ≤ (n₀ : ℝ) := by
      have hcast : ((b * ((H : ℤ) + 1) ^ d : ℤ) : ℝ) = (b : ℝ) * ((H : ℝ) + 1) ^ d := by
        push_cast; ring
      rw [hcast]; linarith
    exact_mod_cast h4c
  · have h5a : Work.Prop36SW.ambK D d c * ((H : ℝ) + 1) ^ d
        ≤ (⌈(Work.Prop36SW.ambK D d c) * ((H : ℝ) + 1) ^ d⌉₊ : ℝ) := Nat.le_ceil _
    have h5b : (⌈(Work.Prop36SW.ambK D d c) * ((H : ℝ) + 1) ^ d⌉₊ : ℝ) ≤ (n₂ : ℝ) := by
      have h : ⌈(Work.Prop36SW.ambK D d c) * ((H : ℝ) + 1) ^ d⌉₊ ≤ n₂ := by
        rw [hn₂def]; exact le_max_right _ _
      exact_mod_cast h
    linarith
  · have hcard2 : ((Work.Peluse.symIcc n₂).card : ℝ)
        ≤ (2 * Cw + 1) * ((Work.Peluse.symIcc N).card : ℝ) := by
      rw [Work.Peluse.P1Aux.card_symIcc n₂, Work.Peluse.P1Aux.card_symIcc N]
      nlinarith [hfinal6, hCwpos, hN1]
    have hRHS : ((((Work.Peluse.symIcc N).card : ℝ) / ((Work.Peluse.symIcc n₀).card : ℝ)) * η
          / (2 : ℝ) ^ s)
        * (((Work.Peluse.symIcc n₀).card : ℝ) / ((Work.Peluse.symIcc n₂).card : ℝ))
        = ((Work.Peluse.symIcc N).card : ℝ) * η
            / ((2 : ℝ) ^ s * ((Work.Peluse.symIcc n₂).card : ℝ)) := by
      have hb0 : ((Work.Peluse.symIcc n₀).card : ℝ) ≠ 0 := by
        rw [Work.Peluse.P1Aux.card_symIcc]; positivity
      have hc2 : ((Work.Peluse.symIcc n₂).card : ℝ) ≠ 0 := by
        rw [Work.Peluse.P1Aux.card_symIcc]; positivity
      have h2s : ((2 : ℝ) ^ s) ≠ 0 := by positivity
      field_simp
    rw [hRHS, inv_mul_eq_div]
    have h1 : 0 < ((2 : ℝ) ^ s) * (2 * Cw + 1) := mul_pos (by positivity) (by linarith)
    have h2 : 0 < ((2 : ℝ) ^ s) * ((Work.Peluse.symIcc n₂).card : ℝ) := by
      refine mul_pos (by positivity) ?_
      rw [Work.Peluse.P1Aux.card_symIcc]; positivity
    rw [div_le_iff₀ h1, div_mul_eq_mul_div, le_div_iff₀ h2]
    have hmul := mul_le_mul_of_nonneg_right hcard2 (show (0 : ℝ) ≤ η * (2 : ℝ) ^ s by positivity)
    nlinarith [hmul]

end Work.Prop36SW
