import Mathlib
import Submission.Work.BMF.Defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.SD

/-- Counting lemma: the number of multiples of `p` in the natural interval `[A, B]` is at
most `(B - A) / p + 1`. -/
theorem card_filter_dvd_Icc_le (p A B : ℕ) (hp : 0 < p) :
    ((Finset.Icc A B).filter (fun m => p ∣ m)).card ≤ (B - A) / p + 1 := by
  have hmap : Set.MapsTo (fun m => (m - A) / p)
      ↑((Finset.Icc A B).filter (fun m => p ∣ m)) ↑(Finset.range ((B - A) / p + 1)) := by
    intro m hm
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc, Finset.mem_range] at hm ⊢
    obtain ⟨⟨_, hmB⟩, _⟩ := hm
    calc (m - A) / p ≤ (B - A) / p := Nat.div_le_div_right (Nat.sub_le_sub_right hmB A)
      _ < (B - A) / p + 1 := Nat.lt_succ_self _
  have hinj : Set.InjOn (fun m => (m - A) / p)
      ↑((Finset.Icc A B).filter (fun m => p ∣ m)) := by
    intro m₁ hm₁ m₂ hm₂ heq
    simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_Icc] at hm₁ hm₂
    obtain ⟨⟨hm2A, _⟩, hd2⟩ := hm₂
    obtain ⟨⟨hm1A, _⟩, hd1⟩ := hm₁
    have key : ∀ x y : ℕ, A ≤ y → y ≤ x → p ∣ x → p ∣ y →
        (x - A) / p = (y - A) / p → x = y := by
      intro x y hyA hyx hdx hdy heqxy
      have hsub : x - y = (x - A) - (y - A) := by omega
      have hlow : p * ((y - A) / p) ≤ y - A := by
        rw [mul_comm]; exact Nat.div_mul_le_self _ _
      have hup : x - A ≤ p * ((x - A) / p) + (p - 1) :=
        (Nat.div_le_iff_le_mul_add_pred (b := p) (a := x - A) (c := (x - A) / p) hp).mp le_rfl
      have hle : x - y ≤ p - 1 := by
        rw [hsub]
        calc (x - A) - (y - A)
            ≤ (p * ((x - A) / p) + (p - 1)) - (y - A) := Nat.sub_le_sub_right hup _
          _ ≤ (p * ((x - A) / p) + (p - 1)) - p * ((y - A) / p) :=
                Nat.sub_le_sub_left hlow _
          _ = p - 1 := by rw [heqxy]; omega
      have hdvd : p ∣ x - y := Nat.dvd_sub hdx hdy
      have hzero : x - y = 0 := by
        by_contra hne
        have hpos : 0 < x - y := Nat.pos_of_ne_zero hne
        have := Nat.le_of_dvd hpos hdvd
        omega
      omega
    rcases le_total m₂ m₁ with h | h
    · exact key m₁ m₂ hm2A h hd1 hd2 heq
    · exact (key m₂ m₁ hm1A h hd2 hd1 heq.symm).symm
  have hcard := Finset.card_le_card_of_injOn (fun m => (m - A) / p) hmap hinj
  calc ((Finset.Icc A B).filter (fun m => p ∣ m)).card
      ≤ (Finset.range ((B - A) / p + 1)).card := hcard
    _ = (B - A) / p + 1 := Finset.card_range _

theorem multiples_card_le (p : ℕ) (a b : ℝ) (hp : 0 < p) (hab : a ≤ b) :
    (((Work.BMF.natIcc a b).filter (fun m => p ∣ m)).card : ℝ) ≤ (b - a) / (p : ℝ) + 2 := by
  have hpR : (0 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hnat : Work.BMF.natIcc a b = Finset.Icc ⌈a⌉₊ ⌊b⌋₊ := rfl
  have hba : 0 ≤ b - a := by linarith
  rcases le_or_gt ⌈a⌉₊ ⌊b⌋₊ with hAB | hAB
  · have hkey := card_filter_dvd_Icc_le p ⌈a⌉₊ ⌊b⌋₊ hp
    have hcast : (((Finset.Icc ⌈a⌉₊ ⌊b⌋₊).filter (fun m => p ∣ m)).card : ℝ)
        ≤ (((⌊b⌋₊ - ⌈a⌉₊) / p : ℕ) : ℝ) + 1 := by
      exact_mod_cast hkey
    have h1 : (((⌊b⌋₊ - ⌈a⌉₊) / p : ℕ) : ℝ)
        ≤ ((⌊b⌋₊ : ℝ) - (⌈a⌉₊ : ℝ)) / (p : ℝ) := by
      have hc : (((⌊b⌋₊ - ⌈a⌉₊) / p : ℕ) : ℝ)
          ≤ (((⌊b⌋₊ - ⌈a⌉₊ : ℕ)) : ℝ) / (p : ℝ) := Nat.cast_div_le
      rwa [Nat.cast_sub hAB] at hc
    have hBbound : (⌊b⌋₊ : ℝ) - (⌈a⌉₊ : ℝ) ≤ b - a + 1 := by
      rcases le_or_gt 0 b with hb | hb
      · have hBb : (⌊b⌋₊ : ℝ) ≤ b := Nat.floor_le hb
        have hAa : a ≤ (⌈a⌉₊ : ℝ) := Nat.le_ceil a
        linarith
      · have hB0 : ⌊b⌋₊ = 0 := Nat.floor_eq_zero.mpr (by linarith)
        have hA0 : ⌈a⌉₊ = 0 := by omega
        rw [hB0, hA0]
        push_cast
        linarith
    have hstep : ((⌊b⌋₊ : ℝ) - (⌈a⌉₊ : ℝ)) / (p : ℝ) + 1
        ≤ (b - a + 1) / (p : ℝ) + 1 := by
      have := div_le_div_of_nonneg_right hBbound (le_of_lt hpR)
      linarith
    have hsplit : (b - a + 1) / (p : ℝ) + 1 = (b - a) / (p : ℝ) + 1 / (p : ℝ) + 1 := by ring
    have hone : 1 / (p : ℝ) ≤ 1 := (div_le_one hpR).mpr (by exact_mod_cast hp)
    calc (((Work.BMF.natIcc a b).filter (fun m => p ∣ m)).card : ℝ)
        = (((Finset.Icc ⌈a⌉₊ ⌊b⌋₊).filter (fun m => p ∣ m)).card : ℝ) := by rw [hnat]
      _ ≤ (((⌊b⌋₊ - ⌈a⌉₊) / p : ℕ) : ℝ) + 1 := hcast
      _ ≤ ((⌊b⌋₊ : ℝ) - (⌈a⌉₊ : ℝ)) / (p : ℝ) + 1 := by linarith
      _ ≤ (b - a + 1) / (p : ℝ) + 1 := hstep
      _ = (b - a) / (p : ℝ) + 1 / (p : ℝ) + 1 := hsplit
      _ ≤ (b - a) / (p : ℝ) + 2 := by linarith
  · have hkey := card_filter_dvd_Icc_le p ⌈a⌉₊ ⌊b⌋₊ hp
    have hzero : (⌊b⌋₊ - ⌈a⌉₊) / p + 1 = 1 := by
      have : ⌊b⌋₊ - ⌈a⌉₊ = 0 := by omega
      simp [this]
    have hle1 : (((Finset.Icc ⌈a⌉₊ ⌊b⌋₊).filter (fun m => p ∣ m)).card : ℝ) ≤ 1 := by
      have h := hkey
      rw [hzero] at h
      exact_mod_cast h
    have hnn : 0 ≤ (b - a) / (p : ℝ) := div_nonneg hba (le_of_lt hpR)
    calc (((Work.BMF.natIcc a b).filter (fun m => p ∣ m)).card : ℝ)
        = (((Finset.Icc ⌈a⌉₊ ⌊b⌋₊).filter (fun m => p ∣ m)).card : ℝ) := by rw [hnat]
      _ ≤ 1 := hle1
      _ ≤ (b - a) / (p : ℝ) + 2 := by linarith

end Work.BMF.SD
