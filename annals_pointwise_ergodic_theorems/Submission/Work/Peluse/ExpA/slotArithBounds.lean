import Mathlib
import Submission.Work.Peluse.ExpA.Defs

/-!
# The arithmetic bounds on the slot data of Lemma 4.10

This module proves the four elementary bounds that the slot family of Lemma 4.10 satisfies on the
arithmetic data of the expansion step (`Work.Peluse.ExpA`):

* `|dotB ω b u| ≤ s·C₀·N` — the corner constants `S_ω = ∑_{ω j} u j · b j` are bounded by the
  window `N` (from `|b i| ≤ C₀·N/M₁` and `|u j| ≤ M₁`);
* `|dotU ω u| ≤ s·M₁` — the corner directions `D_ω = ∑_{ω j} u j`;
* `|cSlot s c u j · y| ≤ winN s C₀ N` for `y ∈ [1, M₂]`, using `c·M₁·M₂ ≤ N`;
* the slot functions `slotFn s b u f j` are supported in the enlarged window `winN s C₀ N`, since
  the `b`-shifts are bounded by `s·C₀·N` and `winN s C₀ N ≥ N + s·C₀·N`.
-/

open scoped BigOperators

namespace Work.Peluse.ExpA

theorem slotArithBounds {s : ℕ} {C₀ M₁ M₂ N : ℕ} {c : ℤ} (hc : 0 < c) (b u : Fin s → ℤ)
    (hM₁ : 1 ≤ M₁) (hcM : c * (M₁ : ℤ) * (M₂ : ℤ) ≤ (N : ℤ))
    (hb : ∀ i : Fin s, |b i| ≤ (C₀ : ℤ) * (N : ℤ) / (M₁ : ℤ))
    (hu : ∀ j : Fin s, |u j| ≤ (M₁ : ℤ)) {f : ℤ → ℂ} (hsup : Work.Peluse.SupportIn f N) :
    (∀ ω : Fin s → Bool, |Work.Peluse.ExpA.dotB ω b u| ≤ (s : ℤ) * (C₀ : ℤ) * (N : ℤ)) ∧
    (∀ ω : Fin s → Bool, |Work.Peluse.ExpA.dotU ω u| ≤ (s : ℤ) * (M₁ : ℤ)) ∧
    (∀ j : Fin (2 ^ s - 1 + 1), ∀ y ∈ Finset.Icc 1 M₂,
      |Work.Peluse.ExpA.cSlot s c u j * (y : ℤ)| ≤ (Work.Peluse.ExpA.winN s C₀ N : ℤ)) ∧
    (∀ j : Fin (2 ^ s - 1 + 1),
      Work.Peluse.SupportIn (Work.Peluse.ExpA.slotFn s b u f j) (Work.Peluse.ExpA.winN s C₀ N)) := by
  have hM1pos : (0 : ℤ) < (M₁ : ℤ) := by exact_mod_cast hM₁
  have hM1nn : (0 : ℤ) ≤ (M₁ : ℤ) := le_of_lt hM1pos
  have hC0nn : (0 : ℤ) ≤ (C₀ : ℤ) := by exact_mod_cast Nat.zero_le C₀
  have hNnn : (0 : ℤ) ≤ (N : ℤ) := by exact_mod_cast Nat.zero_le N
  have hsnn : (0 : ℤ) ≤ (s : ℤ) := by exact_mod_cast Nat.zero_le s
  -- (1) The corner constants `S_ω = ∑_{ω j} u j · b j` are bounded by `s·C₀·N`.
  have hB : ∀ ω : Fin s → Bool, |dotB ω b u| ≤ (s : ℤ) * (C₀ : ℤ) * (N : ℤ) := by
    intro ω
    have hterm : ∀ j : Fin s, |(if ω j then u j else 0) * b j| ≤ (C₀ : ℤ) * (N : ℤ) := by
      intro j
      have hb1 : |b j| * (M₁ : ℤ) ≤ (C₀ : ℤ) * (N : ℤ) :=
        (Int.le_ediv_iff_mul_le hM1pos).mp (hb j)
      by_cases h : ω j
      · rw [if_pos h, abs_mul]
        calc |u j| * |b j| ≤ (M₁ : ℤ) * |b j| :=
              mul_le_mul_of_nonneg_right (hu j) (abs_nonneg _)
          _ = |b j| * (M₁ : ℤ) := by ring
          _ ≤ (C₀ : ℤ) * (N : ℤ) := hb1
      · rw [if_neg h, zero_mul, abs_zero]
        exact mul_nonneg hC0nn hNnn
    calc |dotB ω b u| = |∑ j : Fin s, (if ω j then u j else 0) * b j| := rfl
      _ ≤ ∑ j : Fin s, |(if ω j then u j else 0) * b j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j : Fin s, (C₀ : ℤ) * (N : ℤ) := Finset.sum_le_sum (fun j _ => hterm j)
      _ = (s : ℤ) * ((C₀ : ℤ) * (N : ℤ)) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      _ = (s : ℤ) * (C₀ : ℤ) * (N : ℤ) := by ring
  -- (2) The corner directions `D_ω = ∑_{ω j} u j` are bounded by `s·M₁`.
  have hU : ∀ ω : Fin s → Bool, |dotU ω u| ≤ (s : ℤ) * (M₁ : ℤ) := by
    intro ω
    calc |dotU ω u| = |∑ j : Fin s, (if ω j then u j else 0)| := rfl
      _ ≤ ∑ j : Fin s, |(if ω j then u j else 0)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ _j : Fin s, (M₁ : ℤ) := by
            refine Finset.sum_le_sum (fun j _ => ?_)
            by_cases h : ω j
            · rw [if_pos h]; exact hu j
            · rw [if_neg h, abs_zero]; exact hM1nn
      _ = (s : ℤ) * (M₁ : ℤ) := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  refine ⟨hB, hU, ?_, ?_⟩
  -- (3) The slot shifts: `|cSlot j · y| ≤ s·N ≤ winN` for `y ∈ [1, M₂]`.
  · intro j y hy
    obtain ⟨_, hy2⟩ := Finset.mem_Icc.mp hy
    have hy0 : (0 : ℤ) ≤ (y : ℤ) := by exact_mod_cast (Nat.zero_le y)
    have hyM : (y : ℤ) ≤ (M₂ : ℤ) := by exact_mod_cast hy2
    have hD := hU (slotIdx s j)
    have hcy : c * (s : ℤ) * (M₁ : ℤ) * (M₂ : ℤ) ≤ (s : ℤ) * (N : ℤ) := by
      nlinarith [hcM, hsnn, le_of_lt hc]
    calc |cSlot s c u j * (y : ℤ)| = |c| * |dotU (slotIdx s j) u| * |(y : ℤ)| := by
          rw [cSlot]; simp only [abs_mul]
      _ ≤ c * ((s : ℤ) * (M₁ : ℤ)) * (M₂ : ℤ) := by
          rw [abs_of_pos hc, abs_of_nonneg hy0]
          exact mul_le_mul (mul_le_mul_of_nonneg_left hD (le_of_lt hc)) hyM hy0
            (by positivity)
      _ ≤ (s : ℤ) * (N : ℤ) := by linarith
      _ ≤ (winN s C₀ N : ℤ) := by exact_mod_cast s_mul_le_winN s C₀ N
  -- (4) The slot functions are supported in the enlarged window.
  · intro j x hx
    rw [slotFn]
    simp only [Function.comp_apply, Work.Peluse.shift]
    have hbnd := hB (slotIdx s j)
    have hxabs : ((winN s C₀ N : ℕ) : ℤ) < (x.natAbs : ℤ) := by exact_mod_cast hx
    rw [Int.natCast_natAbs] at hxabs
    have hwin : ((1 + s * C₀) * N : ℤ) ≤ (winN s C₀ N : ℤ) := by
      have h1 : (1 + s * C₀) * N ≤ winN s C₀ N := by
        have := add_mul_le_winN s C₀ N
        calc (1 + s * C₀) * N = N + s * C₀ * N := by ring
          _ ≤ winN s C₀ N := this
      exact_mod_cast h1
    have htri : |x| - |dotB (slotIdx s j) b u| ≤ |x + dotB (slotIdx s j) b u| := by
      have h := abs_add_le (x + dotB (slotIdx s j) b u) (-(dotB (slotIdx s j) b u))
      rw [add_neg_cancel_right, abs_neg] at h
      linarith
    have hlt : (N : ℤ) < |x + dotB (slotIdx s j) b u| := by
      nlinarith [hbnd, htri, hxabs, hwin]
    have hlt' : N < (x + dotB (slotIdx s j) b u).natAbs := by
      have : (N : ℤ) < ((x + dotB (slotIdx s j) b u).natAbs : ℤ) := by
        rw [Int.natCast_natAbs]; exact hlt
      exact_mod_cast this
    rw [hsup _ hlt']
    simp

end Work.Peluse.ExpA
