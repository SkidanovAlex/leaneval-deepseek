import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.SD

/-- If two naturals `a < b` lie in the same integer block `[ks, (k+1)s)` (equivalently have the
same quotient by `s > 0`), then `b - a < s`. -/
lemma sub_lt_of_div_eq {a b s : ℕ} (hs : 0 < s) (h : a / s = b / s) (hab : a < b) :
    b - a < s := by
  have h1 : (b / s) * s ≤ a := by rw [← h]; exact Nat.div_mul_le_self a s
  have h2 : b < (b / s + 1) * s :=
    (Nat.div_lt_iff_lt_mul (k := s) (x := b) (y := b / s + 1) hs).mp (Nat.lt_succ_self _)
  have h2' : b < (b / s) * s + s := by
    rw [Nat.add_mul, Nat.one_mul] at h2; exact h2
  omega

/-- Pigeonhole: a finite set `A ⊆ {0, …, L}` with more than `L / s + 1` elements contains two
distinct elements lying in the same integer block of length `s`. -/
lemma exists_pair_same_div {A : Finset ℕ} {L s : ℕ} (hs : 0 < s)
    (hA : ∀ a ∈ A, a ≤ L) (hcard : L / s + 1 < A.card) :
    ∃ a ∈ A, ∃ b ∈ A, a < b ∧ b - a < s := by
  have hlt : (Finset.Icc 0 (L / s)).card < A.card := by
    rw [Nat.card_Icc]; omega
  obtain ⟨a, ha, b, hb, hne, hfeq⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hlt
      (f := fun d => d / s) (fun d hd =>
        Finset.mem_coe.mpr (Finset.mem_Icc.mpr
          ⟨Nat.zero_le _, Nat.div_le_div_right (hA d hd)⟩))
  rcases lt_or_gt_of_ne hne with hab | hba
  · exact ⟨a, ha, b, hb, hab, sub_lt_of_div_eq hs hfeq hab⟩
  · exact ⟨b, hb, a, ha, hba, sub_lt_of_div_eq hs hfeq.symm hba⟩

theorem small_multiple {L : ℕ} {δ ε β : ℝ} {D : Finset ℕ}
    (hL : 1 ≤ L) (hδ : 0 < δ) (hε : 0 < ε)
    (hD1 : ∀ d ∈ D, 1 ≤ d) (hD2 : ∀ d ∈ D, d ≤ L)
    (hcard : δ * (L:ℝ) ≤ (D.card : ℝ))
    (hgood : ∀ d ∈ D, ∃ m : ℤ, |β * (d:ℝ) - m| ≤ ε) :
    ∃ q : ℕ, 1 ≤ q ∧ (q:ℝ) ≤ 4 / δ ∧ ∃ m : ℤ, |(q:ℝ) * β - m| ≤ 2 * ε := by
  by_cases hbig : (4:ℝ)/3 < δ * (L:ℝ)
  · -- Density is large: pigeonhole forces two elements of `D` in a short block,
    -- and their difference is the desired small `q`.
    set s : ℕ := ⌈(4/δ : ℝ)⌉₊ with hs_def
    have hs_pos : 0 < s := by
      rw [hs_def]; exact Nat.ceil_pos.mpr (div_pos (by norm_num) hδ)
    have hs_ge : (4:ℝ)/δ ≤ (s:ℝ) := by rw [hs_def]; exact Nat.le_ceil _
    have hs_lt : (s:ℝ) < (4:ℝ)/δ + 1 := by
      rw [hs_def]; exact Nat.ceil_lt_add_one (le_of_lt (div_pos (by norm_num) hδ))
    have hcount_real : ((L / s + 1 : ℕ) : ℝ) < (D.card : ℝ) := by
      have h1 : ((L / s : ℕ) : ℝ) ≤ (L:ℝ)/s := Nat.cast_div_le
      have h4 : (0:ℝ) < (4:ℝ)/δ := div_pos (by norm_num) hδ
      have h2 : (L:ℝ)/s ≤ (L:ℝ)/((4:ℝ)/δ) :=
        div_le_div_of_nonneg_left (by positivity : (0:ℝ) ≤ (L:ℝ)) h4 hs_ge
      have h3 : (L:ℝ)/((4:ℝ)/δ) = δ * (L:ℝ) / 4 := by
        rw [div_div_eq_mul_div]; ring
      rw [Nat.cast_add, Nat.cast_one]
      have hgt : δ * (L:ℝ) / 4 + 1 < δ * (L:ℝ) := by linarith [hbig]
      linarith [h1, h2, h3, hgt, hcard]
    have hcount : L / s + 1 < D.card := Nat.cast_lt.mp hcount_real
    obtain ⟨a, ha, b, hb, hab, hbasub⟩ :=
      exists_pair_same_div hs_pos (fun d hd => hD2 d hd) hcount
    have hqpos : 1 ≤ b - a := by omega
    have hqle : ((b - a : ℕ) : ℝ) ≤ 4 / δ := by
      have hle : b - a ≤ s - 1 := by omega
      have hcast : ((b - a : ℕ) : ℝ) ≤ (s : ℝ) - 1 := by
        calc ((b - a : ℕ) : ℝ) ≤ ((s - 1 : ℕ) : ℝ) := by exact_mod_cast hle
          _ = (s : ℝ) - 1 := by rw [Nat.cast_sub (by omega : 1 ≤ s), Nat.cast_one]
      have : ((b - a : ℕ) : ℝ) < 4 / δ := by linarith [hcast, hs_lt]
      exact le_of_lt this
    obtain ⟨ma, hma⟩ := hgood a ha
    obtain ⟨mb, hmb⟩ := hgood b hb
    refine ⟨b - a, hqpos, hqle, mb - ma, ?_⟩
    have hsub : ((b - a : ℕ) : ℝ) = (b:ℝ) - (a:ℝ) := by
      rw [Nat.cast_sub (le_of_lt hab)]
    rw [hsub]
    have hma' : |(a:ℝ) * β - (ma:ℝ)| ≤ ε := by simpa [mul_comm] using hma
    have hmb' : |(b:ℝ) * β - (mb:ℝ)| ≤ ε := by simpa [mul_comm] using hmb
    have key : ((b:ℝ) - (a:ℝ)) * β - ((mb - ma : ℤ) : ℝ)
        = ((b:ℝ) * β - (mb:ℝ)) - ((a:ℝ) * β - (ma:ℝ)) := by
      push_cast; ring
    rw [key]
    calc |((b:ℝ) * β - (mb:ℝ)) - ((a:ℝ) * β - (ma:ℝ))|
        ≤ |(b:ℝ) * β - (mb:ℝ)| + |(a:ℝ) * β - (ma:ℝ)| := by
          have h := abs_add_le ((b:ℝ) * β - (mb:ℝ)) (-((a:ℝ) * β - (ma:ℝ)))
          rw [abs_neg] at h
          simpa [sub_eq_add_neg] using h
      _ ≤ ε + ε := add_le_add hmb' hma'
      _ = 2 * ε := by ring
  · -- Density is small: then `L < 4/δ`, so any single element `d ∈ D` gives `q = d`.
    have hDLpos : (0:ℝ) < (D.card : ℝ) := by
      have : (0:ℝ) < δ * (L:ℝ) := mul_pos hδ (by exact_mod_cast (by omega : 0 < L))
      linarith [hcard]
    have hDpos : 0 < D.card := by exact_mod_cast hDLpos
    obtain ⟨d, hd⟩ := Finset.card_pos.mp hDpos
    obtain ⟨m, hm⟩ := hgood d hd
    refine ⟨d, hD1 d hd, ?_, m, ?_⟩
    · have hdL : (d:ℝ) ≤ (L:ℝ) := by exact_mod_cast hD2 d hd
      have hLle : (L:ℝ) ≤ 4 / δ := by
        have h1 : (L:ℝ) ≤ 4 / (3 * δ) := by
          rw [le_div_iff₀ (by positivity : (0:ℝ) < 3 * δ)]
          nlinarith [not_lt.mp hbig]
        have h2 : (4:ℝ) / (3 * δ) ≤ 4 / δ :=
          div_le_div_of_nonneg_left (by norm_num) hδ (by linarith)
        linarith [h1, h2]
      linarith [hdL, hLle]
    · have hm' : |(d:ℝ) * β - m| ≤ ε := by simpa [mul_comm] using hm
      linarith [hm', hε]

end Work.BMF.SD
