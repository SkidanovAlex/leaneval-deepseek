import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Int.Star

namespace Commons.Analysis.Harmonic

open Finset Real

/-- For a strictly increasing map `f : Fin n → ℤ`, `f i ≥ f 0 + i` (consecutive integers differ
by at least `1`). -/
lemma fin_int_le_of_strictMono {n : ℕ} {f : Fin n → ℤ} (hf : StrictMono f) {b : Fin n}
    (hb : (b : ℕ) = 0) (i : Fin n) : f b + ((i : ℕ) : ℤ) ≤ f i := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (ne_of_gt (Fin.pos_iff_nonempty.mpr ⟨b⟩))
  induction i using Fin.induction with
  | zero =>
      have : b = 0 := Fin.ext (by simpa using hb)
      rw [this]; simp
  | succ j ih =>
      have h1 : f j.castSucc + 1 ≤ f j.succ :=
        Int.lt_iff_add_one_le.mp (hf (Fin.castSucc_lt_succ (i := j)))
      have h2 : ((j.succ : Fin (m+1)) : ℕ) = ((j.castSucc : Fin (m+1)) : ℕ) + 1 := by
        simp [Fin.val_succ, Fin.val_castSucc]
      rw [h2]
      push_cast
      linarith

/-- Sum of `1/(k - x)^2` over a finite set of integers `k` with `k - x ≥ D > 0`, bounded by
`2/D^2 + 2/D`. -/
lemma sum_inv_sq_sub_le {s : Finset ℤ} {x D : ℝ} (hD : 0 < D)
    (hlo : ∀ k ∈ s, D ≤ (k : ℝ) - x) :
    (∑ k ∈ s, 1 / ((k : ℝ) - x) ^ 2) ≤ 2 / D ^ 2 + 2 / D := by
  rcases s.eq_empty_or_nonempty with hs | ⟨k0, hk0⟩
  · rw [hs]; simp
    positivity
  · have hcard : 0 < s.card := Finset.card_pos.mpr ⟨k0, hk0⟩
    -- enumerate the (distinct) integers of `s` increasingly
    have hsum : (∑ k ∈ s, 1 / ((k : ℝ) - x) ^ 2)
        = ∑ i : Fin s.card, 1 / ((s.orderEmbOfFin rfl i : ℝ) - x) ^ 2 := by
      conv_lhs => rw [← Finset.image_orderEmbOfFin_univ s rfl]
      rw [Finset.sum_image]
      exact fun a _ b _ hab => (s.orderEmbOfFin rfl).injective hab
    rw [hsum]
    set c : ℝ := 1 + 1 / D with hc_def
    have hcpos : 0 < c := by rw [hc_def]; positivity
    -- the `i`-th smallest shift `k - x` is at least `D + i`
    have hbnd : ∀ i : Fin s.card,
        1 / ((s.orderEmbOfFin rfl i : ℝ) - x) ^ 2 ≤ 1 / (D + (i : ℝ)) ^ 2 := by
      intro i
      have hbmem : s.orderEmbOfFin rfl (⟨0, hcard⟩ : Fin s.card) ∈ s :=
        Finset.orderEmbOfFin_mem s rfl _
      have hb0 : D ≤ (s.orderEmbOfFin rfl (⟨0, hcard⟩ : Fin s.card) : ℝ) - x := hlo _ hbmem
      have hmono := fin_int_le_of_strictMono (s.orderEmbOfFin rfl).strictMono
        (b := (⟨0, hcard⟩ : Fin s.card)) (by simp) i
      have hmonoR : ((s.orderEmbOfFin rfl (⟨0, hcard⟩ : Fin s.card) : ℤ) : ℝ) + (i : ℝ)
          ≤ ((s.orderEmbOfFin rfl i : ℤ) : ℝ) := by exact_mod_cast hmono
      have hge : D + (i : ℝ) ≤ ((s.orderEmbOfFin rfl i : ℤ) : ℝ) - x := by linarith
      have hpos : 0 < D + (i : ℝ) := by positivity
      have hsq : (D + (i : ℝ)) ^ 2 ≤ (((s.orderEmbOfFin rfl i : ℤ) : ℝ) - x) ^ 2 :=
        pow_le_pow_left₀ (le_of_lt hpos) hge 2
      exact div_le_div_of_nonneg_left (by norm_num) (by positivity) hsq
    -- telescoping bound `1/a^2 ≤ c (1/a - 1/(a+1))` with `c = 1 + 1/D`, valid for `a ≥ D`
    have htel : ∀ i ∈ Finset.range s.card,
        1 / (D + (i : ℝ)) ^ 2
          ≤ c * (1 / (D + (i : ℝ)) - 1 / (D + ((i + 1 : ℕ) : ℝ))) := by
      intro i _
      have ha : 0 < D + (i : ℝ) := by positivity
      have hi : (0:ℝ) ≤ (i : ℝ) := by positivity
      have hle : D ≤ D + (i : ℝ) := by linarith
      have hkey : (D + (i : ℝ)) + 1 ≤ c * (D + (i : ℝ)) := by
        have hca : (1:ℝ) ≤ (D + (i : ℝ)) / D := by
          rw [le_div_iff₀ hD]; linarith
        have : c * (D + (i : ℝ)) = (D + (i : ℝ)) + (D + (i : ℝ)) / D := by
          rw [hc_def]; ring
        rw [this]; linarith
      have hsub : 1 / (D + (i : ℝ)) - 1 / (D + ((i+1:ℕ):ℝ))
          = 1 / ((D + (i : ℝ)) * ((D + (i : ℝ)) + 1)) := by
        have ha' : D + (i : ℝ) ≠ 0 := ne_of_gt ha
        have hd' : D + ((i+1:ℕ):ℝ) ≠ 0 := by positivity
        rw [div_sub_div _ _ ha' hd']
        push_cast
        ring_nf
      rw [hsub, mul_one_div, div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [hkey, ha]
    calc ∑ i : Fin s.card, 1 / ((s.orderEmbOfFin rfl i : ℝ) - x) ^ 2
        ≤ ∑ i : Fin s.card, 1 / (D + (i : ℝ)) ^ 2 := Finset.sum_le_sum (fun i _ => hbnd i)
      _ ≤ ∑ i ∈ Finset.range s.card,
            c * (1 / (D + (i : ℝ)) - 1 / (D + ((i + 1 : ℕ) : ℝ))) := by
          rw [Fin.sum_univ_eq_sum_range (fun j => 1 / (D + (j : ℝ)) ^ 2)]
          exact Finset.sum_le_sum htel
      _ = c * (1 / D - 1 / (D + (s.card : ℝ))) := by
          rw [← Finset.mul_sum, Finset.sum_range_sub' (fun j : ℕ => 1 / (D + (j : ℝ))) s.card]
          rw [Nat.cast_zero, add_zero]
      _ ≤ 2 / D ^ 2 + 2 / D := by
          have h1 : c * (1 / D - 1 / (D + (s.card : ℝ))) ≤ c * (1 / D) := by
            apply mul_le_mul_of_nonneg_left _ (le_of_lt hcpos)
            have hpos : 0 < D + (s.card : ℝ) := by positivity
            have := one_div_pos.mpr hpos
            linarith
          have h2 : c * (1 / D) ≤ 2 / D ^ 2 + 2 / D := by
            have hu : (0:ℝ) < 1 / D := by positivity
            have heq1 : c * (1 / D) = (1 / D) + (1 / D) ^ 2 := by rw [hc_def]; ring
            have heq2 : 2 / D ^ 2 + 2 / D = 2 * (1 / D) ^ 2 + 2 * (1 / D) := by
              field_simp
            rw [heq1, heq2]
            nlinarith [sq_nonneg (1 / D), hu]
          linarith

end Commons.Analysis.Harmonic