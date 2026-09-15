import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Data.Nat.Cast.Order.Field
import Mathlib.Data.Nat.SuccPred
import Mathlib.Order.Lattice.Nat

namespace Commons.Data.Nat

theorem card_pair_bounds_le (a b L : ℕ) (hmax : 0 < max a b) :
    (((Finset.range (L + 1)).filter (fun n : ℕ => b ∣ a * n ∧ a * n ≤ L * b)).card : ℝ)
      ≤ (L : ℝ) * ((Nat.gcd a b : ℝ) / (max a b : ℝ)) + 1 := by
  by_cases ha0 : a = 0
  · -- a = 0
    have hbpos : 0 < b := by
      simpa [ha0] using hmax
    subst a
    have hS : (Finset.range (L + 1)).filter (fun n : ℕ => b ∣ 0 * n ∧ 0 * n ≤ L * b)
        = Finset.range (L + 1) := by
      apply Finset.filter_true_of_mem
      intro x hx
      simp
    have hcard : ((Finset.range (L + 1)).filter (fun n : ℕ => b ∣ 0 * n ∧ 0 * n ≤ L * b)).card = L + 1 := by
      rw [hS, Finset.card_range]
    rw [hcard]
    rw [Nat.gcd_zero_left]
    rw [← Nat.cast_max]
    rw [Nat.max_eq_right (Nat.zero_le b)]
    have hbℝ : (b : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hbpos)
    field_simp [hbℝ]
    norm_num
  · have hapos : 0 < a := Nat.pos_of_ne_zero ha0
    by_cases hb0 : b = 0
    · -- b = 0
      subst b
      have hpred : ∀ n : ℕ, (0 ∣ a * n ∧ a * n ≤ L * 0) ↔ n = 0 := by
        intro n
        constructor
        · intro h
          rcases h.1 with ⟨c, hc⟩
          have ha0' : a * n = 0 := by simpa using hc
          exact (Nat.mul_eq_zero.mp ha0').resolve_left (ne_of_gt hapos)
        · intro hn
          subst n
          simp
      have hf : (Finset.range (L + 1)).filter (fun n : ℕ => 0 ∣ a * n ∧ a * n ≤ L * 0)
          = (Finset.range (L + 1)).filter (fun n : ℕ => n = 0) := by
        apply Finset.filter_congr
        intro n hn
        exact hpred n
      have hcard' : ((Finset.range (L + 1)).filter (fun n : ℕ => n = 0)).card = 1 := by
        have hfs : (Finset.range (L + 1)).filter (fun n : ℕ => n = 0) = {0} := by
          ext x
          simp
        rw [hfs]
        simp
      rw [hf, hcard']
      rw [Nat.gcd_zero_right]
      rw [← Nat.cast_max]
      rw [Nat.max_eq_left (Nat.zero_le a)]
      have haℝ : (a : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hapos)
      field_simp [haℝ]
      norm_num
    · have hbpos : 0 < b := Nat.pos_of_ne_zero hb0
      -- main case: a > 0, b > 0
      let S : Finset ℕ := (Finset.range (L + 1)).filter (fun n => b ∣ a * n ∧ a * n ≤ L * b)
      let g : ℕ := Nat.gcd a b
      let a₁ : ℕ := a / g
      let b₁ : ℕ := b / g
      have hg : 0 < g := by simpa [g] using (Nat.gcd_pos_of_pos_left b hapos)
      have hgda : g ∣ a := by simpa [g] using (Nat.gcd_dvd_left a b)
      have hgdb : g ∣ b := by simpa [g] using (Nat.gcd_dvd_right a b)
      have ha_eq : g * a₁ = a := by
        simpa [a₁, g] using (Nat.mul_div_cancel' hgda)
      have hb_eq : g * b₁ = b := by
        simpa [b₁, g] using (Nat.mul_div_cancel' hgdb)
      have ha1pos : 0 < a₁ := by
        have hg_le : g ≤ a := Nat.le_of_dvd hapos hgda
        dsimp [a₁]
        exact Nat.div_pos hg_le hg
      have hcop : Nat.Coprime a₁ b₁ := by
        dsimp [a₁, b₁, g]
        exact Nat.coprime_div_gcd_div_gcd hg
      have heuclid : ∀ x : ℕ, b ∣ a * x → b₁ ∣ x := by
        intro x hbx
        have hred : b₁ ∣ a₁ * x := by
          rcases hbx with ⟨c, hc⟩
          refine ⟨c, ?_⟩
          have hc' : g * (a₁ * x) = g * (b₁ * c) := by
            calc
              g * (a₁ * x) = (g * a₁) * x := by ring
              _ = a * x := by rw [ha_eq]
              _ = b * c := hc
              _ = (g * b₁) * c := by rw [← hb_eq]
              _ = g * (b₁ * c) := by ring
          exact Nat.eq_of_mul_eq_mul_left hg hc'
        exact hcop.symm.dvd_of_dvd_mul_left hred
      have hmain_bound : ∀ x ∈ S, x / b₁ < L / max a₁ b₁ + 1 := by
        intro x hxS
        have hxmem : x ∈ Finset.range (L + 1) := (Finset.mem_filter.mp hxS).1
        have hxprop : b ∣ a * x ∧ a * x ≤ L * b := (Finset.mem_filter.mp hxS).2
        have hxdvd : b₁ ∣ x := heuclid x hxprop.1
        let t : ℕ := x / b₁
        have hxeq : x = b₁ * t := by
          dsimp [t]
          exact (Nat.mul_div_cancel' hxdvd).symm
        have hxleL : x ≤ L := Nat.le_of_lt_succ (Finset.mem_range.mp hxmem)
        have hb1t : b₁ * t ≤ L := by
          rw [← hxeq]
          exact hxleL
        have htb1 : t * b₁ ≤ L := by
          rw [Nat.mul_comm]
          exact hb1t
        have hax_eq : a * (b₁ * t) = (a₁ * t) * b := by
          rw [← ha_eq, ← hb_eq]
          ring
        have hata : a₁ * t ≤ L := by
          have hineq : (a₁ * t) * b ≤ L * b := by
            calc
              (a₁ * t) * b = a * (b₁ * t) := hax_eq.symm
              _ = a * x := by rw [← hxeq]
              _ ≤ L * b := hxprop.2
          exact Nat.le_of_mul_le_mul_right hineq hbpos
        have hta1 : t * a₁ ≤ L := by
          rw [Nat.mul_comm]
          exact hata
        have hDpos : 0 < max a₁ b₁ := lt_of_lt_of_le ha1pos (le_max_left a₁ b₁)
        have htD : t * max a₁ b₁ ≤ L := by
          have hmaxle : max (t * a₁) (t * b₁) ≤ L := max_le hta1 htb1
          have hmul : t * max a₁ b₁ = max (t * a₁) (t * b₁) := (max_mul_mul_left t a₁ b₁).symm
          rw [hmul]
          exact hmaxle
        have htle : t ≤ L / max a₁ b₁ := (Nat.le_div_iff_mul_le hDpos).2 htD
        exact Nat.lt_succ_of_le htle
      have hcard : S.card ≤ L / max a₁ b₁ + 1 := by
        have hinj : Set.InjOn (fun x : ℕ => x / b₁) (↑S : Set ℕ) := by
          intro x hx y hy h
          have hxdvd : b₁ ∣ x := heuclid x ((Finset.mem_filter.mp hx).2).1
          have hydvd : b₁ ∣ y := heuclid y ((Finset.mem_filter.mp hy).2).1
          change x / b₁ = y / b₁ at h
          calc
            x = b₁ * (x / b₁) := (Nat.mul_div_cancel' hxdvd).symm
            _ = b₁ * (y / b₁) := by rw [h]
            _ = y := Nat.mul_div_cancel' hydvd
        have hmaps : Set.MapsTo (fun x : ℕ => x / b₁) (↑S : Set ℕ)
            (↑(Finset.range (L / max a₁ b₁ + 1)) : Set ℕ) := by
          intro x hx
          change x / b₁ ∈ Finset.range (L / max a₁ b₁ + 1)
          exact Finset.mem_range.mpr (hmain_bound x hx)
        have hle : S.card ≤ (Finset.range (L / max a₁ b₁ + 1)).card := by
          exact Finset.card_le_card_of_injOn (fun x : ℕ => x / b₁) hmaps hinj
        simpa using hle
      have hcard_real : (S.card : ℝ) ≤ (L : ℝ) / (max a₁ b₁ : ℝ) + 1 := by
        have h1 : (S.card : ℝ) ≤ ((L / max a₁ b₁ : ℕ) : ℝ) + 1 := by
          have h1' : (S.card : ℝ) ≤ (((L / max a₁ b₁ + 1 : ℕ) : ℝ)) := by exact_mod_cast hcard
          simpa using h1'
        have h2 : ((L / max a₁ b₁ : ℕ) : ℝ) ≤ (L : ℝ) / (max a₁ b₁ : ℝ) := by
          rw [← Nat.cast_max]
          exact Nat.cast_div_le (α := ℝ) (m := L) (n := max a₁ b₁)
        nlinarith
      have hmax_eq : max a b = g * max a₁ b₁ := by
        calc
          max a b = max (g * a₁) (g * b₁) := by rw [← ha_eq, ← hb_eq]
          _ = g * max a₁ b₁ := max_mul_mul_left g a₁ b₁
      have hgℝ : (g : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hg)
      have hR : (L : ℝ) * ((g : ℝ) / (max a b : ℝ)) = (L : ℝ) / (max a₁ b₁ : ℝ) := by
        rw [← Nat.cast_max, ← Nat.cast_max]
        rw [hmax_eq]
        rw [Nat.cast_mul]
        field_simp [hgℝ]
      have hfin : (S.card : ℝ) ≤ (L : ℝ) * ((g : ℝ) / (max a b : ℝ)) + 1 := by
        rw [hR]
        exact hcard_real
      simpa [S, g] using hfin

end Commons.Data.Nat