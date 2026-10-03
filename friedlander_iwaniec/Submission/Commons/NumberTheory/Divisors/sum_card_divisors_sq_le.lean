import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.NumberTheory.Harmonic.Bounds

open scoped BigOperators

namespace Commons.NumberTheory.Divisors

theorem lcm_eq_gcd_mul_div_div (m n : ℕ) :
    m.lcm n = m.gcd n * (m / m.gcd n) * (n / m.gcd n) := by
  rcases Nat.eq_zero_or_pos (m.gcd n) with hg | hg
  · obtain ⟨hm, hn⟩ := Nat.gcd_eq_zero_iff.mp hg
    subst hm; subst hn; simp
  · have hgm : m.gcd n ∣ m := Nat.gcd_dvd_left m n
    have hgn : m.gcd n ∣ n := Nat.gcd_dvd_right m n
    have hmd : m.gcd n * (m / m.gcd n) = m := Nat.mul_div_cancel' hgm
    have hnd : m.gcd n * (n / m.gcd n) = n := Nat.mul_div_cancel' hgn
    apply Nat.mul_left_cancel hg
    rw [Nat.gcd_mul_lcm]
    calc m * n = (m.gcd n * (m / m.gcd n)) * (m.gcd n * (n / m.gcd n)) := by rw [hmd, hnd]
      _ = m.gcd n * (m.gcd n * (m / m.gcd n) * (n / m.gcd n)) := by ring

lemma card_divisors_sq_le_card_triples (x n : ℕ) (hn1 : 1 ≤ n) (hnx : n ≤ x) :
    n.divisors.card ^ 2
      ≤ (((Finset.Icc 1 x) ×ˢ ((Finset.Icc 1 x) ×ˢ (Finset.Icc 1 x))).filter
          (fun t : ℕ × ℕ × ℕ => t.1 * t.2.1 * t.2.2 ∣ n)).card := by
  classical
  have hn0 : n ≠ 0 := by omega
  set C := (Finset.Icc 1 x) ×ˢ ((Finset.Icc 1 x) ×ˢ (Finset.Icc 1 x)) with hC
  have hmain : (n.divisors.product n.divisors).card ≤
      (C.filter (fun t : ℕ × ℕ × ℕ => t.1 * t.2.1 * t.2.2 ∣ n)).card := by
    apply Finset.card_le_card_of_injOn
      (fun p : ℕ × ℕ => (Nat.gcd p.1 p.2, p.1 / Nat.gcd p.1 p.2, p.2 / Nat.gcd p.1 p.2))
    · intro p hp
      change p ∈ n.divisors.product n.divisors at hp
      obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hp
      rw [Nat.mem_divisors] at hp1 hp2
      obtain ⟨hp1d, -⟩ := hp1
      obtain ⟨hp2d, -⟩ := hp2
      have hp1pos : 0 < p.1 := Nat.pos_of_dvd_of_pos hp1d (by omega)
      have hp2pos : 0 < p.2 := Nat.pos_of_dvd_of_pos hp2d (by omega)
      have hp1le : p.1 ≤ x := le_trans (Nat.le_of_dvd (by omega) hp1d) hnx
      have hp2le : p.2 ≤ x := le_trans (Nat.le_of_dvd (by omega) hp2d) hnx
      have hgpos : 0 < Nat.gcd p.1 p.2 := Nat.gcd_pos_of_pos_left p.2 hp1pos
      have hgle1 : Nat.gcd p.1 p.2 ≤ p.1 := Nat.gcd_le_left p.2 hp1pos
      have hgle2 : Nat.gcd p.1 p.2 ≤ p.2 := Nat.gcd_le_right p.1 hp2pos
      refine Finset.mem_filter.mpr ⟨?_, ?_⟩
      · rw [hC]
        exact Finset.mem_product.mpr ⟨Finset.mem_Icc.mpr ⟨hgpos, le_trans hgle1 hp1le⟩,
          Finset.mem_product.mpr
            ⟨Finset.mem_Icc.mpr ⟨by rw [Nat.one_le_div_iff hgpos]; exact hgle1,
                le_trans (Nat.div_le_self p.1 _) hp1le⟩,
             Finset.mem_Icc.mpr ⟨by rw [Nat.one_le_div_iff hgpos]; exact hgle2,
                le_trans (Nat.div_le_self p.2 _) hp2le⟩⟩⟩
      · calc Nat.gcd p.1 p.2 * (p.1 / Nat.gcd p.1 p.2) * (p.2 / Nat.gcd p.1 p.2)
            = p.1.lcm p.2 := (lcm_eq_gcd_mul_div_div p.1 p.2).symm
          _ ∣ n := Nat.lcm_dvd hp1d hp2d
    · intro p hp q hq heq
      change p ∈ n.divisors.product n.divisors at hp
      change q ∈ n.divisors.product n.divisors at hq
      simp only [Prod.mk.injEq] at heq
      obtain ⟨hg, ha, hb⟩ := heq
      have e1 : p.1 = q.1 := by
        have h1 : p.1 = Nat.gcd p.1 p.2 * (p.1 / Nat.gcd p.1 p.2) :=
          (Nat.mul_div_cancel' (Nat.gcd_dvd_left p.1 p.2)).symm
        have h3 : q.1 = Nat.gcd q.1 q.2 * (q.1 / Nat.gcd q.1 q.2) :=
          (Nat.mul_div_cancel' (Nat.gcd_dvd_left q.1 q.2)).symm
        calc p.1 = Nat.gcd p.1 p.2 * (p.1 / Nat.gcd p.1 p.2) := h1
          _ = Nat.gcd q.1 q.2 * (q.1 / Nat.gcd q.1 q.2) := by rw [ha, hg]
          _ = q.1 := h3.symm
      have e2 : p.2 = q.2 := by
        have h2 : p.2 = Nat.gcd p.1 p.2 * (p.2 / Nat.gcd p.1 p.2) :=
          (Nat.mul_div_cancel' (Nat.gcd_dvd_right p.1 p.2)).symm
        have h4 : q.2 = Nat.gcd q.1 q.2 * (q.2 / Nat.gcd q.1 q.2) :=
          (Nat.mul_div_cancel' (Nat.gcd_dvd_right q.1 q.2)).symm
        calc p.2 = Nat.gcd p.1 p.2 * (p.2 / Nat.gcd p.1 p.2) := h2
          _ = Nat.gcd q.1 q.2 * (q.2 / Nat.gcd q.1 q.2) := by rw [hb, hg]
          _ = q.2 := h4.symm
      exact Prod.ext e1 e2
  rw [pow_two, ← Finset.card_product]
  exact hmain

lemma sum_Icc_triple_one_div_eq_cube (s : Finset ℕ) :
    (∑ g ∈ s, ∑ a ∈ s, ∑ b ∈ s, (1:ℝ)/((g:ℝ)*(a:ℝ)*(b:ℝ)))
      = (∑ i ∈ s, (1:ℝ)/(i:ℝ))^3 := by
  set f : ℕ → ℝ := fun i => (1:ℝ)/(i:ℝ) with hf
  have hterm : ∀ g a b : ℕ, (1:ℝ)/((g:ℝ)*(a:ℝ)*(b:ℝ)) = f g * f a * f b := by
    intro g a b
    rw [hf]; simp only []
    rw [one_div, one_div, one_div, one_div, mul_inv, mul_inv]
  simp_rw [hterm]
  have key : (∑ i ∈ s, f i) * ((∑ i ∈ s, f i) * (∑ i ∈ s, f i))
      = (∑ g ∈ s, ∑ a ∈ s, ∑ b ∈ s, f g * f a * f b) := by
    rw [Finset.sum_mul_sum]
    rw [Finset.sum_mul_sum]
    apply Finset.sum_congr rfl; intro g hg
    apply Finset.sum_congr rfl; intro a ha
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro b hb
    ring
  rw [← key]
  rw [hf]
  ring

lemma sum_Icc_triple_div_eq_mul_cube (s : Finset ℕ) (c : ℝ) :
    (∑ g ∈ s, ∑ a ∈ s, ∑ b ∈ s, c / ((g:ℝ)*(a:ℝ)*(b:ℝ)))
      = c * (∑ i ∈ s, (1:ℝ)/(i:ℝ))^3 := by
  rw [show (∑ g ∈ s, ∑ a ∈ s, ∑ b ∈ s, c / ((g:ℝ)*(a:ℝ)*(b:ℝ)))
      = c * (∑ g ∈ s, ∑ a ∈ s, ∑ b ∈ s, (1:ℝ) / ((g:ℝ)*(a:ℝ)*(b:ℝ))) from by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro g hg
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro a ha
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl; intro b hb
    rw [mul_one_div]]
  rw [sum_Icc_triple_one_div_eq_cube]

lemma harmonic_cast_eq_sum_Icc (n : ℕ) :
    (harmonic n : ℝ) = ∑ k ∈ Finset.Icc 1 n, (1:ℝ)/(k:ℝ) := by
  rw [harmonic_eq_sum_Icc]
  simp only [Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast, one_div]

lemma harmonic_Icc_le_one_add_log (x : ℕ) :
    (∑ k ∈ Finset.Icc 1 x, (1:ℝ)/(k:ℝ)) ≤ 1 + Real.log (x:ℝ) := by
  rw [← harmonic_cast_eq_sum_Icc]
  exact harmonic_le_one_add_log x

lemma cast_card_Icc_filter_dvd_le (z d : ℕ) :
    (((Finset.Icc 1 z).filter (fun f => d ∣ f)).card : ℝ) ≤ (z:ℝ)/d := by
  have hset : Finset.Icc 1 z = Finset.Ioc 0 z := by
    ext x; simp [Finset.mem_Icc, Finset.mem_Ioc]; omega
  calc (((Finset.Icc 1 z).filter (fun f => d ∣ f)).card : ℝ)
      = (((Finset.Ioc 0 z).filter (fun f => d ∣ f)).card : ℝ) := by rw [hset]
    _ = ((z/d : ℕ) : ℝ) := by rw [Nat.Ioc_filter_dvd_card_eq_div]
    _ ≤ (z:ℝ)/d := Nat.cast_div_le

theorem sum_card_divisors_sq_le :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℕ,
      ∑ n ∈ Finset.Icc 1 x, ((n.divisors.card : ℝ)) ^ 2
        ≤ C * (x : ℝ) * (Real.log (2 * (x : ℝ) + 2)) ^ 3 := by
  refine ⟨8, by norm_num, ?_⟩
  intro x
  rcases Nat.eq_zero_or_pos x with hx | hx
  · subst hx; simp
  set H : ℝ := ∑ i ∈ Finset.Icc 1 x, (1:ℝ)/(i:ℝ) with hH
  have hHnn : 0 ≤ H := by
    rw [hH]; exact Finset.sum_nonneg (fun i hi => by positivity)
  have hbound : (∑ n ∈ Finset.Icc 1 x, ((n.divisors.card : ℝ)) ^ 2) ≤ (x:ℝ) * H^3 := by
    set C3 : Finset (ℕ × ℕ × ℕ) :=
      (Finset.Icc 1 x) ×ˢ ((Finset.Icc 1 x) ×ˢ (Finset.Icc 1 x)) with hC3
    have hstep1 : (∑ n ∈ Finset.Icc 1 x, ((n.divisors.card : ℝ)) ^ 2)
        ≤ ∑ n ∈ Finset.Icc 1 x,
            ((C3.filter (fun t : ℕ × ℕ × ℕ => t.1 * t.2.1 * t.2.2 ∣ n)).card : ℝ) := by
      apply Finset.sum_le_sum
      intro n hn
      have hn1 : 1 ≤ n := (Finset.mem_Icc.mp hn).1
      have hnx : n ≤ x := (Finset.mem_Icc.mp hn).2
      have h := card_divisors_sq_le_card_triples x n hn1 hnx
      have h' : (((n.divisors.card : ℝ)) ^ 2)
          ≤ ((((Finset.Icc 1 x) ×ˢ ((Finset.Icc 1 x) ×ˢ (Finset.Icc 1 x))).filter
              (fun t : ℕ × ℕ × ℕ => t.1 * t.2.1 * t.2.2 ∣ n)).card : ℝ) := by
        exact_mod_cast h
      rw [hC3]
      exact h'
    have hstep2 : (∑ n ∈ Finset.Icc 1 x,
            ((C3.filter (fun t : ℕ × ℕ × ℕ => t.1 * t.2.1 * t.2.2 ∣ n)).card : ℝ))
        = ∑ n ∈ Finset.Icc 1 x, ∑ t ∈ C3,
            (if t.1 * t.2.1 * t.2.2 ∣ n then (1:ℝ) else 0) := by
      apply Finset.sum_congr rfl
      intro n hn
      rw [Finset.card_filter]
      push_cast
      apply Finset.sum_congr rfl
      intro t ht
      by_cases h : t.1 * t.2.1 * t.2.2 ∣ n <;> simp [h]
    have hstep3 : (∑ n ∈ Finset.Icc 1 x, ∑ t ∈ C3,
            (if t.1 * t.2.1 * t.2.2 ∣ n then (1:ℝ) else 0))
        = ∑ t ∈ C3, ∑ n ∈ Finset.Icc 1 x,
            (if t.1 * t.2.1 * t.2.2 ∣ n then (1:ℝ) else 0) :=
      Finset.sum_comm
    have hstep4 : (∑ t ∈ C3, ∑ n ∈ Finset.Icc 1 x,
            (if t.1 * t.2.1 * t.2.2 ∣ n then (1:ℝ) else 0))
        = ∑ t ∈ C3, (((Finset.Icc 1 x).filter (fun n => t.1 * t.2.1 * t.2.2 ∣ n)).card : ℝ) := by
      apply Finset.sum_congr rfl
      intro t ht
      rw [Finset.card_filter]
      push_cast
      apply Finset.sum_congr rfl
      intro n hn
      by_cases h : t.1 * t.2.1 * t.2.2 ∣ n <;> simp [h]
    have hstep5 : (∑ t ∈ C3,
            (((Finset.Icc 1 x).filter (fun n => t.1 * t.2.1 * t.2.2 ∣ n)).card : ℝ))
        ≤ (x:ℝ) * H^3 := by
      have h1 : (∑ t ∈ C3,
            (((Finset.Icc 1 x).filter (fun n => t.1 * t.2.1 * t.2.2 ∣ n)).card : ℝ))
          ≤ ∑ t ∈ C3, (x:ℝ) / (t.1 * t.2.1 * t.2.2) := by
        apply Finset.sum_le_sum
        intro t ht
        have := cast_card_Icc_filter_dvd_le x (t.1 * t.2.1 * t.2.2)
        simpa only [Nat.cast_mul] using this
      have h2 : (∑ t ∈ C3, (x:ℝ) / (t.1 * t.2.1 * t.2.2)) = (x:ℝ) * H^3 := by
        rw [hC3]
        simp only [Finset.sum_product]
        rw [sum_Icc_triple_div_eq_mul_cube, hH]
      linarith [h1, h2.le, h2.ge]
    linarith [hstep1, hstep2.le, hstep2.ge, hstep3.le, hstep3.ge, hstep4.le, hstep4.ge, hstep5]
  have hHle : H ≤ 1 + Real.log (x:ℝ) := by
    rw [hH]; exact harmonic_Icc_le_one_add_log x
  have hlogbound : 1 + Real.log (x:ℝ) ≤ 2 * Real.log (2*(x:ℝ)+2) := by
    have hxR : (0:ℝ) < x := by exact_mod_cast (show 0 < x by omega)
    have hx1 : (1:ℝ) ≤ x := by exact_mod_cast hx
    have hlog2x : Real.log ((2:ℝ)*x) ≤ Real.log (2*x+2) := by
      apply Real.log_le_log
      · linarith
      · linarith
    rw [Real.log_mul (by norm_num : (2:ℝ) ≠ 0) (ne_of_gt hxR)] at hlog2x
    have hlog4 : (1:ℝ) ≤ Real.log 4 := by
      rw [Real.le_log_iff_exp_le (by norm_num : (0:ℝ) < 4)]
      exact le_trans (le_of_lt Real.exp_one_lt_three) (by norm_num)
    have hlog4eq : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4:ℝ) = 2*2 from by norm_num, Real.log_mul (by norm_num) (by norm_num)]
      ring
    have hlogxnn : 0 ≤ Real.log (x:ℝ) := Real.log_nonneg hx1
    linarith
  have hcube : H^3 ≤ (2 * Real.log (2*(x:ℝ)+2))^3 :=
    pow_le_pow_left₀ hHnn (le_trans hHle hlogbound) 3
  calc (∑ n ∈ Finset.Icc 1 x, ((n.divisors.card : ℝ)) ^ 2)
      ≤ (x:ℝ) * H^3 := hbound
    _ ≤ (x:ℝ) * (8 * (Real.log (2*(x:ℝ)+2))^3) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        calc H^3 ≤ (2 * Real.log (2*(x:ℝ)+2))^3 := hcube
          _ = 8 * (Real.log (2*(x:ℝ)+2))^3 := by ring
    _ = 8 * (x:ℝ) * (Real.log (2 * (x:ℝ) + 2)) ^ 3 := by ring

end Commons.NumberTheory.Divisors