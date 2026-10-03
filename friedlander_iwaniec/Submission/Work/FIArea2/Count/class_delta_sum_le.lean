import Mathlib
import Submission.Work.FIArea2.card_sol_lin_dioph_le1
import Submission.Work.FIArea2.sum_tau_pow_div_le
import Submission.Commons.NumberTheory.Divisors.sum_filter_dvd_reindex

namespace Work.FIArea2.Count

open Finset

private lemma log_nat_nonneg (n : ℕ) : 0 ≤ Real.log (n : ℝ) := by
  rcases Nat.eq_zero_or_pos n with h | h
  · rw [h]; simp
  · exact Real.log_nonneg (by exact_mod_cast h)

private lemma card_divisors_mul_le (m n : ℕ) :
    (m * n).divisors.card ≤ m.divisors.card * n.divisors.card := by
  rw [Nat.divisors_mul]
  exact Finset.card_mul_le

theorem sum_filter_dvd_tau_three_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (d D : ℕ), 1 ≤ d →
      (∑ k ∈ (Finset.Icc 1 D).filter (fun k => d ∣ k), ((k.divisors.card : ℝ))^3 / (k : ℝ))
        ≤ C * (((d.divisors.card : ℝ))^3 / (d : ℝ)) * (Real.log (D : ℝ) + 2)^8 := by
  obtain ⟨C1, hC1pos, hC1⟩ := Work.FIArea2.sum_tau_pow_div_le 3
  refine ⟨C1, hC1pos, ?_⟩
  intro d D hd
  have hdpos : 0 < d := by omega
  have hdR : (0:ℝ) < (d:ℝ) := by exact_mod_cast hdpos
  have hterm : ∀ m ∈ Finset.Icc 1 (D / d),
      (((d * m).divisors.card : ℝ))^3 / ((d * m : ℕ) : ℝ)
        ≤ (((d.divisors.card : ℝ))^3 / (d : ℝ)) * ((((m.divisors.card : ℝ))^3 / (m : ℝ))) := by
    intro m hm
    have hm1 : 1 ≤ m := (Finset.mem_Icc.mp hm).1
    have hmR : (0:ℝ) < (m:ℝ) := by exact_mod_cast hm1
    have hsub : ((d * m).divisors.card : ℝ) ≤ (d.divisors.card : ℝ) * (m.divisors.card : ℝ) := by
      have h := card_divisors_mul_le d m
      exact_mod_cast h
    have hcube : (((d * m).divisors.card : ℝ))^3 ≤ ((d.divisors.card : ℝ) * (m.divisors.card : ℝ))^3 :=
      pow_le_pow_left₀ (by positivity) hsub 3
    have hden : (0:ℝ) < (d:ℝ) * (m:ℝ) := mul_pos hdR hmR
    have hcast : ((d * m : ℕ) : ℝ) = (d:ℝ) * (m:ℝ) := by push_cast; ring
    rw [hcast]
    have hA : (((d * m).divisors.card : ℝ))^3 / ((d:ℝ)*(m:ℝ))
        ≤ ((d.divisors.card : ℝ) * (m.divisors.card : ℝ))^3 / ((d:ℝ)*(m:ℝ)) :=
      div_le_div_of_nonneg_right hcube hden.le
    have h2 : ((d.divisors.card : ℝ) * (m.divisors.card : ℝ))^3 / ((d:ℝ)*(m:ℝ))
        = (((d.divisors.card : ℝ))^3 / (d : ℝ)) * ((((m.divisors.card : ℝ))^3 / (m : ℝ))) := by
      rw [mul_pow]; field_simp; try ring
    rw [← h2]
    exact hA
  calc (∑ k ∈ (Finset.Icc 1 D).filter (fun k => d ∣ k), ((k.divisors.card : ℝ))^3 / (k : ℝ))
      = ∑ m ∈ Finset.Icc 1 (D / d), (((d * m).divisors.card : ℝ))^3 / ((d * m : ℕ) : ℝ) :=
        Commons.NumberTheory.Divisors.sum_filter_dvd_reindex hdpos _
    _ ≤ ∑ m ∈ Finset.Icc 1 (D / d),
          (((d.divisors.card : ℝ))^3 / (d : ℝ)) * ((((m.divisors.card : ℝ))^3 / (m : ℝ))) :=
        Finset.sum_le_sum hterm
    _ = (((d.divisors.card : ℝ))^3 / (d : ℝ)) * ∑ m ∈ Finset.Icc 1 (D / d), (((m.divisors.card : ℝ))^3 / (m : ℝ)) := by
        rw [Finset.mul_sum]
    _ ≤ (((d.divisors.card : ℝ))^3 / (d : ℝ)) * (C1 * (Real.log ((D / d : ℕ) : ℝ) + 2)^8) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        have h := hC1 (D / d)
        rw [show (2:ℕ)^3 = 8 from by norm_num] at h
        exact h
    _ ≤ (((d.divisors.card : ℝ))^3 / (d : ℝ)) * (C1 * (Real.log (D : ℝ) + 2)^8) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        apply mul_le_mul_of_nonneg_left _ hC1pos.le
        have hlog : Real.log (((D / d : ℕ)) : ℝ) ≤ Real.log (D : ℝ) := by
          rcases Nat.eq_zero_or_pos (D / d) with hM0 | hMpos
          · rw [hM0, Nat.cast_zero, Real.log_zero]
            exact log_nat_nonneg D
          · apply Real.log_le_log (by exact_mod_cast hMpos)
            exact_mod_cast Nat.div_le_self D d
        have hbase : 0 ≤ Real.log (((D / d : ℕ)) : ℝ) + 2 := by
          have := log_nat_nonneg (D / d); linarith
        exact pow_le_pow_left₀ hbase (by linarith) 8
    _ = C1 * (((d.divisors.card : ℝ))^3 / (d : ℝ)) * (Real.log (D : ℝ) + 2)^8 := by ring

/-- Real form of the fiber bound. -/
private lemma card_filter_eq_le_real (r1 r2 Δ a b c dd : ℤ) (hr1 : r1 ≠ 0) :
    ((((Finset.Icc a b).product (Finset.Icc c dd)).filter
        (fun p : ℤ × ℤ => r1 * p.2 - r2 * p.1 = Δ)).card : ℝ)
      ≤ 1 + ((r1.gcd r2 : ℕ) : ℝ) * ((b - a + 1).natAbs : ℝ) / (r1.natAbs : ℝ) := by
  have h := card_sol_lin_dioph_le1 r1 r2 Δ a b c dd hr1
  have hr1pos : (0:ℝ) < (r1.natAbs : ℝ) := by exact_mod_cast Int.natAbs_pos.mpr hr1
  have hR : ((((Finset.Icc a b).product (Finset.Icc c dd)).filter
        (fun p : ℤ × ℤ => r1 * p.2 - r2 * p.1 = Δ)).card : ℝ) * (r1.natAbs : ℝ)
      ≤ (r1.natAbs : ℝ) + ((r1.gcd r2 : ℕ) : ℝ) * ((b - a + 1).natAbs : ℝ) := by
    exact_mod_cast h
  have hdiv := div_le_div_of_nonneg_right hR hr1pos.le
  rw [mul_div_cancel_right₀ _ (ne_of_gt hr1pos)] at hdiv
  have heq : ((r1.natAbs : ℝ) + ((r1.gcd r2 : ℕ) : ℝ) * ((b - a + 1).natAbs : ℝ)) / (r1.natAbs : ℝ)
      = 1 + ((r1.gcd r2 : ℕ) : ℝ) * ((b - a + 1).natAbs : ℝ) / (r1.natAbs : ℝ) := by
    field_simp
  rwa [heq] at hdiv

/-- Grouping a sum by the value of a map into `ℕ`. -/
private lemma sum_eq_sum_fiber_card {α : Type*} [DecidableEq α]
    (s : Finset α) (g : α → ℕ) (K : Finset ℕ) (f : ℕ → ℝ)
    (hK : ∀ a ∈ s, g a ∈ K) :
    ∑ a ∈ s, f (g a) = ∑ k ∈ K, ((s.filter (fun a => g a = k)).card : ℝ) * f k := by
  have key : (∑ k ∈ K, ((s.filter (fun a => g a = k)).card : ℝ) * f k)
      = ∑ k ∈ K, ∑ a ∈ s.filter (fun a => g a = k), f k := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [Finset.sum_const, nsmul_eq_mul]
  rw [key]
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro a ha
  rw [Finset.sum_ite_eq]
  rw [if_pos (hK a ha)]

/-- Bounding a sum by the fiber cardinality. -/
private lemma sum_le_mul_sum_of_fiber_card {α : Type*} [DecidableEq α]
    (s : Finset α) (g : α → ℕ) (K : Finset ℕ) (f : ℕ → ℝ)
    (hf : ∀ k, 0 ≤ f k) (T : ℝ)
    (hK : ∀ a ∈ s, g a ∈ K)
    (hfib : ∀ k, ((s.filter (fun a => g a = k)).card : ℝ) ≤ T) :
    ∑ a ∈ s, f (g a) ≤ T * ∑ k ∈ K, f k := by
  rw [sum_eq_sum_fiber_card s g K f hK]
  calc ∑ k ∈ K, ((s.filter (fun a => g a = k)).card : ℝ) * f k
      ≤ ∑ k ∈ K, T * f k := Finset.sum_le_sum (fun k _ => mul_le_mul_of_nonneg_right (hfib k) (hf k))
    _ = T * ∑ k ∈ K, f k := by rw [Finset.mul_sum]

theorem class_delta_sum_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (r1 r2 : ℤ) (hr1 : r1 ≠ 0) (d : ℕ) (hd : 1 ≤ d) (D : ℕ) (hD : 1 ≤ D)
      (a b c dd : ℤ),
      (∀ p : ℤ × ℤ, p.1 ∈ Finset.Icc a b → p.2 ∈ Finset.Icc c dd →
          (r1 * p.2 - r2 * p.1).natAbs ≤ D) →
      (∑ p ∈ ((Finset.Icc a b).product (Finset.Icc c dd)).filter
            (fun p => (d : ℤ) ∣ r1 * p.2 - r2 * p.1 ∧ r1 * p.2 - r2 * p.1 ≠ 0),
          (((r1 * p.2 - r2 * p.1).natAbs.divisors.card : ℝ))^3 / ((r1 * p.2 - r2 * p.1).natAbs : ℝ))
        ≤ C * (1 + ((r1.gcd r2) : ℝ) * ((b - a + 1).natAbs : ℝ) / ((r1.natAbs : ℝ)))
            * (((d.divisors.card : ℝ))^3 / (d : ℝ)) * (Real.log (D : ℝ) + 2)^8 := by
  obtain ⟨C1, hC1pos, hC1⟩ := sum_filter_dvd_tau_three_le
  refine ⟨2*C1, by positivity, ?_⟩
  intro r1 r2 hr1 d hd D hD a b c dd hbound
  set B : Finset (ℤ×ℤ) := (Finset.Icc a b).product (Finset.Icc c dd) with hB
  set S : Finset (ℤ×ℤ) := B.filter (fun p => (d:ℤ) ∣ r1*p.2 - r2*p.1 ∧ r1*p.2 - r2*p.1 ≠ 0) with hS
  set K : Finset ℕ := (Finset.Icc 1 D).filter (fun k => d ∣ k) with hK
  set G : ℤ×ℤ → ℕ := fun p => (r1*p.2 - r2*p.1).natAbs with hG
  set w : ℕ → ℝ := fun k => ((k.divisors.card:ℝ))^3/(k:ℝ) with hw
  set T : ℝ := 1 + ((r1.gcd r2):ℝ)*(((b-a+1).natAbs):ℝ)/(r1.natAbs:ℝ) with hT
  have hTpos : 0 < T := by
    rw [hT]
    have h0 : (0:ℝ) ≤ ((r1.gcd r2):ℝ)*(((b-a+1).natAbs):ℝ)/(r1.natAbs:ℝ) :=
      div_nonneg (mul_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
    linarith
  have hKmem : ∀ p ∈ S, G p ∈ K := by
    intro p hp
    rw [hS, Finset.mem_filter] at hp
    obtain ⟨hpB, hpd, hpne⟩ := hp
    rw [hK, Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · rw [hG]
      exact Int.natAbs_pos.mpr hpne
    · rw [hB] at hpB
      obtain ⟨hp1, hp2⟩ := Finset.mem_product.mp hpB
      rw [hG]
      exact hbound p hp1 hp2
    · rw [hG]
      exact Int.natCast_dvd_natCast.mp (Int.dvd_natAbs.mpr hpd)
  have hfib : ∀ k : ℕ, ((S.filter (fun p => G p = k)).card : ℝ) ≤ 2 * T := by
    intro k
    set Fk : Finset (ℤ×ℤ) := S.filter (fun p => G p = k) with hFk
    set Dp : Finset (ℤ×ℤ) := B.filter (fun p => r1*p.2 - r2*p.1 = (k:ℤ)) with hDpf
    set Dm : Finset (ℤ×ℤ) := B.filter (fun p => r1*p.2 - r2*p.1 = -((k:ℤ))) with hDmf
    have hsub : Fk ⊆ Dp ∪ Dm := by
      intro p hp
      rw [hFk, Finset.mem_filter] at hp
      obtain ⟨hpS, hpk⟩ := hp
      rw [hS, Finset.mem_filter] at hpS
      obtain ⟨hpB, _, _⟩ := hpS
      have hpk' : (r1*p.2 - r2*p.1).natAbs = k := hpk
      have h : r1*p.2 - r2*p.1 = (k:ℤ) ∨ r1*p.2 - r2*p.1 = -((k:ℤ)) :=
        Int.natAbs_eq_natAbs_iff.mp (by rw [Int.natAbs_natCast]; exact hpk')
      rw [Finset.mem_union, hDpf, hDmf, Finset.mem_filter, Finset.mem_filter]
      rcases h with h | h
      · exact Or.inl ⟨hpB, h⟩
      · exact Or.inr ⟨hpB, h⟩
    have hcard : Fk.card ≤ Dp.card + Dm.card :=
      le_trans (Finset.card_le_card hsub) (Finset.card_union_le Dp Dm)
    have hDpb : (Dp.card : ℝ) ≤ 1 + ((r1.gcd r2):ℝ)*(((b-a+1).natAbs):ℝ)/(r1.natAbs:ℝ) := by
      rw [hDpf, hB]
      exact card_filter_eq_le_real r1 r2 (k:ℤ) a b c dd hr1
    have hDmb : (Dm.card : ℝ) ≤ 1 + ((r1.gcd r2):ℝ)*(((b-a+1).natAbs):ℝ)/(r1.natAbs:ℝ) := by
      rw [hDmf, hB]
      exact card_filter_eq_le_real r1 r2 (-((k:ℤ))) a b c dd hr1
    have hcardR : (Fk.card : ℝ) ≤ (Dp.card : ℝ) + (Dm.card : ℝ) := by exact_mod_cast hcard
    calc (Fk.card : ℝ) ≤ (Dp.card : ℝ) + (Dm.card : ℝ) := hcardR
      _ ≤ (1 + ((r1.gcd r2):ℝ)*(((b-a+1).natAbs):ℝ)/(r1.natAbs:ℝ))
            + (1 + ((r1.gcd r2):ℝ)*(((b-a+1).natAbs):ℝ)/(r1.natAbs:ℝ)) := add_le_add hDpb hDmb
      _ = 2 * T := by rw [hT]; ring
  have hstep : (∑ p ∈ S, w (G p)) ≤ (2*T) * ∑ k ∈ K, w k :=
    sum_le_mul_sum_of_fiber_card S G K w (fun k => by rw [hw]; positivity) (2*T) hKmem hfib
  have hKb : ∑ k ∈ K, w k ≤ C1 * ((d.divisors.card:ℝ)^3/(d:ℝ)) * (Real.log (D:ℝ)+2)^8 := by
    rw [hK, hw]
    exact hC1 d D hd
  calc (∑ p ∈ S, w (G p)) ≤ (2*T) * ∑ k ∈ K, w k := hstep
    _ ≤ (2*T) * (C1 * ((d.divisors.card:ℝ)^3/(d:ℝ)) * (Real.log (D:ℝ)+2)^8) :=
        mul_le_mul_of_nonneg_left hKb (by linarith)
    _ = (2*C1) * T * ((d.divisors.card:ℝ)^3/(d:ℝ)) * (Real.log (D:ℝ)+2)^8 := by ring

end Work.FIArea2.Count
