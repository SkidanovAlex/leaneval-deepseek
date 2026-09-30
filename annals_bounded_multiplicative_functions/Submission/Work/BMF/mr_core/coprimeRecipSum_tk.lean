import Mathlib
import Submission.Work.BMF.Defs
import Submission.Work.BMF.mr_direct.coprime_primesIn_iff

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.mr_core

open Finset

/-- **Turán–Kubilius / Chebyshev variance bound.**

Let `1 ≤ a`, `I` a finset of primes, `ω n = #{p ∈ I : p ∣ n}`, `N = #(Icc a b) = b + 1 - a`,
`S = ∑ p ∈ I, 1/(p)`, `π = #I`.  Then `∑_{n ∈ Icc a b} (ω n - S)^2 ≤ N*S + π^2 + 2*S*π`. -/
theorem tk_variance (a b : ℕ) (ha : 1 ≤ a) (I : Finset ℕ) (hI : ∀ p ∈ I, p.Prime) :
    ∑ n ∈ Finset.Icc a b,
        (((I.filter fun p => p ∣ n).card : ℝ) - ∑ p ∈ I, (1 : ℝ) / (p : ℝ)) ^ 2
      ≤ ((b + 1 - a : ℕ) : ℝ) * (∑ p ∈ I, (1 : ℝ) / (p : ℝ)) + (I.card : ℝ) ^ 2
        + 2 * (I.card : ℝ) * (∑ p ∈ I, (1 : ℝ) / (p : ℝ)) := by
  classical
  set S : ℝ := ∑ p ∈ I, (1 : ℝ) / (p : ℝ) with hSdef
  set π : ℝ := (I.card : ℝ) with hπdef
  have hSnn : 0 ≤ S := by
    rw [hSdef]; exact Finset.sum_nonneg (fun p hp => by positivity)
  have hπnn : 0 ≤ π := by rw [hπdef]; positivity
  have hcoll : ∀ n : ℕ, ((I.filter fun p => p ∣ n).card : ℝ)
      = ∑ p ∈ I, (if p ∣ n then (1 : ℝ) else 0) := by
    intro n
    rw [Finset.card_filter]
    push_cast
    rfl
  have hcardcoll : ∀ p : ℕ, (((Finset.Icc a b).filter fun n => p ∣ n).card : ℝ)
      = ∑ n ∈ Finset.Icc a b, (if p ∣ n then (1 : ℝ) else 0) := by
    intro p
    rw [Finset.card_filter]
    push_cast
    rfl
  rcases le_or_gt a b with hab | hba
  · set N : ℕ := b + 1 - a with hNdef
    have hNcast : (N : ℝ) = (b : ℝ) + 1 - (a : ℝ) := by
      rw [hNdef, Nat.cast_sub (by omega : a ≤ b + 1), Nat.cast_add, Nat.cast_one]
    -- ---------- multiple counts ----------
    have hmc : ∀ d : ℕ, 1 ≤ d →
        ((Finset.Icc a b).filter (fun n => d ∣ n)).card = b / d - (a - 1) / d := by
      intro d hd
      have h1 : ((Finset.Icc 1 b).filter (fun k => d ∣ k)).card = b / d := by
        have h := Nat.card_multiples' b d
        have heq : (Finset.Icc 1 b).filter (fun k => d ∣ k)
            = (Finset.range b.succ).filter (fun k => k ≠ 0 ∧ d ∣ k) := by
          ext k
          simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
          omega
        rw [heq, h]
      have h2 : ((Finset.Icc 1 (a - 1)).filter (fun k => d ∣ k)).card = (a - 1) / d := by
        have h := Nat.card_multiples' (a - 1) d
        have heq : (Finset.Icc 1 (a - 1)).filter (fun k => d ∣ k)
            = (Finset.range (a - 1).succ).filter (fun k => k ≠ 0 ∧ d ∣ k) := by
          ext k
          simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
          omega
        rw [heq, h]
      have hbase : Finset.Icc 1 b = Finset.Icc 1 (a - 1) ∪ Finset.Icc a b := by
        ext k
        simp only [Finset.mem_Icc, Finset.mem_union]
        omega
      have hunion : (Finset.Icc 1 b).filter (fun k => d ∣ k)
          = ((Finset.Icc 1 (a - 1)).filter (fun k => d ∣ k))
            ∪ ((Finset.Icc a b).filter (fun k => d ∣ k)) := by
        rw [hbase, Finset.filter_union]
      have hdisj : Disjoint ((Finset.Icc 1 (a - 1)).filter (fun k => d ∣ k))
          ((Finset.Icc a b).filter (fun k => d ∣ k)) := by
        rw [Finset.disjoint_left]
        intro k hk1 hk2
        simp only [Finset.mem_filter, Finset.mem_Icc] at hk1 hk2
        omega
      have key : b / d = (a - 1) / d + ((Finset.Icc a b).filter (fun k => d ∣ k)).card := by
        rw [← h1, hunion, Finset.card_union_of_disjoint hdisj, h2]
      rw [key, Nat.add_sub_cancel_left]
    -- ---------- the ±1 bounds ----------
    have hbound : ∀ d : ℕ, 1 ≤ d →
        (N : ℝ) / (d : ℝ) - 1 ≤ (((Finset.Icc a b).filter (fun n => d ∣ n)).card : ℝ) ∧
        (((Finset.Icc a b).filter (fun n => d ∣ n)).card : ℝ) ≤ (N : ℝ) / (d : ℝ) + 1 := by
      intro d hd
      have hle : (a - 1) / d ≤ b / d := Nat.div_le_div_right (by omega)
      have hmax : (((Finset.Icc a b).filter (fun n => d ∣ n)).card : ℝ)
          = ((b / d : ℕ) : ℝ) - (((a - 1) / d : ℕ) : ℝ) := by
        rw [hmc d hd, Nat.cast_sub hle]
      have hup : ((b / d : ℕ) : ℝ) ≤ (b : ℝ) / (d : ℝ) := by
        simpa using Nat.cast_div_le (α := ℝ) (m := b) (n := d)
      have hup2 : (b : ℝ) / (d : ℝ) < ((b / d : ℕ) : ℝ) + 1 := by
        have h := Nat.lt_floor_add_one ((b : ℝ) / (d : ℝ))
        rw [Nat.floor_div_eq_div b d] at h
        exact h
      have hlow : (((a - 1) / d : ℕ) : ℝ) ≤ ((a - 1 : ℕ) : ℝ) / (d : ℝ) := by
        simpa using Nat.cast_div_le (α := ℝ) (m := a - 1) (n := d)
      have hlow2 : ((a - 1 : ℕ) : ℝ) / (d : ℝ) - 1 < (((a - 1) / d : ℕ) : ℝ) := by
        have h := Nat.lt_floor_add_one (((a - 1 : ℕ) : ℝ) / (d : ℝ))
        rw [Nat.floor_div_eq_div (a - 1) d] at h
        linarith
      have hid : (b : ℝ) - ((a - 1 : ℕ) : ℝ) = (N : ℝ) := by
        rw [hNcast, Nat.cast_sub ha]
        ring
      have hdiv : (N : ℝ) / (d : ℝ) = (b : ℝ) / (d : ℝ) - ((a - 1 : ℕ) : ℝ) / (d : ℝ) := by
        rw [← hid, sub_div]
      constructor
      · rw [hmax, hdiv]; linarith
      · rw [hmax, hdiv]; linarith
    -- sums of reciprocals
    have hSsum : ∑ p ∈ I, (N : ℝ) / (p : ℝ) = (N : ℝ) * S := by
      rw [hSdef, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      rw [div_eq_mul_one_div]
    have hπsum : ∑ p ∈ I, (1 : ℝ) = π := by
      rw [hπdef, Finset.sum_const, nsmul_eq_mul, mul_one]
    -- ---------- first moment ----------
    have hswap : ∑ n ∈ Finset.Icc a b, ((I.filter fun p => p ∣ n).card : ℝ)
        = ∑ p ∈ I, (((Finset.Icc a b).filter fun n => p ∣ n).card : ℝ) := by
      simp_rw [hcoll]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl (fun p hp => (hcardcoll p).symm)
    have hFirst : (N : ℝ) * S - π ≤ ∑ n ∈ Finset.Icc a b, ((I.filter fun p => p ∣ n).card : ℝ) := by
      rw [hswap]
      have hthis : (N : ℝ) * S - π = ∑ p ∈ I, ((N : ℝ) / (p : ℝ) - 1) := by
        rw [Finset.sum_sub_distrib, hSsum, hπsum]
      rw [hthis]
      apply Finset.sum_le_sum
      intro p hp
      exact (hbound p (le_trans (by norm_num) (hI p hp).two_le)).1
    -- ---------- second moment ----------
    set A : ℕ → ℕ → ℝ :=
      fun p q => (((Finset.Icc a b).filter (fun n => p ∣ n ∧ q ∣ n)).card : ℝ) with hAdef
    have hC : ∀ p q : ℕ, A p q
        = ∑ n ∈ Finset.Icc a b, (if p ∣ n ∧ q ∣ n then (1 : ℝ) else 0) := by
      intro p q
      simp only [hAdef]
      rw [Finset.card_filter]
      push_cast
      rfl
    have hexp : ∑ n ∈ Finset.Icc a b, (((I.filter fun p => p ∣ n).card : ℝ)) ^ 2
        = ∑ p ∈ I, ∑ q ∈ I, A p q := by
      calc ∑ n ∈ Finset.Icc a b, (((I.filter fun p => p ∣ n).card : ℝ)) ^ 2
          = ∑ n ∈ Finset.Icc a b, (∑ p ∈ I, (if p ∣ n then (1 : ℝ) else 0))
              * (∑ q ∈ I, (if q ∣ n then (1 : ℝ) else 0)) := by
            apply Finset.sum_congr rfl
            intro n hn
            rw [hcoll n, sq]
        _ = ∑ n ∈ Finset.Icc a b, ∑ p ∈ I, ∑ q ∈ I,
              (if p ∣ n then (1 : ℝ) else 0) * (if q ∣ n then (1 : ℝ) else 0) := by
            apply Finset.sum_congr rfl
            intro n hn
            rw [Finset.sum_mul_sum]
        _ = ∑ p ∈ I, ∑ n ∈ Finset.Icc a b, ∑ q ∈ I,
              (if p ∣ n then (1 : ℝ) else 0) * (if q ∣ n then (1 : ℝ) else 0) :=
            Finset.sum_comm
        _ = ∑ p ∈ I, ∑ q ∈ I, ∑ n ∈ Finset.Icc a b,
              (if p ∣ n then (1 : ℝ) else 0) * (if q ∣ n then (1 : ℝ) else 0) := by
            apply Finset.sum_congr rfl
            intro p hp
            exact Finset.sum_comm
        _ = ∑ p ∈ I, ∑ q ∈ I, A p q := by
            apply Finset.sum_congr rfl
            intro p hp
            apply Finset.sum_congr rfl
            intro q hq
            rw [hC p q]
            apply Finset.sum_congr rfl
            intro n hn
            by_cases h1 : p ∣ n <;> by_cases h2 : q ∣ n <;> simp [h1, h2]
    have hdiag : ∑ p ∈ I, A p p ≤ (N : ℝ) * S + π := by
      have hAA : ∑ p ∈ I, A p p
          = ∑ p ∈ I, (((Finset.Icc a b).filter (fun n => p ∣ n)).card : ℝ) := by
        apply Finset.sum_congr rfl
        intro p hp
        simp only [hAdef]
        have h1 : (Finset.Icc a b).filter (fun n => p ∣ n ∧ p ∣ n)
            = (Finset.Icc a b).filter (fun n => p ∣ n) :=
          Finset.filter_congr (fun n hn => by simp)
        rw [h1]
      rw [hAA]
      have hle : ∑ p ∈ I, (((Finset.Icc a b).filter (fun n => p ∣ n)).card : ℝ)
          ≤ ∑ p ∈ I, ((N : ℝ) / (p : ℝ) + 1) := by
        apply Finset.sum_le_sum
        intro p hp
        exact (hbound p (le_trans (by norm_num) (hI p hp).two_le)).2
      have hval : ∑ p ∈ I, ((N : ℝ) / (p : ℝ) + 1) = (N : ℝ) * S + π := by
        rw [Finset.sum_add_distrib, hSsum, hπsum]
      linarith
    have hcarderase : ∀ p ∈ I, ((I.filter (fun q => q ≠ p)).card : ℝ) = π - 1 := by
      intro p hp
      have hf : I.filter (fun q => q ≠ p) = I.erase p := by
        ext q
        simp only [Finset.mem_filter, Finset.mem_erase]
        constructor
        · rintro ⟨h1, h2⟩; exact ⟨h2, h1⟩
        · rintro ⟨h1, h2⟩; exact ⟨h2, h1⟩
      have hpos : 1 ≤ I.card := Nat.succ_le_of_lt (Finset.card_pos.mpr ⟨p, hp⟩)
      rw [hf, Finset.card_erase_of_mem hp, hπdef, Nat.cast_sub hpos]
      norm_num
    have hoff : ∑ p ∈ I, ∑ q ∈ I.filter (fun q => q ≠ p), A p q
        ≤ (N : ℝ) * S ^ 2 + (π ^ 2 - π) := by
      have hstep : ∀ p ∈ I, ∑ q ∈ I.filter (fun q => q ≠ p), A p q
          ≤ (N : ℝ) / (p : ℝ) * S + (π - 1) := by
        intro p hp
        have hp2 : 2 ≤ p := (hI p hp).two_le
        have hb1 : ∑ q ∈ I.filter (fun q => q ≠ p), A p q
            ≤ ∑ q ∈ I.filter (fun q => q ≠ p), ((N : ℝ) / ((p : ℝ) * (q : ℝ)) + 1) := by
          apply Finset.sum_le_sum
          intro q hq
          rw [Finset.mem_filter] at hq
          have hpq : p ≠ q := fun h => hq.2 h.symm
          have hAeq : A p q = (((Finset.Icc a b).filter (fun n => p * q ∣ n)).card : ℝ) := by
            simp only [hAdef]
            have h1 : (Finset.Icc a b).filter (fun n => p ∣ n ∧ q ∣ n)
                = (Finset.Icc a b).filter (fun n => p * q ∣ n) :=
              Finset.filter_congr (fun n hn =>
                ⟨fun ⟨h1, h2⟩ => Nat.Prime.dvd_mul_of_dvd_ne hpq (hI p hp) (hI q hq.1) h1 h2,
                 fun h => ⟨dvd_trans (dvd_mul_right p q) h, dvd_trans (dvd_mul_left q p) h⟩⟩)
            rw [h1]
          rw [hAeq]
          simpa [Nat.cast_mul] using
            (hbound (p * q) (by nlinarith [hp2, (hI q hq.1).two_le])).2
        have hb2 : ∑ q ∈ I.filter (fun q => q ≠ p), ((N : ℝ) / ((p : ℝ) * (q : ℝ)) + 1)
            = (N : ℝ) / (p : ℝ) * (∑ q ∈ I.filter (fun q => q ≠ p), (1 : ℝ) / (q : ℝ))
              + ((I.filter (fun q => q ≠ p)).card : ℝ) := by
          rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
          congr 1
          · rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro q hq
            rw [div_mul_eq_div_div, div_eq_mul_one_div]
          · ring
        have hb3 : (∑ q ∈ I.filter (fun q => q ≠ p), (1 : ℝ) / (q : ℝ)) ≤ S := by
          rw [hSdef]
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
          · intro x hx; exact (Finset.mem_filter.mp hx).1
          · intro x hx _; positivity
        have hb4 : ((I.filter (fun q => q ≠ p)).card : ℝ) ≤ π - 1 := by
          rw [hcarderase p hp]
        calc ∑ q ∈ I.filter (fun q => q ≠ p), A p q
            ≤ ∑ q ∈ I.filter (fun q => q ≠ p), ((N : ℝ) / ((p : ℝ) * (q : ℝ)) + 1) := hb1
          _ = (N : ℝ) / (p : ℝ) * (∑ q ∈ I.filter (fun q => q ≠ p), (1 : ℝ) / (q : ℝ))
                + ((I.filter (fun q => q ≠ p)).card : ℝ) := hb2
          _ ≤ (N : ℝ) / (p : ℝ) * S + (π - 1) := by
              have hNN : (0 : ℝ) ≤ (N : ℝ) / (p : ℝ) := by positivity
              have hmm := mul_le_mul_of_nonneg_left hb3 hNN
              linarith
      calc ∑ p ∈ I, ∑ q ∈ I.filter (fun q => q ≠ p), A p q
          ≤ ∑ p ∈ I, ((N : ℝ) / (p : ℝ) * S + (π - 1)) := Finset.sum_le_sum hstep
        _ = (N : ℝ) * S ^ 2 + (π ^ 2 - π) := by
            rw [Finset.sum_add_distrib, ← Finset.sum_mul]
            congr 1
            · rw [hSsum]; ring
            · rw [Finset.sum_const, nsmul_eq_mul]; ring
    have hV : ∑ p ∈ I, ∑ q ∈ I, A p q ≤ (N : ℝ) * S + (N : ℝ) * S ^ 2 + π ^ 2 := by
      have hsplit : ∑ p ∈ I, ∑ q ∈ I, A p q
          = (∑ p ∈ I, A p p) + ∑ p ∈ I, ∑ q ∈ I.filter (fun q => q ≠ p), A p q := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro p hp
        have h := Finset.sum_filter_add_sum_filter_not I (fun q => q ≠ p) (fun q => A p q)
        rw [← h]
        have hfil : I.filter (fun q => ¬ (q ≠ p)) = {p} := by
          ext q
          simp only [Finset.mem_filter, Finset.mem_singleton]
          constructor
          · rintro ⟨-, hq⟩; exact of_not_not hq
          · intro hq; exact ⟨hq.symm ▸ hp, fun h => h hq⟩
        have hs : (∑ q ∈ I.filter (fun q => ¬ (q ≠ p)), A p q) = A p p := by
          rw [hfil, Finset.sum_singleton]
        rw [hs, add_comm]
      rw [hsplit]
      linarith
    -- ---------- assemble ----------
    have hsq : ∑ n ∈ Finset.Icc a b, (((I.filter fun p => p ∣ n).card : ℝ) - S) ^ 2
        = (∑ n ∈ Finset.Icc a b, (((I.filter fun p => p ∣ n).card : ℝ)) ^ 2)
          - 2 * S * (∑ n ∈ Finset.Icc a b, ((I.filter fun p => p ∣ n).card : ℝ))
          + ((Finset.Icc a b).card : ℝ) * S ^ 2 := by
      have h1 : ∀ n : ℕ, (((I.filter fun p => p ∣ n).card : ℝ) - S) ^ 2
          = (((I.filter fun p => p ∣ n).card : ℝ)) ^ 2
            - 2 * S * ((I.filter fun p => p ∣ n).card : ℝ) + S ^ 2 := fun n => by ring
      simp_rw [h1]
      rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul,
        ← Finset.mul_sum]
    have hcardN : ((Finset.Icc a b).card : ℝ) = (N : ℝ) := by
      rw [Nat.card_Icc, hNdef]
    have hfin : ∑ n ∈ Finset.Icc a b, (((I.filter fun p => p ∣ n).card : ℝ) - S) ^ 2
        ≤ (N : ℝ) * S + π ^ 2 + 2 * S * π := by
      have h2 : -2 * S * (∑ n ∈ Finset.Icc a b, ((I.filter fun p => p ∣ n).card : ℝ))
          ≤ -2 * S * ((N : ℝ) * S - π) := by
        have hh := mul_le_mul_of_nonneg_left hFirst (by positivity : (0:ℝ) ≤ 2 * S)
        linarith
      rw [hsq, hexp, hcardN]
      nlinarith [hV, h2]
    nlinarith [hfin]
  · have hempty : Finset.Icc a b = ∅ := by
      rw [← Finset.card_eq_zero, Nat.card_Icc]
      omega
    rw [hempty, Finset.sum_empty]
    have h1 : (0:ℝ) ≤ ((b + 1 - a : ℕ) : ℝ) := by positivity
    nlinarith [hSnn, hπnn, sq_nonneg π]

/-- The target lemma: the reciprocal sum over `[X₁,X₂]` of the integers coprime to the product
of the primes in `[P,Q]` is at most `8 / S`, where `S = ∑_{P ≤ p ≤ Q} 1/p`. -/
theorem coprimeRecipSum_tk (P Q X₁ X₂ : ℝ) (hP2 : 2 ≤ P) (hPQ : P ≤ Q) (hX1 : 1 ≤ X₁)
    (hX12 : X₁ ≤ X₂) (hX24 : X₂ ≤ 4 * X₁) (hQ2 : Q ^ 2 ≤ X₁)
    (hS : 1 ≤ ∑ p ∈ Work.BMF.primesIn P Q, 1 / (p : ℝ)) :
    (∑ n ∈ (Work.BMF.natIcc X₁ X₂).filter
        (fun n => n.Coprime (∏ p ∈ Work.BMF.primesIn P Q, p)), 1 / (n : ℝ))
      ≤ 8 / (∑ p ∈ Work.BMF.primesIn P Q, 1 / (p : ℝ)) := by
  classical
  simp only [Work.BMF.natIcc]
  set I : Finset ℕ := Work.BMF.primesIn P Q with hI_def
  set W : ℕ := ∏ p ∈ I, p with hW_def
  set a : ℕ := ⌈X₁⌉₊ with ha_def
  set b : ℕ := ⌊X₂⌋₊ with hb_def
  set S : ℝ := ∑ p ∈ I, (1 : ℝ) / (p : ℝ) with hS_def
  have hX1pos : 0 < X₁ := by linarith
  have ha1 : 1 ≤ a := by
    rw [ha_def]
    have h : (1 : ℝ) ≤ (⌈X₁⌉₊ : ℝ) := by
      have := Nat.le_ceil X₁; linarith
    exact_mod_cast h
  have hbX2 : (b : ℝ) ≤ X₂ := by rw [hb_def]; exact Nat.floor_le (by linarith)
  have hI_prime : ∀ p ∈ I, p.Prime := by
    intro p hp
    rw [hI_def] at hp
    simp only [Work.BMF.primesIn] at hp
    exact (Finset.mem_filter.mp hp).2
  -- the coprime predicate is `ω = 0`
  have hcop : ∀ n : ℕ, n.Coprime W ↔ ∀ p ∈ I, ¬ p ∣ n := by
    intro n
    rw [hW_def, Nat.coprime_prod_right_iff]
    constructor
    · intro h p hp
      have hp' := h p hp
      rwa [Nat.coprime_comm, (hI_prime p hp).coprime_iff_not_dvd] at hp'
    · intro h p hp
      rw [Nat.coprime_comm, (hI_prime p hp).coprime_iff_not_dvd]
      exact h p hp
  have hzero : ∀ n : ℕ, ((I.filter (fun p => p ∣ n)).card = 0) ↔ ∀ p ∈ I, ¬ p ∣ n := by
    intro n
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
  have hfil0 : (Finset.Icc a b).filter (fun n => n.Coprime W)
      = (Finset.Icc a b).filter (fun n => (I.filter (fun p => p ∣ n)).card = 0) :=
    Finset.filter_congr (fun n _ => (hcop n).trans (hzero n).symm)
  set F : Finset ℕ := (Finset.Icc a b).filter (fun n => (I.filter (fun p => p ∣ n)).card = 0)
    with hF_def
  rw [hfil0]
  have hsub : F ⊆ Finset.Icc a b := by
    intro n hn
    rw [hF_def] at hn
    exact (Finset.mem_filter.mp hn).1
  -- (1) the reciprocal sum is at most `#F / X₁`
  have hsum_le : (∑ n ∈ F, 1 / (n : ℝ)) ≤ (F.card : ℝ) / X₁ := by
    have hXn : ∀ n ∈ F, X₁ ≤ (n : ℝ) := by
      intro n hn
      have hn' : n ∈ Finset.Icc a b := hsub hn
      have ha_le : a ≤ n := (Finset.mem_Icc.mp hn').1
      have had : (a : ℝ) ≤ (n : ℝ) := by exact_mod_cast ha_le
      have haX1 : X₁ ≤ (a : ℝ) := by rw [ha_def]; exact Nat.le_ceil X₁
      linarith
    calc (∑ n ∈ F, 1 / (n : ℝ))
        ≤ ∑ n ∈ F, 1 / X₁ := by
          apply Finset.sum_le_sum
          intro n hn
          exact one_div_le_one_div_of_le hX1pos (hXn n hn)
      _ = (F.card : ℝ) * (1 / X₁) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ = (F.card : ℝ) / X₁ := by ring
  -- (2) Chebyshev
  have hcheb : (F.card : ℝ) * S ^ 2
      ≤ ∑ n ∈ Finset.Icc a b, (((I.filter (fun p => p ∣ n)).card : ℝ) - S) ^ 2 := by
    have h1 := Finset.sum_le_sum_of_subset_of_nonneg hsub
      (fun n hn hn' => sq_nonneg (((I.filter (fun p => p ∣ n)).card : ℝ) - S))
    have h2 : (∑ n ∈ F, (((I.filter (fun p => p ∣ n)).card : ℝ) - S) ^ 2)
        = (F.card : ℝ) * S ^ 2 := by
      have h3 : ∀ n ∈ F, (((I.filter (fun p => p ∣ n)).card : ℝ) - S) ^ 2 = S ^ 2 := by
        intro n hn
        rw [hF_def] at hn
        have hz : (I.filter (fun p => p ∣ n)).card = 0 := (Finset.mem_filter.mp hn).2
        rw [hz]
        norm_num
      rw [Finset.sum_congr rfl h3, Finset.sum_const, nsmul_eq_mul]
    rwa [h2] at h1
  -- (3) Turán–Kubilius
  have htk : ∑ n ∈ Finset.Icc a b, (((I.filter (fun p => p ∣ n)).card : ℝ) - S) ^ 2
      ≤ ((b + 1 - a : ℕ) : ℝ) * S + (I.card : ℝ) ^ 2 + 2 * (I.card : ℝ) * S := by
    have h := tk_variance a b ha1 I hI_prime
    rwa [← hS_def] at h
  -- (4) the arithmetic bound on the right-hand side
  have hbig : ((b + 1 - a : ℕ) : ℝ) * S + (I.card : ℝ) ^ 2 + 2 * (I.card : ℝ) * S
      ≤ 8 * X₁ * S := by
    have hSnn : 0 ≤ S := by linarith
    have hXL : 0 ≤ X₁ := by linarith
    have hIcardnn : (0 : ℝ) ≤ (I.card : ℝ) := by positivity
    have hN4 : ((b + 1 - a : ℕ) : ℝ) ≤ 4 * X₁ := by
      have h1 : (b + 1 - a : ℕ) ≤ b := by omega
      have h2 : ((b + 1 - a : ℕ) : ℝ) ≤ (b : ℝ) := by exact_mod_cast h1
      linarith
    have hIcardQ : ((I.card : ℕ) : ℝ) ≤ Q := by
      have hsubI : I ⊆ Finset.Icc 1 ⌊Q⌋₊ := by
        intro p hp
        rw [hI_def] at hp
        simp only [Work.BMF.primesIn] at hp
        obtain ⟨hp1, hp2⟩ := Finset.mem_filter.mp hp
        simp only [Work.BMF.natIcc, Finset.mem_Icc] at hp1
        exact Finset.mem_Icc.mpr ⟨hp2.one_lt.le, hp1.2⟩
      have h1 : I.card ≤ ⌊Q⌋₊ := by
        have h2 := Finset.card_le_card hsubI
        rw [Nat.card_Icc] at h2
        omega
      have h3 : ((⌊Q⌋₊ : ℕ) : ℝ) ≤ Q := Nat.floor_le (by linarith)
      exact (by exact_mod_cast h1 : ((I.card : ℕ) : ℝ) ≤ ((⌊Q⌋₊ : ℕ) : ℝ)).trans h3
    have hπ2 : (I.card : ℝ) ^ 2 ≤ X₁ :=
      (pow_le_pow_left₀ hIcardnn hIcardQ 2).trans hQ2
    have hSπ : S ≤ (I.card : ℝ) := by
      rw [hS_def]
      calc ∑ p ∈ I, (1 : ℝ) / (p : ℝ) ≤ ∑ p ∈ I, (1 : ℝ) := by
            apply Finset.sum_le_sum
            intro p hp
            have h1 : (1 : ℝ) ≤ (p : ℝ) := by
              have := (hI_prime p hp).one_lt.le
              exact_mod_cast this
            have := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) h1
            simpa using this
        _ = ((I.card : ℕ) : ℝ) := by rw [Finset.sum_const, nsmul_eq_mul, mul_one]
    have h1 : ((b + 1 - a : ℕ) : ℝ) * S ≤ 4 * X₁ * S :=
      mul_le_mul_of_nonneg_right hN4 hSnn
    have h2 : (I.card : ℝ) ^ 2 + 2 * (I.card : ℝ) * S ≤ 3 * X₁ := by
      have h3 : 2 * (I.card : ℝ) * S ≤ 2 * (I.card : ℝ) ^ 2 := by
        nlinarith [hSπ, hIcardnn]
      nlinarith [hπ2, h3]
    have h4 : 3 * X₁ ≤ 3 * X₁ * S := by nlinarith [hS, hXL]
    have h5 : 0 ≤ X₁ * S := mul_nonneg hXL hSnn
    linarith
  have hmid : (F.card : ℝ) * S ^ 2 ≤ 8 * X₁ * S := le_trans hcheb (le_trans htk hbig)
  have hSpos : 0 < S := by linarith
  have hcardBound : (F.card : ℝ) ≤ 8 * X₁ / S := by
    have h1 : (F.card : ℝ) * S ≤ 8 * X₁ := by
      have h2 : (F.card : ℝ) * S ^ 2 = ((F.card : ℝ) * S) * S := by ring
      have h3 : 8 * X₁ * S = (8 * X₁) * S := by ring
      rw [h2, h3] at hmid
      exact (mul_le_mul_iff_of_pos_right hSpos).mp hmid
    exact (le_div_iff₀ hSpos).mpr h1
  calc (∑ n ∈ F, 1 / (n : ℝ)) ≤ (F.card : ℝ) / X₁ := hsum_le
    _ ≤ (8 * X₁ / S) / X₁ := div_le_div_of_nonneg_right hcardBound (by linarith)
    _ = 8 / S := by
        rw [div_div]
        exact mul_div_mul_right 8 S (c := X₁) (ne_of_gt hX1pos)

end Work.BMF.mr_core
