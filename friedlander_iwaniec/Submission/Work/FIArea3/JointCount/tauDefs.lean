import Mathlib

namespace Work.FIArea3.JointCount

/-! ## Bounding the divisor function `τ(n) = n.divisors.card`.

We prove `τ(n) ≤ exp (1.5 * log (n+2) / log (log (n+2)))`. -/

/-- The optimal per-prime "loss" function. -/
noncomputable def Bval (t : ℝ) : ℝ :=
  if t ≤ 1/2 then Real.log (1/t) - 1 + t
  else if t < Real.log 2 then Real.log 2 - t else 0

lemma nat_add_one_le_two_pow (a : ℕ) : a + 1 ≤ 2 ^ a := by
  induction a with
  | zero => norm_num
  | succ n ih =>
    rw [pow_succ]
    have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    omega

/-- `log (a+1) ≤ a * log 2` for `a : ℕ`. -/
lemma log_natCast_add_one_le (a : ℕ) :
    Real.log ((a:ℝ) + 1) ≤ (a:ℝ) * Real.log 2 := by
  have haux : ((a:ℝ) + 1) ≤ (2:ℝ)^a := by
    have h := nat_add_one_le_two_pow a
    have : ((2:ℝ)^a) = ((2:ℕ)^a : ℝ) := by push_cast; ring
    rw [this]
    exact_mod_cast h
  have h2 := Real.log_le_log (by positivity) haux
  rw [Real.log_pow 2 a] at h2
  linarith [h2]

/-- For `0 < x`, `log (1/x) = - log x`. -/
lemma log_one_div (x : ℝ) : Real.log (1/x) = - Real.log x := by
  rw [one_div, Real.log_inv]

/-- `log (a+1) ≤ t * a + Bval t` for `a ≥ 1` and `t > 0`. -/
lemma log_add_one_le {t : ℝ} (ht : 0 < t) {a : ℕ} (ha : 1 ≤ a) :
    Real.log ((a:ℝ) + 1) ≤ t * (a:ℝ) + Bval t := by
  by_cases ht' : t ≤ 1/2
  · rw [Bval, if_pos ht']
    rw [log_one_div]
    have hx : 0 < ((a:ℝ) + 1) * t := by positivity
    have hlog : Real.log (((a:ℝ)+1) * t) ≤ ((a:ℝ)+1) * t - 1 :=
      Real.log_le_sub_one_of_pos hx
    rw [Real.log_mul (by positivity) (ne_of_gt ht)] at hlog
    linarith [hlog]
  · rw [Bval, if_neg ht']
    by_cases ht2 : t < Real.log 2
    · rw [if_pos ht2]
      have ht_ge : (1:ℝ)/2 ≤ t := le_of_lt (not_le.mp ht')
      by_cases ha1 : a = 1
      · subst ha1; norm_num
      · have ha2 : 2 ≤ a := by omega
        have h1 : Real.log ((a:ℝ)+1) ≤ Real.log 2 + ((a:ℝ)-1)/2 := by
          have hsplit : Real.log ((a:ℝ)+1) = Real.log 2 + Real.log (((a:ℝ)+1)/2) := by
            rw [← Real.log_mul (by norm_num) (by positivity)]; congr 1; ring
          rw [hsplit]
          have h2 : Real.log (((a:ℝ)+1)/2) ≤ ((a:ℝ)+1)/2 - 1 :=
            Real.log_le_sub_one_of_pos (by positivity)
          have h3 : ((a:ℝ)+1)/2 - 1 = ((a:ℝ)-1)/2 := by ring
          linarith [h2, h3]
        have h4 : ((a:ℝ)-1)/2 ≤ t * ((a:ℝ)-1) := by
          have hann : (0:ℝ) ≤ (a:ℝ)-1 := by
            have : (1:ℝ) ≤ (a:ℝ) := by exact_mod_cast ha
            linarith
          nlinarith [ht_ge, hann]
        have heq : t * (a:ℝ) + (Real.log 2 - t) = Real.log 2 + t * ((a:ℝ)-1) := by ring
        rw [heq]; linarith [h1, h4]
    · rw [if_neg ht2]
      have ht_ge : Real.log 2 ≤ t := not_lt.mp ht2
      have h1 := log_natCast_add_one_le a
      have h2 : (a:ℝ) * Real.log 2 ≤ (a:ℝ) * t :=
        mul_le_mul_of_nonneg_left ht_ge (by positivity)
      linarith [h1, h2]


/-- `1 - 1/x ≤ log x` for `x > 0`. -/
lemma one_sub_inv_le_log {x : ℝ} (hx : 0 < x) : 1 - 1/x ≤ Real.log x := by
  have h : Real.log (1/x) ≤ 1/x - 1 := Real.log_le_sub_one_of_pos (by positivity)
  rw [log_one_div] at h
  linarith

/-- `Bval` is nonnegative on `(0,∞)`. -/
lemma Bval_nonneg {t : ℝ} (ht : 0 < t) : 0 ≤ Bval t := by
  rw [Bval]
  split_ifs with h1 h2
  · rw [log_one_div]
    have := Real.log_le_sub_one_of_pos ht
    linarith
  · have h2' : t < Real.log 2 := h2
    linarith
  · rfl

/-- `Bval t = 0` for `log 2 ≤ t`. -/
lemma Bval_eq_zero {t : ℝ} (ht : Real.log 2 ≤ t) : Bval t = 0 := by
  rw [Bval]
  split_ifs with h1 h2
  · have h2 := Real.log_two_gt_d9
    have := le_trans ht h1
    linarith
  · exact absurd h2 (not_lt.mpr ht)
  · rfl

/-- `Bval` is antitone on `(0,∞)`. -/
lemma Bval_antitoneOn : AntitoneOn Bval (Set.Ioi 0) := by
  intro a ha b hb hab
  simp only [Set.mem_Ioi] at ha hb
  have hb0 : 0 < b := hb
  have ha0 : 0 < a := ha
  by_cases hb1 : b ≤ 1/2
  · have ha1 : a ≤ 1/2 := le_trans hab hb1
    rw [Bval, if_pos hb1, Bval, if_pos ha1]
    have h0 : Real.log (1/b) - Real.log (1/a) = Real.log (a/b) := by
      rw [log_one_div, log_one_div]
      rw [show - Real.log b - - Real.log a = Real.log a - Real.log b by ring]
      rw [← Real.log_div (ne_of_gt ha0) (ne_of_gt hb0)]
    have key : Real.log (1/b) - Real.log (1/a) ≤ a - b := by
      rw [h0]
      have h1 : Real.log (a/b) ≤ a/b - 1 := Real.log_le_sub_one_of_pos (by positivity)
      have h3 : a/b - 1 ≤ a - b := by
        rw [div_sub_one hb0.ne', div_le_iff₀ hb0]
        nlinarith [hb1, sub_nonneg.mpr hab]
      linarith [h1, h3]
    linarith [key]
  · rw [Bval, if_neg hb1]
    by_cases hb2 : b < Real.log 2
    · rw [if_pos hb2]
      have hbge : (1:ℝ)/2 ≤ b := le_of_lt (not_le.mp hb1)
      by_cases ha1 : a ≤ 1/2
      · rw [Bval, if_pos ha1]
        have hlog : 1 - 1/(1/(2*a)) ≤ Real.log (1/(2*a)) :=
          one_sub_inv_le_log (by positivity)
        have hsimp : 1/(1/(2*a)) = 2*a := by rw [one_div, one_div, inv_inv]
        rw [hsimp] at hlog
        have hla : Real.log (1/a) = Real.log 2 + Real.log (1/(2*a)) := by
          rw [← Real.log_mul (by norm_num) (by positivity)]
          congr 1
          field_simp
        rw [hla]
        linarith [hlog, hab]
      · rw [Bval, if_neg ha1, if_pos (lt_of_le_of_lt hab hb2)]
        linarith
    · rw [Bval, if_neg hb2]
      exact Bval_nonneg ha0


/-- Weight for the `k`-th dyadic block: `#{primes in [2^k,2^(k+1))} ≤ cweight k`. -/
noncomputable def cweight (k : ℕ) : ℝ :=
  if k = 0 then 0 else if k = 1 then 2 else (2:ℝ)^(k-1)

/-- The dyadic majorant of `∑_{p prime} Bval (log p / u)`. -/
noncomputable def SBtau (u : ℝ) : ℝ :=
  ∑ k ∈ Finset.range (Nat.ceil u + 1), cweight k * Bval (k * Real.log 2 / u)

/-- `log (a+1) ≤ t * a + Bval t` for all `a : ℕ` and `t > 0`. -/
lemma log_add_one_le' {t : ℝ} (ht : 0 < t) (a : ℕ) :
    Real.log ((a:ℝ) + 1) ≤ t * (a:ℝ) + Bval t := by
  rcases Nat.eq_zero_or_pos a with h | h
  · subst h; simp only [Nat.cast_zero, zero_add, Real.log_one]
    have := Bval_nonneg ht; linarith
  · exact log_add_one_le ht h

/-- The odd numbers in `[2^j, 2^(j+1))` number at most `2^(j-1)`. -/
lemma card_odd_dyadic (j : ℕ) :
    ((Finset.Icc (2^j) (2^(j+1)-1)).filter (fun m => Odd m)).card ≤ 2^(j-1) := by
  cases j with
  | zero => decide
  | succ j =>
    set B := (Finset.Icc (2^(j+1)) (2^(j+2)-1)).filter (fun m => Odd m)
    have hmaps : Set.MapsTo (fun m => m/2) ↑B ↑(Finset.Icc (2^j) (2^(j+1)-1)) := by
      intro m hm
      simp only [Finset.mem_coe, B, Finset.mem_filter, Finset.mem_Icc] at hm ⊢
      obtain ⟨⟨hm1, hm2⟩, c, hc⟩ := hm
      constructor
      · have h := Nat.div_le_div_right hm1 (c:=2)
        have h2 : 2^(j+1)/2 = 2^j := by omega
        omega
      · have h := Nat.div_le_div_right hm2 (c:=2)
        have h2 : (2^(j+2)-1)/2 = 2^(j+1)-1 := by
          have hh : 2^(j+2) = 2 * 2^(j+1) := by rw [pow_succ]; ring
          rw [hh]; omega
        omega
    have hinj : Set.InjOn (fun m => m/2) ↑B := by
      intro a ha b hb hab
      change a/2 = b/2 at hab
      simp only [Finset.mem_coe, B, Finset.mem_filter] at ha hb
      obtain ⟨_, c, hc⟩ := ha; obtain ⟨_, d, hd⟩ := hb
      omega
    calc B.card ≤ (Finset.Icc (2^j) (2^(j+1)-1)).card := Finset.card_le_card_of_injOn _ hmaps hinj
      _ = 2^j := by
          rw [Nat.card_Icc]
          have hh : 2^(j+1) = 2 * 2^j := by rw [pow_succ]; ring
          rw [hh]; have := Nat.one_le_two_pow (n:=j); omega

/-- Fibre bound: primes in `S` with `Nat.log2 p = k` number at most `cweight k`. -/
lemma card_log2_fiber_le (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) (k : ℕ) :
    (S.filter (fun p => Nat.log2 p = k)).card ≤ cweight k := by
  rcases k with _ | j
  · have hempty : S.filter (fun p => Nat.log2 p = 0) = ∅ := by
      rw [Finset.filter_eq_empty_iff]
      intro p hp hp0
      have h2 : 2 ≤ p := (hS p hp).two_le
      have : 1 ≤ Nat.log2 p := (Nat.le_log2 (by omega)).mpr h2
      omega
    rw [hempty, Finset.card_empty, cweight, if_pos rfl]
    norm_num
  · rcases Nat.eq_zero_or_pos j with hj | hj
    · subst hj
      have hsub : S.filter (fun p => Nat.log2 p = 1) ⊆ ({2, 3} : Finset ℕ) := by
        intro p hp
        rw [Finset.mem_filter] at hp
        obtain ⟨hpS, hpk⟩ := hp
        have h2 : 2 ≤ p := (hS p hpS).two_le
        have hlt : p < 2^(1+1) := (Nat.log2_eq_iff (by omega : p ≠ 0)).mp hpk |>.2
        simp only [Finset.mem_insert, Finset.mem_singleton]
        omega
      have hcard := Finset.card_le_card hsub
      have hc : (({2,3}:Finset ℕ).card) = 2 := by decide
      rw [hc] at hcard
      calc ((S.filter (fun p => Nat.log2 p = 1)).card : ℝ) ≤ (2:ℝ) := by exact_mod_cast hcard
        _ = cweight 1 := by rw [cweight]; norm_num
    · have hsub : S.filter (fun p => Nat.log2 p = j+1) ⊆
          (Finset.Icc (2^(j+1)) (2^(j+2)-1)).filter (fun m => Odd m) := by
        intro p hp
        rw [Finset.mem_filter] at hp
        obtain ⟨hpS, hpk⟩ := hp
        have hpp := hS p hpS
        have h2 : 2 ≤ p := hpp.two_le
        have hiff := (Nat.log2_eq_iff (by omega : p ≠ 0)).mp hpk
        have hlt : p < 2^(j+2) := by rw [show j+1+1 = j+2 by omega] at hiff; exact hiff.2
        have hge : 2^(j+1) ≤ p := hiff.1
        refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hge, by omega⟩, ?_⟩
        apply hpp.odd_of_ne_two
        have h4 : 2^2 ≤ 2^(j+1) := by apply Nat.pow_le_pow_right <;> omega
        omega
      have hcard := Finset.card_le_card hsub
      have hd := card_odd_dyadic (j+1)
      rw [show j+1+1 = j+2 by omega] at hd
      rw [show j+1-1 = j by omega] at hd
      calc ((S.filter (fun p => Nat.log2 p = j+1)).card : ℝ)
          ≤ ((2:ℝ)^j) := by exact_mod_cast le_trans hcard hd
        _ = cweight (j+1) := by
            rw [cweight, if_neg (by omega : ¬(j+1=0)), if_neg (by omega : ¬(j+1=1))]
            rw [show j+1-1 = j by omega]

/-- Dyadic bound on the sum of `Bval (log p / u)` over a finset of primes. -/
lemma sum_Bval_prime_le (u : ℝ) (hu : 0 < u) (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime) :
    ∑ p ∈ S, Bval (Real.log p / u) ≤ SBtau u := by
  classical
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set M := S.sup Nat.log2 with hM
  set g : ℕ → Fin (M+1) := fun p => ⟨min (Nat.log2 p) M, Nat.lt_succ_of_le (min_le_right _ _)⟩ with hg
  have hgS : ∀ p ∈ S, (g p : ℕ) = Nat.log2 p := by
    intro p hp
    simp only [hg, Fin.val_mk]
    exact min_eq_left (Finset.le_sup (f := Nat.log2) hp)
  set F : ℕ → ℝ := fun j => Bval ((j:ℝ) * Real.log 2 / u) with hF
  have hstep1 : ∑ p ∈ S, Bval (Real.log p / u) ≤ ∑ p ∈ S, F (g p) := by
    apply Finset.sum_le_sum
    intro p hp
    have hp2 : 2 ≤ p := (hS p hp).two_le
    have hp0 : p ≠ 0 := by omega
    have hge : (2:ℝ)^(g p : ℕ) ≤ (p:ℝ) := by
      rw [hgS p hp]
      have := (Nat.log2_eq_iff hp0).mp rfl
      exact_mod_cast this.1
    have hlog := Real.log_le_log (by positivity) hge
    rw [Real.log_pow] at hlog
    have hnum : ((g p : ℕ) : ℝ) * Real.log 2 / u ≤ Real.log (p:ℝ) / u := by
      apply div_le_div_of_nonneg_right _ hu.le
      have : ((g p : ℕ) : ℝ) * Real.log 2 ≤ Real.log (p:ℝ) := by
        have := hlog; push_cast at this; linarith
      linarith
    have hge1 : 1 ≤ (g p : ℕ) := by
      rw [hgS p hp]; exact (Nat.le_log2 hp0).mpr (by simpa using hp2)
    have hposa : 0 < ((g p : ℕ) : ℝ) * Real.log 2 / u :=
      div_pos (mul_pos (by exact_mod_cast hge1) hlog2pos) hu
    have hpos : 0 < Real.log (p:ℝ) / u :=
      div_pos (Real.log_pos (by exact_mod_cast (by omega : 1 < p))) hu
    exact Bval_antitoneOn hposa hpos hnum
  have hfib := Finset.sum_fiberwise' S g (fun j : Fin (M+1) => F (j:ℕ))
  have hsum : ∑ j : Fin (M+1), ∑ p ∈ S.filter (fun p => g p = j), F (j:ℕ)
      ≤ ∑ j : Fin (M+1), cweight (j:ℕ) * F (j:ℕ) := by
    apply Finset.sum_le_sum
    intro j _
    rw [Finset.sum_const, nsmul_eq_mul]
    rcases Nat.eq_zero_or_pos (j:ℕ) with hj0 | hj0
    · rw [hj0, show cweight 0 = 0 by rw [cweight, if_pos rfl]]
      simp only [Nat.cast_zero, zero_mul, zero_div, hF, Bval]
      rw [if_pos (by norm_num : (0:ℝ) ≤ 1/2)]
      simp only [Real.log_zero, div_zero, zero_sub, add_zero]
      nlinarith [Nat.cast_nonneg (α:=ℝ) (S.filter (fun p => g p = j)).card]
    · have hsub : S.filter (fun p => g p = j) ⊆ S.filter (fun p => Nat.log2 p = (j:ℕ)) := by
        intro p hp
        rw [Finset.mem_filter] at hp ⊢
        exact ⟨hp.1, by rw [← hgS p hp.1, hp.2]⟩
      have hcard : ((S.filter (fun p => g p = j)).card : ℝ) ≤ cweight (j:ℕ) :=
        le_trans (by exact_mod_cast Finset.card_le_card hsub) (card_log2_fiber_le S hS (j:ℕ))
      have hc : 0 ≤ F (j:ℕ) := Bval_nonneg (by positivity)
      exact mul_le_mul_of_nonneg_right hcard hc
  have hFin : ∑ j : Fin (M+1), cweight (j:ℕ) * F (j:ℕ)
      = ∑ j ∈ Finset.range (M+1), cweight j * F j := by
    rw [Finset.sum_fin_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [Finset.mem_range] at hi
    rw [dif_pos hi]
  have hzero : ∀ j, Nat.ceil u ≤ j → cweight j * F j = 0 := by
    intro j hj
    have huj : u ≤ (j:ℝ) := by
      have h1 : (Nat.ceil u : ℝ) ≤ (j:ℝ) := by exact_mod_cast hj
      linarith [Nat.le_ceil u]
    have hFzero : F j = 0 := by
      rw [hF]
      apply Bval_eq_zero
      rw [le_div_iff₀ hu]; nlinarith [hlog2pos, huj]
    rw [hFzero, mul_zero]
  have hnn : ∀ j, 0 ≤ cweight j * F j := by
    intro j
    rcases Nat.eq_zero_or_pos j with hj0 | hj0
    · rw [hj0, show cweight 0 = 0 by rw [cweight, if_pos rfl], zero_mul]
    · rw [hF]
      exact mul_nonneg (by rw [cweight]; split_ifs <;> positivity) (Bval_nonneg (by positivity))
  have hcomp : ∑ j ∈ Finset.range (M+1), cweight j * F j
      ≤ ∑ j ∈ Finset.range (Nat.ceil u + 1), cweight j * F j := by
    by_cases h : M+1 ≤ Nat.ceil u + 1
    · apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro x hx; simp only [Finset.mem_range] at hx ⊢; omega
      · intro x hx hx2; exact hnn x
    · have hN : M+1 = (Nat.ceil u + 1) + (M+1 - (Nat.ceil u + 1)) := by omega
      conv_lhs => rw [hN, Finset.sum_range_add]
      rw [add_le_iff_nonpos_right]
      apply Finset.sum_nonpos
      intro i hi
      simp only [Finset.mem_range] at hi
      rw [hzero (Nat.ceil u + 1 + i) (by omega)]
  rw [SBtau]
  calc ∑ p ∈ S, Bval (Real.log p / u)
      ≤ ∑ p ∈ S, F (g p) := hstep1
    _ = ∑ j : Fin (M+1), ∑ p ∈ S.filter (fun p => g p = j), F (j:ℕ) := hfib.symm
    _ ≤ ∑ j : Fin (M+1), cweight (j:ℕ) * F (j:ℕ) := hsum
    _ = ∑ j ∈ Finset.range (M+1), cweight j * F j := hFin
    _ ≤ ∑ j ∈ Finset.range (Nat.ceil u + 1), cweight j * F j := hcomp

/-- `log τ(n) ≤ log n / u + SBtau u`. -/
lemma log_card_divisors_le (n : ℕ) (hn : 1 ≤ n) (u : ℝ) (hu : 0 < u) :
    Real.log (n.divisors.card : ℝ) ≤ Real.log (n:ℝ) / u + SBtau u := by
  have hn0 : n ≠ 0 := by omega
  have hlogτ : Real.log (n.divisors.card : ℝ)
      = ∑ p ∈ n.primeFactors, Real.log ((n.factorization p : ℝ) + 1) := by
    have hcast : (n.divisors.card : ℝ)
        = ∏ p ∈ n.primeFactors, ((n.factorization p : ℝ) + 1) := by
      rw [Nat.card_divisors hn0, Nat.cast_prod]
      exact Finset.prod_congr rfl (fun p hp => by push_cast; ring)
    rw [hcast, Real.log_prod]
    intro p hp; exact ne_of_gt (by positivity)
  have hsumlog : ∑ p ∈ n.primeFactors, ((n.factorization p : ℕ) : ℝ) * Real.log (p:ℝ)
      = Real.log (n:ℝ) := by
    have hnat := Nat.prod_primeFactors_pow_factorization hn0
    have hmprod : ((n:ℝ)) = ∏ p ∈ n.primeFactors, (p:ℝ) ^ (n.factorization p) := by
      conv_lhs => rw [hnat]
      push_cast
      rfl
    rw [hmprod, Real.log_prod]
    · apply Finset.sum_congr rfl
      intro p hp
      rw [Real.log_pow]
    · intro p hp
      have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
      exact pow_ne_zero _ (Nat.cast_ne_zero.mpr hpp.ne_zero)
  rw [hlogτ]
  calc ∑ p ∈ n.primeFactors, Real.log ((n.factorization p : ℝ) + 1)
      ≤ ∑ p ∈ n.primeFactors,
          (Real.log (p:ℝ) / u * (n.factorization p : ℝ) + Bval (Real.log (p:ℝ) / u)) := by
        apply Finset.sum_le_sum
        intro p hp
        have hpprime : p.Prime := Nat.prime_of_mem_primeFactors hp
        have hp0 : 0 < Real.log (p:ℝ) := Real.log_pos (by exact_mod_cast hpprime.one_lt)
        exact log_add_one_le' (div_pos hp0 hu) (n.factorization p)
    _ = Real.log (n:ℝ) / u + ∑ p ∈ n.primeFactors, Bval (Real.log (p:ℝ) / u) := by
        rw [Finset.sum_add_distrib]
        congr 1
        rw [← hsumlog, Finset.sum_div]
        apply Finset.sum_congr rfl
        intro p hp; ring
    _ ≤ Real.log (n:ℝ) / u + SBtau u := by
        have := sum_Bval_prime_le u hu n.primeFactors (fun p hp => Nat.prime_of_mem_primeFactors hp)
        linarith

/-- `SBtau 3 ≤ 2`. -/
lemma SBtau_three_le : SBtau 3 ≤ 2 := by
  have hloglog2 : -(2:ℝ)/5 ≤ Real.log (Real.log 2) := by
    have h1 : Real.exp (-(2:ℝ)/5) ≤ Real.log 2 := by
      have he : Real.exp (-(2:ℝ)/5) = (Real.exp ((2:ℝ)/5))⁻¹ := by
        rw [show -(2:ℝ)/5 = -((2:ℝ)/5) by ring, Real.exp_neg]
      have h2 : (1.4641:ℝ) ≤ Real.exp ((2:ℝ)/5) := by
        have h := Real.sum_le_exp_of_nonneg (by norm_num : (0:ℝ) ≤ (2:ℝ)/5) 5
        rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
            Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero] at h
        norm_num at h
        linarith
      calc Real.exp (-(2:ℝ)/5) = (Real.exp ((2:ℝ)/5))⁻¹ := he
        _ ≤ ((1.4641:ℝ))⁻¹ := (inv_le_inv₀ (Real.exp_pos _) (by norm_num)).mpr h2
        _ ≤ Real.log 2 := by
            have h' : ((1.4641:ℝ))⁻¹ ≤ 0.6931471803 := by norm_num
            linarith [Real.log_two_gt_d9, h']
    have := Real.log_le_log (Real.exp_pos (-(2:ℝ)/5)) h1
    rwa [Real.log_exp] at this
  have hlog3 : Real.log 3 ≤ 1.0987 := by
    rw [Real.log_le_iff_le_exp (by norm_num : (0:ℝ)<3)]
    have h := Real.sum_le_exp_of_nonneg (by norm_num : (0:ℝ) ≤ (1.0987:ℝ)) 12
    norm_num [Finset.sum_range_succ] at h ⊢
    linarith
  have hlog2le : Real.log 2 ≤ 0.6931471808 := le_of_lt Real.log_two_lt_d9
  have hlog2ge : (0.6931471803:ℝ) ≤ Real.log 2 := le_of_lt Real.log_two_gt_d9
  rw [SBtau, show Nat.ceil (3:ℝ) = 3 by norm_num]
  rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_succ,
      Finset.sum_range_succ, Finset.sum_range_zero]
  simp only [cweight, zero_mul, add_zero]
  norm_num
  have hBval0 : Bval (Real.log 2) = 0 := by
    rw [Bval, if_neg (by linarith [hlog2ge] : ¬ Real.log 2 ≤ 1/2),
        if_neg (by linarith : ¬ Real.log 2 < Real.log 2)]
  rw [hBval0]
  have hb1 : Bval (Real.log 2/3) ≤ 0.73 := by
    rw [Bval, if_pos (by linarith [hlog2le] : Real.log 2/3 ≤ 1/2)]
    rw [show (1:ℝ)/(Real.log 2/3) = 3/Real.log 2 by field_simp]
    rw [Real.log_div (by norm_num) (ne_of_gt (Real.log_pos (by norm_num)))]
    linarith [hlog3, hloglog2, hlog2le]
  have hb2 : Bval (2*Real.log 2/3) ≤ 0.27 := by
    rw [Bval, if_pos (by linarith [hlog2le] : 2*Real.log 2/3 ≤ 1/2)]
    rw [show (1:ℝ)/(2*Real.log 2/3) = 3/(2*Real.log 2) by field_simp]
    rw [Real.log_div (by norm_num) (by positivity),
        Real.log_mul (by norm_num) (ne_of_gt (Real.log_pos (by norm_num)))]
    linarith [hlog3, hloglog2, hlog2le, hlog2ge]
  linarith [hb1, hb2]

end Work.FIArea3.JointCount
