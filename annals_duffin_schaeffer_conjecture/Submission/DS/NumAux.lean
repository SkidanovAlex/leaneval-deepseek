import Mathlib

open scoped Nat BigOperators

/-!
# Totatives in every short window (auxiliary for the non-decay zero-one reduction)

Let `k(q)` be the number of distinct prime factors of `q`.  We need the elementary
fact that every window of `2^(2k(q)+1)` consecutive natural numbers contains an integer
coprime to `q`.

The proof is by inclusion-exclusion over the subsets `S` of the distinct prime
factors of `q` (`q.primeFactors.powerset`):

`#{t < L : Coprime (b+t) q} = Σ_{S ⊆ PF(q)} (−1)^|S| · #{t < L : (∏_{p∈S} p) | b+t}`

because for a fixed `t` with `S₀ = {p ∈ PF(q) : p | b+t}`, the sum over `S ⊆ S₀` of
`(−1)^|S|` is `1` if `S₀ = ∅` (i.e. `Coprime (b+t) q`) and `0` otherwise.

Each inner count of multiples of `d = ∏_{p∈S} p` in an interval of `L` consecutive
integers is between `L/d − 1` and `L/d + 1`; summing gives

`T ≥ L·φ(q)/q − 2^k ≥ L/2^k − 2^k`,

so with `L = 2^(2k+1)`: `T ≥ 2^(k+1) − 2^k = 2^k ≥ 1`.
-/

namespace Submission.DS

/-! ## Counting multiples of `d` in a window of `L` consecutive integers -/

/-- `q ≤ L/d` for the natural division `L/d`. -/
lemma nat_div_le_real_div (L d : ℕ) : ((L / d : ℕ) : ℝ) ≤ (L : ℝ) / (d : ℝ) := by
  by_cases hd0 : d = 0
  · subst d; simp
  · have hd : 0 < d := Nat.pos_of_ne_zero hd0
    have hd' : 0 < (d : ℝ) := by exact_mod_cast hd
    rw [le_div_iff₀ hd']
    exact_mod_cast Nat.div_mul_le_self L d

/-- `L/d < q + 1` for the natural division `q = L/d`. -/
lemma real_div_lt_nat_div_add_one (L d : ℕ) : (L : ℝ) / (d : ℝ) < ((L / d : ℕ) : ℝ) + 1 := by
  by_cases hd0 : d = 0
  · subst d; simp
  · have hd : 0 < d := Nat.pos_of_ne_zero hd0
    have hmod : L % d < d := Nat.mod_lt L hd
    have hmain : L = (L / d) * d + L % d := by
      simpa [Nat.mul_comm] using (Nat.div_add_mod L d).symm
    have hlt : L < (L / d + 1) * d := by
      rw [add_mul, one_mul]
      nlinarith
    have hlt' : (L : ℝ) < (((L / d + 1) * d : ℕ) : ℝ) := by exact_mod_cast hlt
    have hd' : 0 < (d : ℝ) := by exact_mod_cast hd
    rw [div_lt_iff₀ hd']
    simpa [Nat.cast_mul, Nat.cast_add, Nat.cast_one] using hlt'

/-- The solutions of `d ∣ r+s` with `0 ≤ r,s < d` are exactly `s ≡ -r (mod d)`. -/
lemma sum_mod_eq_zero_iff (r s d : ℕ) (_hd : 0 < d) (hr : r < d) (hs : s < d) :
    (r + s) % d = 0 ↔ s = (d - r) % d := by
  constructor
  · intro h
    by_cases hr0 : r = 0
    · subst r
      have : s % d = 0 := by simpa using h
      have hs0 : s = 0 := by
        exact Nat.eq_zero_of_dvd_of_lt (Nat.dvd_iff_mod_eq_zero.mpr this) hs
      simp [hs0]
    · by_cases hlt : r + s < d
      · exfalso
        have : (r + s) % d = r + s := Nat.mod_eq_of_lt hlt
        omega
      · have hge : d ≤ r + s := by omega
        have hred : (r + s) % d = (r + s - d) % d := Nat.mod_eq_sub_mod hge
        have hsm : r + s - d < d := by omega
        have h0 : r + s - d = 0 := by
          have : (r + s - d) % d = 0 := by simpa [hred] using h
          exact (Nat.mod_eq_of_lt hsm).symm.trans this
        have hrs : r + s = d := by omega
        have hsdr : s = d - r := by omega
        have hdr_lt : d - r < d := by omega
        have hdr_mod : (d - r) % d = d - r := Nat.mod_eq_of_lt hdr_lt
        rw [hsdr, hdr_mod]
  · intro h
    by_cases hr0 : r = 0
    · subst r
      have hs0 : s = 0 := by simpa using h
      simp [hs0]
    · have hdr_lt : d - r < d := by omega
      have hdr_mod : (d - r) % d = d - r := Nat.mod_eq_of_lt hdr_lt
      have hs' : s = d - r := by rw [hdr_mod] at h; exact h
      have hrs : r + s = d := by omega
      simp [hrs]

/-- `d | b + t` is a congruence condition on `t` modulo `d`. -/
lemma modEq_dvd_add_iff (b t d : ℕ) (hd : 0 < d) :
    d ∣ b + t ↔ t ≡ (d - b % d) % d [MOD d] := by
  rw [Nat.ModEq]
  have hv : ((d - b % d) % d) % d = (d - b % d) % d := Nat.mod_mod _ _
  rw [hv]
  rw [Nat.dvd_iff_mod_eq_zero]
  have hr : b % d < d := Nat.mod_lt b hd
  have hs : t % d < d := Nat.mod_lt t hd
  rw [Nat.add_mod]
  exact sum_mod_eq_zero_iff (b % d) (t % d) d hd hr hs

/-- The number of `t < L` with `d | b+t` is either `⌊L/d⌋` or `⌈L/d⌉`. -/
lemma card_valid_window_bound (L b d : ℕ) (hd : 0 < d) :
    let m := ((Finset.range L).filter (fun t => d ∣ b + t)).card
    L / d ≤ m ∧ m ≤ L / d + 1 := by
  intro m
  let v := (d - b % d) % d
  have hcnt : m = Nat.count (fun t => t ≡ v [MOD d]) L := by
    dsimp [m, v]
    rw [Nat.count_eq_card_filter_range]
    congr 1
    ext t
    simp only [Finset.mem_filter, Finset.mem_range]
    rw [modEq_dvd_add_iff b t d hd]
  have hcnt2 := Nat.count_modEq_card (b := L) hd (v := v)
  constructor
  · rw [hcnt, hcnt2]
    by_cases h : v % d < L % d
    · simp [h]
    · simp [h]
  · rw [hcnt, hcnt2]
    by_cases h : v % d < L % d
    · simp [h]
    · simp [h]

/-- The window multiple count is within `1` of `L/d`. -/
lemma card_multiples_window_real (L b d : ℕ) (hd : 0 < d) :
    let m := ((Finset.range L).filter (fun t => d ∣ b + t)).card
    (m : ℝ) ≤ (L : ℝ) / (d : ℝ) + 1 ∧ (L : ℝ) / (d : ℝ) - 1 ≤ (m : ℝ) := by
  intro m
  have hb := card_valid_window_bound L b d hd
  constructor
  · have hle : (m : ℝ) ≤ ((L / d : ℕ) : ℝ) + 1 := by exact_mod_cast hb.2
    have hdvd : ((L / d : ℕ) : ℝ) ≤ (L : ℝ) / (d : ℝ) := nat_div_le_real_div L d
    nlinarith
  · have hge : ((L / d : ℕ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast hb.1
    have hlt : (L : ℝ) / (d : ℝ) < ((L / d : ℕ) : ℝ) + 1 := real_div_lt_nat_div_add_one L d
    nlinarith

/-! ## Inclusion--exclusion over the prime factors -/

/-- The alternating sum over a powerset. -/
lemma sum_powerset_neg_one_pow_card_real (x : Finset ℕ) :
    (∑ m ∈ x.powerset, ((-1 : ℝ) ^ m.card)) = if x = ∅ then (1 : ℝ) else 0 := by
  have hz : (∑ m ∈ x.powerset, ((-1 : ℤ) ^ m.card) : ℤ) = if x = ∅ then 1 else 0 :=
    Finset.sum_powerset_neg_one_pow_card (α := ℕ) (x := x)
  have hc := congrArg (fun z : ℤ => (z : ℝ)) hz
  rw [Int.cast_sum] at hc
  norm_num at hc
  simpa using hc

/-- A product of distinct primes divides `x` iff each of them divides `x`. -/
lemma prod_dvd_iff_all_dvd {q x : ℕ} {S : Finset ℕ} (hS : S ⊆ q.primeFactors) :
    (∏ p ∈ S, p) ∣ x ↔ ∀ p ∈ S, p ∣ x := by
  constructor
  · intro hdiv p hp
    exact (Finset.dvd_prod_of_mem (fun p => p) hp).trans hdiv
  · intro hdiv
    classical
    induction S using Finset.induction_on with
    | empty => simp
    | insert a r har ih =>
      rw [Finset.prod_insert har]
      refine Nat.Coprime.mul_dvd_of_dvd_of_dvd ?_ ?_ ?_
      · rw [Nat.coprime_prod_right_iff]
        intro p hp
        have hpa : a.Prime := (Nat.mem_primeFactors.mp (hS (by simp))).1
        have hpp : p.Prime := (Nat.mem_primeFactors.mp (hS (by simp [hp]))).1
        have hap : a ≠ p := by
          intro hsub
          subst a
          exact har hp
        exact (Nat.coprime_primes hpa hpp).2 hap
      · exact hdiv a (by simp)
      · exact ih (fun p hp => hS (by simp [hp])) (fun p hp => hdiv p (by simp [hp]))

/-- `x` is coprime to `q` iff no prime factor of `q` divides `x`. -/
lemma coprime_iff_forall_primeFactors_not_dvd {x q : ℕ} (hq : q ≠ 0) :
    x.Coprime q ↔ ∀ p ∈ q.primeFactors, ¬ p ∣ x := by
  constructor
  · intro hcop p hp hpx
    have hpq : p ∣ q := (Nat.mem_primeFactors.mp hp).2.1
    have hpp : p.Prime := (Nat.mem_primeFactors.mp hp).1
    have hpg : p ∣ x.gcd q := Nat.dvd_gcd hpx hpq
    have hg : x.gcd q = 1 := hcop
    have : p ∣ 1 := by simpa [hg] using hpg
    exact hpp.not_dvd_one this
  · intro h
    by_cases hcop : x.Coprime q
    · exact hcop
    · exfalso
      have hne : x.gcd q ≠ 1 := by simpa [Nat.Coprime] using hcop
      rcases Nat.exists_prime_and_dvd hne with ⟨p, hpp, hpg⟩
      have hpx : p ∣ x := hpg.trans (Nat.gcd_dvd_left x q)
      have hpq : p ∣ q := hpg.trans (Nat.gcd_dvd_right x q)
      have hpf : p ∈ q.primeFactors := Nat.Prime.mem_primeFactors hpp hpq hq
      exact h p hpf hpx

/-- Pointwise inclusion--exclusion for coprimality with `q`. -/
lemma indicator_coprime (q x : ℕ) (hq : q ≠ 0) :
    (if x.Coprime q then (1 : ℝ) else 0) =
      ∑ S ∈ q.primeFactors.powerset,
        (-1 : ℝ) ^ S.card * (if (∏ p ∈ S, p) ∣ x then 1 else 0) := by
  classical
  let bad : Finset ℕ := q.primeFactors.filter (fun p => p ∣ x)
  have hEq : (∑ S ∈ q.primeFactors.powerset,
        (-1 : ℝ) ^ S.card * (if (∏ p ∈ S, p) ∣ x then 1 else 0)) =
      ∑ S ∈ q.primeFactors.powerset,
        (-1 : ℝ) ^ S.card * (if S ⊆ bad then 1 else 0) := by
    apply Finset.sum_congr rfl
    intro S hS
    have hSsub : S ⊆ q.primeFactors := Finset.mem_powerset.mp hS
    have hiff : (∏ p ∈ S, p) ∣ x ↔ S ⊆ bad := by
      rw [prod_dvd_iff_all_dvd hSsub]
      constructor
      · intro h p hp
        exact Finset.mem_filter.mpr ⟨hSsub hp, h p hp⟩
      · intro h p hp
        exact (Finset.mem_filter.mp (h hp)).2
    by_cases hd : (∏ p ∈ S, p) ∣ x
    · have hs : S ⊆ bad := hiff.mp hd
      simp [hd, hs]
    · have hs : ¬ S ⊆ bad := fun hs => hd (hiff.mpr hs)
      simp [hd, hs]
  have hfilter : q.primeFactors.powerset.filter (fun S => S ⊆ bad) = bad.powerset := by
    ext S
    simp only [Finset.mem_filter, Finset.mem_powerset]
    constructor
    · rintro ⟨hSpf, hSb⟩
      exact hSb
    · intro hSb
      exact ⟨hSb.trans (Finset.filter_subset (fun p => p ∣ x) q.primeFactors), hSb⟩
  have hsum : (∑ S ∈ q.primeFactors.powerset,
        (-1 : ℝ) ^ S.card * (if S ⊆ bad then 1 else 0)) =
      (∑ S ∈ bad.powerset, (-1 : ℝ) ^ S.card) := by
    calc
      (∑ S ∈ q.primeFactors.powerset,
          (-1 : ℝ) ^ S.card * (if S ⊆ bad then 1 else 0))
          = ∑ S ∈ q.primeFactors.powerset, (if S ⊆ bad then (-1 : ℝ) ^ S.card else 0) := by
              apply Finset.sum_congr rfl
              intro S hS
              by_cases h : S ⊆ bad <;> simp [h]
      _ = ∑ S ∈ (q.primeFactors.powerset.filter (fun S => S ⊆ bad)), (-1 : ℝ) ^ S.card := by
              rw [← Finset.sum_filter]
      _ = ∑ S ∈ bad.powerset, (-1 : ℝ) ^ S.card := by rw [hfilter]
  have hbad : bad = ∅ ↔ x.Coprime q := by
    rw [show bad = q.primeFactors.filter (fun p => p ∣ x) by rfl]
    rw [Finset.filter_eq_empty_iff, coprime_iff_forall_primeFactors_not_dvd hq]
  have hpow : (∑ S ∈ bad.powerset, (-1 : ℝ) ^ S.card) = if bad = ∅ then (1 : ℝ) else 0 :=
    sum_powerset_neg_one_pow_card_real bad
  calc
    (if x.Coprime q then (1 : ℝ) else 0) = (if bad = ∅ then (1 : ℝ) else 0) := by
      by_cases hc : x.Coprime q
      · have hb : bad = ∅ := hbad.mpr hc
        simp [hc, hb]
      · have hb : bad ≠ ∅ := fun hz => hc (hbad.mp hz)
        simp [hc, hb]
    _ = (∑ S ∈ bad.powerset, (-1 : ℝ) ^ S.card) := hpow.symm
    _ = ∑ S ∈ q.primeFactors.powerset,
        (-1 : ℝ) ^ S.card * (if S ⊆ bad then 1 else 0) := hsum.symm
    _ = ∑ S ∈ q.primeFactors.powerset,
        (-1 : ℝ) ^ S.card * (if (∏ p ∈ S, p) ∣ x then 1 else 0) := hEq.symm

/-- Inclusion--exclusion for the number of totatives in `[b, b+L)`. -/
lemma count_IE (q b L : ℕ) (hq : q ≠ 0) :
    (((Finset.range L).filter (fun t => (b + t).Coprime q)).card : ℝ) =
      ∑ S ∈ q.primeFactors.powerset,
        (-1 : ℝ) ^ S.card *
          (((Finset.range L).filter (fun t => (∏ p ∈ S, p) ∣ b + t)).card : ℝ) := by
  classical
  calc
    (((Finset.range L).filter (fun t => (b + t).Coprime q)).card : ℝ)
        = ∑ t ∈ Finset.range L, (if (b + t).Coprime q then (1 : ℝ) else 0) := by
            rw [Finset.sum_boole]
    _ = ∑ t ∈ Finset.range L,
          (∑ S ∈ q.primeFactors.powerset,
            (-1 : ℝ) ^ S.card * (if (∏ p ∈ S, p) ∣ b + t then (1 : ℝ) else 0)) := by
            apply Finset.sum_congr rfl
            intro t ht
            exact (indicator_coprime q (b + t) hq)
    _ = ∑ S ∈ q.primeFactors.powerset,
          ∑ t ∈ Finset.range L,
            (-1 : ℝ) ^ S.card * (if (∏ p ∈ S, p) ∣ b + t then (1 : ℝ) else 0) := by
            rw [Finset.sum_comm]
    _ = ∑ S ∈ q.primeFactors.powerset,
          (-1 : ℝ) ^ S.card *
            (∑ t ∈ Finset.range L, (if (∏ p ∈ S, p) ∣ b + t then (1 : ℝ) else 0)) := by
            apply Finset.sum_congr rfl
            intro S hS
            rw [← Finset.mul_sum]
    _ = ∑ S ∈ q.primeFactors.powerset,
          (-1 : ℝ) ^ S.card *
            (((Finset.range L).filter (fun t => (∏ p ∈ S, p) ∣ b + t)).card : ℝ) := by
            apply Finset.sum_congr rfl
            intro S hS
            rw [Finset.sum_boole]

/-! ## The main term: an alternating sum becomes a product -/

/-- The sum over `q.primeFactors.powerset` of `∏ (1/p)` type terms: expansion of the product. -/
lemma psum_eq_prod (q : ℕ) :
    (∑ S ∈ q.primeFactors.powerset,
        (-1 : ℝ) ^ S.card * (1 / ∏ p ∈ S, (p : ℝ))) =
      ∏ p ∈ q.primeFactors, (1 - (1 : ℝ) / (p : ℝ)) := by
  classical
  rw [Finset.prod_sub (s := q.primeFactors) (f := fun _ : ℕ => (1 : ℝ))
    (g := fun p : ℕ => (1 : ℝ) / (p : ℝ))]
  apply Finset.sum_congr rfl
  intro t ht
  have hpf : (∏ p ∈ q.primeFactors \ t, (1 : ℝ)) = 1 := by simp
  have hden : (∏ p ∈ t, (1 : ℝ) / (p : ℝ)) = 1 / ∏ p ∈ t, (p : ℝ) := by
    rw [Finset.prod_div_distrib]
    simp
  calc
    (-1 : ℝ) ^ t.card * (1 / ∏ p ∈ t, (p : ℝ))
        = ((-1 : ℝ) ^ t.card * (∏ p ∈ q.primeFactors \ t, (1 : ℝ))) *
            (∏ p ∈ t, (1 : ℝ) / (p : ℝ)) := by
              rw [hpf, hden]
              ring
    _ = ((-1 : ℝ) ^ t.card * ∏ p ∈ q.primeFactors \ t, (1 : ℝ)) *
            ∏ p ∈ t, (1 : ℝ) / (p : ℝ) := rfl

/-- The alternating sum with the window length factored out equals `L·∏(1−1/p)`. -/
lemma main_eq_prod (q L : ℕ) :
    (∑ S ∈ q.primeFactors.powerset,
        (-1 : ℝ) ^ S.card * ((L : ℝ) / ∏ p ∈ S, (p : ℝ))) =
      (L : ℝ) * ∏ p ∈ q.primeFactors, (1 - (1 : ℝ) / (p : ℝ)) := by
  classical
  calc
    (∑ S ∈ q.primeFactors.powerset,
        (-1 : ℝ) ^ S.card * ((L : ℝ) / ∏ p ∈ S, (p : ℝ)))
        = (∑ S ∈ q.primeFactors.powerset,
            (-1 : ℝ) ^ S.card * (1 / ∏ p ∈ S, (p : ℝ))) * (L : ℝ) := by
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro S hS
            ring
    _ = (∏ p ∈ q.primeFactors, (1 - (1 : ℝ) / (p : ℝ))) * (L : ℝ) := by
            rw [psum_eq_prod q]
    _ = (L : ℝ) * ∏ p ∈ q.primeFactors, (1 - (1 : ℝ) / (p : ℝ)) := by ring

/-- Each factor `1 − 1/p ≥ 1/2`, so the product is at least `2^{-k}`. -/
lemma prod_one_sub_inv_ge (q : ℕ) :
    (1 / 2 : ℝ) ^ q.primeFactors.card ≤
      ∏ p ∈ q.primeFactors, (1 - (1 : ℝ) / (p : ℝ)) := by
  classical
  rw [← Finset.prod_const (s := q.primeFactors) ((1 / 2 : ℝ))]
  refine Finset.prod_le_prod₀ (s := q.primeFactors)
    (f := fun _ : ℕ => (1 / 2 : ℝ))
    (g := fun p : ℕ => 1 - (1 : ℝ) / (p : ℝ)) ?h0 ?h1
  · intro p hp
    norm_num
  · intro p hp
    have hpp : p.Prime := (Nat.mem_primeFactors.mp hp).1
    have hp2 : 2 ≤ (p : ℝ) := by exact_mod_cast (Nat.Prime.two_le hpp)
    have hp0 : 0 < (p : ℝ) := by exact_mod_cast hpp.pos
    have hfrac : (1 : ℝ) / (p : ℝ) ≤ 1 / 2 := by
      rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
      field_simp [hp0.ne']
      nlinarith
    nlinarith

/-- subset products over prime factors are positive -/
lemma prod_primeFactors_pos {q : ℕ} {S : Finset ℕ} (hS : S ⊆ q.primeFactors) :
    0 < ∏ p ∈ S, p := by
  exact Finset.prod_pos (fun p hp => (Nat.mem_primeFactors.mp (hS hp)).1.pos)

/-- casting a product of naturals into ℝ -/
lemma cast_prod_prime (S : Finset ℕ) : (((∏ p ∈ S, p) : ℕ) : ℝ) = ∏ p ∈ S, (p : ℝ) := by
  simp

/-- The per-subset multiple counts are within `1` of `L / ∏_{p∈S} p`. -/
lemma err_bound (q b L : ℕ) {S : Finset ℕ} (hS : S ⊆ q.primeFactors) :
    |(((Finset.range L).filter (fun t => (∏ p ∈ S, p) ∣ b + t)).card : ℝ)
      - (L : ℝ) / ∏ p ∈ S, (p : ℝ)| ≤ 1 := by
  have hd : 0 < ∏ p ∈ S, p := prod_primeFactors_pos hS
  have hb := card_multiples_window_real L b (∏ p ∈ S, p) hd
  have hc : (((∏ p ∈ S, p) : ℕ) : ℝ) = ∏ p ∈ S, (p : ℝ) := cast_prod_prime S
  have hb' : |(((Finset.range L).filter (fun t => (∏ p ∈ S, p) ∣ b + t)).card : ℝ)
      - (L : ℝ) / (∏ p ∈ S, (p : ℝ))| ≤ 1 := by
    rw [← hc]
    -- use hb
    have h1 : (((Finset.range L).filter (fun t => (∏ p ∈ S, p) ∣ b + t)).card : ℝ)
        ≤ (L : ℝ) / (((∏ p ∈ S, p) : ℕ) : ℝ) + 1 := by
      simpa using hb.1
    have h2 : (L : ℝ) / (((∏ p ∈ S, p) : ℕ) : ℝ) - 1
        ≤ (((Finset.range L).filter (fun t => (∏ p ∈ S, p) ∣ b + t)).card : ℝ) := by
      simpa using hb.2
    -- |x − y| ≤ 1 from y − 1 ≤ x and x ≤ y + 1
    rw [abs_le]
    constructor
    · nlinarith
    · nlinarith
  simpa using hb'

/-! ## The main theorem -/

/-- Every window of `2^(2k+1)` consecutive naturals contains an integer coprime to `q`,
where `k` is the number of distinct prime factors of `q`. -/
theorem totative_in_window (q b : ℕ) (hq : 1 ≤ q) :
    ∃ t : ℕ, t < 2 ^ (2 * q.primeFactors.card + 1) ∧ Nat.Coprime (b + t) q := by
  classical
  let k := q.primeFactors.card
  let L := 2 ^ (2 * k + 1)
  have hq0 : q ≠ 0 := by omega
  let C : Finset ℕ := (Finset.range L).filter (fun t => (b + t).Coprime q)
  -- A real lower bound for the number of totatives in the window
  have hC : (L : ℝ) * (1 / 2 : ℝ) ^ k - (2 : ℝ) ^ k ≤ (C.card : ℝ) := by
    -- inclusion-exclusion
    have hIE := count_IE q b L hq0
    -- main term and error term
    let main := ∑ S ∈ q.primeFactors.powerset,
        (-1 : ℝ) ^ S.card * ((L : ℝ) / ∏ p ∈ S, (p : ℝ))
    let rest := ∑ S ∈ q.primeFactors.powerset,
        (-1 : ℝ) ^ S.card *
          ((((Finset.range L).filter (fun t => (∏ p ∈ S, p) ∣ b + t)).card : ℝ)
            - (L : ℝ) / ∏ p ∈ S, (p : ℝ))
    have hsplit : (C.card : ℝ) = main + rest := by
      dsimp [C, main, rest]
      -- hIE says C = Σ (-1)^card · mS; need to rewrite as main + rest by splitting each term
      calc
        (((Finset.range L).filter (fun t => (b + t).Coprime q)).card : ℝ)
            = ∑ S ∈ q.primeFactors.powerset,
                (-1 : ℝ) ^ S.card *
                  (((Finset.range L).filter (fun t => (∏ p ∈ S, p) ∣ b + t)).card : ℝ) := hIE
        _ = ∑ S ∈ q.primeFactors.powerset,
                ((-1 : ℝ) ^ S.card * ((L : ℝ) / ∏ p ∈ S, (p : ℝ)) +
                 (-1 : ℝ) ^ S.card *
                  ((((Finset.range L).filter (fun t => (∏ p ∈ S, p) ∣ b + t)).card : ℝ)
                    - (L : ℝ) / ∏ p ∈ S, (p : ℝ))) := by
                apply Finset.sum_congr rfl
                intro S hS
                ring
        _ = main + rest := by
                dsimp [main, rest]
                rw [Finset.sum_add_distrib]
    -- bound on the error
    have herr : |rest| ≤ (2 : ℝ) ^ k := by
      dsimp [rest]
      calc
        |∑ S ∈ q.primeFactors.powerset,
            (-1 : ℝ) ^ S.card *
              ((((Finset.range L).filter (fun t => (∏ p ∈ S, p) ∣ b + t)).card : ℝ)
                - (L : ℝ) / ∏ p ∈ S, (p : ℝ))|
            ≤ ∑ S ∈ q.primeFactors.powerset,
                |(-1 : ℝ) ^ S.card *
                  ((((Finset.range L).filter (fun t => (∏ p ∈ S, p) ∣ b + t)).card : ℝ)
                    - (L : ℝ) / ∏ p ∈ S, (p : ℝ))| := by
                exact Finset.abs_sum_le_sum_abs _ _
        _ = ∑ S ∈ q.primeFactors.powerset,
                |(((Finset.range L).filter (fun t => (∏ p ∈ S, p) ∣ b + t)).card : ℝ)
                    - (L : ℝ) / ∏ p ∈ S, (p : ℝ)| := by
                apply Finset.sum_congr rfl
                intro S hS
                simp [abs_mul]
        _ ≤ ∑ S ∈ q.primeFactors.powerset, (1 : ℝ) := by
                apply Finset.sum_le_sum
                intro S hS
                exact err_bound q b L (Finset.mem_powerset.mp hS)
        _ = (q.primeFactors.powerset.card : ℝ) := by simp
        _ = (2 : ℝ) ^ q.primeFactors.card := by
                rw [Finset.card_powerset]
                norm_num
        _ = (2 : ℝ) ^ k := by dsimp [k]
    have herr' : - (2 : ℝ) ^ k ≤ rest := (abs_le.mp herr).1
    -- main term
    have hmain : main = (L : ℝ) * ∏ p ∈ q.primeFactors, (1 - (1 : ℝ) / (p : ℝ)) := by
      dsimp [main]
      exact main_eq_prod q L
    have hprod : (1 / 2 : ℝ) ^ k ≤ ∏ p ∈ q.primeFactors, (1 - (1 : ℝ) / (p : ℝ)) := by
      dsimp [k]
      exact prod_one_sub_inv_ge q
    nlinarith
  -- plug in L = 2^(2k+1)
  have hLval : (L : ℝ) = (2 : ℝ) ^ (2 * k + 1) := by
    dsimp [L]
    rw [Nat.cast_pow]
    norm_num
  have hpow : (2 : ℝ) ^ (2 * k + 1) * (1 / 2 : ℝ) ^ k = (2 : ℝ) ^ (k + 1) := by
    have hk : 2 * k + 1 = (k + 1) + k := by omega
    rw [hk, pow_add]
    have hmul : (2 : ℝ) ^ k * (1 / 2 : ℝ) ^ k = 1 := by
      rw [← mul_pow]
      norm_num
    rw [mul_assoc, hmul, mul_one]
  have hbig1 : (1 : ℝ) ≤ (2 : ℝ) ^ k := by
    exact one_le_pow₀ (by norm_num : (1 : ℝ) ≤ (2 : ℝ))
  have hge2 : (2 : ℝ) ^ (k + 1) - (2 : ℝ) ^ k ≥ (1 : ℝ) := by
    have h2 : (2 : ℝ) ^ (k + 1) = (2 : ℝ) ^ k * 2 := by rw [pow_succ]
    have hdiff : (2 : ℝ) ^ (k + 1) - (2 : ℝ) ^ k = (2 : ℝ) ^ k := by
      rw [h2]
      ring
    rw [hdiff]
    exact hbig1
  have hone : (1 : ℝ) ≤ (C.card : ℝ) := by
    have hc2 : (L : ℝ) * (1 / 2 : ℝ) ^ k - (2 : ℝ) ^ k ≥ (1 : ℝ) := by
      rw [hLval]
      rw [hpow]
      exact hge2
    exact le_trans hc2 hC
  have hnat : 1 ≤ C.card := by
    exact_mod_cast hone
  -- a nonempty set of totatives
  have hne : C.Nonempty := Finset.card_pos.mp hnat
  rcases hne with ⟨t, htC⟩
  refine ⟨t, ?_, ?_⟩
  · have htL : t ∈ Finset.range L := (Finset.mem_filter.mp htC).1
    exact (Finset.mem_range.mp htL).trans_le (by dsimp [L]; exact Nat.le_refl _)
  · exact (Finset.mem_filter.mp htC).2

end Submission.DS
