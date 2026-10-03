import Mathlib

set_option maxHeartbeats 1000000

open Finset
open scoped BigOperators

namespace Work.FIArea3

/-! ## Auxiliary lemmas toward FI Lemma 2.2 -/

/-- Divisor count of a product of powers of a finset of primes:
`τ(∏ p^{e p}) = ∏ (e p + 1)`. -/
lemma card_divisors_prime_pow_prod (s : Finset ℕ) (hs : ∀ p ∈ s, Nat.Prime p) (e : ℕ → ℕ) :
    (∏ p ∈ s, p ^ e p).divisors.card = ∏ p ∈ s, (e p + 1) := by
  classical
  revert hs
  refine Finset.induction (motive := fun S => (∀ p ∈ S, Nat.Prime p) →
      (∏ p ∈ S, p ^ e p).divisors.card = ∏ p ∈ S, (e p + 1)) ?_ ?_ s
  · intro _
    simp
  · intro a T ha ih hs
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    have hT : ∀ p ∈ T, Nat.Prime p := fun p hp => hs p (Finset.mem_insert_of_mem hp)
    have ha' : Nat.Prime a := hs a (Finset.mem_insert_self a T)
    have hcop : Nat.Coprime (a ^ e a) (∏ p ∈ T, p ^ e p) :=
      (Nat.Coprime.prod_right fun p hp =>
        (ha'.coprime_iff_not_dvd.mpr (fun hd =>
          ha ((Nat.prime_dvd_prime_iff_eq ha' (hT p hp)).mp hd ▸ hp))).pow_right (e p)).pow_left (e a)
    rw [Nat.Coprime.card_divisors_mul hcop, ih hT, Nat.divisors_prime_pow ha']
    simp

/-- Factorization of a product of powers of a finset of primes. -/
lemma factorization_finset_prod_pow {s : Finset ℕ} {e : ℕ → ℕ}
    (hs : ∀ p ∈ s, Nat.Prime p) (p : ℕ) :
    (∏ q ∈ s, q ^ e q).factorization p = if p ∈ s then e p else 0 := by
  have hne : ∀ q ∈ s, q ^ e q ≠ 0 := fun q hq => pow_ne_zero _ (hs q hq).ne_zero
  have hfac : (∏ q ∈ s, q ^ e q).factorization = ∑ q ∈ s, Finsupp.single q (e q) := by
    rw [Nat.factorization_prod hne]
    refine Finset.sum_congr rfl ?_
    intro q hq
    rw [Nat.factorization_pow, (hs q hq).factorization, Finsupp.smul_single, smul_eq_mul, mul_one]
  rw [hfac, Finsupp.finsetSum_apply]
  rw [show (∑ i ∈ s, (Finsupp.single i (e i)) p) = ∑ i ∈ s, (if i = p then e i else 0) from
    Finset.sum_congr rfl (fun i _ => Finsupp.single_apply)]
  rw [Finset.sum_ite_eq']

/-! ### The squarefree case (Lemma 1 of the companion paper) -/

lemma prod_take_eq_prod_range_getD (L : List ℕ) :
    ∀ m : ℕ, (L.take m).prod = ∏ i ∈ Finset.range m, L.getD i 1 := by
  induction L with
  | nil => intro m; simp
  | cons a t ih =>
      intro m
      cases m with
      | zero => simp
      | succ m =>
          have hP : (∏ i ∈ Finset.range m, t.getD i 1) =
              ∏ i ∈ Finset.range m, (a :: t).getD (i + 1) 1 := by
            apply Finset.prod_congr rfl
            intro i _
            simp
          calc
            ((a :: t).take (m + 1)).prod = (a :: t.take m).prod := by rw [List.take_succ_cons]
            _ = a * (t.take m).prod := by simp
            _ = a * (∏ i ∈ Finset.range m, t.getD i 1) := by rw [ih m]
            _ = (∏ i ∈ Finset.range m, t.getD i 1) * a := by rw [Nat.mul_comm]
            _ = (∏ i ∈ Finset.range m, (a :: t).getD (i + 1) 1) * a := by rw [hP]
            _ = ∏ i ∈ Finset.range (m + 1), (a :: t).getD i 1 := by
              rw [Finset.prod_range_succ']
              simp

lemma prod_range_block {f : ℕ → ℕ} (k s : ℕ) :
    (∏ i ∈ Finset.range s, ∏ j ∈ Finset.range k, f (k * i + j)) =
      ∏ m ∈ Finset.range (k * s), f m := by
  induction s with
  | zero => simp
  | succ s ih =>
      calc
        (∏ i ∈ Finset.range (s + 1), ∏ j ∈ Finset.range k, f (k * i + j))
            = (∏ i ∈ Finset.range s, ∏ j ∈ Finset.range k, f (k * i + j)) *
                (∏ j ∈ Finset.range k, f (k * s + j)) := by
              rw [Finset.prod_range_succ]
        _ = (∏ m ∈ Finset.range (k * s), f m) * (∏ j ∈ Finset.range k, f (k * s + j)) := by
              rw [ih]
        _ = ∏ m ∈ Finset.range (k * s + k), f m := by
              rw [Finset.prod_range_add]
        _ = ∏ m ∈ Finset.range (k * (s + 1)), f m := by
              rw [show k * (s + 1) = k * s + k by ring]

lemma prod_pow_le_prod_blocks (f : ℕ → ℕ) {k s : ℕ} (hk : 1 ≤ k)
    (hf : ∀ ⦃i j : ℕ⦄, i ≤ j → j < k * s → f i ≤ f j) :
    (∏ i ∈ Finset.range s, f i) ^ k ≤ ∏ m ∈ Finset.range (k * s), f m := by
  calc
    (∏ i ∈ Finset.range s, f i) ^ k = ∏ i ∈ Finset.range s, (f i) ^ k := by
      rw [← Finset.prod_pow]
    _ = ∏ i ∈ Finset.range s, ∏ j ∈ Finset.range k, f i := by
      apply Finset.prod_congr rfl
      intro i _
      rw [Finset.prod_const, Finset.card_range]
    _ ≤ ∏ i ∈ Finset.range s, ∏ j ∈ Finset.range k, f (k * i + j) := by
      apply Finset.prod_le_prod₀
      · intro i _; exact Nat.zero_le _
      · intro i hi
        have hi_lt : i < s := by simpa using hi
        apply Finset.prod_le_prod₀
        · intro j _; exact Nat.zero_le _
        · intro j hj
          have hj_lt : j < k := by simpa using hj
          refine hf ?_ ?_
          · have hi2 : i ≤ k * i := by
              have h : i ≤ i * k := Nat.le_mul_of_pos_right i (lt_of_lt_of_le zero_lt_one hk)
              simpa [Nat.mul_comm] using h
            exact le_trans hi2 (Nat.le_add_right (k * i) j)
          · have hi1 : i + 1 ≤ s := Nat.succ_le_of_lt hi_lt
            have hm : (i + 1) * k ≤ s * k := Nat.mul_le_mul_right k hi1
            have hjk : j + 1 ≤ k := Nat.succ_le_of_lt hj_lt
            nlinarith
    _ = ∏ m ∈ Finset.range (k * s), f m := prod_range_block k s

lemma take_prod_pow_le_take_prod {L : List ℕ} {k s : ℕ} (hk : 1 ≤ k)
    (hs : k * s ≤ L.length) (hsorted : L.SortedLE) :
    (L.take s).prod ^ k ≤ (L.take (k * s)).prod := by
  let f : ℕ → ℕ := fun i => L.getD i 1
  have hf : ∀ ⦃i j : ℕ⦄, i ≤ j → j < k * s → f i ≤ f j := by
    intro i j hij hj
    have hjL : j < L.length := lt_of_lt_of_le hj hs
    have hiL : i < L.length := lt_of_le_of_lt hij hjL
    dsimp [f]
    rw [List.getD_eq_getElem L 1 hiL, List.getD_eq_getElem L 1 hjL]
    have hmono : Monotone L.get := List.SortedLE.monotone_get hsorted
    have hfin : (⟨i, hiL⟩ : Fin L.length) ≤ ⟨j, hjL⟩ := by simpa using hij
    exact hmono hfin
  have hblk := prod_pow_le_prod_blocks f hk hf
  calc
    (L.take s).prod ^ k = (∏ i ∈ Finset.range s, f i) ^ k := by
      rw [prod_take_eq_prod_range_getD L s]
    _ ≤ ∏ m ∈ Finset.range (k * s), f m := hblk
    _ = (L.take (k * s)).prod := by
      rw [prod_take_eq_prod_range_getD L (k * s)]

lemma le_mul_div_add_one {r k : ℕ} (hk : 1 ≤ k) : r ≤ k * (r / k + 1) := by
  have hkpos : 0 < k := lt_of_lt_of_le zero_lt_one hk
  have hlt : r < k * (r / k + 1) := by
    calc
      r = k * (r / k) + r % k := (Nat.div_add_mod r k).symm
      _ < k * (r / k) + k := Nat.add_lt_add_left (Nat.mod_lt r hkpos) (k * (r / k))
      _ = k * (r / k + 1) := by ring
  exact le_of_lt hlt

lemma card_primeFactors_eq_length {x : ℕ} (hsq : Squarefree x) :
    (x.primeFactors).card = (x.primeFactorsList).length := by
  have hnd : x.primeFactorsList.Nodup := hsq.nodup_primeFactorsList
  have hEq : x.primeFactors = x.primeFactorsList.toFinset := by
    ext p
    rw [List.mem_toFinset]
    exact Nat.mem_primeFactors_iff_mem_primeFactorsList
  rw [hEq]
  exact List.toFinset_card_of_nodup hnd

lemma s_le_card_primeFactors {d : ℕ} (hd0 : d ≠ 0) {s : ℕ} {p : Fin s → ℕ}
    (hpri : ∀ i, (p i).Prime) (hdiv : ∀ i, p i ∣ d) (hinj : Function.Injective p) :
    s ≤ (d.primeFactors).card := by
  classical
  let f : Fin s ↪ {x // x ∈ d.primeFactors} :=
    { toFun := fun i => ⟨p i, Nat.Prime.mem_primeFactors (hpri i) (hdiv i) hd0⟩
      inj' := by intro i j h; exact hinj (by simpa using congrArg Subtype.val h) }
  have hcard := Fintype.card_le_of_embedding (α := Fin s) (β := {x // x ∈ d.primeFactors}) f
  simpa [Fintype.card_fin, Fintype.card_coe] using hcard

lemma tau_card_of_squarefree {x : ℕ} (hsq : Squarefree x) :
    x.divisors.card = 2 ^ (x.primeFactors).card := by
  classical
  have hprod1 : (∏ p ∈ x.primeFactors, p ^ (1 : ℕ)) = x := by
    rw [Finset.prod_congr rfl (fun p _ => by rw [pow_one])]
    exact Nat.prod_primeFactors_of_squarefree hsq
  calc x.divisors.card = (∏ p ∈ x.primeFactors, p ^ (1 : ℕ)).divisors.card := by rw [hprod1]
    _ = ∏ p ∈ x.primeFactors, (2 : ℕ) := by
          rw [card_divisors_prime_pow_prod x.primeFactors
            (fun p hp => (Nat.mem_primeFactors.mp hp).1) (fun _ => 1)]
    _ = 2 ^ (x.primeFactors).card := Finset.prod_const 2

theorem squarefree_tau_bound {k n : ℕ} (hk : 2 ≤ k) (hn : 1 ≤ n) (hsq : Squarefree n) :
    ∃ d : ℕ, d ∣ n ∧ d ^ k ≤ n ∧ n.divisors.card ≤ (2 * d.divisors.card) ^ k := by
  rcases eq_or_lt_of_le hn with h | h
  · subst h
    refine ⟨1, one_dvd 1, by simp, ?_⟩
    rw [Nat.divisors_one, Finset.card_singleton, mul_one]
    exact Nat.one_le_pow k 2 (by norm_num)
  · have hn0 : n ≠ 0 := by omega
    let L : List ℕ := n.primeFactorsList
    let r : ℕ := L.length
    let s : ℕ := r / k
    let d : ℕ := (L.take s).prod
    have hs_le_r : s ≤ L.length := by
      dsimp [s, r]; exact Nat.div_le_self L.length k
    have hs_ks : k * s ≤ L.length := by
      dsimp [s, r]
      have hh := Nat.div_mul_le_self L.length k
      simpa [Nat.mul_comm] using hh
    have hprod : L.prod = n := by
      dsimp [L]; exact Nat.prod_primeFactorsList hn0
    have hsort : L.SortedLE := by dsimp [L]; exact Nat.primeFactorsList_sorted n
    have hnd : L.Nodup := by dsimp [L]; exact hsq.nodup_primeFactorsList
    have hprim : ∀ p ∈ L, p.Prime := by
      dsimp [L]; intro p hp; exact Nat.prime_of_mem_primeFactorsList hp
    have hposL : 0 < L.prod := by rw [hprod]; omega
    have hdvd0 : d ∣ n := by
      dsimp [d]
      refine ⟨(L.drop s).prod, ?_⟩
      calc
        n = L.prod := hprod.symm
        _ = (L.take s).prod * (L.drop s).prod := (List.prod_take_mul_prod_drop L s).symm
    have hpow0 : d ^ k ≤ n := by
      dsimp [d]
      have h1 := take_prod_pow_le_take_prod (L := L) (k := k) (s := s) (by omega) hs_ks hsort
      calc
        (L.take s).prod ^ k ≤ (L.take (k * s)).prod := h1
        _ ≤ L.prod := by
              have hdvd2 : (L.take (k * s)).prod ∣ L.prod :=
                (List.take_sublist (k * s) L).prod_dvd_prod
              exact Nat.le_of_dvd hposL hdvd2
        _ = n := hprod
    have htau_n : n.divisors.card = 2 ^ r := by
      rw [tau_card_of_squarefree hsq, card_primeFactors_eq_length hsq]
    have hsq_d : Squarefree d := hsq.squarefree_of_dvd hdvd0
    have hd0 : d ≠ 0 := ne_of_gt (Nat.pos_of_dvd_of_pos hdvd0 (by omega))
    have hs_le_omega_d : s ≤ (d.primeFactors).card := by
      classical
      let p : Fin s → ℕ := fun i => L.get ⟨i.1, lt_of_lt_of_le i.2 hs_le_r⟩
      have hpri : ∀ i, (p i).Prime := by
        intro i
        dsimp [p]
        exact hprim _ (List.get_mem L ⟨i.1, lt_of_lt_of_le i.2 hs_le_r⟩)
      have hdiv : ∀ i, p i ∣ d := by
        intro i
        dsimp [d, p]
        have hlen : i.1 < (L.take s).length := by
          rw [List.length_take, Nat.min_eq_left hs_le_r]; exact i.2
        have hmem : L.get ⟨i.1, lt_of_lt_of_le i.2 hs_le_r⟩ ∈ L.take s := by
          have heq : L.get ⟨i.1, lt_of_lt_of_le i.2 hs_le_r⟩ =
              (L.take s).get ⟨i.1, hlen⟩ := by
            rw [List.get_eq_getElem, List.get_eq_getElem, List.getElem_take]
          rw [heq]
          exact List.get_mem (L.take s) ⟨i.1, hlen⟩
        exact List.dvd_prod hmem
      have hinj : Function.Injective p := by
        let q : Fin s → Fin L.length := fun i => ⟨i.1, lt_of_lt_of_le i.2 hs_le_r⟩
        have hinj_q : Function.Injective q := by
          intro i j hij
          apply Fin.ext
          have hv := congrArg (fun x : Fin L.length => x.1) hij
          simpa [q] using hv
        change Function.Injective (fun i => L.get (q i))
        exact hnd.injective_get.comp hinj_q
      exact s_le_card_primeFactors hd0 hpri hdiv hinj
    have htau_d_ge : 2 ^ s ≤ d.divisors.card := by
      rw [tau_card_of_squarefree hsq_d]
      exact pow_le_pow_right₀ (by norm_num : (1 : ℕ) ≤ 2) hs_le_omega_d
    have hs_le_ks1 : r ≤ k * (s + 1) := by
      dsimp [s]; exact le_mul_div_add_one (r := r) (by omega : 1 ≤ k)
    refine ⟨d, hdvd0, hpow0, ?_⟩
    calc
      n.divisors.card = 2 ^ r := htau_n
      _ ≤ (2 * 2 ^ s) ^ k := by
            have h_eq : (2 * 2 ^ s) ^ k = 2 ^ (k * (s + 1)) := by
              calc
                (2 * 2 ^ s) ^ k = (2 ^ (s + 1)) ^ k := by congr 1; rw [pow_succ']
                _ = 2 ^ ((s + 1) * k) := by rw [pow_mul]
                _ = 2 ^ (k * (s + 1)) := by congr 1; rw [Nat.mul_comm]
            rw [h_eq]
            exact pow_le_pow_right₀ (by norm_num : (1 : ℕ) ≤ 2) hs_le_ks1
      _ ≤ (2 * d.divisors.card) ^ k := by
            apply Nat.pow_le_pow_left
            exact Nat.mul_le_mul_left 2 htau_d_ge

/-! ### The general case -/

lemma mul_le_pow_self {m k : ℕ} (hm : 2 ≤ m) (hk : 1 ≤ k) : k * m ≤ m ^ k := by
  have h2k : k ≤ 2 ^ (k - 1) := by have := Nat.lt_two_pow_self (n := k - 1); omega
  calc k * m ≤ m ^ (k - 1) * m := by
        apply Nat.mul_le_mul_right
        exact le_trans h2k (Nat.pow_le_pow_left hm _)
    _ = m ^ k := by
        conv_rhs => rw [show k = k - 1 + 1 by omega, pow_succ]

lemma le_pow_div_add_one {k α : ℕ} (hk : 0 < k) (hα : k ≤ α) :
    α + 1 ≤ (α / k + 1) ^ k := by
  have hmod : α % k < k := Nat.mod_lt α hk
  have hq : 1 ≤ α / k := (Nat.one_le_div_iff hk).mpr hα
  have hαeq : α = k * (α / k) + α % k := (Nat.div_add_mod α k).symm
  have hstep : α + 1 ≤ k * (α / k + 1) := by
    have h1 : α + 1 = k * (α / k) + α % k + 1 := by nth_rewrite 1 [hαeq]; ring
    rw [h1]
    have : α % k + 1 ≤ k := by omega
    nlinarith
  exact le_trans hstep (mul_le_pow_self (by omega) (by omega))

lemma pow_nat_le_rpow_of_le {r k : ℕ} {c : ℝ} (hk : 2 ≤ k) (hc : 1 ≤ c)
    (h : (2 : ℝ) ^ r ≤ c ^ k) : (k : ℝ) ^ r ≤ c ^ ((k : ℝ) * Real.logb 2 k) := by
  have hlogb : 0 ≤ Real.logb 2 k :=
    Real.logb_nonneg (by norm_num) (by exact_mod_cast (by omega : 1 ≤ k))
  have hc0 : 0 ≤ c := le_trans zero_le_one hc
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (by omega : 0 < k)
  have h2 : (2 : ℝ) ^ Real.logb 2 k = (k : ℝ) := Real.rpow_logb (by norm_num) (by norm_num) hk0
  calc (k : ℝ) ^ r = ((2 : ℝ) ^ Real.logb 2 k) ^ r := by rw [h2]
    _ = ((2 : ℝ) ^ Real.logb 2 k) ^ (r : ℝ) := by rw [Real.rpow_natCast]
    _ = (2 : ℝ) ^ (Real.logb 2 k * r) := by rw [Real.rpow_mul (by norm_num)]
    _ = (2 : ℝ) ^ (r * Real.logb 2 k) := by rw [mul_comm]
    _ = ((2 : ℝ) ^ (r : ℝ)) ^ Real.logb 2 k := by rw [Real.rpow_mul (by norm_num)]
    _ = ((2 : ℝ) ^ r) ^ Real.logb 2 k := by rw [Real.rpow_natCast]
    _ ≤ (c ^ (k : ℝ)) ^ Real.logb 2 k := by
        refine Real.rpow_le_rpow (by positivity) ?_ hlogb
        rw [Real.rpow_natCast]; exact h
    _ = c ^ ((k : ℝ) * Real.logb 2 k) := by rw [Real.rpow_mul hc0]

/-- **FI Lemma 2.2, first assertion.**  For `k ≥ 2` and `n ≥ 1` there is a divisor `d` of `n` with
`d^k ≤ n` and `τ(n) ≤ (2τ(d))^{k log k / log 2}`.  (Paper: "Fix `k ≥ 2`.  Any `n ≥ 1` has a divisor
`d ≤ n^{1/k}` such that `τ(n) ≤ (2τ(d))^{k log k/log 2}`"; the proof is in the companion paper
[FI3], Lemmata 1–2.  This is the device that replaces a full divisor function `τ(n)` by `τ` of a
*small* divisor, which is what makes the lattice counts in §10 possible.) -/
theorem lemma_2_2 {k n : ℕ} (hk : 2 ≤ k) (hn : 1 ≤ n) :
    ∃ d : ℕ, d ∣ n ∧ d ^ k ≤ n ∧
      ((n.divisors.card : ℝ)) ≤ (2 * ((d.divisors.card : ℝ))) ^ (k * Real.log k / Real.log 2) := by
  have hn0 : n ≠ 0 := by omega
  have hk0 : 0 < k := by omega
  set Sp : Finset ℕ := n.primeFactors.filter (fun p => k ≤ n.factorization p) with hSp
  set Tp : Finset ℕ := n.primeFactors.filter (fun p => ¬ k ≤ n.factorization p) with hTp
  have hSp_mem : ∀ p, p ∈ Sp ↔ p ∈ n.primeFactors ∧ k ≤ n.factorization p := by
    intro p; rw [hSp, Finset.mem_filter]
  have hTp_mem : ∀ p, p ∈ Tp ↔ p ∈ n.primeFactors ∧ ¬ k ≤ n.factorization p := by
    intro p; rw [hTp, Finset.mem_filter]
  have hprim : ∀ p ∈ Sp, Nat.Prime p := fun p hp => by
    have h := (hSp_mem p).mp hp
    exact (Nat.mem_primeFactors.mp h.1).1
  have hprimT : ∀ p ∈ Tp, Nat.Prime p := fun p hp => by
    have h := (hTp_mem p).mp hp
    exact (Nat.mem_primeFactors.mp h.1).1
  have hSge : ∀ p ∈ Sp, k ≤ n.factorization p := fun p hp => ((hSp_mem p).mp hp).2
  have hSpos : ∀ p ∈ Sp, 0 < n.factorization p := fun p hp => by have := hSge p hp; omega
  have hTlt : ∀ p ∈ Tp, n.factorization p < k := fun p hp => by
    have := ((hTp_mem p).mp hp).2; omega
  have hTpos : ∀ p ∈ Tp, 0 < n.factorization p := fun p hp => by
    have h1 := (hTp_mem p).mp hp
    have hpp := (Nat.mem_primeFactors.mp h1.1).1
    have hdvd := (Nat.mem_primeFactors.mp h1.1).2.1
    exact Nat.pos_of_ne_zero (by
      intro h0
      rw [Nat.factorization_eq_zero_iff] at h0
      rcases h0 with h | h | h
      · exact h hpp
      · exact h hdvd
      · exact hn0 h)
  set L : ℕ := ∏ p ∈ Sp, p ^ n.factorization p with hL
  set M : ℕ := ∏ p ∈ Tp, p ^ n.factorization p with hM
  set DL : ℕ := ∏ p ∈ Sp, p ^ (n.factorization p / k) with hDL
  set RD : ℕ := ∏ p ∈ Tp, p ^ 1 with hRD
  have hL0 : L ≠ 0 := by
    rw [hL]
    exact Finset.prod_ne_zero_iff.mpr (fun p hp => pow_ne_zero _ (hprim p hp).ne_zero)
  have hLpos : 0 < L := Nat.pos_of_ne_zero hL0
  have hM0 : M ≠ 0 := by
    rw [hM]
    exact Finset.prod_ne_zero_iff.mpr (fun p hp => pow_ne_zero _ (hprimT p hp).ne_zero)
  have hMpos : 0 < M := Nat.pos_of_ne_zero hM0
  have hRD0 : RD ≠ 0 := by
    rw [hRD]
    exact Finset.prod_ne_zero_iff.mpr (fun p hp => pow_ne_zero _ (hprimT p hp).ne_zero)
  have hRD1 : 1 ≤ RD := Nat.one_le_iff_ne_zero.mpr hRD0
  have hRDsq : Squarefree RD := by
    rw [Nat.squarefree_iff_factorization_le_one hRD0]
    intro p
    rw [hRD, factorization_finset_prod_pow hprimT]
    split <;> omega
  obtain ⟨DM, hdmdvd, hdmpow, hdmcard⟩ := squarefree_tau_bound hk hRD1 hRDsq
  have hLM : L * M = n := by
    rw [hL, hM, hSp, hTp]
    rw [Finset.prod_filter_mul_prod_filter_not n.primeFactors
      (fun p => k ≤ n.factorization p) (fun p => p ^ n.factorization p)]
    rw [← Nat.prod_primeFactors_pow_factorization hn0]
  have htl : L.divisors.card = ∏ p ∈ Sp, (n.factorization p + 1) := by
    rw [hL]; exact card_divisors_prime_pow_prod Sp hprim (fun p => n.factorization p)
  have htm : M.divisors.card = ∏ p ∈ Tp, (n.factorization p + 1) := by
    rw [hM]; exact card_divisors_prime_pow_prod Tp hprimT (fun p => n.factorization p)
  have htdl : DL.divisors.card = ∏ p ∈ Sp, (n.factorization p / k + 1) := by
    rw [hDL]; exact card_divisors_prime_pow_prod Sp hprim (fun p => n.factorization p / k)
  have htR : RD.divisors.card = 2 ^ Tp.card := by
    rw [hRD, card_divisors_prime_pow_prod Tp hprimT (fun _ => 1), Finset.prod_const]
  have htn : n.divisors.card = L.divisors.card * M.divisors.card := by
    rw [Nat.card_divisors hn0, htl, htm, hSp, hTp]
    exact (Finset.prod_filter_mul_prod_filter_not n.primeFactors
      (fun p => k ≤ n.factorization p) (fun p => n.factorization p + 1)).symm
  have hl_le : L.divisors.card ≤ DL.divisors.card ^ k := by
    rw [htl, htdl, ← Finset.prod_pow]
    refine Finset.prod_le_prod₀ (fun p _ => Nat.zero_le _) ?_
    intro p hp
    exact le_pow_div_add_one hk0 (hSge p hp)
  have hm_le : M.divisors.card ≤ k ^ Tp.card := by
    rw [htm]
    calc ∏ p ∈ Tp, (n.factorization p + 1) ≤ ∏ p ∈ Tp, k := by
          refine Finset.prod_le_prod₀ (fun p _ => Nat.zero_le _) ?_
          intro p hp; have := hTlt p hp; omega
      _ = k ^ Tp.card := Finset.prod_const k
  have hRle : 2 ^ Tp.card ≤ (2 * DM.divisors.card) ^ k := by
    rw [← htR]; exact hdmcard
  have hDLdvd : DL ∣ L := by
    rw [hDL, hL]
    refine Finset.prod_dvd_prod_of_dvd _ _ ?_
    intro p hp
    exact pow_dvd_pow p (Nat.div_le_self _ _)
  have hRDdvd : RD ∣ M := by
    rw [hRD, hM]
    refine Finset.prod_dvd_prod_of_dvd _ _ ?_
    intro p hp
    exact pow_dvd_pow p (Nat.one_le_iff_ne_zero.mpr (hTpos p hp).ne')
  have hRDle : RD ≤ M := Nat.le_of_dvd hMpos hRDdvd
  have hdvd : (DL * DM) ∣ n := by
    rw [← hLM]
    exact mul_dvd_mul hDLdvd (dvd_trans hdmdvd hRDdvd)
  have hDLpow : DL ^ k ≤ L := by
    rw [hDL, hL, ← Finset.prod_pow]
    refine Nat.le_of_dvd hLpos (Finset.prod_dvd_prod_of_dvd _ _ ?_)
    intro p hp
    rw [← pow_mul]
    exact pow_dvd_pow p (Nat.div_mul_le_self _ _)
  have hdpow : (DL * DM) ^ k ≤ n := by
    rw [mul_pow, ← hLM]
    exact mul_le_mul hDLpow (le_trans hdmpow hRDle) (Nat.zero_le _) (Nat.zero_le _)
  refine ⟨DL * DM, hdvd, hdpow, ?_⟩
  have hdlR : Nat.Coprime DL RD := by
    rw [hDL, hRD]
    refine Nat.Coprime.prod_left ?_
    intro p hp
    refine Nat.Coprime.prod_right ?_
    intro q hq
    have hpne : p ≠ q := by
      intro hpq
      have h1 := hSge q (hpq ▸ hp)
      have h2 := ((hTp_mem q).mp hq).2
      omega
    rw [pow_one]
    exact ((Nat.coprime_primes (hprim p hp) (hprimT q hq)).mpr hpne).pow_left _
  have hdlm : Nat.Coprime DL DM := hdlR.coprime_dvd_right hdmdvd
  have hdd : (DL * DM).divisors.card = DL.divisors.card * DM.divisors.card :=
    Nat.Coprime.card_divisors_mul hdlm
  set K : ℝ := (k : ℝ) * Real.log (k : ℝ) / Real.log 2 with hK
  have hKlogb : K = (k : ℝ) * Real.logb 2 k := by
    rw [hK]; simp only [Real.logb]; ring
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hratio : 1 ≤ Real.log (k : ℝ) / Real.log 2 := by
    rw [le_div_iff₀ hlog2pos]
    have : Real.log 2 ≤ Real.log (k : ℝ) := Real.log_le_log (by norm_num) (by exact_mod_cast hk)
    linarith
  have hKge : (k : ℝ) ≤ K := by
    rw [hK]
    calc (k : ℝ) = (k : ℝ) * 1 := by ring
      _ ≤ (k : ℝ) * (Real.log (k : ℝ) / Real.log 2) :=
          mul_le_mul_of_nonneg_left hratio (by positivity)
      _ = (k : ℝ) * Real.log (k : ℝ) / Real.log 2 := by ring
  have hDL0 : DL ≠ 0 := by
    rw [hDL]
    exact Finset.prod_ne_zero_iff.mpr (fun p hp => pow_ne_zero _ (hprim p hp).ne_zero)
  have hDM0 : DM ≠ 0 := by
    intro h'
    rw [h'] at hdmdvd
    exact hRD0 (zero_dvd_iff.mp hdmdvd)
  have hA1 : (1 : ℝ) ≤ (DL.divisors.card : ℝ) := by
    have h1 : 1 ≤ DL.divisors.card := by
      have := (Finset.card_pos).mpr ⟨1, Nat.one_mem_divisors.mpr hDL0⟩
      omega
    exact_mod_cast h1
  have hB1 : (1 : ℝ) ≤ (DM.divisors.card : ℝ) := by
    have h1 : 1 ≤ DM.divisors.card := by
      have := (Finset.card_pos).mpr ⟨1, Nat.one_mem_divisors.mpr hDM0⟩
      omega
    exact_mod_cast h1
  have hlR : (L.divisors.card : ℝ) ≤ (DL.divisors.card : ℝ) ^ k := by
    exact_mod_cast hl_le
  have hmR : (M.divisors.card : ℝ) ≤ (2 * (DM.divisors.card : ℝ)) ^ K := by
    have h1 : (2 : ℝ) ^ Tp.card ≤ (2 * (DM.divisors.card : ℝ)) ^ k := by
      exact_mod_cast hRle
    have h2 : (M.divisors.card : ℝ) ≤ (k : ℝ) ^ Tp.card := by exact_mod_cast hm_le
    have h3 : (k : ℝ) ^ Tp.card ≤ (2 * (DM.divisors.card : ℝ)) ^ K := by
      have := pow_nat_le_rpow_of_le hk (by linarith [hB1]) h1
      rwa [hKlogb]
    linarith
  have hAK : (DL.divisors.card : ℝ) ^ k ≤ (DL.divisors.card : ℝ) ^ K := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hA1 hKge
  have hKex : K = k * Real.log k / Real.log 2 := by
    rw [hK]
  calc (n.divisors.card : ℝ)
      = (L.divisors.card : ℝ) * (M.divisors.card : ℝ) := by rw [htn]; push_cast; ring
    _ ≤ (DL.divisors.card : ℝ) ^ k * (2 * (DM.divisors.card : ℝ)) ^ K :=
        mul_le_mul hlR hmR (by positivity) (by positivity)
    _ ≤ (DL.divisors.card : ℝ) ^ K * (2 * (DM.divisors.card : ℝ)) ^ K :=
        mul_le_mul_of_nonneg_right hAK (Real.rpow_nonneg (by positivity) K)
    _ = (2 * ((DL * DM).divisors.card : ℝ)) ^ (k * Real.log k / Real.log 2) := by
        rw [hKex, hdd]; push_cast
        rw [← Real.mul_rpow (by positivity) (by positivity)]
        congr 1
        ring

end Work.FIArea3
