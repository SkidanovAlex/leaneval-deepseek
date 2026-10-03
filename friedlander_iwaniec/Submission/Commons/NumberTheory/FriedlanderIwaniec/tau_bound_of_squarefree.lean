import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Int.ConditionallyCompleteOrder
import Mathlib.Data.Int.Star
import Mathlib.Data.List.GetD
import Submission.Commons.Data.Nat.card_squarefree_divisors

open scoped BigOperators

namespace Commons.NumberTheory.FriedlanderIwaniec

lemma le_mul_div_add_one {r k : ℕ} (hk : 1 ≤ k) : r ≤ k * (r / k + 1) := by
  have hkpos : 0 < k := lt_of_lt_of_le zero_lt_one hk
  have hlt : r < k * (r / k + 1) := by
    calc
      r = k * (r / k) + r % k := (Nat.div_add_mod r k).symm
      _ < k * (r / k) + k := Nat.add_lt_add_left (Nat.mod_lt r hkpos) (k * (r / k))
      _ = k * (r / k + 1) := by ring
  exact le_of_lt hlt

lemma prod_take_eq_prod_range_getD (L : List ℕ) :
    ∀ m : ℕ, (L.take m).prod = ∏ i ∈ Finset.range m, L.getD i 1 := by
  induction L with
  | nil =>
      intro m
      simp
  | cons a t ih =>
      intro m
      cases m with
      | zero => simp
      | succ m =>
          have hP : (∏ i ∈ Finset.range m, t.getD i 1) =
              ∏ i ∈ Finset.range m, (a :: t).getD (i + 1) 1 := by
            apply Finset.prod_congr rfl
            intro i hi
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
      intro i hi
      rw [Finset.prod_const, Finset.card_range]
    _ ≤ ∏ i ∈ Finset.range s, ∏ j ∈ Finset.range k, f (k * i + j) := by
      apply Finset.prod_le_prod₀
      · intro i hi
        exact Nat.zero_le _
      · intro i hi
        have hi_lt : i < s := by simpa using hi
        apply Finset.prod_le_prod₀
        · intro j hj
          exact Nat.zero_le _
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
    have hfin : (⟨i, hiL⟩ : Fin L.length) ≤ ⟨j, hjL⟩ := by
      simpa using hij
    exact hmono hfin
  have hblk := prod_pow_le_prod_blocks f hk hf
  calc
    (L.take s).prod ^ k = (∏ i ∈ Finset.range s, f i) ^ k := by
      rw [prod_take_eq_prod_range_getD L s]
    _ ≤ ∏ m ∈ Finset.range (k * s), f m := hblk
    _ = (L.take (k * s)).prod := by
      rw [prod_take_eq_prod_range_getD L (k * s)]

lemma card_divisors_of_squarefree {x : ℕ} (hx0 : x ≠ 0) (hsq : Squarefree x) :
    (Nat.divisors x).card = 2 ^ (x.primeFactors).card := by
  have h1 := Commons.Data.Nat.card_squarefree_divisors x hx0
  have h2 := Nat.divisors_filter_squarefree_of_squarefree hsq
  rw [h2] at h1
  exact h1

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
      inj' := by
        intro i j h
        exact hinj (by simpa using congrArg Subtype.val h) }
  have hcard := Fintype.card_le_of_embedding (α := Fin s) (β := {x // x ∈ d.primeFactors}) f
  simpa [Fintype.card_fin, Fintype.card_coe] using hcard

theorem tau_bound_of_squarefree {n k : ℕ} (hn1 : 1 < n) (hsq : Squarefree n) (hk : 1 ≤ k) :
    ∃ d : ℕ, d ∣ n ∧ d ^ k ≤ n ∧ (Nat.divisors n).card ≤ (2 * (Nat.divisors d).card) ^ k := by
  have hn0 : n ≠ 0 := by
    exact ne_of_gt (lt_trans zero_lt_one hn1)
  let L : List ℕ := n.primeFactorsList
  let r : ℕ := L.length
  let s : ℕ := r / k
  let d : ℕ := (L.take s).prod
  have hs_le_r : s ≤ L.length := by
    dsimp [s, r]
    exact Nat.div_le_self L.length k
  have hs_ks : k * s ≤ L.length := by
    dsimp [s, r]
    have h := Nat.div_mul_le_self L.length k
    simpa [Nat.mul_comm] using h
  have hprod : L.prod = n := by
    dsimp [L]
    exact Nat.prod_primeFactorsList hn0
  have hsort : L.SortedLE := by
    dsimp [L]
    exact Nat.primeFactorsList_sorted n
  have hnd : L.Nodup := by
    dsimp [L]
    exact hsq.nodup_primeFactorsList
  have hprim : ∀ p ∈ L, p.Prime := by
    dsimp [L]
    intro p hp
    exact Nat.prime_of_mem_primeFactorsList hp
  have hposL : 0 < L.prod := by
    rw [hprod]
    exact lt_trans zero_lt_one hn1
  -- (1) divisibility
  have hdvd0 : d ∣ n := by
    dsimp [d]
    refine ⟨(L.drop s).prod, ?_⟩
    calc
      n = L.prod := hprod.symm
      _ = (L.take s).prod * (L.drop s).prod := by
        rw [List.prod_take_mul_prod_drop]
  -- (2) d^k ≤ n
  have hpow0 : d ^ k ≤ n := by
    dsimp [d]
    have h1 := take_prod_pow_le_take_prod (L := L) (k := k) (s := s) hk hs_ks hsort
    calc
      (L.take s).prod ^ k ≤ (L.take (k * s)).prod := h1
      _ ≤ L.prod := by
        have hdvd2 : (L.take (k * s)).prod ∣ L.prod :=
          (List.take_sublist (k * s) L).prod_dvd_prod
        exact Nat.le_of_dvd hposL hdvd2
      _ = n := hprod
  -- (3) divisor-count bound
  have htau_n : (Nat.divisors n).card = 2 ^ r := by
    have h1 := card_divisors_of_squarefree (x := n) hn0 hsq
    have h2 : (n.primeFactors).card = L.length := by
      dsimp [L]
      exact card_primeFactors_eq_length hsq
    rw [h2] at h1
    simpa [r] using h1
  have hsq_d : Squarefree d := by
    exact hsq.squarefree_of_dvd hdvd0
  have hd0 : d ≠ 0 := by
    exact ne_of_gt (Nat.pos_of_dvd_of_pos hdvd0 (lt_trans zero_lt_one hn1))
  -- d has at least s distinct prime factors
  have hs_le_omega_d : s ≤ (d.primeFactors).card := by
    classical
    let p : Fin s → ℕ := fun i => L.get ⟨i.1, lt_of_lt_of_le i.2 hs_le_r⟩
    have hpri : ∀ i, (p i).Prime := by
      intro i
      dsimp [p]
      exact hprim (L.get ⟨i.1, lt_of_lt_of_le i.2 hs_le_r⟩)
        (List.get_mem L ⟨i.1, lt_of_lt_of_le i.2 hs_le_r⟩)
    have hdiv : ∀ i, p i ∣ d := by
      intro i
      dsimp [d, p]
      have hlen : i.1 < (L.take s).length := by
        rw [List.length_take, Nat.min_eq_left hs_le_r]
        exact i.2
      have hmem : L.get ⟨i.1, lt_of_lt_of_le i.2 hs_le_r⟩ ∈ L.take s := by
        -- L[i] = (L.take s)[i], and (L.take s)[i] ∈ L.take s
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
    exact s_le_card_primeFactors (d := d) hd0 (s := s) hpri hdiv hinj
  -- tau(d) ≥ 2^s
  have htau_d_ge : 2 ^ s ≤ (Nat.divisors d).card := by
    have h1 := card_divisors_of_squarefree (x := d) hd0 hsq_d
    have hle := pow_le_pow_right₀ (a := 2) (m := s)
      (n := (d.primeFactors).card) (by norm_num) hs_le_omega_d
    rw [← h1] at hle
    simpa using hle
  -- exponent arithmetic
  have hs_le_ks1 : r ≤ k * (s + 1) := by
    dsimp [s]
    exact le_mul_div_add_one (r := r) hk
  have htau_goal : (Nat.divisors n).card ≤ (2 * (Nat.divisors d).card) ^ k := by
    calc
      (Nat.divisors n).card = 2 ^ r := htau_n
      _ ≤ (2 * 2 ^ s) ^ k := by
        have h_eq : (2 * 2 ^ s) ^ k = 2 ^ (k * (s + 1)) := by
          calc
            (2 * 2 ^ s) ^ k = (2 ^ (s + 1)) ^ k := by
              congr 1
              rw [pow_succ']
            _ = 2 ^ ((s + 1) * k) := by rw [pow_mul]
            _ = 2 ^ (k * (s + 1)) := by
              congr 1
              rw [Nat.mul_comm]
        rw [h_eq]
        exact pow_le_pow_right₀ (a := 2) (m := r) (n := k * (s + 1)) (by norm_num) hs_le_ks1
      _ ≤ (2 * (Nat.divisors d).card) ^ k := by
        apply Nat.pow_le_pow_left
        exact Nat.mul_le_mul_left 2 htau_d_ge
  exact ⟨d, hdvd0, hpow0, htau_goal⟩
end Commons.NumberTheory.FriedlanderIwaniec