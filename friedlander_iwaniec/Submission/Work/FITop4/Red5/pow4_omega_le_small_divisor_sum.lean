import Mathlib

namespace Work.FITop4.Red5

open Finset
open scoped BigOperators

noncomputable section

/-- `pi A = ∏_{p ∈ A} p`, the product of the elements of the finite set `A`. -/
def pi (A : Finset ℕ) : ℕ := ∏ p ∈ A, p

lemma pi_sdiff_mul {P A : Finset ℕ} (hA : A ⊆ P) : pi (P \ A) * pi A = pi P := by
  rw [pi, pi, pi]
  exact Finset.prod_sdiff (f := fun x => x) hA

/-- Combinatorial core: a family `T` of subsets of `P` which meets every complement
pair `{A, P \ A}` has a large weighted sum. -/
theorem powerset_complement_sum (P : Finset ℕ) (T : Finset (Finset ℕ))
    (hTsub : T ⊆ P.powerset)
    (hor : ∀ A ∈ P.powerset, A ∈ T ∨ P \ A ∈ T) :
    (4:ℝ) ^ (P.card) ≤
      2 * ((P.card : ℝ) + 1) * ∑ A ∈ T, (4:ℝ) ^ (A.card) := by
  classical
  set k : ℕ := P.card with hk
  set ℓ : ℕ := k / 2 with hℓ
  set W : Finset (Finset ℕ) := P.powersetCard ℓ with hW
  set Y : ℝ := ∑ A ∈ T, (4:ℝ) ^ (A.card) with hY
  have hWmem : ∀ A, A ∈ W → A ⊆ P ∧ A.card = ℓ := by
    intro A hA
    rw [hW, Finset.mem_powersetCard] at hA
    exact hA
  -- the "selector" of the T-element of the complement orbit, applied to `A`
  have hselT : ∀ A ∈ W, (if A ∈ T then A else P \ A) ∈ T := by
    intro A hA
    obtain ⟨hAP, -⟩ := hWmem A hA
    by_cases hAin : A ∈ T
    · rw [if_pos hAin]; exact hAin
    · rw [if_neg hAin]
      rcases hor A (Finset.mem_powerset.mpr hAP) with h | h
      · exact absurd h hAin
      · exact h
  have hselcard : ∀ A ∈ W, ℓ ≤ (if A ∈ T then A else P \ A).card := by
    intro A hA
    obtain ⟨hAP, hAc⟩ := hWmem A hA
    by_cases hAin : A ∈ T
    · rw [if_pos hAin, hAc]
    · rw [if_neg hAin]
      have hcard : (P \ A).card = k - ℓ := by
        rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hAP, ← hk, hAc]
      rw [hcard]
      have hmul : ℓ * 2 ≤ k := by rw [hℓ]; exact Nat.div_mul_le_self k 2
      omega
  set T' : Finset (Finset ℕ) := W.image (fun A => if A ∈ T then A else P \ A) with hT'
  have hT'b : ∀ B, B ∈ T' → ∃ A ∈ W, (if A ∈ T then A else P \ A) = B := by
    intro B hB; rw [hT'] at hB; exact Finset.mem_image.mp hB
  have hT'sub : T' ⊆ T := by
    rw [hT']
    exact Finset.image_subset_iff.mpr (fun A hA => hselT A hA)
  -- each fibre of the selector has at most two elements
  have hfiber_bd : ∀ B ∈ T',
      (W.filter (fun A => (if A ∈ T then A else P \ A) = B)).card ≤ 2 := by
    intro B hB
    have hsub : W.filter (fun A => (if A ∈ T then A else P \ A) = B)
        ⊆ ({B, P \ B} : Finset (Finset ℕ)) := by
      intro A hA
      rw [Finset.mem_filter] at hA
      obtain ⟨hAW, hAφ⟩ := hA
      obtain ⟨hAP, -⟩ := hWmem A hAW
      by_cases hAin : A ∈ T
      · have hAB : A = B := by rw [if_pos hAin] at hAφ; exact hAφ
        rw [hAB]; exact Finset.mem_insert_self B {P \ B}
      · have hPA : P \ A = B := by rw [if_neg hAin] at hAφ; exact hAφ
        have hAB : A = P \ B := by
          have h1 : P \ (P \ A) = P \ B := by rw [hPA]
          rwa [Finset.sdiff_sdiff_eq_self hAP] at h1
        rw [hAB]
        exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr rfl))
    calc (W.filter (fun A => (if A ∈ T then A else P \ A) = B)).card
        ≤ ({B, P \ B} : Finset (Finset ℕ)).card := Finset.card_le_card hsub
      _ ≤ 2 := Finset.card_le_two
  have hcardW : W.card
      = ∑ B ∈ T', (W.filter (fun A => (if A ∈ T then A else P \ A) = B)).card := by
    rw [hT']
    refine Finset.card_eq_sum_card_fiberwise ?_
    intro A hA
    exact Finset.mem_image.mpr ⟨A, hA, rfl⟩
  have hcard_le : W.card ≤ 2 * T'.card := by
    rw [hcardW]
    calc ∑ B ∈ T', (W.filter (fun A => (if A ∈ T then A else P \ A) = B)).card
        ≤ ∑ B ∈ T', 2 := Finset.sum_le_sum hfiber_bd
      _ = 2 * T'.card := by simp [Finset.sum_const, nsmul_eq_mul, mul_comm]
  have hYlow : (T'.card : ℝ) * (4:ℝ) ^ ℓ ≤ Y := by
    rw [hY]
    calc (T'.card : ℝ) * (4:ℝ) ^ ℓ
        = ∑ B ∈ T', (4:ℝ) ^ ℓ := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ B ∈ T', (4:ℝ) ^ (B.card) := by
            apply Finset.sum_le_sum
            intro B hB
            obtain ⟨A, hAW, rfl⟩ := hT'b B hB
            exact pow_le_pow_right₀ (by norm_num) (hselcard A hAW)
      _ ≤ ∑ B ∈ T, (4:ℝ) ^ (B.card) := by
            apply Finset.sum_le_sum_of_subset_of_nonneg hT'sub
            intro B _ _; positivity
  have hWcard : W.card = k.choose ℓ := by
    rw [hW, Finset.card_powersetCard, hk]
  have hhalf : (k.choose ℓ : ℝ) * (4:ℝ) ^ ℓ ≤ 2 * Y := by
    have h1 : (W.card : ℝ) ≤ 2 * (T'.card : ℝ) := by exact_mod_cast hcard_le
    have h1' : (W.card : ℝ) * (4:ℝ) ^ ℓ ≤ 2 * ((T'.card : ℝ) * (4:ℝ) ^ ℓ) := by
      have h := mul_le_mul_of_nonneg_right h1 (by positivity : (0:ℝ) ≤ (4:ℝ)^ℓ)
      linarith
    have h2 : 2 * ((T'.card : ℝ) * (4:ℝ) ^ ℓ) ≤ 2 * Y :=
      mul_le_mul_of_nonneg_left hYlow (by norm_num)
    have h3 : (W.card : ℝ) = (k.choose ℓ : ℝ) := by exact_mod_cast hWcard
    rw [h3] at h1'
    linarith
  have hfull : Odd k → (k.choose ℓ : ℝ) * (4:ℝ) ^ ℓ ≤ Y := by
    intro hodd
    have hfiber1 : ∀ B ∈ T',
        (W.filter (fun A => (if A ∈ T then A else P \ A) = B)).card ≤ 1 := by
      intro B hB
      rw [Finset.card_le_one]
      intro A1 hA1 A2 hA2
      rw [Finset.mem_filter] at hA1 hA2
      obtain ⟨hA1W, hA1φ⟩ := hA1
      obtain ⟨hA2W, hA2φ⟩ := hA2
      have key : ∀ A : Finset ℕ, A ∈ W → (if A ∈ T then A else P \ A) = B →
          (A = B ∨ A = P \ B) := by
        intro A hAW hAφ
        obtain ⟨hAP, -⟩ := hWmem A hAW
        by_cases hAin : A ∈ T
        · left; rw [if_pos hAin] at hAφ; exact hAφ
        · right
          have hPA : P \ A = B := by rw [if_neg hAin] at hAφ; exact hAφ
          have h1 : P \ (P \ A) = P \ B := by rw [hPA]
          rwa [Finset.sdiff_sdiff_eq_self hAP] at h1
      have hBsub : B ⊆ P := Finset.mem_powerset.mp (hTsub (hT'sub hB))
      have hPB : (P \ B).card = k - B.card := by
        rw [Finset.card_sdiff, Finset.inter_eq_left.mpr hBsub, ← hk]
      have hkodd : 2 * ℓ + 1 = k := by
        rw [hℓ]
        have h := Nat.div_add_mod k 2
        have hmod : k % 2 = 1 := Nat.odd_iff.mp hodd
        omega
      rcases key A1 hA1W hA1φ with h1 | h1 <;> rcases key A2 hA2W hA2φ with h2 | h2
      · rw [h1, h2]
      · exfalso
        have hBc : B.card = ℓ := by
          have h := (hWmem A1 hA1W).2; rwa [h1] at h
        have hpBc : (P \ B).card = ℓ := by
          have h := (hWmem A2 hA2W).2; rwa [h2] at h
        rw [hBc] at hPB
        omega
      · exfalso
        have hBc : B.card = ℓ := by
          have h := (hWmem A2 hA2W).2; rwa [h2] at h
        have hpBc : (P \ B).card = ℓ := by
          have h := (hWmem A1 hA1W).2; rwa [h1] at h
        rw [hBc] at hPB
        omega
      · rw [h1, h2]
    have hle : W.card ≤ T'.card := by
      rw [hcardW]
      calc ∑ B ∈ T', (W.filter (fun A => (if A ∈ T then A else P \ A) = B)).card
          ≤ ∑ B ∈ T', 1 := Finset.sum_le_sum hfiber1
        _ = T'.card := by simp
    have hT'le : T'.card ≤ W.card := by rw [hT']; exact Finset.card_image_le
    have hcardeq : T'.card = W.card := le_antisymm hT'le hle
    have h := hYlow
    rw [hcardeq, hWcard] at h
    exact h
  have hbin : (2:ℝ) ^ k ≤ ((k:ℝ) + 1) * (k.choose ℓ : ℝ) := by
    have hnat : 2 ^ k ≤ (k + 1) * k.choose ℓ := by
      have h1 : ∑ j ∈ Finset.range (k+1), k.choose j
          ≤ ∑ j ∈ Finset.range (k+1), k.choose ℓ :=
        Finset.sum_le_sum (fun j _ => by rw [hℓ]; exact Nat.choose_le_middle j k)
      rw [Nat.sum_range_choose] at h1
      rwa [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at h1
    exact_mod_cast hnat
  rcases Nat.mod_two_eq_zero_or_one k with hk2 | hk2
  · have h2ℓ : 2 * ℓ = k := by
      rw [hℓ]; have h := Nat.div_add_mod k 2; omega
    have hfour : (4:ℝ) ^ ℓ = (2:ℝ) ^ k := by
      rw [show (4:ℝ) = (2:ℝ)^2 by norm_num, ← pow_mul, h2ℓ]
    have hkey : (4:ℝ) ^ k ≤ ((k:ℝ) + 1) * (k.choose ℓ : ℝ) * (4:ℝ) ^ ℓ := by
      rw [hfour]
      have hm := mul_le_mul_of_nonneg_right hbin (by positivity : (0:ℝ) ≤ (2:ℝ)^k)
      have he : (4:ℝ) ^ k = (2:ℝ)^k * (2:ℝ)^k := by
        rw [show (4:ℝ) = (2:ℝ) * 2 by norm_num, mul_pow]
      rw [he]
      exact hm
    calc (4:ℝ) ^ k ≤ ((k:ℝ) + 1) * (k.choose ℓ : ℝ) * (4:ℝ) ^ ℓ := hkey
      _ = ((k:ℝ) + 1) * ((k.choose ℓ : ℝ) * (4:ℝ) ^ ℓ) := by ring
      _ ≤ ((k:ℝ) + 1) * (2 * Y) := by
            apply mul_le_mul_of_nonneg_left hhalf; positivity
      _ = 2 * ((k:ℝ) + 1) * Y := by ring
  · have hodd : Odd k := Nat.odd_iff.mpr hk2
    have h2ℓ : 2 * ℓ + 1 = k := by
      rw [hℓ]; have h := Nat.div_add_mod k 2; omega
    have hkey : (4:ℝ) ^ k ≤ 2 * ((k:ℝ) + 1) * (k.choose ℓ : ℝ) * (4:ℝ) ^ ℓ := by
      rw [show (4:ℝ) ^ ℓ = (2:ℝ)^(2*ℓ) by
            rw [show (4:ℝ) = (2:ℝ)^2 by norm_num, ← pow_mul]]
      rw [show (4:ℝ) ^ k = (2:ℝ)^(2*k) by
            rw [show (4:ℝ) = (2:ℝ)^2 by norm_num, ← pow_mul]]
      have hm := mul_le_mul_of_nonneg_left hbin (by positivity : (0:ℝ) ≤ 2 * (2:ℝ)^(2*ℓ))
      have he : (2:ℝ)^(2*k) = 2 * (2:ℝ)^(2*ℓ) * (2:ℝ)^k := by
        rw [show 2*k = 2*ℓ + (k+1) from by omega, pow_add, pow_succ]; ring
      calc (2:ℝ)^(2*k) = 2 * (2:ℝ)^(2*ℓ) * (2:ℝ)^k := he
        _ ≤ (2 * (2:ℝ)^(2*ℓ)) * (((k:ℝ) + 1) * (k.choose ℓ : ℝ)) := hm
        _ = 2 * ((k:ℝ) + 1) * (k.choose ℓ : ℝ) * (2:ℝ)^(2*ℓ) := by ring
    calc (4:ℝ) ^ k ≤ 2 * ((k:ℝ) + 1) * (k.choose ℓ : ℝ) * (4:ℝ) ^ ℓ := hkey
      _ = 2 * ((k:ℝ) + 1) * ((k.choose ℓ : ℝ) * (4:ℝ) ^ ℓ) := by ring
      _ ≤ 2 * ((k:ℝ) + 1) * Y := by
            apply mul_le_mul_of_nonneg_left (hfull hodd); positivity

theorem pow4_omega_le_small_divisor_sum (n : ℕ) (hn : 1 ≤ n) :
    (4:ℝ) ^ (n.primeFactors.card) ≤
      2 * ((n.primeFactors.card : ℝ) + 1) *
        ∑ d ∈ n.divisors.filter (fun d => d * d ≤ n), (4:ℝ) ^ (d.primeFactors.card) := by
  classical
  set P : Finset ℕ := n.primeFactors with hP
  set T : Finset (Finset ℕ) := P.powerset.filter (fun A => pi A ≤ pi (P \ A)) with hT
  have hn0 : n ≠ 0 := by omega
  have hRPvd : pi P ∣ n := by
    rw [hP]; simpa only [pi] using Nat.prod_primeFactors_dvd n
  have hRPle : pi P ≤ n := Nat.le_of_dvd (by omega) hRPvd
  have hTsub : T ⊆ P.powerset := by rw [hT]; exact Finset.filter_subset _ _
  have hor : ∀ A ∈ P.powerset, A ∈ T ∨ P \ A ∈ T := by
    intro A hA
    rw [Finset.mem_powerset] at hA
    by_cases hle : pi A ≤ pi (P \ A)
    · left
      rw [hT, Finset.mem_filter]
      exact ⟨Finset.mem_powerset.mpr hA, hle⟩
    · right
      rw [hT, Finset.mem_filter]
      refine ⟨Finset.mem_powerset.mpr Finset.sdiff_subset, ?_⟩
      have hlt : pi (P \ A) < pi A := lt_of_not_ge hle
      have : pi (P \ (P \ A)) = pi A := by rw [Finset.sdiff_sdiff_eq_self hA]
      rw [this]
      exact le_of_lt hlt
  have hcomb := powerset_complement_sum P T hTsub hor
  have hAT : ∀ A ∈ T, A ⊆ P ∧ pi A ∣ n ∧ pi A * pi A ≤ n ∧ (pi A).primeFactors = A := by
    intro A hA
    rw [hT, Finset.mem_filter] at hA
    obtain ⟨hApow, hAle⟩ := hA
    have hA' : A ⊆ P := Finset.mem_powerset.mp hApow
    have hA'P : A ⊆ n.primeFactors := by rw [← hP]; exact hA'
    refine ⟨hA', ?_, ?_, ?_⟩
    · have h1 : pi A ∣ pi P := by
        simpa only [pi] using Finset.prod_dvd_prod_of_subset A P (fun x => x) hA'
      exact dvd_trans h1 hRPvd
    · have h2 : pi A * pi (P \ A) = pi P := by
        rw [mul_comm]; exact pi_sdiff_mul hA'
      calc pi A * pi A ≤ pi A * pi (P \ A) := Nat.mul_le_mul_left _ hAle
        _ = pi P := h2
        _ ≤ n := hRPle
    · have hp : ∀ p ∈ A, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors (hA'P hp)
      simp only [pi]; exact Nat.primeFactors_prod hp
  have hinj : Set.InjOn pi ↑T := by
    intro A1 hA1 A2 hA2 heq
    have h1 := (hAT A1 hA1).2.2.2
    have h2 := (hAT A2 hA2).2.2.2
    rw [← h1, ← h2, heq]
  have himg : T.image pi ⊆ n.divisors.filter (fun d => d * d ≤ n) := by
    intro d hd
    rw [Finset.mem_image] at hd
    obtain ⟨A, hA, rfl⟩ := hd
    obtain ⟨_, hAdvd, hAsq, _⟩ := hAT A hA
    rw [Finset.mem_filter]
    exact ⟨Nat.mem_divisors.mpr ⟨hAdvd, hn0⟩, hAsq⟩
  have hsum_le : ∑ A ∈ T, (4:ℝ) ^ (A.card)
      ≤ ∑ d ∈ n.divisors.filter (fun d => d * d ≤ n), (4:ℝ) ^ (d.primeFactors.card) := by
    calc ∑ A ∈ T, (4:ℝ) ^ (A.card)
        = ∑ A ∈ T, (4:ℝ) ^ ((pi A).primeFactors.card) := by
            refine Finset.sum_congr rfl ?_
            intro A hA
            rw [(hAT A hA).2.2.2]
      _ = ∑ d ∈ T.image pi, (4:ℝ) ^ (d.primeFactors.card) := by
            rw [Finset.sum_image hinj]
      _ ≤ ∑ d ∈ n.divisors.filter (fun d => d * d ≤ n), (4:ℝ) ^ (d.primeFactors.card) := by
            apply Finset.sum_le_sum_of_subset_of_nonneg himg
            intro d _ _; positivity
  calc (4:ℝ) ^ (P.card)
      ≤ 2 * ((P.card : ℝ) + 1) * ∑ A ∈ T, (4:ℝ) ^ (A.card) := hcomb
    _ ≤ 2 * ((P.card : ℝ) + 1)
          * ∑ d ∈ n.divisors.filter (fun d => d * d ≤ n), (4:ℝ) ^ (d.primeFactors.card) :=
        mul_le_mul_of_nonneg_left hsum_le (by positivity)

end

end Work.FITop4.Red5
