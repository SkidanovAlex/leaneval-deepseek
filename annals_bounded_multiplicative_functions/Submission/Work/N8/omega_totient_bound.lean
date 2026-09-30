import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.N8

/-- For a finset of natural numbers all of which are at least `2`, the product is at
least `(card + 1)!`.  This is the key combinatorial input for bounding `ω(q)` against
the size of `q`. -/
lemma factorial_card_succ_le_prod (s : Finset ℕ) (h : ∀ x ∈ s, 2 ≤ x) :
    (s.card + 1).factorial ≤ ∏ x ∈ s, x := by
  classical
  revert h
  refine Finset.induction_on_max (motive := fun t => (∀ x ∈ t, 2 ≤ x) →
      (t.card + 1).factorial ≤ ∏ x ∈ t, x) s ?_ ?_
  · intro _; simp
  · intro a t hlt ih h
    have hat : a ∉ t := fun ha => absurd (hlt a ha) (lt_irrefl a)
    have ih' : (t.card + 1).factorial ≤ ∏ x ∈ t, x :=
      ih (fun x hx => h x (Finset.mem_insert_of_mem hx))
    rw [Finset.prod_insert hat, Finset.card_insert_of_notMem hat]
    have hcard : t.card + 2 ≤ a := by
      have ha : 2 ≤ a := h a (Finset.mem_insert_self a t)
      have hsub : t ⊆ Finset.Ico 2 a := fun x hx =>
        Finset.mem_Ico.mpr ⟨h x (Finset.mem_insert_of_mem hx), hlt x hx⟩
      have hc := Finset.card_le_card hsub
      rw [Nat.card_Ico] at hc
      omega
    calc (t.card + 1 + 1).factorial = (t.card + 2) * (t.card + 1).factorial := by
          rw [show t.card + 1 + 1 = t.card + 2 from rfl]; exact Nat.factorial_succ _
      _ ≤ a * (t.card + 1).factorial := Nat.mul_le_mul_right _ hcard
      _ ≤ a * ∏ x ∈ t, x := Nat.mul_le_mul_left _ ih'

/-- A number with `r` distinct prime factors is at least the product of the `r` smallest
primes, hence at least `(r + 1)!`. -/
theorem factorial_le_primeFactors_card (n : ℕ) (hn : 1 ≤ n) :
    (n.primeFactors.card + 1).factorial ≤ n := by
  have h1 : (n.primeFactors.card + 1).factorial ≤ ∏ p ∈ n.primeFactors, p :=
    factorial_card_succ_le_prod n.primeFactors
      (fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le)
  have h2 : ∏ p ∈ n.primeFactors, p ≤ n :=
    Nat.le_of_dvd (by omega) (Nat.prod_primeFactors_dvd n)
  exact le_trans h1 h2

/-- Euler's totient is at least `n / 2^{ω(n)}`. -/
theorem totient_lower_bound (n : ℕ) (hn : 1 ≤ n) :
    (n : ℝ) ≤ (n.totient : ℝ) * (2 : ℝ) ^ n.primeFactors.card := by
  have hnat : n ≤ n.totient * 2 ^ n.primeFactors.card := by
    have hid := Nat.totient_mul_prod_primeFactors n
    have hkey : (∏ p ∈ n.primeFactors, p) ≤
        2 ^ n.primeFactors.card * ∏ p ∈ n.primeFactors, (p - 1) := by
      calc (∏ p ∈ n.primeFactors, p) ≤ ∏ p ∈ n.primeFactors, (2 * (p - 1)) := by
            apply Finset.prod_le_prod
            intro p hp
            have := (Nat.prime_of_mem_primeFactors hp).two_le
            omega
        _ = (∏ _p ∈ n.primeFactors, (2:ℕ)) * ∏ p ∈ n.primeFactors, (p - 1) :=
              Finset.prod_mul_distrib
        _ = 2 ^ n.primeFactors.card * ∏ p ∈ n.primeFactors, (p - 1) := by
              rw [Finset.prod_const]
    have hPpos : 0 < ∏ p ∈ n.primeFactors, p :=
      Finset.prod_pos (fun p hp => (Nat.prime_of_mem_primeFactors hp).pos)
    have h2 : n * (2 ^ n.primeFactors.card * ∏ p ∈ n.primeFactors, (p - 1))
        = (n.totient * 2 ^ n.primeFactors.card) * ∏ p ∈ n.primeFactors, p := by
      have hQ : n * (∏ p ∈ n.primeFactors, (p - 1)) =
          n.totient * ∏ p ∈ n.primeFactors, p := hid.symm
      calc n * (2 ^ n.primeFactors.card * ∏ p ∈ n.primeFactors, (p - 1))
          = 2 ^ n.primeFactors.card * (n * ∏ p ∈ n.primeFactors, (p - 1)) := by ring
        _ = 2 ^ n.primeFactors.card * (n.totient * ∏ p ∈ n.primeFactors, p) := by rw [hQ]
        _ = (n.totient * 2 ^ n.primeFactors.card) * ∏ p ∈ n.primeFactors, p := by ring
    have h1 : n * (∏ p ∈ n.primeFactors, p) ≤
        n * (2 ^ n.primeFactors.card * ∏ p ∈ n.primeFactors, (p - 1)) :=
      Nat.mul_le_mul_left n hkey
    rw [h2] at h1
    exact Nat.le_of_mul_le_mul_right h1 hPpos
  exact_mod_cast hnat

/-- For `c ≥ 1` and `c ^ 2 ≤ N`, the quantity `c ^ r / √((r+1)!)` is bounded by `c ^ (N+1)`. -/
theorem pow_div_sqrt_factorial_le (c : ℝ) (N : ℕ) (hc : 1 ≤ c) (hcN : c^2 ≤ (N:ℝ)) (r : ℕ) :
    c^r / Real.sqrt ((Nat.factorial (r+1) : ℕ) : ℝ) ≤ c^(N+1) := by
  have hcpos : 0 < c := lt_of_lt_of_le zero_lt_one hc
  let f : ℕ → ℝ := fun k => c^k / Real.sqrt ((Nat.factorial (k+1):ℕ):ℝ)
  change f r ≤ c^(N+1)
  have hf_nonneg : ∀ k, 0 ≤ f k := fun k =>
    div_nonneg (pow_nonneg hcpos.le k) (Real.sqrt_nonneg _)
  have hsqrt_ge_one : ∀ k, 1 ≤ Real.sqrt ((Nat.factorial (k+1):ℕ):ℝ) := by
    intro k
    rw [← Real.sqrt_one]
    apply Real.sqrt_le_sqrt
    have h1 : (1:ℕ) ≤ Nat.factorial (k+1) := by have := Nat.factorial_pos (k+1); omega
    exact_mod_cast h1
  have hf_le : ∀ k, f k ≤ c^k := fun k => div_le_self (pow_nonneg hcpos.le k) (hsqrt_ge_one k)
  have hstep : ∀ k, N ≤ k → f (k+1) ≤ f k := by
    intro k hk
    have hk2pos : (0:ℝ) < (k:ℝ) + 2 := by positivity
    have hsq : c^2 ≤ (k:ℝ)+2 := by
      have h1 : (N:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
      linarith
    have hc_le : c ≤ Real.sqrt ((k:ℝ)+2) := ((Real.le_sqrt hcpos.le (by positivity)).2 hsq)
    have hcle : c / Real.sqrt ((k:ℝ)+2) ≤ 1 := (div_le_one (Real.sqrt_pos.2 hk2pos)).2 hc_le
    have hfeq : f (k+1) = (c / Real.sqrt ((k:ℝ)+2)) * f k := by
      simp only [f]
      have hB : ((Nat.factorial (k+1+1):ℕ):ℝ) =
          ((Nat.factorial (k+1):ℕ):ℝ) * ((k:ℝ)+2) := by
        rw [Nat.factorial_succ]
        push_cast
        ring
      rw [hB, Real.sqrt_mul (by positivity) ((k:ℝ)+2), pow_succ]
      field_simp
    calc f (k+1) = (c / Real.sqrt ((k:ℝ)+2)) * f k := hfeq
      _ ≤ 1 * f k := mul_le_mul_of_nonneg_right hcle (hf_nonneg k)
      _ = f k := one_mul _
  have hanti : ∀ r, N ≤ r → f r ≤ f N := by
    intro r hr
    induction r, hr using Nat.le_induction with
    | base => exact le_refl _
    | succ m hm ih => exact le_trans (hstep m hm) ih
  by_cases hr : r ≤ N
  · calc f r ≤ c^r := hf_le r
      _ ≤ c^N := pow_le_pow_right₀ hc hr
      _ ≤ c^(N+1) := pow_le_pow_right₀ hc (Nat.le_succ N)
  · calc f r ≤ f N := hanti r (not_le.mp hr).le
      _ ≤ c^N := hf_le N
      _ ≤ c^(N+1) := pow_le_pow_right₀ hc (Nat.le_succ N)

theorem omega_totient_bound (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (m q : ℕ), 1 ≤ m → m ≤ k → 1 ≤ q →
      (((2 * m : ℕ) : ℝ) ^ q.primeFactors.card / (q.totient : ℝ)) ≤ C / Real.sqrt (q : ℝ)
:= by
  set c : ℝ := 4 * ((k : ℝ) + 1) with hc
  set N : ℕ := 16 * (k + 1) ^ 2 with hN
  have hc1 : 1 ≤ c := by rw [hc]; nlinarith [show (0:ℝ) ≤ (k:ℝ) from Nat.cast_nonneg k]
  have hcpos : 0 < c := lt_of_lt_of_le zero_lt_one hc1
  have hcN : c ^ 2 ≤ (N : ℝ) := by
    rw [hc, hN]; push_cast; nlinarith
  refine ⟨c ^ (N + 1), pow_pos hcpos _, ?_⟩
  intro m q hm1 hmk hq1
  have hqpos : 0 < q := hq1
  have hqposR : (0:ℝ) < (q:ℝ) := by exact_mod_cast hqpos
  have hsqpos : (0:ℝ) < Real.sqrt (q:ℝ) := Real.sqrt_pos.2 hqposR
  have htotpos : (0:ℝ) < (q.totient:ℝ) := by
    have := Nat.totient_pos.2 hqpos; exact_mod_cast this
  rw [div_le_div_iff₀ htotpos hsqpos]
  -- goal : ((2*m:ℕ):ℝ)^ω(q) * √q ≤ c^(N+1) * φ(q)
  have h2r : (0:ℝ) < (2:ℝ)^(q.primeFactors.card) := by positivity
  refine le_of_mul_le_mul_right ?_ h2r
  have hA : (q:ℝ) ≤ (q.totient:ℝ) * (2:ℝ)^(q.primeFactors.card) :=
    totient_lower_bound q hq1
  have hB := factorial_le_primeFactors_card q hq1
  have hFR : ((Nat.factorial (q.primeFactors.card + 1):ℕ):ℝ) ≤ (q:ℝ) := by
    exact_mod_cast hB
  have hFpos : (0:ℝ) < Real.sqrt ((Nat.factorial (q.primeFactors.card + 1):ℕ):ℝ) :=
    Real.sqrt_pos.2 (by exact_mod_cast Nat.factorial_pos (q.primeFactors.card + 1))
  have hC := pow_div_sqrt_factorial_le c N hc1 hcN (q.primeFactors.card)
  rw [div_le_iff₀ hFpos] at hC
  have hCpos : (0:ℝ) < c^(N+1) := pow_pos hcpos _
  have hpow4 : ((2*m:ℕ):ℝ)^(q.primeFactors.card) * (2:ℝ)^(q.primeFactors.card)
      = (4*(m:ℝ))^(q.primeFactors.card) := by
    rw [show ((2*m:ℕ):ℝ) = 2*(m:ℝ) from by push_cast; ring, ← mul_pow]
    ring_nf
  have hmkR : (m:ℝ) ≤ (k:ℝ) := by exact_mod_cast hmk
  have h4mc' : 4*(m:ℝ) ≤ c := by rw [hc]; nlinarith
  have h4mc : (4*(m:ℝ))^(q.primeFactors.card) ≤ c^(q.primeFactors.card) :=
    pow_le_pow_left₀ (by positivity) h4mc' _
  have h4 : (4*(m:ℝ))^(q.primeFactors.card) ≤ c^(N+1) * Real.sqrt (q:ℝ) :=
    le_trans h4mc (le_trans hC (mul_le_mul_of_nonneg_left (Real.sqrt_le_sqrt hFR) hCpos.le))
  have h4q : (4*(m:ℝ))^(q.primeFactors.card) * Real.sqrt (q:ℝ) ≤ c^(N+1) * (q:ℝ) := by
    have h := mul_le_mul_of_nonneg_right h4 (Real.sqrt_nonneg (q:ℝ))
    rwa [mul_assoc, Real.mul_self_sqrt hqposR.le] at h
  calc (((2*m:ℕ):ℝ)^(q.primeFactors.card) * Real.sqrt (q:ℝ)) * (2:ℝ)^(q.primeFactors.card)
      = (4*(m:ℝ))^(q.primeFactors.card) * Real.sqrt (q:ℝ) := by
        rw [show (((2*m:ℕ):ℝ)^(q.primeFactors.card) * Real.sqrt (q:ℝ)) *
              (2:ℝ)^(q.primeFactors.card)
            = ((2*m:ℕ):ℝ)^(q.primeFactors.card) * (2:ℝ)^(q.primeFactors.card) *
              Real.sqrt (q:ℝ) from by ring,
          hpow4]
    _ ≤ c^(N+1) * (q:ℝ) := h4q
    _ ≤ c^(N+1) * ((q.totient:ℝ) * (2:ℝ)^(q.primeFactors.card)) :=
          mul_le_mul_of_nonneg_left hA hCpos.le
    _ = (c^(N+1) * (q.totient:ℝ)) * (2:ℝ)^(q.primeFactors.card) := by ring

end Work.N8
