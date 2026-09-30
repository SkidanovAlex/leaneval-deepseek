import Mathlib
import Submission.Work.BMF.mr_direct.buchstab_aux

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# At most one prime lies in a `j`-window with `j ≠ ⌊K log p⌋`

`winPrimes K j` is the set of primes in the `j`-th logarithmic window
`[e^{j/K}, e^{(j+1)/K}]`, while `jdex K p = ⌊K log p⌋` is the window index
"naturally" attached to `p`. The main result says that the number of pairs
`(j, p)` with `j` ranging over `indexSet K P Q`, `p ∈ winPrimes K j`, `P ≤ p ≤ Q`
and `j ≠ jdex K p` is at most `1`.

The reason is rigidity: if `p` is prime and `p ∈ [e^{j/K}, e^{(j+1)/K}]` then
`j ≤ K log p ≤ j+1`, so `⌊K log p⌋ ∈ {j, j+1}`; the condition `j ≠ ⌊K log p⌋`
forces `⌊K log p⌋ = j+1`, and then `j+1 ≤ K log p ≤ j+1` pins `p` down to
`p = e^{(j+1)/K}`, i.e. `K log p = j+1` is an integer. Two primes `p, q` cannot
both satisfy `K log p, K log q ∈ ℤ`: it would force `p^m = q^n` for positive
integers `m, n`, impossible for distinct primes by unique factorization.
-/

set_option autoImplicit false

namespace Work.BMF.mr_direct

open Work.BMF.mrDirect

/-- Rigidity of a logarithmic window: if the prime `p` lies in the `j`-th window
and `j` is not the index `⌊K log p⌋`, then `p` is exactly the right endpoint of the
window, so that `K * log p = j + 1` is an integer. -/
lemma mul_log_eq_of_mem_winPrimes_ne_jdex (K : ℝ) (hK : 0 < K) {j p : ℕ}
    (hp : p ∈ winPrimes K j) (hne : j ≠ jdex K p) :
    K * Real.log (p : ℝ) = (j : ℝ) + 1 := by
  obtain ⟨hprime, h1, h2⟩ := mem_winPrimes.mp hp
  have hp_pos : (0 : ℝ) < p := by exact_mod_cast hprime.pos
  -- `e^{j/K} ≤ p` gives `j ≤ K log p`
  have hlog1 : (j : ℝ) ≤ K * Real.log (p : ℝ) := by
    have h := Real.log_le_log (Real.exp_pos _) h1
    rw [Real.log_exp] at h
    rw [div_le_iff₀ hK] at h
    simpa [mul_comm] using h
  -- `p ≤ e^{(j+1)/K}` gives `K log p ≤ j + 1`
  have hlog2 : K * Real.log (p : ℝ) ≤ (j : ℝ) + 1 := by
    have h := Real.log_le_log hp_pos h2
    rw [Real.log_exp] at h
    rw [le_div_iff₀ hK] at h
    simpa [mul_comm] using h
  -- hence `⌊K log p⌋ ∈ {j, j+1}`, and `≠ j` forces `⌊K log p⌋ = j + 1`
  have hle_floor : j ≤ jdex K p := Nat.le_floor hlog1
  have hfloor_le : jdex K p ≤ j + 1 := by
    have h : jdex K p ≤ ⌊(j : ℝ) + 1⌋₊ := Nat.floor_mono hlog2
    have h2' : ⌊(j : ℝ) + 1⌋₊ = j + 1 := by
      rw [show (j : ℝ) + 1 = ((j + 1 : ℕ) : ℝ) by rw [Nat.cast_add_one],
        Nat.floor_natCast]
    rwa [h2'] at h
  have hjdex : jdex K p = j + 1 := by omega
  -- `j + 1 ≤ K log p`, and combined with `K log p ≤ j + 1` this is an equality,
  -- giving `p = e^{(j+1)/K}`
  have h0 : (0 : ℝ) ≤ K * Real.log (p : ℝ) := le_trans (Nat.cast_nonneg j) hlog1
  have hge : ((j : ℝ) + 1) ≤ K * Real.log (p : ℝ) := by
    have h : ((jdex K p : ℕ) : ℝ) ≤ K * Real.log (p : ℝ) := Nat.floor_le h0
    rw [hjdex, Nat.cast_add_one] at h
    exact h
  have hexp_le : Real.exp (((j : ℝ) + 1) / K) ≤ (p : ℝ) := by
    have hle : ((j : ℝ) + 1) / K ≤ Real.log (p : ℝ) :=
      (div_le_iff₀ hK).mpr (by simpa [mul_comm] using hge)
    calc Real.exp (((j : ℝ) + 1) / K) ≤ Real.exp (Real.log (p : ℝ)) :=
          (Real.exp_le_exp).mpr hle
      _ = (p : ℝ) := Real.exp_log hp_pos
  have heq : (p : ℝ) = Real.exp (((j : ℝ) + 1) / K) := le_antisymm h2 hexp_le
  have hlogeq := congrArg Real.log heq
  rw [Real.log_exp] at hlogeq
  rw [hlogeq, mul_div_cancel₀ _ (ne_of_gt hK)]

/-- At most one pair `(j, p)` with `j ∈ indexSet K P Q`, `p ∈ winPrimes K j` a prime
in `[P, Q]`, and `j ≠ ⌊K log p⌋`. -/
theorem card_winPrimes_filter_inQ_ne_jdex_le_one (K P Q : ℝ) (hK : 0 < K) :
    ((Work.BMF.mrDirect.indexSet K P Q).sigma (fun j =>
        (Work.BMF.mrDirect.winPrimes K j).filter
          (fun (p : ℕ) =>
            P ≤ (p : ℝ) ∧ (p : ℝ) ≤ Q ∧ j ≠ Work.BMF.mrDirect.jdex K p))).card ≤ 1 := by
  rw [Finset.card_le_one]
  rintro ⟨j1, p1⟩ h1 ⟨j2, p2⟩ h2
  rw [Finset.mem_sigma] at h1 h2
  obtain ⟨_, h1'⟩ := h1
  obtain ⟨_, h2'⟩ := h2
  obtain ⟨hp1, hP1, hQ1, hne1⟩ := Finset.mem_filter.mp h1'
  obtain ⟨hp2, hP2, hQ2, hne2⟩ := Finset.mem_filter.mp h2'
  have e1 := mul_log_eq_of_mem_winPrimes_ne_jdex K hK hp1 hne1
  have e2 := mul_log_eq_of_mem_winPrimes_ne_jdex K hK hp2 hne2
  have hp1prime : p1.Prime := (mem_winPrimes.mp hp1).1
  have hp2prime : p2.Prime := (mem_winPrimes.mp hp2).1
  have hp1pos : (0 : ℝ) < p1 := by exact_mod_cast hp1prime.pos
  have hp2pos : (0 : ℝ) < p2 := by exact_mod_cast hp2prime.pos
  -- `(j2+1) log p1 = (j1+1) log p2`, since both sides equal `(j1+1)(j2+1)/K`
  have hcross : ((j2 : ℝ) + 1) * Real.log (p1 : ℝ) = ((j1 : ℝ) + 1) * Real.log (p2 : ℝ) := by
    rw [← e2, ← e1]; ring
  -- exponentiate: `p1^(j2+1) = p2^(j1+1)`
  have hpow : (p1 : ℝ) ^ (j2 + 1) = (p2 : ℝ) ^ (j1 + 1) := by
    have h := congrArg Real.exp hcross
    rw [← Nat.cast_add_one (j2), Real.exp_nat_mul, Real.exp_log hp1pos,
        ← Nat.cast_add_one (j1), Real.exp_nat_mul, Real.exp_log hp2pos] at h
    exact h
  have hnat : p1 ^ (j2 + 1) = p2 ^ (j1 + 1) := by exact_mod_cast hpow
  -- unique factorization forces `p1 = p2`
  have hp_eq : p1 = p2 := by
    have hdvd : p1 ∣ p2 := by
      have h : p1 ∣ p2 ^ (j1 + 1) := by
        rw [← hnat]
        exact dvd_pow_self p1 (by omega)
      exact hp1prime.dvd_of_dvd_pow h
    exact ((hp2prime.dvd_iff_eq hp1prime.ne_one).mp hdvd).symm
  -- and then `j1 + 1 = j2 + 1`
  have hj_eq : j1 = j2 := by
    have h : ((j1 : ℝ) + 1) = ((j2 : ℝ) + 1) := by rw [← e1, hp_eq, e2]
    have h2 : (j1 : ℝ) = (j2 : ℝ) := by linarith
    exact_mod_cast h2
  subst hj_eq
  subst hp_eq
  rfl

end Work.BMF.mr_direct
