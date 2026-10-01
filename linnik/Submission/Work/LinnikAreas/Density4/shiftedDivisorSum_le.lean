/-
# The shifted divisor sum estimate `shiftedDivisorSum_le`

For squarefree `r ≥ 1` we prove
`Σ_{d ∣ r, d ≥ 2} 1/(d · σ_{-1/2}(r/d)) ≤ 9/10`,  `σ_{-1/2}(m) = Σ_{e ∣ m} e^{-1/2}`.

Write `Tall r = Σ_{d ∣ r} 1/(d · σ_{-1/2}(r/d))`.  The sum in the statement is
`Tall r - 1/σ_{-1/2}(r)` (the `d = 1` term).  For squarefree `r` we prove the two
Euler-product identities
`Tall r = Π_{p ∣ r} f(p) = Φ r.primeFactors`  and
`1/σ_{-1/2}(r) = Π_{p ∣ r} g(p) = Ψ r.primeFactors`,
where `f(p) = 1/p + g(p)` and `g(p) = (1+p^{-1/2})^{-1}`; both are proved by strong
induction on `r`, splitting off a prime factor and using the multiplicativity of
`σ_{-1/2}` and the recursion `Tall (p*m) = f(p) · Tall m`.  The final numerical bound
`Φ s - Ψ s ≤ 9/10` for finite prime sets `s` is
`Work.LinnikAreas.Density4.Phi_sub_Psi_le`.
-/
import Mathlib
import Submission.Work.LinnikAreas.Density4.ShiftedDefs
import Submission.Work.LinnikAreas.Density4.sig_mul_of_coprime
import Submission.Work.LinnikAreas.Density4.sum_divisors_prime_mul
import Submission.Work.LinnikAreas.Density4.Phi_sub_Psi_le

namespace Work.LinnikAreas.Density4
noncomputable section

open Finset

-- ===== basic =====
lemma sigR_one : sigR 1 = 1 := by
  rw [sigR, Nat.divisors_one]
  simp

lemma sigR_prime {p : ℕ} (hp : p.Prime) : sigR p = 1 + 1 / Real.sqrt (p : ℝ) := by
  rw [sigR, hp.divisors]
  have h1p : (1:ℕ) ≠ p := by have := hp.one_lt; omega
  rw [Finset.sum_insert (by simp [h1p])]
  simp

lemma one_div_sigR_prime {p : ℕ} (hp : p.Prime) : 1 / sigR p = gR p := by
  rw [sigR_prime hp, gR, one_div]

lemma one_le_sigR {n : ℕ} (hn : n ≠ 0) : 1 ≤ sigR n := by
  rw [sigR]
  have h1 : (1:ℕ) ∈ n.divisors := Nat.mem_divisors.mpr ⟨one_dvd n, hn⟩
  have hnn : ∀ d ∈ n.divisors, (0:ℝ) ≤ (1:ℝ) / Real.sqrt (d : ℝ) := by
    intro d _
    exact div_nonneg zero_le_one (Real.sqrt_nonneg _)
  calc (1:ℝ) = (1:ℝ)/Real.sqrt ((1:ℕ):ℝ) := by simp
    _ ≤ ∑ d ∈ n.divisors, (1:ℝ) / Real.sqrt (d : ℝ) := Finset.single_le_sum hnn h1

lemma sigR_pos {n : ℕ} (hn : n ≠ 0) : 0 < sigR n := lt_of_lt_of_le one_pos (one_le_sigR hn)

-- ===== PhiSh / Psi insertion =====
lemma Phi_insert {p : ℕ} {s : Finset ℕ} (hp : p ∉ s) :
    PhiSh (insert p s) = fR p * PhiSh s := by
  rw [PhiSh, PhiSh, Finset.prod_insert hp]

lemma Psi_insert {p : ℕ} {s : Finset ℕ} (hp : p ∉ s) :
    Psi (insert p s) = gR p * Psi s := by
  rw [Psi, Psi, Finset.prod_insert hp]

-- ===== recursion for Tall under multiplying by a prime =====
lemma Tall_mul_prime {p m : ℕ} (hp : p.Prime) (hm : p.Coprime m) :
    Tall (p * m) = fR p * Tall m := by
  have hpm : p ≠ 0 := hp.ne_zero
  rw [Tall, sum_divisors_prime_mul hp hm (fun d => (1:ℝ)/((d:ℝ)*sigR (p*m/d))), Tall,
      Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl ?_
  intro d hd
  have hdvd : d ∣ m := (Nat.mem_divisors.mp hd).1
  have hm0 : m ≠ 0 := (Nat.mem_divisors.mp hd).2
  have hmpos : 0 < m := Nat.pos_of_ne_zero hm0
  have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdvd hmpos
  have hdn : d ≠ 0 := ne_of_gt hdpos
  have hcd : p.Coprime (m/d) := hm.coprime_dvd_right (Nat.div_dvd_of_dvd hdvd)
  have hmdn : m/d ≠ 0 := ne_of_gt (Nat.div_pos (Nat.le_of_dvd hmpos hdvd) hdpos)
  rw [Nat.mul_div_assoc p hdvd, Nat.mul_div_mul_left m d hp.pos, sig_mul_of_coprime hcd,
      Nat.cast_mul, fR, ← one_div_sigR_prime hp]
  have hdr : (d:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hdn
  have hpr : (p:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hpm
  have hsp : sigR p ≠ 0 := ne_of_gt (sigR_pos hpm)
  have hsm : sigR (m/d) ≠ 0 := ne_of_gt (sigR_pos hmdn)
  field_simp
  ring


-- ===== main identities =====
lemma Tall_eq_Phi (n : ℕ) (hsq : Squarefree n) : Tall n = PhiSh n.primeFactors := by
  revert hsq
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hsq
    rcases Nat.lt_or_ge n 2 with hlt | hge
    · interval_cases n
      · exfalso
        rw [Nat.squarefree_iff_prime_squarefree] at hsq
        exact (hsq 2 (by norm_num)) (dvd_zero (2*2))
      · simp [Tall, PhiSh, sigR, Nat.divisors_one, Nat.primeFactors_one]
    · have hnpos : 0 < n := by omega
      obtain ⟨p, hpp, hpdvd⟩ := Nat.exists_prime_and_dvd (by omega : n ≠ 1)
      set m := n / p with hmdef
      have hn_eq : p * m = n := by rw [hmdef]; exact Nat.mul_div_cancel' hpdvd
      have hmdvd : m ∣ n := by rw [hmdef]; exact Nat.div_dvd_of_dvd hpdvd
      have hm0 : m ≠ 0 := by rintro h; rw [h, mul_zero] at hn_eq; omega
      have hm_lt : m < n := by rw [hmdef]; exact Nat.div_lt_self hnpos hpp.one_lt
      have hsqm : Squarefree m := Squarefree.squarefree_of_dvd hmdvd hsq
      have hcop : p.Coprime m := by
        rw [hpp.coprime_iff_not_dvd]
        intro hpm
        have hppn : p * p ∣ n := by rw [← hn_eq]; exact mul_dvd_mul_left p hpm
        exact (Nat.squarefree_iff_prime_squarefree.mp hsq p hpp) hppn
      have hpmem : p ∉ m.primeFactors := by
        rw [Nat.mem_primeFactors]
        rintro ⟨_, hpdm, _⟩
        exact (hpp.coprime_iff_not_dvd.mp hcop) hpdm
      have hpf : n.primeFactors = insert p m.primeFactors := by
        rw [← hn_eq, Nat.primeFactors_mul hpp.ne_zero hm0, hpp.primeFactors, Finset.singleton_union]
      have hTall : Tall n = fR p * Tall m := by rw [← hn_eq]; exact Tall_mul_prime hpp hcop
      rw [hTall, ih m hm_lt hsqm, hpf, Phi_insert hpmem]

lemma inv_sigR_eq_Psi (n : ℕ) (hsq : Squarefree n) : 1 / sigR n = Psi n.primeFactors := by
  revert hsq
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hsq
    rcases Nat.lt_or_ge n 2 with hlt | hge
    · interval_cases n
      · exfalso
        rw [Nat.squarefree_iff_prime_squarefree] at hsq
        exact (hsq 2 (by norm_num)) (dvd_zero (2*2))
      · simp [Psi, sigR, Nat.divisors_one, Nat.primeFactors_one]
    · have hnpos : 0 < n := by omega
      obtain ⟨p, hpp, hpdvd⟩ := Nat.exists_prime_and_dvd (by omega : n ≠ 1)
      set m := n / p with hmdef
      have hn_eq : p * m = n := by rw [hmdef]; exact Nat.mul_div_cancel' hpdvd
      have hmdvd : m ∣ n := by rw [hmdef]; exact Nat.div_dvd_of_dvd hpdvd
      have hm0 : m ≠ 0 := by rintro h; rw [h, mul_zero] at hn_eq; omega
      have hm_lt : m < n := by rw [hmdef]; exact Nat.div_lt_self hnpos hpp.one_lt
      have hsqm : Squarefree m := Squarefree.squarefree_of_dvd hmdvd hsq
      have hcop : p.Coprime m := by
        rw [hpp.coprime_iff_not_dvd]
        intro hpm
        have hppn : p * p ∣ n := by rw [← hn_eq]; exact mul_dvd_mul_left p hpm
        exact (Nat.squarefree_iff_prime_squarefree.mp hsq p hpp) hppn
      have hpmem : p ∉ m.primeFactors := by
        rw [Nat.mem_primeFactors]
        rintro ⟨_, hpdm, _⟩
        exact (hpp.coprime_iff_not_dvd.mp hcop) hpdm
      have hpf : n.primeFactors = insert p m.primeFactors := by
        rw [← hn_eq, Nat.primeFactors_mul hpp.ne_zero hm0, hpp.primeFactors, Finset.singleton_union]
      have hsig : sigR n = sigR p * sigR m := by rw [← hn_eq]; exact sig_mul_of_coprime hcop
      have hsplit : 1 / (sigR p * sigR m) = (1 / sigR p) * (1 / sigR m) := by
        have hp : sigR p ≠ 0 := ne_of_gt (sigR_pos hpp.ne_zero)
        have hm : sigR m ≠ 0 := ne_of_gt (sigR_pos hm0)
        field_simp
      rw [hsig, hsplit, one_div_sigR_prime hpp, ih m hm_lt hsqm, hpf, Psi_insert hpmem]

/-- Key bookkeeping estimate for the recursion: for squarefree `r ≥ 1`,
`Σ_{d | r, d ≥ 2} 1/( d · σ_{-1/2}(r/d) ) ≤ 9/10`, where `σ_{-1/2}(m) = Σ_{e | m} 1/√e`.
(Equivalently, writing `f(p) = (p+1+p^{-1/2})/(p+√p)` and `g(p) = (1+p^{-1/2})^{-1}`, the sum
equals `Π_{p | r} f(p) - Π_{p | r} g(p)`; one has `f(p) - g(p) = 1/p`, `f(p) ≤ 1` for `p ≥ 3`,
`f(2) = 1.0858…`, and numerically the supremum over squarefree `r` is `0.6792…`, attained at
`r = 6` and `r = 30`.  A workable route: use the telescoping identity
`Π f - Π g = Σ_j (f(p_j)-g(p_j))·Π_{i<j} f(p_i)·Π_{i>j} g(p_i)` over the primes `p | r`
(in a suitable order), and note `Π_{p | r} f(p) ≤ 1.1` while
`Σ_j 1/p_j · Π_{i>j} g(p_i)` is small — or an induction on the primes using the recursion
`Φ(r·p) = Φ(r)·f(p)` for `Φ(r) := Π_{p|r} f(p)` together with `1 - Π g/f ≤ Σ (1 - g(p)/f(p))`.) -/
theorem shiftedDivisorSum_le {r : ℕ} (hr : 1 ≤ r) (hsq : Squarefree r) :
    (∑ d ∈ r.divisors.filter (fun d => 2 ≤ d),
        (1:ℝ) / ((d:ℝ) * (∑ e ∈ (r/d).divisors, (1:ℝ)/Real.sqrt (e:ℝ)))) ≤ 9/10 := by
  have hr0 : r ≠ 0 := by omega
  have hrpos : 0 < r := by omega
  change (∑ d ∈ r.divisors.filter (fun d => 2 ≤ d), (1:ℝ) / ((d:ℝ) * sigR (r/d))) ≤ 9/10
  have hfilter : r.divisors.filter (fun d => 2 ≤ d) = r.divisors.erase 1 := by
    ext d
    simp only [Finset.mem_filter, Finset.mem_erase]
    constructor
    · rintro ⟨hd, h2⟩
      exact ⟨by omega, hd⟩
    · rintro ⟨hd1, hd⟩
      refine ⟨hd, ?_⟩
      have hdvd : d ∣ r := (Nat.mem_divisors.mp hd).1
      have hdpos : 0 < d := Nat.pos_of_dvd_of_pos hdvd hrpos
      omega
  rw [hfilter]
  have hmem1 : (1:ℕ) ∈ r.divisors := Nat.mem_divisors.mpr ⟨one_dvd r, hr0⟩
  have hsplit : ∑ d ∈ r.divisors.erase 1, (1:ℝ) / ((d:ℝ) * sigR (r/d))
      = Tall r - 1/sigR r := by
    have h := Finset.sum_erase_add r.divisors (fun d => (1:ℝ) / ((d:ℝ) * sigR (r/d))) hmem1
    have hf1 : (1:ℝ) / (((1:ℕ):ℝ) * sigR (r/1)) = 1/sigR r := by simp
    rw [Tall]
    linarith [h, hf1]
  rw [hsplit]
  calc Tall r - 1/sigR r = PhiSh r.primeFactors - Psi r.primeFactors := by
        rw [Tall_eq_Phi r hsq, inv_sigR_eq_Psi r hsq]
    _ ≤ 9/10 := Phi_sub_Psi_le r.primeFactors (fun p hp => (Nat.mem_primeFactors.mp hp).1)

end
end Work.LinnikAreas.Density4
