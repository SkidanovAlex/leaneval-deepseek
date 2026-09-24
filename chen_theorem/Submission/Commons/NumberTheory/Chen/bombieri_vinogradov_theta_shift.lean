import Mathlib
import Submission.Commons.NumberTheory.BombieriVinogradov.bombieri_vinogradov_family
import Submission.Commons.NumberTheory.PrimeNumberTheorem.psi_sub_id_powLog

/-!
# `bombieri_vinogradov_theta_shift` (θ-shifted Bombieri–Vinogradov)

For every `A > 0` there is `B > 0` such that, for all sufficiently large `x`,

`Σ_{d odd, 1 ≤ d ≤ √x/(log x)^B} | Σ_{p ≤ x prime, d | p+2} log p  −  x/φ(d) | ≤ x/(log x)^A`.

This is the Bombieri–Vinogradov error estimate for the **theta** (prime, `log p`)
weights of the shifted sequence `p + 2`; it is the analytic input required by the
theta-weighted sieve steps of Chen's theorem (`chen_rough_prime_theta_lower`,
`rough_theta_lower_of_bv`, …).

## Proof

The prime/log-`p` (θ) sums are reduced to the von-Mangoldt (ψ) sums and then to
the **family-form Bombieri–Vinogradov theorem**, both available in the commons:

* `import Submission.Commons.NumberTheory.BombieriVinogradov.bombieri_vinogradov_family`
  — the root black box: for every admissible residue family `a` (`gcd (a q) q = 1`),
  `Σ_{2 ≤ q ≤ √x/log^B x} |ψ(x; q, a q) − x/φ(q)| ≤ x/log^A x`;
* `import Submission.Commons.NumberTheory.PrimeNumberTheorem.psi_sub_id_powLog`
  — the Prime Number Theorem with power-of-log error (used for the modulus `d = 1`).

The reduction (all lemmas below, proved from Mathlib + the two commons imports):

1. `psiDSum`/`thetaDSum` are the shifted ψ- and θ-sums over `n ≤ x` with `d ∣ n+2`.
   `psiDSum_eq_thetaDSum_add` decomposes `ψ_d = θ_d + (prime-power correction)`,
   `sum_notPrime_eq_psi_sub_theta` identifies the total correction with `ψ(x) − θ(x)`
   (via `Chebyshev.psi_eq_sum_Icc`/`theta_eq_sum_Icc`), and
   `theta_psi_abs_bound` gives the uniform bound `|θ_d(x) − ψ_d(x)| ≤ C·√x`
   (from `Chebyshev.psi_sub_theta_le_mul_sqrt`).
2. `famRes q` (`= q − 2` for odd `q ≥ 3`, `= 1` otherwise) is the admissible
   residue family with `famRes q ≡ −2 (mod q)`; `psiTermT_eq_famTerm` shows that
   for odd `d ≥ 3` the ψ-shift term coincides with the family term.
3. `oddIcc_split` separates the modulus `d = 1`, handled by `psi_sub_id_powLog`
   with exponent `A + 3`; the odd moduli `d ≥ 3` are compared with the family sum
   restricted to a smaller cutoff (`oddIcc2_card_le`, `qCutT_mono`).
4. The correction `Σ_d |θ_d − ψ_d| ≤ (#moduli)·C√x ≤ C·x/(log x)^B` is absorbed by
   the two logarithms of slack built into `B = max B_fam (A+2) + 1`
   (`div_rpow_add_le_quarter`, `eventually_mul_log_pow_le_sqrt`,
   `eventually_const_le_log_sq`, `eventually_one_le_qCutT`).

A shorter alternative proof of this theorem from the *ψ-shift* form
`bombieri_vinogradov_shift` is available in the commons as the adapter
`Commons.NumberTheory.BombieriVinogradov.theta_shift_of_psi_shift`.
-/


open Filter Finset
open scoped BigOperators



namespace Commons.NumberTheory.Chen

noncomputable section

/-- von Mangoldt-shifted sum: Σ_{n ≤ x, d ∣ n+2} Λ(n) -/
noncomputable def psiDSum (x d : ℕ) : ℝ :=
  ((Finset.range (x + 1)).filter (fun n => d ∣ n + 2)).sum
    (fun n => ArithmeticFunction.vonMangoldt n)

/-- theta-shifted sum: Σ_{p ≤ x, p prime, d ∣ p+2} log p -/
noncomputable def thetaDSum (x d : ℕ) : ℝ :=
  ((Finset.range (x + 1)).filter (fun p => p.Prime ∧ d ∣ p + 2)).sum
    (fun p => Real.log (p : ℝ))

/-- decomposition of ψ-shifted sum: primes (= θ part) plus prime-powers with k ≥ 2 -/
lemma psiDSum_eq_thetaDSum_add (x d : ℕ) :
    psiDSum x d = thetaDSum x d +
      ((Finset.range (x + 1)).filter (fun n => ¬ n.Prime ∧ d ∣ n + 2)).sum
        (fun n => ArithmeticFunction.vonMangoldt n) := by
  unfold psiDSum thetaDSum
  let R : Finset ℕ := (Finset.range (x + 1)).filter (fun n => d ∣ n + 2)
  have hdecomp : (∑ n ∈ R, ArithmeticFunction.vonMangoldt n) =
      (∑ n ∈ R with n.Prime, ArithmeticFunction.vonMangoldt n) +
        (∑ n ∈ R with ¬ n.Prime, ArithmeticFunction.vonMangoldt n) := by
    exact (Finset.sum_filter_add_sum_filter_not R (fun n => n.Prime)
      (fun n => ArithmeticFunction.vonMangoldt n)).symm
  calc
    (∑ n ∈ (Finset.range (x + 1)).filter (fun n => d ∣ n + 2), ArithmeticFunction.vonMangoldt n)
        = (∑ n ∈ R, ArithmeticFunction.vonMangoldt n) := rfl
    _ = (∑ n ∈ R with n.Prime, ArithmeticFunction.vonMangoldt n) +
          (∑ n ∈ R with ¬ n.Prime, ArithmeticFunction.vonMangoldt n) := hdecomp
    _ = (∑ p ∈ (Finset.range (x + 1)).filter (fun p => p.Prime ∧ d ∣ p + 2), Real.log (p : ℝ)) +
          (∑ n ∈ (Finset.range (x + 1)).filter (fun n => ¬ n.Prime ∧ d ∣ n + 2),
              ArithmeticFunction.vonMangoldt n) := by
          congr 1
          · -- prime part: Λ p = log p on primes, and filter-filter coincidence
            have hR : R.filter (fun n => n.Prime) =
                (Finset.range (x + 1)).filter (fun p => p.Prime ∧ d ∣ p + 2) := by
              rw [Finset.filter_filter]
              congr 1
              funext p
              by_cases hprime : p.Prime <;> simp [hprime, and_comm]
            rw [hR]
            refine Finset.sum_congr rfl ?_
            intro p hp
            exact ArithmeticFunction.vonMangoldt_apply_prime (Finset.mem_filter.mp hp).2.1
          · have hR2 : R.filter (fun n => ¬ n.Prime) =
                (Finset.range (x + 1)).filter (fun n => ¬ n.Prime ∧ d ∣ n + 2) := by
              rw [Finset.filter_filter]
              congr 1
              funext n
              by_cases hn : n.Prime <;> simp [hn]
            rw [hR2]

/-- the extra (prime power) part is nonnegative -/
lemma psiDSum_sub_thetaDSum_nonneg (x d : ℕ) : 0 ≤ psiDSum x d - thetaDSum x d := by
  rw [psiDSum_eq_thetaDSum_add x d]
  have hExtra : 0 ≤ ((Finset.range (x + 1)).filter (fun n => ¬ n.Prime ∧ d ∣ n + 2)).sum
        (fun n => ArithmeticFunction.vonMangoldt n) :=
    Finset.sum_nonneg (fun n hn => ArithmeticFunction.vonMangoldt_nonneg)
  linarith

/-- θ-shift ≤ ψ-shift -/
lemma thetaDSum_le_psiDSum (x d : ℕ) : thetaDSum x d ≤ psiDSum x d := by
  rw [psiDSum_eq_thetaDSum_add x d]
  exact le_add_of_nonneg_right (Finset.sum_nonneg (fun n hn => ArithmeticFunction.vonMangoldt_nonneg))

/-- extra ≤ global ψ − θ over all non-prime n -/
lemma psiDSum_sub_thetaDSum_le_notPrime (x d : ℕ) :
    psiDSum x d - thetaDSum x d ≤
      ((Finset.range (x + 1)).filter (fun n => ¬ n.Prime)).sum
        (fun n => ArithmeticFunction.vonMangoldt n) := by
  rw [psiDSum_eq_thetaDSum_add x d]
  have hsub : (Finset.range (x + 1)).filter (fun n => ¬ n.Prime ∧ d ∣ n + 2) ⊆
      (Finset.range (x + 1)).filter (fun n => ¬ n.Prime) := by
    intro n hn
    rw [Finset.mem_filter] at hn ⊢
    exact ⟨hn.1, hn.2.1⟩
  simpa using
    (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n hn _ => ArithmeticFunction.vonMangoldt_nonneg))

/-- Σ_{n ≤ x, ¬n prime} Λ(n) = ψ(x) − θ(x) (x a natural number) -/
lemma sum_notPrime_eq_psi_sub_theta (x : ℕ) :
    ((Finset.range (x + 1)).filter (fun n => ¬ n.Prime)).sum
        (fun n => ArithmeticFunction.vonMangoldt n)
      = Chebyshev.psi (x : ℝ) - Chebyshev.theta (x : ℝ) := by
  have hpsi : Chebyshev.psi (x : ℝ) = (∑ n ∈ Finset.Icc 0 x, ArithmeticFunction.vonMangoldt n) := by
    simpa [Nat.floor_natCast] using (Chebyshev.psi_eq_sum_Icc (x : ℝ))
  have htheta : Chebyshev.theta (x : ℝ) =
      (∑ p ∈ Finset.Icc 0 x with p.Prime, Real.log (p : ℝ)) := by
    simpa [Nat.floor_natCast] using (Chebyshev.theta_eq_sum_Icc (x : ℝ))
  have hdecomp : (∑ n ∈ Finset.Icc 0 x, ArithmeticFunction.vonMangoldt n) =
      (∑ n ∈ Finset.Icc 0 x with n.Prime, ArithmeticFunction.vonMangoldt n) +
        (∑ n ∈ Finset.Icc 0 x with ¬ n.Prime, ArithmeticFunction.vonMangoldt n) := by
    exact (Finset.sum_filter_add_sum_filter_not (Finset.Icc 0 x) (fun n => n.Prime)
      (fun n => ArithmeticFunction.vonMangoldt n)).symm
  have hprime : (∑ n ∈ Finset.Icc 0 x with n.Prime, ArithmeticFunction.vonMangoldt n) =
      (∑ p ∈ Finset.Icc 0 x with p.Prime, Real.log (p : ℝ)) := by
    refine Finset.sum_congr rfl ?_
    intro p hp
    exact ArithmeticFunction.vonMangoldt_apply_prime (Finset.mem_filter.mp hp).2
  have hset : (Finset.range (x + 1)).filter (fun n => ¬ n.Prime) =
      (Finset.Icc 0 x).filter (fun n => ¬ n.Prime) := by
    ext n
    by_cases hnp : n.Prime
    · simp [hnp]
    · simp [hnp, Finset.mem_range, Finset.mem_Icc]
  calc
    ((Finset.range (x + 1)).filter (fun n => ¬ n.Prime)).sum
        (fun n => ArithmeticFunction.vonMangoldt n)
        = ((Finset.Icc 0 x).filter (fun n => ¬ n.Prime)).sum
            (fun n => ArithmeticFunction.vonMangoldt n) := by rw [hset]
    _ = (∑ n ∈ Finset.Icc 0 x with ¬ n.Prime, ArithmeticFunction.vonMangoldt n) := rfl
    _ = (∑ n ∈ Finset.Icc 0 x, ArithmeticFunction.vonMangoldt n) -
          (∑ n ∈ Finset.Icc 0 x with n.Prime, ArithmeticFunction.vonMangoldt n) := by
          rw [hdecomp]
          ring
    _ = Chebyshev.psi (x : ℝ) - Chebyshev.theta (x : ℝ) := by
          rw [hpsi, hprime, htheta]

/-- per-modulus ψ − θ extra ≤ global ψ(x) − θ(x) -/
lemma psiDSum_sub_thetaDSum_le_psi_sub_theta (x d : ℕ) :
    psiDSum x d - thetaDSum x d ≤ Chebyshev.psi (x : ℝ) - Chebyshev.theta (x : ℝ) := by
  calc
    psiDSum x d - thetaDSum x d
        ≤ ((Finset.range (x + 1)).filter (fun n => ¬ n.Prime)).sum
            (fun n => ArithmeticFunction.vonMangoldt n) := psiDSum_sub_thetaDSum_le_notPrime x d
    _ = Chebyshev.psi (x : ℝ) - Chebyshev.theta (x : ℝ) := sum_notPrime_eq_psi_sub_theta x

/-- main bridge: |θ_d(x) − ψ_d(x)| ≤ C·√x uniformly in the modulus d -/
lemma theta_psi_abs_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (x d : ℕ), |thetaDSum x d - psiDSum x d| ≤ C * Real.sqrt (x : ℝ) := by
  rcases Chebyshev.psi_sub_theta_le_mul_sqrt with ⟨C0, hC0⟩
  refine ⟨max C0 1, ?_, ?_⟩
  · exact lt_of_lt_of_le zero_lt_one (le_max_right C0 1)
  · intro x d
    have hnonneg : 0 ≤ psiDSum x d - thetaDSum x d := psiDSum_sub_thetaDSum_nonneg x d
    have hle : psiDSum x d - thetaDSum x d ≤ max C0 1 * Real.sqrt (x : ℝ) := by
      calc
        psiDSum x d - thetaDSum x d
            ≤ Chebyshev.psi (x : ℝ) - Chebyshev.theta (x : ℝ) := psiDSum_sub_thetaDSum_le_psi_sub_theta x d
        _ ≤ C0 * Real.sqrt (x : ℝ) := hC0 (x : ℝ)
        _ ≤ max C0 1 * Real.sqrt (x : ℝ) := by
            exact mul_le_mul_of_nonneg_right (le_max_left C0 1) (Real.sqrt_nonneg (x : ℝ))
    calc
      |thetaDSum x d - psiDSum x d| = psiDSum x d - thetaDSum x d := by
          rw [abs_sub_comm, abs_of_nonneg hnonneg]
      _ ≤ max C0 1 * Real.sqrt (x : ℝ) := hle

/-- admissible residue family: residue `q-2 ≡ -2` for odd `q ≥ 3`, else `1`. -/
def famRes (q : ℕ) : ℕ := if 3 ≤ q ∧ q % 2 = 1 then q - 2 else 1

/-- the family `famRes` is admissible: every residue is coprime to its modulus. -/
lemma famRes_coprime (q : ℕ) : Nat.Coprime (famRes q) q := by
  by_cases h : 3 ≤ q ∧ q % 2 = 1
  · have hq2 : 2 ≤ q := by omega
    rw [show famRes q = q - 2 by simp [famRes, h]]
    rw [Nat.coprime_self_sub_left hq2]
    rw [Nat.coprime_two_left]
    exact (Nat.odd_iff).2 h.2
  · rw [show famRes q = 1 by simp [famRes, h]]
    exact Nat.coprime_one_left q

/-- for odd `d ≥ 3`, the family residue reduces to `d - 2` modulo `d`. -/
lemma famRes_mod (d : ℕ) (hd3 : 3 ≤ d) (hodd : d % 2 = 1) : famRes d % d = d - 2 := by
  rw [show famRes d = d - 2 by simp [famRes, hd3, hodd]]
  exact Nat.mod_eq_of_lt (by omega)

/-- for `d ≥ 2` and `r < d`: `(r+2) % d = 0 ↔ r = d - 2`. -/
lemma mod_add_two_eq_zero_iff {d r : ℕ} (hd : 2 ≤ d) (hr : r < d) :
    (r + 2) % d = 0 ↔ r = d - 2 := by
  by_cases h : r + 2 < d
  · rw [Nat.mod_eq_of_lt h]
    omega
  · have hge : d ≤ r + 2 := not_lt.mp h
    have hlt : r + 2 - d < d := by omega
    rw [Nat.mod_eq_sub_mod hge, Nat.mod_eq_of_lt hlt]
    omega

/-- for `d ≥ 2`: `d ∣ n + 2` iff `n % d = d - 2`. -/
lemma bvTheta_dvd_add_two_iff_mod (d n : ℕ) (hd : 2 ≤ d) : d ∣ n + 2 ↔ n % d = d - 2 := by
  have hmod : (n + 2) % d = (n % d + 2) % d := by
    have h : n + 2 = d * (n / d) + (n % d + 2) := by
      have := Nat.div_add_mod n d
      omega
    rw [h, Nat.mul_add_mod_self_left]
  rw [Nat.dvd_iff_mod_eq_zero, hmod]
  exact mod_add_two_eq_zero_iff hd (Nat.mod_lt n (by omega))

/-- the ψ-shifted sum at odd `d ≥ 3` is the family-residue sum. -/
lemma psiDSum_eq_famRes_sum (x d : ℕ) (hd3 : 3 ≤ d) (hodd : d % 2 = 1) :
    psiDSum x d =
      ((Finset.range (x + 1)).filter (fun n => n % d = (famRes d) % d)).sum
        (fun n => ArithmeticFunction.vonMangoldt n) := by
  have hset : (Finset.range (x + 1)).filter (fun n => d ∣ n + 2) =
      (Finset.range (x + 1)).filter (fun n => n % d = (famRes d) % d) := by
    ext n
    simp only [Finset.mem_filter]
    rw [bvTheta_dvd_add_two_iff_mod d n (by omega), famRes_mod d hd3 hodd]
  unfold psiDSum
  rw [hset]

/-- `psiDSum x 1` is the full von-Mangoldt sum up to `x`. -/
lemma psiDSum_one (x : ℕ) :
    psiDSum x 1 = ∑ n ∈ Finset.range (x + 1), ArithmeticFunction.vonMangoldt n := by
  unfold psiDSum
  rw [Finset.filter_true_of_mem (fun n _ => one_dvd (n + 2))]

/-- modulus cutoff `⌊√x / (log x)^B⌋₊`. -/
noncomputable def qCutT (x : ℕ) (B : ℝ) : ℕ :=
  ⌊Real.sqrt (x : ℝ) / (Real.log (x : ℝ)) ^ B⌋₊

/-- odd moduli in `[1, Q]`. -/
noncomputable def oddIcc (Q : ℕ) : Finset ℕ := (Finset.Icc 1 Q).filter (fun d => d % 2 = 1)

/-- odd moduli in `[2, Q]`. -/
noncomputable def oddIcc2 (Q : ℕ) : Finset ℕ := (Finset.Icc 2 Q).filter (fun d => d % 2 = 1)

/-- ψ-shift per-modulus term. -/
noncomputable def psiTermT (x d : ℕ) : ℝ :=
  |psiDSum x d - (x : ℝ) / (Nat.totient d : ℝ)|

/-- θ-shift per-modulus term. -/
noncomputable def thetaTermT (x d : ℕ) : ℝ :=
  |thetaDSum x d - (x : ℝ) / (Nat.totient d : ℝ)|

/-- θ-vs-ψ per-modulus difference. -/
noncomputable def deltaTermT (x d : ℕ) : ℝ :=
  |thetaDSum x d - psiDSum x d|

/-- family (black box) per-modulus term. -/
noncomputable def famTerm (x q : ℕ) : ℝ :=
  |((Finset.range (x + 1)).filter (fun n => n % q = (famRes q) % q)).sum
      (fun n => ArithmeticFunction.vonMangoldt n)
    - (x : ℝ) / (Nat.totient q : ℝ)|

/-- for odd `d ≥ 3` the ψ-shift term equals the family term. -/
lemma psiTermT_eq_famTerm (x d : ℕ) (hd3 : 3 ≤ d) (hodd : d % 2 = 1) :
    psiTermT x d = famTerm x d := by
  unfold psiTermT famTerm
  rw [psiDSum_eq_famRes_sum x d hd3 hodd]

/-- pointwise triangle: θ-term ≤ ψ-term + difference. -/
lemma thetaTermT_le (x d : ℕ) :
    thetaTermT x d ≤ psiTermT x d + deltaTermT x d := by
  unfold thetaTermT psiTermT deltaTermT
  have htri : |thetaDSum x d - (x : ℝ) / (Nat.totient d : ℝ)| ≤
      |thetaDSum x d - psiDSum x d| + |psiDSum x d - (x : ℝ) / (Nat.totient d : ℝ)| := by
    calc
      |thetaDSum x d - (x : ℝ) / (Nat.totient d : ℝ)|
          = |(thetaDSum x d - psiDSum x d) + (psiDSum x d - (x : ℝ) / (Nat.totient d : ℝ))| := by
            congr 1
            ring
      _ ≤ |thetaDSum x d - psiDSum x d| + |psiDSum x d - (x : ℝ) / (Nat.totient d : ℝ)| :=
            abs_add_le _ _
  simpa [add_comm, add_left_comm, add_assoc] using htri

/-- monotonicity of the modulus cutoff in the exponent (base ≥ 1). -/
lemma qCutT_mono {x : ℕ} {B1 B2 : ℝ} (hLog : 1 ≤ Real.log (x : ℝ)) (hB : B1 ≤ B2) :
    qCutT x B2 ≤ qCutT x B1 := by
  unfold qCutT
  have hx0 : 0 ≤ Real.sqrt (x : ℝ) := Real.sqrt_nonneg _
  have hpow : (Real.log (x : ℝ)) ^ B1 ≤ (Real.log (x : ℝ)) ^ B2 :=
    Real.rpow_le_rpow_of_exponent_le hLog hB
  have hLpos : 0 < Real.log (x : ℝ) := lt_of_lt_of_le zero_lt_one hLog
  have hp1 : 0 < (Real.log (x : ℝ)) ^ B1 := Real.rpow_pos_of_pos hLpos B1
  have hdiv : Real.sqrt (x : ℝ) / (Real.log (x : ℝ)) ^ B2 ≤
      Real.sqrt (x : ℝ) / (Real.log (x : ℝ)) ^ B1 := by
    exact div_le_div_of_nonneg_left hx0 hp1 hpow
  exact Nat.floor_mono hdiv

/-- the odd `[1,Q]` sum splits off `d = 1`. -/
lemma oddIcc_split {α : Type*} [AddCommMonoid α] (Q : ℕ) (hQ : 1 ≤ Q) (f : ℕ → α) :
    (∑ d ∈ oddIcc Q, f d) = f 1 + ∑ d ∈ oddIcc2 Q, f d := by
  have hdecomp : oddIcc Q = ({1} : Finset ℕ) ∪ oddIcc2 Q := by
    unfold oddIcc oddIcc2
    ext d
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_union, Finset.mem_singleton]
    constructor
    · intro h
      rcases h with ⟨⟨h1d, hdQ⟩, hodd⟩
      by_cases hd1 : d = 1
      · exact Or.inl hd1
      · exact Or.inr ⟨⟨by omega, hdQ⟩, hodd⟩
    · intro h
      rcases h with h1 | hrest
      · subst d
        exact ⟨⟨le_refl 1, hQ⟩, by norm_num⟩
      · rcases hrest with ⟨⟨h2d, hdQ⟩, hodd⟩
        exact ⟨⟨by omega, hdQ⟩, hodd⟩
  have hnot : (1 : ℕ) ∉ oddIcc2 Q := by
    intro h
    simp only [oddIcc2, Finset.mem_filter, Finset.mem_Icc] at h
    omega
  have hdisj : Disjoint ({1} : Finset ℕ) (oddIcc2 Q) := by
    rw [Finset.disjoint_left]
    intro d hd hds
    rw [Finset.mem_singleton] at hd
    exact hnot (hd ▸ hds)
  rw [hdecomp, Finset.sum_union hdisj]
  simp

/-- odd `[2,Q]` is contained in `Icc 2 Q'` for `Q ≤ Q'`. -/
lemma oddIcc2_subset_Icc {Q Q' : ℕ} (hQ : Q ≤ Q') :
    oddIcc2 Q ⊆ Finset.Icc 2 Q' := by
  intro d hd
  simp only [oddIcc2, Finset.mem_filter, Finset.mem_Icc] at hd
  exact Finset.mem_Icc.mpr ⟨hd.1.1, le_trans hd.1.2 hQ⟩

/-- cardinality of the odd `[2,Q]` set is at most `Q`. -/
lemma oddIcc2_card_le (Q : ℕ) : (oddIcc2 Q).card ≤ Q := by
  have h1 : (oddIcc2 Q).card ≤ (Finset.Icc 2 Q).card := by
    exact Finset.card_le_card (by intro d hd; exact (Finset.mem_filter.mp hd).1)
  have h2 : (Finset.Icc 2 Q).card = Q + 1 - 2 := Nat.card_Icc 2 Q
  omega

/-- eventually `2 ≤ log x`. -/
lemma bvTheta_eventually_two_le_log :
    ∀ᶠ x : ℕ in Filter.atTop, (2 : ℝ) ≤ Real.log (x : ℝ) :=
  (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop (2 : ℝ)

/-- eventually any fixed constant is below `(log x)^2`. -/
lemma eventually_const_le_log_sq (c : ℝ) :
    ∀ᶠ x : ℕ in Filter.atTop, c ≤ (Real.log (x : ℝ)) ^ (2 : ℝ) := by
  let t : ℝ := Real.sqrt (max c 1)
  have ht0 : 0 ≤ t := Real.sqrt_nonneg _
  have hte : ∀ᶠ x : ℕ in Filter.atTop, t ≤ Real.log (x : ℝ) :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop t
  filter_upwards [hte] with x hx
  have hsq : t ^ (2 : ℝ) ≤ (Real.log (x : ℝ)) ^ (2 : ℝ) :=
    Real.rpow_le_rpow ht0 hx (by norm_num : (0 : ℝ) ≤ (2 : ℝ))
  have ht : t ^ (2 : ℝ) = max c 1 := by
    dsimp [t]
    rw [Real.rpow_two]
    rw [Real.sq_sqrt (show 0 ≤ max c 1 by positivity)]
  calc
    c ≤ max c 1 := le_max_left c 1
    _ = t ^ (2 : ℝ) := ht.symm
    _ ≤ (Real.log (x : ℝ)) ^ (2 : ℝ) := hsq

/-- eventually `1 ≤ ⌊√x / (log x)^B⌋₊` for fixed `B > 0`. -/
lemma eventually_one_le_qCutT (B : ℝ) :
    ∀ᶠ x : ℕ in Filter.atTop, 1 ≤ qCutT x B := by
  have hlit : (fun t : ℝ => Real.log t ^ B) =o[Filter.atTop] (fun t : ℝ => t ^ (1 / 2 : ℝ)) :=
    isLittleO_log_rpow_rpow_atTop B (by norm_num)
  have hEv := (Asymptotics.isLittleO_iff.mp hlit) (show (0 : ℝ) < 1 by norm_num)
  have hEvNat : ∀ᶠ x : ℕ in Filter.atTop,
      ‖Real.log (x : ℝ) ^ B‖ ≤ 1 * ‖(x : ℝ) ^ (1 / 2 : ℝ)‖ :=
    Filter.Tendsto.eventually tendsto_natCast_atTop_atTop hEv
  have hLog : ∀ᶠ x : ℕ in Filter.atTop, (2 : ℝ) ≤ Real.log (x : ℝ) := bvTheta_eventually_two_le_log
  filter_upwards [hEvNat, hLog] with x hx hxLog
  have hx0 : (0 : ℝ) ≤ (x : ℝ) := by exact_mod_cast (Nat.zero_le x)
  have hL0 : 0 ≤ Real.log (x : ℝ) := le_of_lt (lt_of_lt_of_le (by norm_num) hxLog)
  have hnorm1 : ‖Real.log (x : ℝ) ^ B‖ = Real.log (x : ℝ) ^ B :=
    Real.norm_of_nonneg (Real.rpow_nonneg hL0 B)
  have hnorm2 : ‖(x : ℝ) ^ (1 / 2 : ℝ)‖ = Real.sqrt (x : ℝ) := by
    rw [Real.norm_of_nonneg (Real.rpow_nonneg hx0 _), Real.sqrt_eq_rpow]
  rw [hnorm1, hnorm2, one_mul] at hx
  have hLpos : 0 < Real.log (x : ℝ) := lt_of_lt_of_le (by norm_num) hxLog
  have hLpowpos : 0 < Real.log (x : ℝ) ^ B := Real.rpow_pos_of_pos hLpos B
  have hle : ((1 : ℕ) : ℝ) ≤ Real.sqrt (x : ℝ) / Real.log (x : ℝ) ^ B := by
    rw [le_div_iff₀ hLpowpos]
    simpa using hx
  unfold qCutT
  exact Nat.le_floor hle

/-- eventually `c · (log x)^A ≤ (1/4)·√x` for fixed `c > 0`, `A`. -/
lemma eventually_mul_log_pow_le_sqrt (c A : ℝ) (hc : 0 < c) :
    ∀ᶠ x : ℕ in Filter.atTop,
      c * (Real.log (x : ℝ)) ^ A ≤ (1 / 4) * Real.sqrt (x : ℝ) := by
  have hlit : (fun t : ℝ => Real.log t ^ A) =o[Filter.atTop] (fun t : ℝ => t ^ (1 / 2 : ℝ)) :=
    isLittleO_log_rpow_rpow_atTop A (by norm_num)
  have hEv := (Asymptotics.isLittleO_iff.mp hlit) (show (0 : ℝ) < 1 / (4 * c) by positivity)
  have hEvNat : ∀ᶠ x : ℕ in Filter.atTop,
      ‖Real.log (x : ℝ) ^ A‖ ≤ (1 / (4 * c)) * ‖(x : ℝ) ^ (1 / 2 : ℝ)‖ :=
    Filter.Tendsto.eventually tendsto_natCast_atTop_atTop hEv
  have hXge : ∀ᶠ x : ℕ in Filter.atTop, (1 : ℕ) ≤ x := Filter.eventually_ge_atTop 1
  filter_upwards [hEvNat, hXge] with x hx hx1
  have hx0 : (0 : ℝ) ≤ (x : ℝ) := by exact_mod_cast (Nat.zero_le x)
  have hL0 : 0 ≤ Real.log (x : ℝ) := Real.log_nonneg (by exact_mod_cast hx1 : (1 : ℝ) ≤ (x : ℝ))
  have hnorm1 : ‖Real.log (x : ℝ) ^ A‖ = Real.log (x : ℝ) ^ A :=
    Real.norm_of_nonneg (Real.rpow_nonneg hL0 A)
  have hnorm2 : ‖(x : ℝ) ^ (1 / 2 : ℝ)‖ = Real.sqrt (x : ℝ) := by
    rw [Real.norm_of_nonneg (Real.rpow_nonneg hx0 _), Real.sqrt_eq_rpow]
  rw [hnorm1, hnorm2] at hx
  calc
    c * (Real.log (x : ℝ)) ^ A ≤ c * ((1 / (4 * c)) * Real.sqrt (x : ℝ)) :=
      mul_le_mul_of_nonneg_left hx (le_of_lt hc)
    _ = (1 / 4) * Real.sqrt (x : ℝ) := by
      field_simp [ne_of_gt hc]
      try ring

/-- `x / L^(A+e) = (x/L^A) · (1/L^e)`. -/
lemma div_rpow_add_eq (x L : ℝ) (hL : 0 < L) (A e : ℝ) :
    x / L ^ (A + e) = (x / L ^ A) * (1 / L ^ e) := by
  rw [Real.rpow_add hL A e]
  field_simp
  try ring

/-- `x/L^(A+e) ≤ (1/4)·(x/L^A)` when `4 ≤ L^e`. -/
lemma div_rpow_add_le_quarter {x L : ℝ} (hL : 0 < L) (hx : 0 ≤ x) {A e : ℝ}
    (he4 : (4 : ℝ) ≤ L ^ e) :
    x / L ^ (A + e) ≤ (1 / 4) * (x / L ^ A) := by
  rw [div_rpow_add_eq x L hL A e]
  have hle : 1 / L ^ e ≤ 1 / 4 := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 4) he4
  calc
    (x / L ^ A) * (1 / L ^ e) ≤ (x / L ^ A) * (1 / 4) :=
      mul_le_mul_of_nonneg_left hle (div_nonneg hx (le_of_lt (Real.rpow_pos_of_pos hL A)))
    _ = (1 / 4) * (x / L ^ A) := by ring

/-- θ-shifted Bombieri–Vinogradov (theta weights = log p over primes). -/
theorem bombieri_vinogradov_theta_shift :
    ∀ A : ℝ, 0 < A →
    ∃ B : ℝ, 0 < B ∧ ∀ᶠ x : ℕ in Filter.atTop,
      ((Finset.Icc 1 ⌊Real.sqrt (x : ℝ) / (Real.log (x : ℝ)) ^ B⌋₊).filter (fun d => d % 2 = 1)).sum
        (fun d =>
          |((Finset.range (x + 1)).filter (fun p => p.Prime ∧ d ∣ p + 2)).sum
              (fun p => Real.log (p : ℝ))
            - (x : ℝ) / (Nat.totient d : ℝ)|)
        ≤ (x : ℝ) / (Real.log (x : ℝ)) ^ A := by
  intro A hA
  obtain ⟨C, hCpos, hBridge⟩ := theta_psi_abs_bound
  rcases Commons.NumberTheory.BombieriVinogradov.bombieri_vinogradov_family (A + 2) (by linarith) with ⟨Bf, hBfpos, hFam⟩
  let B : ℝ := max Bf (A + 2) + 1
  have hBpos : 0 < B := by
    dsimp [B]
    have h1 : 0 < max Bf (A + 2) := lt_of_lt_of_le hBfpos (le_max_left Bf (A + 2))
    linarith
  refine ⟨B, hBpos, ?_⟩
  have hBf_le_B : Bf ≤ B := by
    dsimp [B]
    linarith [le_max_left Bf (A + 2)]
  have hB2 : (A + 2 : ℝ) ≤ B := by
    dsimp [B]
    linarith [le_max_right Bf (A + 2)]
  -- events
  have hFamEv : ∀ᶠ x : ℕ in Filter.atTop,
      (∑ q ∈ Finset.Icc 2 (qCutT x Bf), famTerm x q)
        ≤ (x : ℝ) / (Real.log (x : ℝ)) ^ (A + 2) := by
    filter_upwards [hFam famRes famRes_coprime] with x hx
    simpa [famTerm, qCutT] using hx
  have hPsiEv : ∀ᶠ x : ℕ in Filter.atTop,
      |psiDSum x 1 - (x : ℝ)| ≤ (x : ℝ) / (Real.log (x : ℝ)) ^ (A + 3) := by
    filter_upwards [Commons.NumberTheory.PrimeNumberTheorem.psi_sub_id_powLog (A + 3) (by linarith)]
      with x hx
    simpa [psiDSum_one x] using hx
  have hLog : ∀ᶠ x : ℕ in Filter.atTop, (2 : ℝ) ≤ Real.log (x : ℝ) := bvTheta_eventually_two_le_log
  have hXge : ∀ᶠ x : ℕ in Filter.atTop, (1 : ℕ) ≤ x := Filter.eventually_ge_atTop 1
  have hM2 : ∀ᶠ x : ℕ in Filter.atTop, 4 * C ≤ (Real.log (x : ℝ)) ^ (2 : ℝ) :=
    eventually_const_le_log_sq (4 * C)
  have hQ1 : ∀ᶠ x : ℕ in Filter.atTop, 1 ≤ qCutT x B := eventually_one_le_qCutT B
  have hCsmall : ∀ᶠ x : ℕ in Filter.atTop,
      C * (Real.log (x : ℝ)) ^ A ≤ (1 / 4) * Real.sqrt (x : ℝ) :=
    eventually_mul_log_pow_le_sqrt C A hCpos
  filter_upwards [hFamEv, hPsiEv, hLog, hXge, hM2, hQ1, hCsmall]
    with x hxHfam hxHpsi hxLog hxXge hxM2 hxQ1 hxCsmall
  let L : ℝ := Real.log (x : ℝ)
  let Q : ℕ := qCutT x B
  have hxpos : (0 : ℝ) < (x : ℝ) := by exact_mod_cast (lt_of_lt_of_le (by norm_num) hxXge)
  have hx0 : (0 : ℝ) ≤ (x : ℝ) := le_of_lt hxpos
  have hL1 : (1 : ℝ) ≤ L := by dsimp [L]; linarith
  have hLpos : (0 : ℝ) < L := lt_of_lt_of_le zero_lt_one hL1
  have hLa : 0 < L ^ A := Real.rpow_pos_of_pos hLpos A
  have hL2pos : 0 < L ^ (2 : ℝ) := Real.rpow_pos_of_pos hLpos (2 : ℝ)
  have hLa2 : L ^ (A + 2) = L ^ A * L ^ (2 : ℝ) := by
    simpa using (Real.rpow_add hLpos A (2 : ℝ))
  have hPower2 : (4 : ℝ) ≤ L ^ (2 : ℝ) := by
    have h := Real.rpow_le_rpow (show (0 : ℝ) ≤ 2 by norm_num) hxLog (show (0 : ℝ) ≤ (2 : ℝ) by norm_num)
    have h24 : (2 : ℝ) ^ (2 : ℝ) = 4 := by rw [Real.rpow_ofNat]; norm_num
    rw [h24] at h
    simpa using h
  have hPower3 : (4 : ℝ) ≤ L ^ (3 : ℝ) := by
    have h := Real.rpow_le_rpow (show (0 : ℝ) ≤ 2 by norm_num) hxLog (show (0 : ℝ) ≤ (3 : ℝ) by norm_num)
    have h23 : (2 : ℝ) ^ (3 : ℝ) = 8 := by rw [Real.rpow_ofNat]; norm_num
    rw [h23] at h
    have h8 : (8 : ℝ) ≤ L ^ (3 : ℝ) := by simpa using h
    linarith
  -- convert the eventual hypotheses to this `x`, this `L`
  have hfam : (∑ q ∈ Finset.Icc 2 (qCutT x Bf), famTerm x q) ≤ (x : ℝ) / L ^ (A + 2) := by
    simpa [L] using hxHfam
  have hpsi1 : |psiDSum x 1 - (x : ℝ)| ≤ (x : ℝ) / L ^ (A + 3) := by
    simpa [L] using hxHpsi
  have hM2' : 4 * C ≤ L ^ (2 : ℝ) := by simpa [L] using hxM2
  have hCsmall' : C * L ^ A ≤ (1 / 4) * Real.sqrt (x : ℝ) := by simpa [L] using hxCsmall
  have hQ1' : 1 ≤ Q := by simpa [Q] using hxQ1
  have hQQ : Q ≤ qCutT x Bf := by
    dsimp [Q]
    exact qCutT_mono (B1 := Bf) (B2 := B) hL1 hBf_le_B
  -- family sum restricted to the smaller modulus range
  have hfamPartial : (∑ d ∈ oddIcc2 Q, famTerm x d) ≤ (x : ℝ) / L ^ (A + 2) := by
    calc
      (∑ d ∈ oddIcc2 Q, famTerm x d)
          ≤ (∑ q ∈ Finset.Icc 2 (qCutT x Bf), famTerm x q) := by
            refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
            · intro d hd
              exact oddIcc2_subset_Icc hQQ hd
            · intro d _ _
              exact abs_nonneg _
      _ ≤ (x : ℝ) / L ^ (A + 2) := hfam
  -- split off d = 1
  have hsplit : (∑ d ∈ oddIcc Q, thetaTermT x d) =
      thetaTermT x 1 + ∑ d ∈ oddIcc2 Q, thetaTermT x d :=
    oddIcc_split Q hQ1' (fun d => thetaTermT x d)
  -- the d = 1 term
  have h1term : thetaTermT x 1 ≤ (x : ℝ) / L ^ (A + 3) + C * Real.sqrt (x : ℝ) := by
    have hle1 := thetaTermT_le x 1
    have hpsi1Term : psiTermT x 1 = |psiDSum x 1 - (x : ℝ)| := by
      unfold psiTermT
      rw [show (Nat.totient 1 : ℝ) = 1 by rw [Nat.totient_one]; norm_num]
      ring_nf
    have hdelta1 : deltaTermT x 1 ≤ C * Real.sqrt (x : ℝ) := by
      simpa [deltaTermT] using hBridge x 1
    rw [hpsi1Term] at hle1
    linarith
  -- triangle over the odd moduli `d ≥ 3`
  have htri : (∑ d ∈ oddIcc2 Q, thetaTermT x d) ≤
      (∑ d ∈ oddIcc2 Q, psiTermT x d) + (∑ d ∈ oddIcc2 Q, deltaTermT x d) := by
    calc
      (∑ d ∈ oddIcc2 Q, thetaTermT x d)
          ≤ (∑ d ∈ oddIcc2 Q, (psiTermT x d + deltaTermT x d)) :=
            Finset.sum_le_sum (fun d hd => thetaTermT_le x d)
      _ = (∑ d ∈ oddIcc2 Q, psiTermT x d) + (∑ d ∈ oddIcc2 Q, deltaTermT x d) := by
            rw [Finset.sum_add_distrib]
  -- replace the ψ-terms by the family terms
  have hfamEq : (∑ d ∈ oddIcc2 Q, psiTermT x d) = (∑ d ∈ oddIcc2 Q, famTerm x d) := by
    refine Finset.sum_congr rfl ?_
    intro d hd
    simp only [oddIcc2, Finset.mem_filter, Finset.mem_Icc] at hd
    have hd3 : 3 ≤ d := by
      rcases hd with ⟨⟨h2d, _⟩, hodd⟩
      by_contra hlt
      have hd2 : d = 2 := by omega
      rw [hd2] at hodd
      norm_num at hodd
    exact psiTermT_eq_famTerm x d hd3 hd.2
  -- the difference part, bounded by the cardinality
  have hconv : (∑ d ∈ oddIcc2 Q, deltaTermT x d) ≤ C * (x : ℝ) / L ^ B := by
    calc
      (∑ d ∈ oddIcc2 Q, deltaTermT x d)
          ≤ ∑ d ∈ oddIcc2 Q, C * Real.sqrt (x : ℝ) := by
            refine Finset.sum_le_sum ?_
            intro d hd
            simpa [deltaTermT] using hBridge x d
      _ = ((oddIcc2 Q).card : ℝ) * (C * Real.sqrt (x : ℝ)) := by
            rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (Q : ℝ) * (C * Real.sqrt (x : ℝ)) := by
            exact mul_le_mul_of_nonneg_right (by exact_mod_cast oddIcc2_card_le Q)
              (mul_nonneg (le_of_lt hCpos) (Real.sqrt_nonneg (x : ℝ)))
      _ ≤ C * (x : ℝ) / L ^ B := by
            have hQle : (Q : ℝ) ≤ Real.sqrt (x : ℝ) / L ^ B := by
              dsimp [Q, qCutT]
              exact Nat.floor_le (div_nonneg (Real.sqrt_nonneg (x : ℝ))
                (le_of_lt (Real.rpow_pos_of_pos hLpos B)))
            calc
              (Q : ℝ) * (C * Real.sqrt (x : ℝ))
                  ≤ (Real.sqrt (x : ℝ) / L ^ B) * (C * Real.sqrt (x : ℝ)) := by
                    exact mul_le_mul_of_nonneg_right hQle
                      (mul_nonneg (le_of_lt hCpos) (Real.sqrt_nonneg (x : ℝ)))
              _ = C * (x : ℝ) / L ^ B := by
                    calc
                      (Real.sqrt (x : ℝ) / L ^ B) * (C * Real.sqrt (x : ℝ))
                          = C * (Real.sqrt (x : ℝ) * Real.sqrt (x : ℝ)) / L ^ B := by ring
                      _ = C * (x : ℝ) / L ^ B := by rw [Real.mul_self_sqrt hx0]
  -- four margin bounds, each ≤ (1/4)·x/L^A
  have hm1 : (x : ℝ) / L ^ (A + 3) ≤ (1 / 4) * ((x : ℝ) / L ^ A) :=
    div_rpow_add_le_quarter hLpos hx0 hPower3
  have hm3 : (x : ℝ) / L ^ (A + 2) ≤ (1 / 4) * ((x : ℝ) / L ^ A) :=
    div_rpow_add_le_quarter hLpos hx0 hPower2
  have hm4 : C * (x : ℝ) / L ^ B ≤ (1 / 4) * ((x : ℝ) / L ^ A) := by
    have hBpow : L ^ (A + 2) ≤ L ^ B := Real.rpow_le_rpow_of_exponent_le hL1 hB2
    have hCdiv : C * (x : ℝ) / L ^ B ≤ C * (x : ℝ) / L ^ (A + 2) :=
      div_le_div_of_nonneg_left (mul_nonneg (le_of_lt hCpos) hx0)
        (Real.rpow_pos_of_pos hLpos (A + 2)) hBpow
    have hstep : C * (x : ℝ) / L ^ (A + 2) ≤ (1 / 4) * ((x : ℝ) / L ^ A) := by
      have heq : C * (x : ℝ) / L ^ (A + 2) = ((x : ℝ) / L ^ A) * (C / L ^ (2 : ℝ)) := by
        rw [hLa2]
        field_simp
        try ring
      rw [heq]
      have hCL2 : C / L ^ (2 : ℝ) ≤ 1 / 4 := by
        rw [div_le_iff₀ hL2pos]
        linarith
      calc
        ((x : ℝ) / L ^ A) * (C / L ^ (2 : ℝ)) ≤ ((x : ℝ) / L ^ A) * (1 / 4) :=
            mul_le_mul_of_nonneg_left hCL2 (div_nonneg hx0 (le_of_lt hLa))
        _ = (1 / 4) * ((x : ℝ) / L ^ A) := by ring
    linarith
  have hm2 : C * Real.sqrt (x : ℝ) ≤ (1 / 4) * ((x : ℝ) / L ^ A) := by
    have hm : C * Real.sqrt (x : ℝ) * L ^ A ≤ (1 / 4) * (x : ℝ) := by
      calc
        C * Real.sqrt (x : ℝ) * L ^ A = (C * L ^ A) * Real.sqrt (x : ℝ) := by ring
        _ ≤ ((1 / 4) * Real.sqrt (x : ℝ)) * Real.sqrt (x : ℝ) :=
              mul_le_mul_of_nonneg_right hCsmall' (Real.sqrt_nonneg _)
        _ = (1 / 4) * (Real.sqrt (x : ℝ) * Real.sqrt (x : ℝ)) := by ring
        _ = (1 / 4) * (x : ℝ) := by rw [Real.mul_self_sqrt hx0]
    calc
      C * Real.sqrt (x : ℝ) = (C * Real.sqrt (x : ℝ) * L ^ A) / L ^ A := by
            field_simp [ne_of_gt hLa]
      _ ≤ ((1 / 4) * (x : ℝ)) / L ^ A := div_le_div_of_nonneg_right hm (le_of_lt hLa)
      _ = (1 / 4) * ((x : ℝ) / L ^ A) := by ring
  -- assemble
  have hbound : (∑ d ∈ oddIcc Q, thetaTermT x d) ≤
      (x : ℝ) / L ^ (A + 3) + C * Real.sqrt (x : ℝ) + (x : ℝ) / L ^ (A + 2) + C * (x : ℝ) / L ^ B := by
    rw [hsplit]
    have hstep : (∑ d ∈ oddIcc2 Q, thetaTermT x d) ≤
        (∑ d ∈ oddIcc2 Q, famTerm x d) + C * (x : ℝ) / L ^ B := by
      rw [← hfamEq]
      linarith [htri, hconv]
    linarith [h1term, hstep, hfamPartial]
  have hfinal : (x : ℝ) / L ^ (A + 3) + C * Real.sqrt (x : ℝ) + (x : ℝ) / L ^ (A + 2)
      + C * (x : ℝ) / L ^ B ≤ (x : ℝ) / L ^ A := by
    nlinarith [hm1, hm2, hm3, hm4]
  exact le_trans hbound hfinal

end

end Commons.NumberTheory.Chen
