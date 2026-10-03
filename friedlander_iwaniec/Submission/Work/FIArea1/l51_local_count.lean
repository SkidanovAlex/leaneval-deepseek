import Mathlib
import Submission.Work.FIArea2.congAux
import Submission.Work.FIArea2.congCount
import Submission.Work.FIArea2.Ncount_mul
import Submission.Work.FIArea1.L51Count
import Submission.Work.FIArea1.L51Local
import Submission.Work.FIArea1.l51_Nc_prod

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.FIArea1

open Finset

attribute [local instance] Classical.propDecidable

/-- The `ZMod d`-class of an integer `a` is the class of the natural number `(a % d).toNat`. -/
lemma intCast_eq_toNat_emod (d : ℕ) [NeZero d] (a : ℤ) :
    ((a : ZMod d)) = (((a % d).toNat : ℕ) : ZMod d) := by
  have hd0 : (d : ℤ) ≠ 0 := by simpa using (NeZero.ne d : d ≠ 0)
  have hnn : 0 ≤ a % d := Int.emod_nonneg a hd0
  have hnat : (((a % d).toNat : ℕ) : ZMod d)
      = (((Int.toNat (a % (d : ℤ)) : ℤ)) : ZMod d) := by
    push_cast
    ring
  rw [hnat, Int.toNat_of_nonneg hnn]
  rw [ZMod.intCast_eq_intCast_iff, Int.modEq_iff_dvd]
  refine ⟨-(a / d), ?_⟩
  have h := Int.emod_add_mul_ediv a (d : ℤ)
  linarith

/-- For a prime `p` dividing `d ≠ 0`, divisibility of `(a % d).toNat` by `p` is divisibility of
`a.natAbs` by `p`. -/
lemma prime_dvd_toNat_emod {d p : ℕ} (hd : d ≠ 0) (hpd : p ∣ d) (a : ℤ) :
    p ∣ (a % d).toNat ↔ p ∣ a.natAbs := by
  have hdn : (d : ℤ) ≠ 0 := by simpa using hd
  have hnn : 0 ≤ a % d := Int.emod_nonneg a hdn
  have hpz : (p : ℤ) ∣ (d : ℤ) := by exact_mod_cast hpd
  have hkey : (p : ℤ) ∣ (a % d) ↔ (p : ℤ) ∣ a := by
    constructor
    · intro h
      have h2 : (p : ℤ) ∣ (d : ℤ) * (a / d) := hpz.mul_right (a / d)
      have h3 : (p : ℤ) ∣ (a % d) + (d : ℤ) * (a / d) := Int.dvd_add h h2
      rwa [Int.emod_add_mul_ediv] at h3
    · intro h
      have h2 : (p : ℤ) ∣ (d : ℤ) * (a / d) := hpz.mul_right (a / d)
      have h3 : (p : ℤ) ∣ a - (d : ℤ) * (a / d) := Int.dvd_sub h h2
      have h4 : a - (d : ℤ) * (a / d) = a % d := by
        have h5 := Int.emod_add_mul_ediv a (d : ℤ)
        linarith
      rwa [h4] at h3
  rw [← Int.natCast_dvd_natCast (m := p) (n := (a % d).toNat), Int.toNat_of_nonneg hnn, hkey,
    Int.natCast_dvd]

/-- **Reduction of the local count to natural coefficients.** -/
lemma zmod_count_eq_nc (d : ℕ) [NeZero d] (a b : ℤ) :
    ((Finset.univ : Finset (ZMod d × ZMod d)).filter
        (fun z => (a : ZMod d) * z.1 ^ 2 = (b : ZMod d) * z.2 ^ 2)).card
      = Nc d (a % d).toNat (b % d).toNat := by
  rw [← Ncount_eq_Nc, Work.FIArea2.Ncount]
  congr 1
  ext z
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [intCast_eq_toNat_emod d a, intCast_eq_toNat_emod d b]

/-- The arithmetic assembly of the refined local count. -/
lemma prod_all_assembly (d : ℕ) (hd : 1 ≤ d) :
    (∏ p ∈ d.primeFactors,
        (d.factorization p + 1) * p ^ d.factorization p * p ^ (d.factorization p / 2))
      = d * d.divisors.card * ∏ p ∈ d.primeFactors, p ^ (d.factorization p / 2) := by
  have hd0 : d ≠ 0 := by omega
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib,
    ← Nat.card_divisors hd0, ← Nat.prod_primeFactors_pow_factorization hd0]
  ring

/-- **Refined local count for the divisor average of the binary quadratic form `a c₁² - b c₂²`.**
For coprime `a, b : ℤ` and `d ≥ 1`, the number of pairs `(γ₁,γ₂)` modulo `d` solving
`a γ₁² ≡ b γ₂² (mod d)` is at most `d·τ(d)·∏_{p ∣ d} p^{⌊v_p(d)/2⌋}`, where
`τ(m) = m.divisors.card` and `∏_{p ∣ d} p^{⌊v_p(d)/2⌋} = ∏_{p ∈ d.primeFactors} p^(d.factorization p / 2)`.

*Route.* Write `N(d) = #{(γ₁,γ₂) : a γ₁² = b γ₂² in ZMod d}`. `N` is multiplicative in `d`
(CRT: for `d = m n`, `gcd m n = 1`, use `ZMod.chineseRemainder`), as are `d`, `τ(d)` and
`d ↦ ∏_{p ∈ d.primeFactors} p^(d.factorization p / 2)`, so it suffices to prove that for a prime
`p` and `e ≥ 1` one has `N(p^e) ≤ (e+1)·p^e·p^{⌊e/2⌋}` for coprime `a, b`:
* `p ∤ ab`: at most `(e+1)p^e` solutions — for each `γ₂` the equation `aγ₁² = bγ₂²` becomes
  `γ₁² = (b/a)γ₂²`, which has at most `2` solutions for `p` odd (`4` for `p = 2`);
* `p ∣ a` (so `p ∤ b`): every solution has `p ∣ γ₂`; writing `γ₂ = p γ₂'` and reducing gives an
  induction on `e` bounding the count by `(e+1)p^e p^{⌊e/2⌋}` (the
  `γ₁ ≡ 0 (mod p^{⌈(e-α)/2⌉})`, `γ₂ ≡ 0 (mod p^{⌈e/2⌉})` contribution is
  `p^{⌊(e+α)/2⌋+⌊e/2⌋} ≤ p^{e+⌊e/2⌋}` when `α = v_p(a) ≤ e`, and `p^{e+⌊e/2⌋}` when `α ≥ e`);
* `p ∣ b`: symmetric.

For the `ℤ` coefficients multiply the equation `aγ₁² = bγ₂²` by `sign a`, reducing to the pair
`(a.natAbs, sign a * b)`; the RHS `d·τ(d)·∏_{p ∈ d.primeFactors} p^(…)` only depends on `d`.
`sq_root_card_le_two`, `sq_root_card_le_four`, `isUnit_fst_iff_snd`, `dvd_val_of_dvd_val` are
useful helpers (the last two live in `Submission.Work.FIArea1.L51Rec` /
`Submission.Work.FIArea2.congRed` and may have to be reproved or imported). -/
theorem l51_local_count (d : ℕ) [NeZero d] (a b : ℤ) (hcop : Nat.Coprime a.natAbs b.natAbs) :
    ((Finset.univ.filter (fun z : ZMod d × ZMod d =>
        (a : ZMod d) * z.1 ^ 2 = (b : ZMod d) * z.2 ^ 2)).card : ℝ)
      ≤ (d : ℝ) * (d.divisors.card : ℝ)
          * ((∏ p ∈ d.primeFactors, p ^ (d.factorization p / 2) : ℕ) : ℝ) := by
  have hd0 : d ≠ 0 := NeZero.ne d
  have hd1 : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr hd0
  have hprime : ∀ p ∈ d.primeFactors,
      Nc (p ^ d.factorization p) (a % d).toNat (b % d).toNat
        ≤ (d.factorization p + 1) * p ^ (d.factorization p) * p ^ (d.factorization p / 2) := by
    intro p hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp
    have hpd : p ∣ d := Nat.dvd_of_mem_primeFactors hp
    have hA : p ∣ (a % d).toNat ↔ p ∣ a.natAbs := prime_dvd_toNat_emod hd0 hpd a
    have hB : p ∣ (b % d).toNat ↔ p ∣ b.natAbs := prime_dvd_toNat_emod hd0 hpd b
    have hnot : ¬ (p ∣ (a % d).toNat ∧ p ∣ (b % d).toNat) := by
      rintro ⟨h1, h2⟩
      have h3 : p ∣ Nat.gcd a.natAbs b.natAbs := Nat.dvd_gcd (hA.mp h1) (hB.mp h2)
      rw [hcop.gcd_eq_one] at h3
      exact hpp.not_dvd_one h3
    by_cases h1 : p ∣ (a % d).toNat
    · exact Nc_pow_le_of_dvd p hpp _ _ _ (Or.inl ⟨h1, fun h2 => hnot ⟨h1, h2⟩⟩)
    · by_cases h2 : p ∣ (b % d).toNat
      · exact Nc_pow_le_of_dvd p hpp _ _ _ (Or.inr ⟨h1, h2⟩)
      · refine (Nc_pow_le_of_not_dvd p hpp _ _ _ h1 h2).trans ?_
        exact le_mul_of_one_le_right' (one_le_pow₀ hpp.one_le)
  have hmain : ((Finset.univ.filter (fun z : ZMod d × ZMod d =>
        (a : ZMod d) * z.1 ^ 2 = (b : ZMod d) * z.2 ^ 2)).card)
      ≤ d * d.divisors.card * (∏ p ∈ d.primeFactors, p ^ (d.factorization p / 2)) := by
    rw [zmod_count_eq_nc, l51_Nc_prod d _ _ hd0]
    refine le_trans (Finset.prod_le_prod₀ (fun p _ => Nat.zero_le _) hprime) ?_
    exact le_of_eq (prod_all_assembly d hd1)
  have hcast : ((d * d.divisors.card * (∏ p ∈ d.primeFactors, p ^ (d.factorization p / 2)) : ℕ) : ℝ)
      = (d : ℝ) * (d.divisors.card : ℝ)
          * ((∏ p ∈ d.primeFactors, p ^ (d.factorization p / 2) : ℕ) : ℝ) := by
    rw [Nat.cast_mul, Nat.cast_mul]
  exact hcast ▸ (Nat.cast_le.mpr hmain)


end Work.FIArea1
