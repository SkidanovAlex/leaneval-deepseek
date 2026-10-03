import Mathlib
import Submission.Work.FIArea2.area2_r3
import Submission.Work.FIArea2.NsolDefs
import Submission.Work.FIArea2.Nsol_mul
import Submission.Work.FIArea2.Jsum_mul
import Submission.Work.FIArea2.Jsum_prime_pow
import Submission.Work.FIArea2.sqRoots_card
import Submission.Work.FIArea2.card_sq_roots_nat
import Submission.Work.FIArea2.card_p_dvd_sq_cong

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.FIArea2

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

/-! ## The local count `N(a;p^ν)` (*FI* Lemma 8.2 / (8.10))

The proof of the prime-power case of (8.13) is self-contained here: `Nnat`/`DNat`/`UNat` are the
residue-level counts of the solutions of `aγ₁² ≡ γ₂² (mod p^ν)` (all, those with `p ∣ γ₁`, and
those with `p ∤ γ₁`), `UNat_eq` evaluates the unit part by `card_sq_roots_nat`, `DNat_eq` is the
recursion `D ν = p² N (ν-2)`, and the two-step recursion
`N_ν = φ(p^ν)(1 + (a/p)) + p²N_{ν-2}` is matched by the same recursion for
`Jsum (p^ν) (a:ℤ) = Σ_{α≤ν} φ(p^α)(a/p)^α p^{ν-α}` (`Jloc_rec`), giving the local case by
induction. -/

/-- Residue-level version of `Nsol`. -/
def Nnat (p ν a : ℕ) : ℕ :=
  ((Finset.range (p ^ ν) ×ˢ Finset.range (p ^ ν)).filter
      (fun z => (a * z.1 ^ 2) % p ^ ν = (z.2 ^ 2) % p ^ ν)).card

/-- The part with `p ∣ x`. -/
def DNat (p ν a : ℕ) : ℕ :=
  ((Finset.range (p ^ ν) ×ˢ Finset.range (p ^ ν)).filter
      (fun z => p ∣ z.1 ∧ (a * z.1 ^ 2) % p ^ ν = (z.2 ^ 2) % p ^ ν)).card

/-- The part with `¬ p ∣ x` (both coordinates are units). -/
def UNat (p ν a : ℕ) : ℕ :=
  ((Finset.range (p ^ ν) ×ˢ Finset.range (p ^ ν)).filter
      (fun z => ¬ p ∣ z.1 ∧ (a * z.1 ^ 2) % p ^ ν = (z.2 ^ 2) % p ^ ν)).card

lemma Nsol_eq_Nnat (p ν a : ℕ) (hp : p.Prime) :
    Nsol (p ^ ν) a = Nnat p ν a := by
  have hpν : NeZero (p ^ ν) := ⟨pow_ne_zero _ hp.ne_zero⟩
  rw [Nsol_eq_filter]
  unfold Nnat
  refine Finset.card_bij (fun (z : ZMod (p ^ ν) × ZMod (p ^ ν)) _ => (z.1.val, z.2.val)) ?_ ?_ ?_
  · intro z hz
    rw [Finset.mem_filter] at hz ⊢
    obtain ⟨-, hP⟩ := hz
    refine ⟨Finset.mem_product.mpr ⟨Finset.mem_range.mpr (ZMod.val_lt _),
      Finset.mem_range.mpr (ZMod.val_lt _)⟩, ?_⟩
    have h2 : ((a * z.1.val ^ 2 : ℕ) : ZMod (p ^ ν)) = ((z.2.val ^ 2 : ℕ) : ZMod (p ^ ν)) := by
      push_cast
      rw [ZMod.natCast_zmod_val, ZMod.natCast_zmod_val]
      exact hP
    exact (ZMod.natCast_eq_natCast_iff _ _ _).mp h2
  · intro z _ w _ h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext (by rw [← ZMod.natCast_zmod_val z.1, ← ZMod.natCast_zmod_val w.1, h.1])
      (by rw [← ZMod.natCast_zmod_val z.2, ← ZMod.natCast_zmod_val w.2, h.2])
  · intro y hy
    rw [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_range] at hy
    obtain ⟨⟨hx1, hx2⟩, hcon⟩ := hy
    refine ⟨((y.1 : ZMod (p ^ ν)), (y.2 : ZMod (p ^ ν))), ?_, ?_⟩
    · rw [Finset.mem_filter]
      refine ⟨Finset.mem_univ _, ?_⟩
      have h2 : ((a * y.1 ^ 2 : ℕ) : ZMod (p ^ ν)) = ((y.2 ^ 2 : ℕ) : ZMod (p ^ ν)) :=
        (ZMod.natCast_eq_natCast_iff _ _ _).mpr hcon
      push_cast at h2 ⊢
      exact h2
    · simp only [ZMod.val_cast_of_lt hx1, ZMod.val_cast_of_lt hx2]

lemma Nnat_eq_D_add_U (p ν a : ℕ) : Nnat p ν a = DNat p ν a + UNat p ν a := by
  unfold Nnat DNat UNat
  rw [← Finset.card_filter_add_card_filter_not
        (s := (Finset.range (p ^ ν) ×ˢ Finset.range (p ^ ν)).filter
          (fun z => (a * z.1 ^ 2) % p ^ ν = (z.2 ^ 2) % p ^ ν))
        (p := fun z => p ∣ z.1)]
  congr 1
  · apply congrArg Finset.card
    ext z
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
    tauto
  · apply congrArg Finset.card
    ext z
    simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range]
    tauto

lemma UNat_eq_sum (p ν a : ℕ) :
    UNat p ν a = ∑ x ∈ (Finset.range (p ^ ν)).filter (fun x => ¬ p ∣ x),
        ((Finset.range (p ^ ν)).filter (fun y => (a * x ^ 2) % p ^ ν = (y ^ 2) % p ^ ν)).card := by
  unfold UNat
  rw [Finset.card_filter, Finset.sum_product, Finset.sum_filter]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [Finset.card_filter]
  by_cases h : ¬ p ∣ x <;> simp [h]

lemma jacobiSym_sq_left (x p : ℕ) (h : Nat.Coprime x p) :
    jacobiSym ((x : ℤ) ^ 2) p = 1 := by
  rw [jacobiSym.pow_left]
  have hg : (x : ℤ).gcd (↑p : ℤ) = 1 := by
    rw [Int.gcd_natCast_natCast]; exact h
  exact jacobiSym.sq_one hg

lemma UNat_eq (p ν a : ℕ) (hp : p.Prime) (hodd : Odd p) (hν : 0 < ν) (ha : Nat.Coprime a p) :
    ((UNat p ν a : ℕ) : ℤ) = (Nat.totient (p ^ ν) : ℤ) * (1 + jacobiSym (a : ℤ) p) := by
  have hterm : ∀ x ∈ (Finset.range (p ^ ν)).filter (fun x => ¬ p ∣ x),
      ((((Finset.range (p ^ ν)).filter (fun y => (a * x ^ 2) % p ^ ν = (y ^ 2) % p ^ ν)).card : ℕ) : ℤ)
        = 1 + jacobiSym (a : ℤ) p := by
    intro x hx
    rw [Finset.mem_filter, Finset.mem_range] at hx
    obtain ⟨-, hpx⟩ := hx
    have hcop : Nat.Coprime x p := ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpx).symm
    have hc : ¬ p ∣ a * x ^ 2 := by
      intro hd
      rcases hp.dvd_mul.mp hd with h | h
      · exact ((Nat.Prime.coprime_iff_not_dvd hp).mp ha.symm) h
      · exact hpx (hp.dvd_of_dvd_pow h)
    have h1 := card_sq_roots_nat p ν hp hodd hν (a * x ^ 2) hc
    rw [Finset.filter_congr (fun y _ => eq_comm)] at h1
    have h2 : jacobiSym ((a * x ^ 2 : ℕ) : ℤ) p = jacobiSym (a : ℤ) p := by
      rw [Nat.cast_mul, Nat.cast_pow, jacobiSym.mul_left, jacobiSym_sq_left x p hcop]
      ring
    rw [← h2]
    exact h1
  have hcard : ((Finset.range (p ^ ν)).filter (fun x => ¬ p ∣ x)).card = Nat.totient (p ^ ν) := by
    rw [Nat.totient_eq_card_coprime]
    apply congrArg Finset.card
    apply Finset.filter_congr
    intro x _
    rw [Nat.coprime_comm, Nat.coprime_pow_right_iff hν, Nat.coprime_comm]
    exact (Nat.Prime.coprime_iff_not_dvd hp).symm
  rw [UNat_eq_sum]
  push_cast
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul, hcard]

lemma DNat_eq (p ν a : ℕ) (hp : p.Prime) (hν : 2 ≤ ν) :
    DNat p ν a = p ^ 2 * Nnat p (ν - 2) a := by
  unfold DNat Nnat
  rw [card_p_dvd_sq_cong p ν a hp hν]

lemma DNat_one (p a : ℕ) (hp : p.Prime) : DNat p 1 a = 1 := by
  unfold DNat
  rw [show p ^ 1 = p by ring]
  rw [Finset.card_eq_one]
  refine ⟨(0, 0), ?_⟩
  ext z
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_singleton]
  constructor
  · intro hz
    obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hz
    have hz1 : z.1 = 0 := Nat.eq_zero_of_dvd_of_lt h3 h1
    have hz2 : z.2 = 0 := by
      have h4' : z.2 ^ 2 % p = 0 := by rw [← h4, hz1]; simp
      exact Nat.eq_zero_of_dvd_of_lt (hp.dvd_of_dvd_pow (Nat.dvd_of_mod_eq_zero h4')) h2
    exact Prod.ext hz1 hz2
  · intro hz
    rw [hz]
    exact ⟨⟨hp.pos, hp.pos⟩, by simp, by simp⟩

lemma Nnat_zero (p a : ℕ) : Nnat p 0 a = 1 := by
  unfold Nnat
  rw [show p ^ 0 = 1 by ring, Finset.card_eq_one]
  refine ⟨(0, 0), ?_⟩
  ext z
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_range, Finset.mem_singleton]
  constructor
  · rintro ⟨⟨h1, h2⟩, -⟩
    exact Prod.ext (by omega) (by omega)
  · intro hz
    rw [hz]
    exact ⟨⟨by omega, by omega⟩, by simp⟩

lemma UNat_eq_R (p ν a : ℕ) (hp : p.Prime) (hodd : Odd p) (hν : 0 < ν) (ha : Nat.Coprime a p) :
    ((UNat p ν a : ℕ) : ℝ) = (Nat.totient (p ^ ν) : ℝ) * (1 + (jacobiSym (a : ℤ) p : ℝ)) := by
  have h := UNat_eq p ν a hp hodd hν ha
  have h2 : (((UNat p ν a : ℕ) : ℤ) : ℝ)
      = (((Nat.totient (p ^ ν) : ℤ) * (1 + jacobiSym (a : ℤ) p) : ℤ) : ℝ) := by
    rw [h]
  push_cast at h2
  exact h2

lemma jacobiSym_chi (p a : ℕ) (ha : Nat.Coprime a p) :
    (jacobiSym (a : ℤ) p : ℝ) = 1 ∨ (jacobiSym (a : ℤ) p : ℝ) = -1 := by
  have hg : (a : ℤ).gcd (↑p : ℤ) = 1 := by
    rw [Int.gcd_natCast_natCast]
    exact ha
  rcases jacobiSym.eq_one_or_neg_one hg with h | h
  · exact Or.inl (by exact_mod_cast h)
  · exact Or.inr (by exact_mod_cast h)

lemma sum_range_add_two (f : ℕ → ℝ) (n : ℕ) :
    (∑ α ∈ Finset.range (n + 2), f α) = (∑ α ∈ Finset.range n, f α) + f n + f (n + 1) := by
  rw [Finset.sum_range_succ, Finset.sum_range_succ]

lemma Jsum_one_prime (p a : ℕ) (hp : p.Prime) :
    Jsum p (a : ℤ) = 1 + (Nat.totient p : ℝ) * (1 + (jacobiSym (a : ℤ) p : ℝ)) := by
  rw [show p = p ^ 1 by ring, Jsum_prime_pow (a : ℤ) p 1 hp, Finset.sum_range_succ,
    Finset.sum_range_succ, Finset.sum_range_zero]
  simp only [Nat.totient_one, pow_one, Nat.cast_one, div_one, pow_zero, mul_one, zero_add]
  have hφp : (Nat.totient p : ℝ) = (p : ℝ) - 1 := by
    rw [Nat.totient_prime hp]
    push_cast [Nat.cast_sub hp.one_le]
    ring
  rw [hφp]
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  field_simp
  ring

/-- The summand of the local factor `(8.13)` at `p^ν`. -/
noncomputable def Jterm (p : ℕ) (a : ℤ) (ν α : ℕ) : ℝ :=
  (Nat.totient (p ^ α) : ℝ) * (jacobiSym a p : ℝ) ^ α * (p : ℝ) ^ (ν - α)

/-- The local factor of (8.13) at `p^ν`, written as `Σ_{α ≤ ν} φ(p^α)(a/p)^α p^{ν-α}`. -/
noncomputable def Jloc (p ν : ℕ) (a : ℤ) : ℝ :=
  ∑ α ∈ Finset.range (ν + 1), Jterm p a ν α

lemma Jsum_eq_Jloc (p ν : ℕ) (a : ℤ) (hp : p.Prime) : Jsum (p ^ ν) a = Jloc p ν a := by
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  rw [Jsum_prime_pow a p ν hp, Jloc, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro α hα
  rw [Finset.mem_range] at hα
  have hle : α ≤ ν := by omega
  have h1 : (p : ℝ) ^ ν = (p : ℝ) ^ α * (p : ℝ) ^ (ν - α) := by
    rw [← pow_add]
    congr 1
    omega
  rw [Jterm, h1]
  have h2 : (p : ℝ) ^ α ≠ 0 := pow_ne_zero _ hp0
  field_simp

lemma Jloc_rec (p ν : ℕ) (a : ℤ) (hp : p.Prime) (ha : a.gcd (↑p : ℤ) = 1) :
    Jloc p (ν + 2) a = (p : ℝ) ^ 2 * Jloc p ν a
      + (Nat.totient (p ^ (ν + 2)) : ℝ) * (1 + (jacobiSym a p : ℝ)) := by
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hfac : (jacobiSym a p : ℝ) = 1 ∨ (jacobiSym a p : ℝ) = -1 := by
    rcases jacobiSym.eq_one_or_neg_one ha with h | h
    · exact Or.inl (by exact_mod_cast h)
    · exact Or.inr (by exact_mod_cast h)
  have hsplit : (∑ α ∈ Finset.range (ν + 3), Jterm p a (ν + 2) α)
      = (∑ α ∈ Finset.range (ν + 1), Jterm p a (ν + 2) α)
        + Jterm p a (ν + 2) (ν + 1) + Jterm p a (ν + 2) (ν + 2) := by
    rw [show ν + 3 = (ν + 1) + 2 by ring]
    exact sum_range_add_two (fun α => Jterm p a (ν + 2) α) (ν + 1)
  have hshift : (∑ α ∈ Finset.range (ν + 1), Jterm p a (ν + 2) α)
      = (p : ℝ) ^ 2 * (∑ α ∈ Finset.range (ν + 1), Jterm p a ν α) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro α hα
    rw [Finset.mem_range] at hα
    have hle : α ≤ ν := by omega
    rw [Jterm, Jterm]
    have h1 : (p : ℝ) ^ (ν + 2 - α) = (p : ℝ) ^ 2 * (p : ℝ) ^ (ν - α) := by
      rw [show ν + 2 - α = 2 + (ν - α) by omega, pow_add]
    rw [h1]; ring
  have hlast : Jterm p a (ν + 2) (ν + 1) + Jterm p a (ν + 2) (ν + 2)
      = (Nat.totient (p ^ (ν + 2)) : ℝ) * (1 + (jacobiSym a p : ℝ)) := by
    have hφ1 : (Nat.totient (p ^ (ν + 1)) : ℝ) = (p : ℝ) ^ ν * ((p : ℝ) - 1) := by
      rw [Nat.totient_prime_pow hp (by omega)]
      push_cast [Nat.cast_sub hp.one_le]
      ring
    have hφ2 : (Nat.totient (p ^ (ν + 2)) : ℝ) = (p : ℝ) ^ (ν + 1) * ((p : ℝ) - 1) := by
      rw [Nat.totient_prime_pow hp (by omega)]
      push_cast [Nat.cast_sub hp.one_le]
      ring
    have hs : (jacobiSym a p : ℝ) ^ (ν + 1) + (jacobiSym a p : ℝ) ^ (ν + 2)
        = 1 + (jacobiSym a p : ℝ) := by
      have h2 : (jacobiSym a p : ℝ) ^ (ν + 2)
          = (jacobiSym a p : ℝ) ^ (ν + 1) * (jacobiSym a p : ℝ) := by
        rw [show ν + 2 = (ν + 1) + 1 by ring, pow_succ]
      rw [h2]
      have h3 : (jacobiSym a p : ℝ) ^ (ν + 1) + (jacobiSym a p : ℝ) ^ (ν + 1)
            * (jacobiSym a p : ℝ)
          = (jacobiSym a p : ℝ) ^ (ν + 1) * (1 + (jacobiSym a p : ℝ)) := by ring
      rw [h3]
      rcases hfac with h | h <;> rw [h]
      · simp
      · ring
    rw [Jterm, Jterm]
    rw [show (ν + 2) - (ν + 1) = 1 by omega, show (ν + 2) - (ν + 2) = 0 by omega]
    simp only [pow_one, pow_zero, mul_one]
    rw [hφ1, hφ2]
    have hpν : (p : ℝ) ^ ν * ((p : ℝ) - 1) * (jacobiSym a p : ℝ) ^ (ν + 1) * (p : ℝ)
        + (p : ℝ) ^ (ν + 1) * ((p : ℝ) - 1) * (jacobiSym a p : ℝ) ^ (ν + 2)
        = (p : ℝ) ^ (ν + 1) * ((p : ℝ) - 1)
          * ((jacobiSym a p : ℝ) ^ (ν + 1) + (jacobiSym a p : ℝ) ^ (ν + 2)) := by
      ring
    rw [hpν, hs]
  rw [Jloc, Jloc, hsplit, hshift, add_assoc, hlast]

lemma Jrec (p ν : ℕ) (a : ℕ) (hp : p.Prime) (hν : 2 ≤ ν) (ha : Nat.Coprime a p) :
    Jsum (p ^ ν) (a : ℤ) = (p : ℝ) ^ 2 * Jsum (p ^ (ν - 2)) (a : ℤ)
      + (Nat.totient (p ^ ν) : ℝ) * (1 + (jacobiSym (a : ℤ) p : ℝ)) := by
  have hg : (a : ℤ).gcd (↑p : ℤ) = 1 := by
    rw [Int.gcd_natCast_natCast]; exact ha
  rw [Jsum_eq_Jloc p ν (a : ℤ) hp, Jsum_eq_Jloc p (ν - 2) (a : ℤ) hp]
  rw [show ν = (ν - 2) + 2 by omega]
  exact Jloc_rec p (ν - 2) (a : ℤ) hp hg

theorem Nsol_prime_pow_local (p ν : ℕ) (hp : p.Prime) (hodd : Odd p) (hν : 0 < ν) (a : ℕ)
    (ha : Nat.Coprime a p) : (Nsol (p ^ ν) a : ℝ) = Jsum (p ^ ν) (a : ℤ) := by
  have key : ∀ n : ℕ, (Nsol (p ^ n) a : ℝ) = Jsum (p ^ n) (a : ℤ) := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      rcases Nat.lt_or_ge n 2 with h2 | h2
      · interval_cases n
        · rw [show p ^ 0 = 1 by ring, Nsol_one, Jsum_one]
          norm_num
        · rw [Nsol_eq_Nnat p 1 a hp, Nnat_eq_D_add_U, DNat_one p a hp]
          push_cast
          rw [UNat_eq_R p 1 a hp hodd (by omega) ha, show p ^ 1 = p by ring, Jsum_one_prime p a hp]
      · have hIH : (Nnat p (n - 2) a : ℝ) = Jsum (p ^ (n - 2)) (a : ℤ) := by
          rw [← Nsol_eq_Nnat p (n - 2) a hp]
          exact ih (n - 2) (by omega)
        rw [Nsol_eq_Nnat p n a hp, Nnat_eq_D_add_U, DNat_eq p n a hp h2]
        push_cast
        rw [hIH, UNat_eq_R p n a hp hodd (by omega) ha, Jrec p n a hp h2 ha]
  exact key ν



/-! ## Assembly of (8.13) -/

/-- If two multiplicative arithmetic functions agree at all prime powers `p^k` with `p` a prime
divisor of `n`, then they agree at `n` (`n ≠ 0`).  This is the form of
`ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers` that is applicable to (8.13):
the identity `N(a;q) = q Σ_{d|q}(φ(d)/d)(a/d)` is only available for `(a,p) = 1`, i.e. for the
primes `p` dividing `q`. -/
lemma af_eq_of_eq_on_primeFactors {R : Type*} [CommMonoidWithZero R]
    (f g : ArithmeticFunction R) (hf : f.IsMultiplicative) (hg : g.IsMultiplicative)
    {n : ℕ} (hn : n ≠ 0) (h : ∀ p ∈ n.primeFactors, ∀ k : ℕ, f (p ^ k) = g (p ^ k)) :
    f n = g n := by
  rw [hf.multiplicative_factorization f hn, hg.multiplicative_factorization g hn,
    Nat.prod_factorization_eq_prod_primeFactors, Nat.prod_factorization_eq_prod_primeFactors]
  exact Finset.prod_congr rfl fun p hp => h p hp _

lemma NsolF_isMultiplicative (a : ℕ) : (NsolF a).IsMultiplicative := by
  rw [ArithmeticFunction.IsMultiplicative.iff_ne_zero]
  refine ⟨by simp [NsolF, Nsol_one], ?_⟩
  intro m n _ _ hcop
  show (Nsol (m * n) a : ℝ) = (Nsol m a : ℝ) * (Nsol n a : ℝ)
  rw [Nsol_mul a m n hcop, Nat.cast_mul]

lemma JsumF_isMultiplicative (a : ℤ) : (JsumF a).IsMultiplicative := by
  rw [ArithmeticFunction.IsMultiplicative.iff_ne_zero]
  refine ⟨by simp [JsumF, Jsum_one], ?_⟩
  intro m n _ _ hcop
  rw [JsumF_apply a m, JsumF_apply a n, JsumF_apply a (m * n), Jsum_mul a m n hcop]

/-- **(*FI* Corollary 8.3, (8.13)): the exact count of the quadratic congruence `aγ₁² ≡ γ₂²`
for odd moduli.**  For odd `q ≥ 1` and `(a,q) = 1`, `N(a;q) = #{(γ₁,γ₂) ∈ (ℤ/q)² : aγ₁² ≡ γ₂²}`
equals `q·Σ_{d|q}(φ(d)/d)(a/d)` (Jacobi symbol).  This is the arithmetic content of Lemma 8.4:
combined with (8.9) `G₀ = Π_{p^ν‖Δ} p^{-ν}N(z₂/z₁;p^ν)` it gives `G₀ = ν·Σ_{d odd|Δ}(φ(d)/d)(z₂/z₁/d)`
for `ν = ord₂(Δ) ≥ 3` — i.e. the `2Σ_{4d|Δ}` kernel that `Defs3.G0` formalises, via
`Σ_{α≤ν-2}φ(2^α)/2^α = ν/2`.  (Verified numerically for all odd `q < 300`, all `a` coprime to `q`.) -/
theorem card_solutions_eight_thirteen (q : ℕ) [NeZero q] (hodd : Odd q) (a : ℕ)
    (ha : Nat.Coprime a q) :
    (((Finset.univ : Finset (ZMod q × ZMod q)).filter
        (fun p => (a : ZMod q) * p.1 ^ 2 = p.2 ^ 2)).card : ℝ)
      = (q : ℝ) * ∑ d ∈ q.divisors, ((Nat.totient d : ℝ) / (d : ℝ)) * (jacobiSym (a : ℤ) d : ℝ) :=
  by
  have hq : q ≠ 0 := NeZero.ne q
  rw [← Nsol_eq_filter q a]
  have heq : (NsolF a) q = (JsumF (a : ℤ)) q :=
    af_eq_of_eq_on_primeFactors (NsolF a) (JsumF (a : ℤ)) (NsolF_isMultiplicative a)
      (JsumF_isMultiplicative (a : ℤ)) hq fun p hp k => by
        have hpprime : p.Prime := Nat.prime_of_mem_primeFactors hp
        have hpq : p ∣ q := Nat.dvd_of_mem_primeFactors hp
        have hpodd : Odd p := Odd.of_dvd_nat hodd hpq
        have hcop : Nat.Coprime a p := ha.coprime_dvd_right hpq
        rcases Nat.eq_zero_or_pos k with hk | hk
        · subst hk
          rw [pow_zero, (NsolF_isMultiplicative a).map_one,
            (JsumF_isMultiplicative (a : ℤ)).map_one]
        · rw [NsolF_eq a (pow_ne_zero k hpprime.ne_zero), JsumF_apply]
          exact Nsol_prime_pow_local p k hpprime hpodd hk a hcop
  rw [NsolF_apply, JsumF_apply] at heq
  exact heq

end Work.FIArea2
