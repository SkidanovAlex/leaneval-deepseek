/-
# `Nsol d ≤ d · τ(d)`

`Nsol d` is the number of pairs `(r,s) ∈ (ZMod d)²` with `r² + s² = 0` (`Defs.lean`).
This file proves the elementary divisor bound

  `Nsol d ≤ d · (Nat.divisors d).card`  for `d ≥ 1`,

the only arithmetic input of the divisor-sum estimate of *FI* §5.  Route: `Nsol` is
multiplicative (CRT, `Nsol_mul`), the prime powers are handled by the delegated lemma
`Nsol_prime_pow_le` (`Nsol (p^e) ≤ (e+1) p^e`), `τ` is multiplicative, and the bound
follows by strong induction on `d` splitting off the full `p`-primary part.
-/
import Mathlib
import Submission.Work.FIArea1.Defs
import Submission.Work.FIArea1.Nsol_prime_pow_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false
namespace Work.FIArea1

open Set Finset

attribute [local instance] Classical.propDecidable

noncomputable section

private lemma Nsol_one : Nsol 1 = 1 := by
  rw [Nsol]
  have h : ({z : ZMod 1 × ZMod 1 | z.1 ^ 2 + z.2 ^ 2 = 0} : Set (ZMod 1 × ZMod 1)) = Set.univ := by
    ext z
    have hz : z = (0, 0) := Subsingleton.elim z (0, 0)
    rw [hz]
    simp
  rw [h, Set.ncard_univ]
  simp

/-- `Nsol` is multiplicative in coprime arguments (Chinese remainder theorem). -/
private lemma Nsol_mul {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (hcop : Nat.Coprime m n) :
    Nsol (m * n) = Nsol m * Nsol n := by
  have hmn : m * n ≠ 0 := by positivity
  let e : ZMod (m * n) ≃+* ZMod m × ZMod n := ZMod.chineseRemainder hcop
  let Φ : ZMod (m * n) × ZMod (m * n) → (ZMod m × ZMod m) × (ZMod n × ZMod n) :=
    fun z => (((e z.1).1, (e z.2).1), ((e z.1).2, (e z.2).2))
  have hΦinj : Function.Injective Φ := by
    intro z z' h
    simp only [Φ, Prod.mk.injEq] at h
    obtain ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩ := h
    exact Prod.ext (e.injective (Prod.ext h1 h3)) (e.injective (Prod.ext h2 h4))
  have hΦset : Φ '' {z : ZMod (m*n) × ZMod (m*n) | z.1^2 + z.2^2 = 0} =
      ({a : ZMod m × ZMod m | a.1^2 + a.2^2 = 0} ×ˢ
        {b : ZMod n × ZMod n | b.1^2 + b.2^2 = 0}) := by
    ext w
    constructor
    · rintro ⟨z, hz, rfl⟩
      simp only [Set.mem_ofPred_eq] at hz ⊢
      have h0 : (e z.1)^2 + (e z.2)^2 = 0 := by
        have : e (z.1^2 + z.2^2) = (e z.1)^2 + (e z.2)^2 := by rw [map_add, map_pow, map_pow]
        rw [← this, hz, map_zero]
      refine ⟨?_, ?_⟩
      · have h1 := congrArg Prod.fst h0
        simpa [Φ] using h1
      · have h2 := congrArg Prod.snd h0
        simpa [Φ] using h2
    · rintro ⟨h1, h2⟩
      simp only [Set.mem_ofPred_eq] at h1 h2
      refine ⟨(e.symm (w.1.1, w.2.1), e.symm (w.1.2, w.2.2)), ?_, ?_⟩
      · simp only [Set.mem_ofPred_eq]
        apply e.injective
        rw [map_add, map_pow, map_pow, map_zero, e.apply_symm_apply, e.apply_symm_apply]
        ext
        · simpa [pow_two] using h1
        · simpa [pow_two] using h2
      · simp only [Φ]
        rw [e.apply_symm_apply, e.apply_symm_apply]
  rw [Nsol, ← Set.ncard_image_of_injective _ hΦinj, hΦset, Set.ncard_prod]
  rfl

/-- The number of divisors of a prime power. -/
private lemma tau_prime_pow (p v : ℕ) (hp : p.Prime) : (p^v).divisors.card = v + 1 := by
  rw [Nat.divisors_prime_pow hp, Finset.card_map, Finset.card_range]

theorem Nsol_le_tau_mul (d : ℕ) (hd : 1 ≤ d) : Work.FIArea1.Nsol d ≤ d * d.divisors.card := by
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    rcases eq_or_lt_of_le hd with h1 | hgt
    · rw [← h1, Nsol_one]; simp
    · have hd0 : d ≠ 0 := by omega
      obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd (by omega : d ≠ 1)
      set v := d.factorization p with hv
      have hv1 : 1 ≤ v := (hp.dvd_iff_one_le_factorization hd0).mp hpd
      have hpdvd : p ^ v ∣ d := (hp.pow_dvd_iff_le_factorization hd0).mpr (le_of_eq hv)
      set m := d / p ^ v with hmdef
      have hd_eq : p ^ v * m = d := Nat.mul_div_cancel' hpdvd
      have hmpos : 0 < m := Nat.div_pos (Nat.le_of_dvd (by omega) hpdvd) (pow_pos hp.pos v)
      have hmlt : m < d := Nat.div_lt_self (by omega) (by
        have : 1 < p ^ v := by
          calc 1 < p := hp.one_lt
            _ ≤ p ^ v := Nat.le_self_pow (by omega) p
        exact this)
      have hpm : ¬ p ∣ m := by
        intro hpm
        obtain ⟨k, hk⟩ := hpm
        have hdvd : p ^ (v + 1) ∣ d := by
          refine ⟨k, ?_⟩
          rw [← hd_eq, hk, pow_succ']; ring
        have hle : v + 1 ≤ d.factorization p := (hp.pow_dvd_iff_le_factorization hd0).mp hdvd
        rw [hv] at hle; omega
      have hcop : Nat.Coprime (p ^ v) m := by
        rw [Nat.coprime_pow_left_iff (by omega : 0 < v)]
        exact (hp.coprime_iff_not_dvd).mpr hpm
      rw [← hd_eq, Nsol_mul (pow_pos hp.pos v) hmpos hcop]
      have hih := ih m hmlt (by omega)
      have hstep : Nsol (p ^ v) * Nsol m ≤ ((v + 1) * p ^ v) * (m * m.divisors.card) :=
        Nat.mul_le_mul (Nsol_prime_pow_le hp) hih
      have heq : ((v + 1) * p ^ v) * (m * m.divisors.card) =
          p ^ v * m * (p ^ v * m).divisors.card := by
        have hτ : (p ^ v * m).divisors.card = (v + 1) * m.divisors.card := by
          rw [Nat.Coprime.card_divisors_mul hcop, tau_prime_pow p v hp]
        rw [hτ]; ring
      exact hstep.trans (le_of_eq heq)

end

end Work.FIArea1
