import Mathlib
import Submission.Work.HP.Defs

/-!
# Primitivity of the Veronese vector

If `x : Fin (n+1) → ℤ` is primitive (`IsPrim x`, i.e. the gcd of its coordinates is `1`) and
`1 ≤ d`, then the Veronese vector
`ν_{d,n}(x) = (∏ i, x i ^ (m i))_{m ∈ Mon d n}`
is again primitive.

The proof is elementary: a prime `p` dividing every coefficient of `ν_{d,n}(x)` divides in
particular `ν_{d,n}(x)(X_i^d) = x_i^d` for every `i`, hence `p ∣ x_i` for every `i` (as `d ≥ 1`),
which contradicts `gcd(x) = 1`.
-/

set_option autoImplicit false

noncomputable section

open Finset

namespace Work.HP

/-- The exponent vector of the monomial `X_i ^ d`. -/
def monDiHP (d n : ℕ) (i : Fin (n + 1)) : Mon d n :=
  ⟨fun k => ⟨if k = i then d else 0, by split <;> omega⟩,
   by rw [Finset.sum_ite_eq' Finset.univ i (fun _ => d)]; simp⟩

lemma veronese_monDiHP (d n : ℕ) (x : Fin (n + 1) → ℤ) (i : Fin (n + 1)) :
    veronese d n x (monDiHP d n i) = x i ^ d := by
  simp only [veronese, monDiHP]
  rw [Finset.prod_eq_single i]
  · simp
  · intro b _ hb; simp [hb]
  · intro h; exact absurd (Finset.mem_univ i) h

theorem isPrim_veronese (d n : ℕ) (hd : 1 ≤ d) {x : Fin (n + 1) → ℤ} (hx : IsPrim x) :
    IsPrim (veronese d n x) := by
  classical
  rw [IsPrim] at hx ⊢
  have hDnn : 0 ≤ Finset.univ.gcd (veronese d n x) := Finset.Int.finsetGcd_nonneg
  have hDi : ∀ i : Fin (n + 1), Finset.univ.gcd (veronese d n x) ∣ x i ^ d := by
    intro i
    have h1 := Finset.gcd_dvd (s := Finset.univ) (f := veronese d n x)
      (Finset.mem_univ (monDiHP d n i))
    rwa [veronese_monDiHP] at h1
  have hnat : (Finset.univ.gcd (veronese d n x)).natAbs = 1 := by
    by_contra hne
    obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hne
    have hpdvd : (p : ℤ) ∣ Finset.univ.gcd (veronese d n x) := by
      rw [← Int.natAbs_dvd_natAbs]; simpa using hpd
    have hpx : ∀ i : Fin (n + 1), (p : ℤ) ∣ x i := by
      intro i
      exact Prime.dvd_of_dvd_pow (p := (p : ℤ)) (Nat.prime_iff_prime_int.mp hp)
        (hpdvd.trans (hDi i))
    have hp1 : (p : ℤ) ∣ (1 : ℤ) := by
      rw [← hx]; exact Finset.dvd_gcd fun i _ => hpx i
    have hp1' : p ∣ 1 := by
      have h := Int.natAbs_dvd_natAbs.mpr hp1
      simpa using h
    exact hp.not_dvd_one hp1'
  rcases Int.natAbs_eq_iff.mp hnat with h | h
  · simpa using h
  · omega

end Work.HP
