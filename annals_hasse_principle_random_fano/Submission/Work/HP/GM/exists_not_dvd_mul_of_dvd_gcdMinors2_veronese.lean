import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.NA.VeroAux

/-!
# `exists_not_dvd_mul_of_dvd_gcdMinors2_veronese`

Let `p` be a prime, `d ≥ 1` and `x y : ℤ^{n+1}` primitive vectors.  If `p` divides the gcd of the
`2 × 2` minors of the two columns `ν_{d,n}(x)`, `ν_{d,n}(y)` of the Veronese embedding, then some
coordinate `j` has `p ∤ x_j y_j`.

The proof is elementary.  Suppose `p ∣ x_j y_j` for every `j`.  Since `x` (and `y`) is primitive,
there is an index `i` with `p ∤ x_i` and an index `k` with `p ∤ y_k`; primitivity together with
`p ∣ x_i y_i` forces `p ∣ y_i`, so `i ≠ k`.  Applying `gcdMinors2_dvd_iff` to the two monomials
`X_i^d` and `X_k^d` (whose Veronese coordinates are `x_i^d`, `y_k^d`, ...) gives

  `p ∣ x_i^d * y_k^d - x_k^d * y_i^d`.

Now `p ∣ y_i^d` and `p ∣ x_k^d` (the latter because `p ∤ y_k` and `p ∣ x_k y_k`), so the second
term is divisible by `p`; hence `p ∣ x_i^d y_k^d = (x_i y_k)^d`.  Primality of `p` gives
`p ∣ x_i y_k`, contradicting `p ∤ x_i` and `p ∤ y_k`.
-/

set_option autoImplicit false

noncomputable section

open Finset

namespace Work.HP.GM

open Work.HP

/-- A primitive vector `v` has a coordinate not divisible by the prime `p`. -/
lemma exists_not_dvd_of_isPrim {ι : Type*} [Fintype ι] (v : ι → ℤ) (hv : IsPrim v)
    {p : ℕ} (hp : p.Prime) : ∃ i, ¬ (p : ℤ) ∣ v i := by
  by_contra hcon
  push Not at hcon
  have hgcd : (p : ℤ) ∣ Finset.univ.gcd v := Finset.dvd_gcd (fun i _ => hcon i)
  rw [IsPrim] at hv
  rw [hv] at hgcd
  have h1 : p ∣ 1 := by
    have := (Int.natAbs_dvd_natAbs (a := (p : ℤ)) (b := 1)).mpr hgcd
    simpa using this
  exact hp.not_dvd_one h1

theorem exists_not_dvd_mul_of_dvd_gcdMinors2_veronese (d n p : ℕ) (hd : 1 ≤ d) (hp : p.Prime)
    (x y : Fin (n + 1) → ℤ) (hx : Work.HP.IsPrim x) (hy : Work.HP.IsPrim y)
    (h : (p : ℤ) ∣ Work.HP.gcdMinors2 (Work.HP.veronese d n x) (Work.HP.veronese d n y)) :
    ∃ j : Fin (n + 1), ¬ (p : ℤ) ∣ x j * y j := by
  by_contra hcon
  push Not at hcon
  have hpz : Prime (p : ℤ) := by rw [Int.prime_iff_natAbs_prime]; simpa using hp
  -- coordinates not divisible by `p`
  obtain ⟨i, hi⟩ := exists_not_dvd_of_isPrim x hx hp
  obtain ⟨k, hk⟩ := exists_not_dvd_of_isPrim y hy hp
  -- `p ∣ x_i y_i` forces `p ∣ y_i`, and `p ∣ x_k y_k` forces `p ∣ x_k`
  have hyi : (p : ℤ) ∣ y i := by
    rcases hpz.dvd_or_dvd (hcon i) with h' | h'
    · exact absurd h' hi
    · exact h'
  have hkx : (p : ℤ) ∣ x k := by
    rcases hpz.dvd_or_dvd (hcon k) with h' | h'
    · exact h'
    · exact absurd h' hk
  have hik : i ≠ k := by
    intro hik
    rw [hik] at hyi
    exact hk hyi
  -- the `2 × 2` minor of `ν x`, `ν y` indexed by the monomials `X_i^d`, `X_k^d`
  have hminor : (p : ℤ) ∣ x i ^ d * y k ^ d - x k ^ d * y i ^ d := by
    have h' := (NA.gcdMinors2_dvd_iff (p : ℤ) (veronese d n x) (veronese d n y)).mp h
      (NA.monDi d n i) (NA.monDi d n k)
    simpa [NA.veronese_monDi] using h'
  have hpyid : (p : ℤ) ∣ y i ^ d := dvd_pow hyi (by omega)
  have hpxkd : (p : ℤ) ∣ x k ^ d := dvd_pow hkx (by omega)
  have hprod : (p : ℤ) ∣ x k ^ d * y i ^ d := hpxkd.mul_right (y i ^ d)
  have h1 : (p : ℤ) ∣ x i ^ d * y k ^ d := by
    simpa using dvd_add hminor hprod
  have h2 : (p : ℤ) ∣ (x i * y k) ^ d := by
    rw [mul_pow]
    exact h1
  have hxyk : (p : ℤ) ∣ x i * y k := hpz.dvd_of_dvd_pow h2
  rcases hpz.dvd_or_dvd hxyk with h' | h'
  · exact hi h'
  · exact hk h'

end Work.HP.GM
