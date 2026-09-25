import Mathlib
import Submission.Work.QuadraticFields.CertificateReal

/-!
# The product of any nonempty set of primes of the real quadratic certificate is not a square

`gsPrimesQ = {5, 13, 17, 29, 37, 41, 53}` is the set of seven prime discriminants appearing in the
real quadratic certificate `F = ℚ(√(5·13·17·29·37·41·53))` of
`Work.QuadraticFields.CertificateReal`.  All seven are (positive) primes, pairwise distinct.

The point of this file is that a product of a nonempty family of *distinct* primes is never a
rational square.  (For the conjugate imaginary certificate `certPrimes`, the corresponding fact is
`Work.QuadraticFields.certPrimesQ_nonsquare`; there one also has to handle the negative prime
`-3`, which is the reason for the extra case split in that proof.)

The proof is elementary.  Index `T ⊆ gsPrimesQ` by the finite set `S ⊆ ℤ` of integers mapping to
it, so that `∏ a ∈ T, a = ((∏ d ∈ S, d : ℤ) : ℚ)` with `S` a nonempty set of distinct primes.  Pick
any prime `p ∈ S`.  Then `p` divides the integer product exactly once: it divides it (one factor is
`p`), but `p²` does not (after cancelling the factor `p`, a prime dividing the remaining product
would have to divide one remaining factor, i.e. one of the distinct primes different from `p`).
An integer divisible by a prime exactly once is never a rational square.

This is the "the characters `√5, …, √53` are independent" input of the genus-theoretic rank
computation for the real quadratic base field.
-/

namespace Work.QuadraticFields

set_option autoImplicit false

noncomputable section

/-- The elements of `gsPrimes` are exactly the seven listed values. -/
theorem mem_gsPrimes {a : ℤ} (h : a ∈ gsPrimes) :
    a = 5 ∨ a = 13 ∨ a = 17 ∨ a = 29 ∨ a = 37 ∨ a = 41 ∨ a = 53 := by
  simpa [gsPrimes] using h

/-- Every element of `gsPrimes` is a prime integer. -/
theorem prime_of_mem_gsPrimes {a : ℤ} (ha : a ∈ gsPrimes) : Prime a := by
  rcases mem_gsPrimes ha with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

/-- Distinct elements of `gsPrimes` do not divide one another. -/
theorem not_dvd_of_mem_gsPrimes {p d : ℤ} (hp : p ∈ gsPrimes) (hd : d ∈ gsPrimes) (hpd : p ≠ d) :
    ¬ p ∣ d := by
  rcases mem_gsPrimes hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases mem_gsPrimes hd with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    first
      | (exfalso; exact hpd rfl)
      | norm_num

/-- An integer divisible by a prime `p` exactly once is not a rational square. -/
theorem gs_not_isSquare_int_of_dvd_not_dvd_sq {p n : ℤ} (hp : Prime p) (h1 : p ∣ n)
    (h2 : ¬ p ^ 2 ∣ n) : ¬ IsSquare (n : ℚ) := by
  rw [Rat.isSquare_intCast_iff]
  rintro ⟨k, hk⟩
  apply h2
  have hpk : p ∣ k := by
    apply hp.dvd_of_dvd_pow (n := 2)
    rw [pow_two, ← hk]
    exact h1
  obtain ⟨c, hc⟩ := hpk
  rw [hk, hc]
  exact ⟨c * c, by ring⟩

/-- **The main result.**  The product of any nonempty subfamily of the seven prime discriminants of
the real quadratic certificate is not a square in `ℚ`; equivalently, the square-root characters
`√5, √13, √17, √29, √37, √41, √53` are independent modulo squares. -/
theorem gsPrimesQ_nonsquare {T : Finset ℚ} (hT : T ⊆ gsPrimesQ) (hne : T.Nonempty) :
    ∀ r : ℚ, r ^ 2 ≠ ∏ a ∈ T, a := by
  intro r hr
  -- The set of integers of `gsPrimes` whose images are the elements of `T`.
  set S : Finset ℤ := gsPrimes.filter (fun d => (d : ℚ) ∈ T) with hSdef
  have hSmem : ∀ d : ℤ, d ∈ S ↔ d ∈ gsPrimes ∧ (d : ℚ) ∈ T := by
    intro d
    rw [hSdef, Finset.mem_filter]
  have himg : S.image (fun d : ℤ => (d : ℚ)) = T := by
    ext a
    constructor
    · intro ha
      obtain ⟨d, hdS, hda⟩ := Finset.mem_image.mp ha
      have hdT := ((hSmem d).mp hdS).2
      rwa [hda] at hdT
    · intro ha
      have ha' : a ∈ gsPrimesQ := hT ha
      simp only [gsPrimesQ, Finset.mem_image] at ha'
      obtain ⟨d, hdgs, hda⟩ := ha'
      exact Finset.mem_image.mpr
        ⟨d, (hSmem d).mpr ⟨hdgs, by rw [hda]; exact ha⟩, hda⟩
  have hSne : S.Nonempty := by
    rw [← himg] at hne
    exact Finset.image_nonempty.mp hne
  have hprod : ∏ a ∈ T, a = ((∏ d ∈ S, d : ℤ) : ℚ) := by
    rw [← himg]
    rw [Finset.prod_image (f := fun a : ℚ => a) (g := fun d : ℤ => (d : ℚ))
      (fun x _ y _ hxy => Int.cast_injective hxy)]
    exact (Int.cast_prod (fun d : ℤ => d) S).symm
  -- any element of `S` is a prime dividing the product exactly once
  set p : ℤ := S.max' hSne with hpdef
  have hpS : p ∈ S := by
    rw [hpdef]
    exact Finset.max'_mem S hSne
  have hpgs : p ∈ gsPrimes := ((hSmem p).mp hpS).1
  have hpprime : Prime p := prime_of_mem_gsPrimes hpgs
  have hdvd : p ∣ ∏ d ∈ S, d := Finset.dvd_prod_of_mem (fun d : ℤ => d) hpS
  have hndvd : ¬ p ^ 2 ∣ ∏ d ∈ S, d := by
    intro h2
    rw [← Finset.mul_prod_erase S (fun d : ℤ => d) hpS] at h2
    rw [pow_two] at h2
    have hm : p ∣ ∏ d ∈ S.erase p, d := (mul_dvd_mul_iff_left hpprime.ne_zero).mp h2
    obtain ⟨d, hdmem, hpdvd⟩ := (hpprime.dvd_finsetProd_iff (fun d : ℤ => d)).mp hm
    rw [Finset.mem_erase] at hdmem
    exact not_dvd_of_mem_gsPrimes hpgs ((hSmem d).mp hdmem.2).1 (Ne.symm hdmem.1) hpdvd
  rw [hprod] at hr
  exact gs_not_isSquare_int_of_dvd_not_dvd_sq hpprime hdvd hndvd ⟨r, by rw [← hr]; ring⟩

end

end Work.QuadraticFields
