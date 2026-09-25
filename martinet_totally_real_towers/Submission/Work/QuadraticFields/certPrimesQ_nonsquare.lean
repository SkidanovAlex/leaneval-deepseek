import Mathlib
import Submission.Work.QuadraticFields.Certificate

/-!
# The product of any nonempty set of certificate primes is not a rational square

`certPrimesQ = {-3, 5, 13, 17, 29, 37}` is the set of six prime discriminants of the numerical
certificate of `Work.QuadraticFields.Certificate`.  Its product is `-3556995`.  More importantly,
every nonempty sub-product is a rational non-square: either it is negative (if `-3` is among the
factors), or it is a product of *distinct* positive primes and hence not a square.

This is the "the six characters are independent" input of the genus-theoretic argument: the
multiquadratic field `M = ℚ(√d : d ∈ certPrimes)` has the single relation
`√-3 · √5 · √13 · √17 · √29 · √37 = ±√(-3556995)`, which is exactly the statement that only the
full product of all six is a square.

The proof is elementary: an integer which is a rational square and is divisible by a prime `p`
exactly once is a square of an integer, but `p` divides `k²` only if `p²` divides `k²`.
-/

namespace Work.QuadraticFields

set_option autoImplicit false

noncomputable section

/-- The elements of `certPrimes` are exactly the six listed values. -/
theorem mem_certPrimes {a : ℤ} (h : a ∈ certPrimes) :
    a = -3 ∨ a = 5 ∨ a = 13 ∨ a = 17 ∨ a = 29 ∨ a = 37 := by
  simpa [certPrimes] using h

/-- Every element of `certPrimes` other than `-3` is positive. -/
theorem pos_of_mem_certPrimes_ne {a : ℤ} (ha : a ∈ certPrimes) (h3 : a ≠ -3) : 0 < a := by
  rcases mem_certPrimes ha with rfl | rfl | rfl | rfl | rfl | rfl <;>
    first
      | (exfalso; exact h3 rfl)
      | norm_num

/-- Every element of `certPrimes` other than `-3` is a prime integer. -/
theorem prime_of_mem_certPrimes_ne {a : ℤ} (ha : a ∈ certPrimes) (h3 : a ≠ -3) : Prime a := by
  rcases mem_certPrimes ha with rfl | rfl | rfl | rfl | rfl | rfl
  · exact absurd rfl h3
  · norm_num
  · norm_num
  · norm_num
  · norm_num
  · norm_num

/-- Distinct elements of `certPrimes` do not divide one another (the hypothesis `p ≠ -3`
is only there to make the statement about a prime divisor). -/
theorem not_dvd_of_mem_certPrimes_ne {p d : ℤ} (hp : p ∈ certPrimes) (h3 : p ≠ -3)
    (hd : d ∈ certPrimes) (hpd : p ≠ d) : ¬ p ∣ d := by
  rcases mem_certPrimes hp with rfl | rfl | rfl | rfl | rfl | rfl <;>
    rcases mem_certPrimes hd with rfl | rfl | rfl | rfl | rfl | rfl <;>
    first
      | (exfalso; exact h3 rfl)
      | (exfalso; exact hpd rfl)
      | norm_num

/-- An integer divisible by a prime `p` exactly once is not a rational square. -/
theorem not_isSquare_int_of_dvd_not_dvd_sq {p n : ℤ} (hp : Prime p) (h1 : p ∣ n)
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

theorem certPrimesQ_nonsquare {T : Finset ℚ} (hT : T ⊆ certPrimesQ) (hne : T.Nonempty) :
    ∀ r : ℚ, r ^ 2 ≠ ∏ a ∈ T, a := by
  intro r hr
  -- The integer subset of `certPrimes` whose images are the elements of `T`.
  set S : Finset ℤ := certPrimes.filter (fun d => (d : ℚ) ∈ T) with hSdef
  have hSmem : ∀ d : ℤ, d ∈ S ↔ d ∈ certPrimes ∧ (d : ℚ) ∈ T := by
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
      have ha' : a ∈ certPrimesQ := hT ha
      simp only [certPrimesQ, Finset.mem_image] at ha'
      obtain ⟨d, hdcert, hda⟩ := ha'
      exact Finset.mem_image.mpr
        ⟨d, (hSmem d).mpr ⟨hdcert, by rw [hda]; exact ha⟩, hda⟩
  have hSne : S.Nonempty := by
    have h1 := hne
    rw [← himg] at h1
    exact Finset.image_nonempty.mp h1
  have hprod : ∏ a ∈ T, a = ((∏ d ∈ S, d : ℤ) : ℚ) := by
    rw [← himg]
    rw [Finset.prod_image (f := fun a : ℚ => a) (g := fun d : ℤ => (d : ℚ))
      (fun x _ y _ hxy => Int.cast_injective hxy)]
    exact (Int.cast_prod (fun d : ℤ => d) S).symm
  by_cases h3 : (-3 : ℤ) ∈ S
  · -- the product is negative
    have hpos : 0 < ∏ d ∈ S.erase (-3 : ℤ), d := by
      apply Finset.prod_pos
      intro d hd
      rw [Finset.mem_erase] at hd
      exact pos_of_mem_certPrimes_ne ((hSmem d).mp hd.2).1 hd.1
    have hn : (∏ d ∈ S, d : ℤ) < 0 := by
      rw [← Finset.mul_prod_erase S (fun d : ℤ => d) h3]
      exact mul_neg_of_neg_of_pos (by norm_num) hpos
    have hq : ((∏ d ∈ S, d : ℤ) : ℚ) < 0 := by exact_mod_cast hn
    rw [hprod] at hr
    nlinarith [sq_nonneg r]
  · -- the product is a product of distinct primes
    set p : ℤ := S.max' hSne with hpdef
    have hpS : p ∈ S := by
      rw [hpdef]
      exact Finset.max'_mem S hSne
    have hpcert : p ∈ certPrimes := ((hSmem p).mp hpS).1
    have hp3 : p ≠ -3 := by
      intro h
      exact h3 (h ▸ hpS)
    have hpprime : Prime p := prime_of_mem_certPrimes_ne hpcert hp3
    have hdvd : p ∣ ∏ d ∈ S, d := Finset.dvd_prod_of_mem (fun d : ℤ => d) hpS
    have hndvd : ¬ p ^ 2 ∣ ∏ d ∈ S, d := by
      intro h2
      rw [← Finset.mul_prod_erase S (fun d : ℤ => d) hpS] at h2
      rw [pow_two] at h2
      have hm : p ∣ ∏ d ∈ S.erase p, d := (mul_dvd_mul_iff_left hpprime.ne_zero).mp h2
      obtain ⟨d, hdmem, hpdvd⟩ := (hpprime.dvd_finsetProd_iff (fun d : ℤ => d)).mp hm
      rw [Finset.mem_erase] at hdmem
      exact not_dvd_of_mem_certPrimes_ne hpcert hp3 ((hSmem d).mp hdmem.2).1 (Ne.symm hdmem.1) hpdvd
    rw [hprod] at hr
    refine not_isSquare_int_of_dvd_not_dvd_sq hpprime hdvd hndvd ⟨r, ?_⟩
    rw [← hr]
    ring

end

end Work.QuadraticFields
