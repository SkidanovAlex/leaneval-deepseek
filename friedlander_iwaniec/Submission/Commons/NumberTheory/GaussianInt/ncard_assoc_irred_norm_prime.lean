import Mathlib.NumberTheory.SumTwoSquares
import Mathlib.Order.CompletePartialOrder
import Submission.Commons.NumberTheory.GaussianInt.units_classification
import Submission.Commons.NumberTheory.GaussianInt.irreducible_norm_eq_prime_or_sq

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option linter.style.haveILetI false

namespace Commons.NumberTheory.GaussianInt

open Zsqrtd

local notation "ℤ[i]" => GaussianInt

/-- The norm of a Gaussian integer is the sum of the squares of its coordinates. -/
theorem norm_eq_re_sq_add_im_sq (z : GaussianInt) : z.norm = z.re ^ 2 + z.im ^ 2 := by
  rw [Zsqrtd.norm_def]; ring

/-- `z.norm.natAbs = p` (for a natural number `p`) is equivalent to
`z.re ^ 2 + z.im ^ 2 = p`. -/
theorem norm_natAbs_eq_iff (z : GaussianInt) (p : ℕ) :
    z.norm.natAbs = p ↔ z.re ^ 2 + z.im ^ 2 = (p : ℤ) := by
  rw [norm_eq_re_sq_add_im_sq]
  constructor
  · intro h
    have hx : 0 ≤ z.re ^ 2 + z.im ^ 2 := by positivity
    calc z.re ^ 2 + z.im ^ 2 = (((z.re ^ 2 + z.im ^ 2).natAbs : ℕ) : ℤ) :=
          (Int.natAbs_of_nonneg hx).symm
      _ = (p : ℤ) := by rw [h]
  · intro h
    have hx : 0 ≤ z.re ^ 2 + z.im ^ 2 := by positivity
    have h2 : (((z.re ^ 2 + z.im ^ 2).natAbs : ℕ) : ℤ) = ((p : ℕ) : ℤ) := by
      rw [Int.natAbs_of_nonneg hx, h]
    exact_mod_cast h2

/-- A Gaussian integer divides its own norm. -/
theorem norm_natAbs_cast_eq (z : GaussianInt) :
    ((z.norm.natAbs : ℕ) : ℤ[i]) = z * star z := by
  have hx : 0 ≤ z.norm := Zsqrtd.norm_nonneg (show (-1 : ℤ) ≤ 0 by norm_num) z
  have h := congrArg (fun t : ℤ => (t : ℤ[i])) (Int.natAbs_of_nonneg hx)
  simpa using h.trans (Zsqrtd.norm_eq_mul_conj z)

/-- If `p ≡ 3 (mod 4)` then no Gaussian integer has norm `p`: the squares modulo `4`
are `0` and `1`, so a sum of two squares is never `3` modulo `4`. -/
theorem norm_natAbs_ne_of_mod_four_eq_three {p : ℕ} (h3 : p % 4 = 3) (z : GaussianInt) :
    z.norm.natAbs ≠ p := by
  intro h
  have hx : z.re ^ 2 + z.im ^ 2 = (p : ℤ) := (norm_natAbs_eq_iff z p).mp h
  have hcast : ((z.re : ZMod 4)) ^ 2 + ((z.im : ZMod 4)) ^ 2 = (p : ZMod 4) := by
    have h' := congrArg (fun t : ℤ => (t : ZMod 4)) hx
    push_cast at h'
    simpa using h'
  have hne : ∀ a b : ZMod 4, a ^ 2 + b ^ 2 ≠ (p : ZMod 4) := by
    rw [← ZMod.natCast_mod p 4, h3]; decide
  exact hne z.re z.im hcast

/-- A natural number that is `1` mod `4` is not even. -/
theorem not_even_of_mod_four_eq_one {p : ℕ} (h : p % 4 = 1) : ¬ Even p := by
  intro he
  rw [even_iff_two_dvd] at he
  obtain ⟨k, hk⟩ := he
  omega

/-- No prime is a perfect square. -/
theorem prime_ne_sq {p : ℕ} (hp : p.Prime) (a : ℕ) : p ≠ a ^ 2 := by
  intro h
  have hdvd : a ∣ p := ⟨a, by rw [h, pow_two]⟩
  rcases hp.eq_one_or_self_of_dvd a hdvd with ha | ha
  · rw [ha] at h
    simp only [one_pow] at h
    exact hp.ne_one h
  · rw [ha, pow_two] at h
    have h2 : p * 1 = p * p := by rw [mul_one]; exact h
    exact hp.ne_one (Nat.mul_left_cancel hp.pos h2).symm

/-- A Gaussian integer whose norm (in absolute value) is a prime is irreducible. -/
theorem irreducible_of_norm_natAbs_eq_prime {z : GaussianInt} {p : ℕ} (hp : p.Prime)
    (hz : z.norm.natAbs = p) : Irreducible z := by
  rw [irreducible_iff]
  refine ⟨?_, ?_⟩
  · intro hu
    have h1 : z.norm = 1 := (Zsqrtd.norm_eq_one_iff' (d := -1) (by norm_num) z).mpr hu
    rw [h1] at hz
    simp at hz
    exact hp.ne_one hz.symm
  · intro a b hab
    have hnorm : z.norm = a.norm * b.norm := by rw [hab, Zsqrtd.norm_mul]
    have habs : p = a.norm.natAbs * b.norm.natAbs := by
      rw [← hz, hnorm, Int.natAbs_mul]
    rcases hp.eq_one_or_self_of_dvd a.norm.natAbs ⟨b.norm.natAbs, habs⟩ with hA | hA
    · left; exact Zsqrtd.norm_eq_one_iff.mp hA
    · right
      have hB : b.norm.natAbs = 1 := by
        have h2 : p = p * b.norm.natAbs := habs.trans (by rw [hA])
        have h3 : p * 1 = p * b.norm.natAbs := by rw [mul_one]; exact h2
        exact Nat.mul_left_cancel hp.pos h3.symm
      exact Zsqrtd.norm_eq_one_iff.mp hB

/-- At most two associate classes of irreducible Gaussian integers can have norm `p`. -/
theorem image_subset_pair {p : ℕ} (hp : p.Prime) {z0 : GaussianInt} (hz0 : z0.norm.natAbs = p) :
    Associates.mk '' {z : GaussianInt | Irreducible z ∧ z.norm.natAbs = p} ⊆
      ({Associates.mk z0, Associates.mk (star z0)} : Set (Associates GaussianInt)) := by
  rintro x ⟨z, ⟨hzirr, hznorm⟩, rfl⟩
  have hzprime : Prime z := (UniqueFactorizationMonoid.irreducible_iff_prime).mp hzirr
  have hdvd : z ∣ (p : GaussianInt) := by
    rw [← hznorm]
    exact ⟨star z, norm_natAbs_cast_eq z⟩
  have hp_eq : (p : GaussianInt) = z0 * star z0 := by
    rw [← hz0]
    exact norm_natAbs_cast_eq z0
  rw [hp_eq] at hdvd
  rcases hzprime.dvd_or_dvd hdvd with h | h
  · left
    obtain ⟨m, hm⟩ := h
    have hmn : m.norm.natAbs = 1 := by
      have hnorm : z0.norm = z.norm * m.norm := by rw [hm, Zsqrtd.norm_mul]
      have hA : z0.norm.natAbs = z.norm.natAbs * m.norm.natAbs := by rw [hnorm, Int.natAbs_mul]
      have h2 : p = p * m.norm.natAbs := by
        calc p = z0.norm.natAbs := hz0.symm
          _ = z.norm.natAbs * m.norm.natAbs := hA
          _ = p * m.norm.natAbs := by rw [hznorm]
      have h3 : p * 1 = p * m.norm.natAbs := by rw [mul_one]; exact h2
      exact Nat.mul_left_cancel hp.pos h3.symm
    have hmu : IsUnit m := Zsqrtd.norm_eq_one_iff.mp hmn
    obtain ⟨u, hu⟩ := hmu
    exact Associates.mk_eq_mk_iff_associated.mpr ⟨u, by rw [hu, hm]⟩
  · right
    obtain ⟨m, hm⟩ := h
    have hmn : m.norm.natAbs = 1 := by
      have hnorm : (star z0).norm = z.norm * m.norm := by rw [hm, Zsqrtd.norm_mul]
      have hA : (star z0).norm.natAbs = z.norm.natAbs * m.norm.natAbs := by
        rw [hnorm, Int.natAbs_mul]
      have h2 : p = p * m.norm.natAbs := by
        calc p = z0.norm.natAbs := hz0.symm
          _ = (star z0).norm.natAbs := by rw [Zsqrtd.norm_conj]
          _ = z.norm.natAbs * m.norm.natAbs := hA
          _ = p * m.norm.natAbs := by rw [hznorm]
      have h3 : p * 1 = p * m.norm.natAbs := by rw [mul_one]; exact h2
      exact Nat.mul_left_cancel hp.pos h3.symm
    have hmu : IsUnit m := Zsqrtd.norm_eq_one_iff.mp hmn
    obtain ⟨u, hu⟩ := hmu
    exact Associates.mk_eq_mk_iff_associated.mpr ⟨u, by rw [hu, hm]⟩


/-- For a prime `p ≡ 1 (mod 4)` and a representation `p = a ^ 2 + b ^ 2`, the Gaussian
integer `a + b i` is not associated to its conjugate. -/
theorem mk_ne_mk_star {p : ℕ} (hp : p.Prime) (h1 : p % 4 = 1) {a b : ℕ}
    (hab : a ^ 2 + b ^ 2 = p) :
    Associates.mk (⟨(a : ℤ), (b : ℤ)⟩ : GaussianInt) ≠
      Associates.mk (star (⟨(a : ℤ), (b : ℤ)⟩ : GaussianInt)) := by
  intro h
  rw [Associates.mk_eq_mk_iff_associated] at h
  obtain ⟨u, hu⟩ := h
  rcases (units_classification (u : GaussianInt)).mp u.isUnit with hu1 | hu1 | hu1 | hu1
  · rw [hu1, mul_one] at hu
    have him := congrArg Zsqrtd.im hu
    simp at him
    have hb0 : b = 0 := by omega
    refine prime_ne_sq hp a ?_
    rw [← hab, hb0]
    ring
  · rw [hu1, mul_neg, mul_one] at hu
    have hre := congrArg Zsqrtd.re hu
    simp at hre
    have ha0 : a = 0 := by omega
    refine prime_ne_sq hp b ?_
    rw [← hab, ha0]
    ring
  · rw [hu1] at hu
    have hre := congrArg Zsqrtd.re hu
    simp at hre
    have ha0 : a = 0 := by omega
    have hb0 : b = 0 := by omega
    exact hp.ne_zero (by rw [← hab, ha0, hb0]; norm_num)
  · rw [hu1] at hu
    have hre := congrArg Zsqrtd.re hu
    simp at hre
    have hab_eq : a = b := by omega
    have h2 : p = 2 * a ^ 2 := by rw [← hab, hab_eq]; ring
    exact not_even_of_mod_four_eq_one h1 (by rw [even_iff_two_dvd]; exact ⟨a ^ 2, h2⟩)


/-- The number of associate classes of irreducible Gaussian integers of norm `p` is
`1`, `2`, `0` according as `p` is `2`, `≡ 1 (mod 4)`, or `≡ 3 (mod 4)`. -/
theorem ncard_assoc_irred_norm_prime (p : ℕ) (hp : p.Prime) :
    (Associates.mk '' {z : GaussianInt | Irreducible z ∧ z.norm.natAbs = p}).ncard =
      (if p = 2 then 1 else if p % 4 = 1 then 2 else 0) := by
  by_cases hp2 : p = 2
  · rw [if_pos hp2, hp2]
    set z0 : GaussianInt := ⟨1, 1⟩ with hz0def
    have hz0norm : z0.norm.natAbs = 2 := by
      rw [hz0def, norm_natAbs_eq_iff]
      norm_num
    have hz0irr : Irreducible z0 := irreducible_of_norm_natAbs_eq_prime Nat.prime_two hz0norm
    have hstar : Associates.mk (star z0) = Associates.mk z0 := by
      have hmem : z0 * (⟨0, -1⟩ : GaussianInt) = star z0 := by
        rw [hz0def]; ext <;> simp [Zsqrtd.re_mul, Zsqrtd.im_mul]
      have hunit : IsUnit (⟨0, -1⟩ : GaussianInt) :=
        (units_classification _).mpr (Or.inr (Or.inr (Or.inr rfl)))
      obtain ⟨u, huu⟩ := hunit
      exact Associates.mk_eq_mk_iff_associated.mpr (Associated.symm ⟨u, by rw [huu, hmem]⟩)
    have hsub := image_subset_pair Nat.prime_two hz0norm
    have hEqSet : ({Associates.mk z0, Associates.mk (star z0)} : Set (Associates GaussianInt))
        = {Associates.mk z0} := by rw [hstar]; simp
    have hmem : Associates.mk z0 ∈
        Associates.mk '' {z : GaussianInt | Irreducible z ∧ z.norm.natAbs = 2} :=
      ⟨z0, show Irreducible z0 ∧ z0.norm.natAbs = 2 from ⟨hz0irr, hz0norm⟩, rfl⟩
    have hEq : Associates.mk '' {z : GaussianInt | Irreducible z ∧ z.norm.natAbs = 2}
        = {Associates.mk z0} := by
      apply Set.Subset.antisymm
      · exact hsub.trans (le_of_eq hEqSet)
      · intro x hx; rw [Set.mem_singleton_iff] at hx; rw [hx]; exact hmem
    rw [hEq, Set.ncard_singleton]
  · rw [if_neg hp2]
    by_cases h1 : p % 4 = 1
    · rw [if_pos h1]
      haveI : Fact p.Prime := ⟨hp⟩
      obtain ⟨a, b, hab⟩ := Nat.Prime.sq_add_sq (p := p) (by omega)
      set z0 : GaussianInt := ⟨(a : ℤ), (b : ℤ)⟩ with hz0def
      have hz0norm : z0.norm.natAbs = p := by
        rw [hz0def, norm_natAbs_eq_iff]
        change (a : ℤ) ^ 2 + (b : ℤ) ^ 2 = (p : ℤ)
        rw [← hab]; push_cast; ring
      have hz0irr : Irreducible z0 := irreducible_of_norm_natAbs_eq_prime hp hz0norm
      have hstarnorm : (star z0).norm.natAbs = p := by
        rw [Zsqrtd.norm_conj]; exact hz0norm
      have hstarirr : Irreducible (star z0) :=
        irreducible_of_norm_natAbs_eq_prime hp hstarnorm
      have hne : Associates.mk z0 ≠ Associates.mk (star z0) := by
        rw [hz0def]
        exact mk_ne_mk_star hp h1 hab
      have hsub := image_subset_pair hp hz0norm
      have hEq : Associates.mk '' {z : GaussianInt | Irreducible z ∧ z.norm.natAbs = p}
          = {Associates.mk z0, Associates.mk (star z0)} := by
        apply Set.Subset.antisymm hsub
        intro x hx
        rcases hx with hx | hx
        · rw [hx]
          exact ⟨z0, show Irreducible z0 ∧ z0.norm.natAbs = p from ⟨hz0irr, hz0norm⟩, rfl⟩
        · rw [hx]
          exact ⟨star z0, show Irreducible (star z0) ∧ (star z0).norm.natAbs = p from ⟨hstarirr, hstarnorm⟩, rfl⟩
      rw [hEq, Set.ncard_pair hne]
    · rw [if_neg h1]
      have h3 : p % 4 = 3 := by
        have hodd : p % 2 = 1 := by
          rcases hp.eq_two_or_odd with h | h
          · exact absurd h hp2
          · exact h
        omega
      have hS : {z : GaussianInt | Irreducible z ∧ z.norm.natAbs = p} = ∅ := by
        rw [← Set.not_nonempty_iff_eq_empty]
        rintro ⟨z, -, hznorm⟩
        exact norm_natAbs_ne_of_mod_four_eq_three h3 z hznorm
      rw [hS, Set.image_empty, Set.ncard_empty]

end Commons.NumberTheory.GaussianInt