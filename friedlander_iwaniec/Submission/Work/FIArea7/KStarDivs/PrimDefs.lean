import Mathlib
import Submission.Work.FIArea7.KStarDefs
import Submission.Commons.NumberTheory.GaussianInt.primary_associate_exists_unique

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

namespace Work.FIArea7.KStarDivs

open Classical
attribute [local instance] Classical.propDecidable

noncomputable section

open Finset
open scoped BigOperators

/-! ## 1. Elementary facts about `IsPrimary` and `gnorm` -/

/-- The definition of `IsPrimary` with the congruence expressed in `ZMod 4`. -/
lemma isPrimary_iff_zmod (z : GaussianInt) :
    Work.FIPlan.IsPrimary z ↔
      Odd z.re ∧ Even z.im ∧ (z.im : ZMod 4) = (z.re : ZMod 4) - 1 := by
  unfold Work.FIPlan.IsPrimary
  refine and_congr_right fun _ => and_congr_right fun _ => ?_
  rw [show ((z.re : ZMod 4) - 1) = ((z.re - 1 : ℤ) : ZMod 4) by push_cast; ring,
      ZMod.intCast_eq_intCast_iff_dvd_sub, Int.modEq_iff_dvd]
  norm_num

lemma isPrimary_of_zmod {z : GaussianInt} (h1 : Odd z.re) (h2 : Even z.im)
    (h4 : (z.im : ZMod 4) = (z.re : ZMod 4) - 1) : Work.FIPlan.IsPrimary z :=
  (isPrimary_iff_zmod z).mpr ⟨h1, h2, h4⟩

lemma isPrimary_ne_zero {z : GaussianInt} (h : Work.FIPlan.IsPrimary z) : z ≠ 0 := by
  rintro rfl
  obtain ⟨ho, _, _⟩ := h
  rw [Int.odd_iff] at ho
  norm_num at ho

lemma isPrimary_odd_gnorm {z : GaussianInt} (h : Work.FIPlan.IsPrimary z) :
    Odd (Work.FIPlan.gnorm z) := by
  obtain ⟨ho, he, _⟩ := h
  have hnorm : ((Work.FIPlan.gnorm z : ℕ) : ℤ) = z.re ^ 2 + z.im ^ 2 := Work.FIArea7.norm_eq z
  have hZ : Odd ((Work.FIPlan.gnorm z : ℕ) : ℤ) := by
    rw [hnorm]
    exact (ho.pow).add_even (by rw [pow_two]; exact he.mul_right z.im)
  exact_mod_cast hZ

lemma isPrimary_one : Work.FIPlan.IsPrimary (1 : GaussianInt) := by
  refine ⟨odd_one, ?_, ?_⟩
  · exact ⟨0, by norm_num⟩
  · show (0 : ℤ) ≡ (1 : ℤ) - 1 [ZMOD 4]
    norm_num

/-- Primary elements are closed under multiplication. -/
lemma isPrimary_mul {z w : GaussianInt} (hz : Work.FIPlan.IsPrimary z)
    (hw : Work.FIPlan.IsPrimary w) : Work.FIPlan.IsPrimary (z * w) := by
  obtain ⟨hzo, hze, hzc⟩ := hz
  obtain ⟨hwo, hwe, hwc⟩ := hw
  have hre : (z * w).re = z.re * w.re - z.im * w.im := Work.FIArea7.re_mul z w
  have him : (z * w).im = z.re * w.im + z.im * w.re := Work.FIArea7.im_mul z w
  refine ⟨?_, ?_, ?_⟩
  · rw [hre]
    exact (hzo.mul hwo).sub_even (hze.mul_right w.im)
  · rw [him]
    exact (hwe.mul_left z.re).add (hze.mul_right w.re)
  · rw [him, hre]
    have L1 : z.re * w.im ≡ z.re * (w.re - 1) [ZMOD 4] := Int.ModEq.mul_left z.re hwc
    have L2 : z.im * w.re ≡ (z.re - 1) * w.re [ZMOD 4] := Int.ModEq.mul_right w.re hzc
    have hmid : z.re * (w.re - 1) + (z.re - 1) * w.re
        ≡ (z.re * w.re - (z.re - 1) * (w.re - 1)) - 1 [ZMOD 4] := by
      rw [Int.modEq_iff_dvd]
      obtain ⟨k, hk⟩ := hzo
      obtain ⟨l, hl⟩ := hwo
      use -2 * k * l
      rw [hk, hl]; ring
    have hR : z.re * w.re - z.im * w.im - 1
        ≡ z.re * w.re - (z.re - 1) * (w.re - 1) - 1 [ZMOD 4] :=
      ((Int.ModEq.refl (z.re * w.re)).sub (Int.ModEq.mul hzc hwc)).sub (Int.ModEq.refl 1)
    exact (L1.add L2).trans (hmid.trans hR.symm)

/-- Two primary associates are equal. -/
lemma isPrimary_associated_eq {a b : GaussianInt} (ha : Work.FIPlan.IsPrimary a)
    (hb : Work.FIPlan.IsPrimary b) (h : Associated a b) : a = b := by
  obtain ⟨-, huniq⟩ := Classical.choose_spec
    (Commons.NumberTheory.GaussianInt.primary_associate_exists_unique
      (isPrimary_ne_zero ha) (isPrimary_odd_gnorm ha))
  have pa : a = Classical.choose (Commons.NumberTheory.GaussianInt.primary_associate_exists_unique
      (isPrimary_ne_zero ha) (isPrimary_odd_gnorm ha)) :=
    huniq a ⟨Associated.refl a, (isPrimary_iff_zmod a).mp ha⟩
  have pb : b = Classical.choose (Commons.NumberTheory.GaussianInt.primary_associate_exists_unique
      (isPrimary_ne_zero ha) (isPrimary_odd_gnorm ha)) :=
    huniq b ⟨h.symm, (isPrimary_iff_zmod b).mp hb⟩
  exact pa.trans pb.symm

/-! ## 2. Norm bounds -/

lemma int_abs_le_sq_add_sq (a b : ℤ) : |a| ≤ a ^ 2 + b ^ 2 := by
  have hb : 0 ≤ b ^ 2 := sq_nonneg b
  have ha : |a| ≤ a ^ 2 ∨ |a| = 0 := by
    by_cases h : |a| = 0
    · exact Or.inr h
    · left
      have h0 : 0 ≤ |a| := abs_nonneg a
      have h1 : 1 ≤ |a| := by omega
      nlinarith [sq_abs a, h1, abs_nonneg a]
  rcases ha with h | h
  · linarith
  · rw [h]; linarith [sq_nonneg a]

lemma abs_re_le_gnorm (e : GaussianInt) : |e.re| ≤ ((Work.FIPlan.gnorm e : ℕ) : ℤ) := by
  have hnorm : ((Work.FIPlan.gnorm e : ℕ) : ℤ) = e.re ^ 2 + e.im ^ 2 := Work.FIArea7.norm_eq e
  rw [hnorm]; exact int_abs_le_sq_add_sq e.re e.im

lemma abs_im_le_gnorm (e : GaussianInt) : |e.im| ≤ ((Work.FIPlan.gnorm e : ℕ) : ℤ) := by
  have hnorm : ((Work.FIPlan.gnorm e : ℕ) : ℤ) = e.re ^ 2 + e.im ^ 2 := Work.FIArea7.norm_eq e
  rw [hnorm, add_comm]; exact int_abs_le_sq_add_sq e.im e.re

lemma gnorm_dvd_of_dvd {e w : GaussianInt} (h : e ∣ w) :
    Work.FIPlan.gnorm e ∣ Work.FIPlan.gnorm w := by
  obtain ⟨c, rfl⟩ := h
  exact ⟨Work.FIPlan.gnorm c, by rw [Work.FIArea7.gnorm_mul]⟩

lemma odd_gnorm_of_dvd_of_primary {w e : GaussianInt} (hw : Work.FIPlan.IsPrimary w)
    (h : e ∣ w) : Odd (Work.FIPlan.gnorm e) := by
  obtain ⟨c, hc⟩ := gnorm_dvd_of_dvd h
  have hwodd : Odd (Work.FIPlan.gnorm e * c) := by rw [← hc]; exact isPrimary_odd_gnorm hw
  exact (Nat.odd_mul.mp hwodd).1

/-! ## 3. Membership in `gaussPrimDivs` -/

lemma mem_gaussPrimDivs {w e : GaussianInt} (hw : Work.FIPlan.IsPrimary w) :
    e ∈ gaussPrimDivs w ↔ e ∣ w ∧ Work.FIPlan.IsPrimary e := by
  unfold gaussPrimDivs
  rw [Finset.mem_filter]
  constructor
  · rintro ⟨_, h⟩; exact h
  · rintro ⟨hdvd, hprim⟩
    refine ⟨?_, hdvd, hprim⟩
    rw [Finset.mem_image]
    refine ⟨(e.re, e.im), ?_, by simp⟩
    rw [Finset.product_eq_sprod, Finset.mem_product]
    have hge : Work.FIPlan.gnorm e ≤ Work.FIPlan.gnorm w :=
      Nat.le_of_dvd (Work.FIArea7.gnorm_pos_of_ne_zero (isPrimary_ne_zero hw))
        (gnorm_dvd_of_dvd hdvd)
    have hre : |e.re| ≤ ((Work.FIPlan.gnorm w : ℕ) : ℤ) :=
      le_trans (abs_re_le_gnorm e) (by exact_mod_cast hge)
    have him : |e.im| ≤ ((Work.FIPlan.gnorm w : ℕ) : ℤ) :=
      le_trans (abs_im_le_gnorm e) (by exact_mod_cast hge)
    refine ⟨?_, ?_⟩
    · simp only [Finset.mem_Icc]; exact abs_le.mp hre
    · simp only [Finset.mem_Icc]; exact abs_le.mp him

/-- The set of **primary prime divisors** of `w`: the irreducible elements of `gaussPrimDivs w`. -/
def primPrimes (w : GaussianInt) : Finset GaussianInt :=
  (gaussPrimDivs w).filter (fun p => Irreducible p)

lemma mem_primPrimes {w p : GaussianInt} (hw : Work.FIPlan.IsPrimary w) :
    p ∈ primPrimes w ↔ Irreducible p ∧ Work.FIPlan.IsPrimary p ∧ p ∣ w := by
  rw [primPrimes, Finset.mem_filter, mem_gaussPrimDivs hw]
  tauto

lemma irreducible_of_mem_primPrimes {w p : GaussianInt} (hp : p ∈ primPrimes w) : Irreducible p := by
  rw [primPrimes, Finset.mem_filter] at hp
  exact hp.2

lemma isPrimary_of_mem_primPrimes {w p : GaussianInt} (hp : p ∈ primPrimes w) :
    Work.FIPlan.IsPrimary p := by
  rw [primPrimes, gaussPrimDivs, Finset.mem_filter, Finset.mem_filter] at hp
  exact hp.1.2.2

lemma dvd_of_mem_primPrimes {w p : GaussianInt} (hp : p ∈ primPrimes w) : p ∣ w := by
  rw [primPrimes, gaussPrimDivs, Finset.mem_filter, Finset.mem_filter] at hp
  exact hp.1.2.1

lemma ne_zero_of_mem_primPrimes {w p : GaussianInt} (hp : p ∈ primPrimes w) : p ≠ 0 :=
  isPrimary_ne_zero (isPrimary_of_mem_primPrimes hp)

lemma isRelPrime_of_mem_primPrimes {w p q : GaussianInt} (hp : p ∈ primPrimes w)
    (hq : q ∈ primPrimes w) (hpq : p ≠ q) : IsRelPrime p q := by
  have hip := irreducible_of_mem_primPrimes hp
  have hiq := irreducible_of_mem_primPrimes hq
  rw [Irreducible.isRelPrime_iff_not_dvd hip]
  intro hdvd
  have hqd : q ∣ p := Irreducible.dvd_symm (p := p) (q := q) hip hiq hdvd
  exact hpq (isPrimary_associated_eq (isPrimary_of_mem_primPrimes hp)
    (isPrimary_of_mem_primPrimes hq) (associated_of_dvd_dvd hdvd hqd))

/-! ## 4. The primary associate of a divisor -/

/-- The primary associate of `q`, when `q ≠ 0` has odd norm; otherwise `q` itself. -/
def primAssoc (q : GaussianInt) : GaussianInt :=
  if h : q ≠ 0 ∧ Odd (Work.FIPlan.gnorm q) then
    Classical.choose (Commons.NumberTheory.GaussianInt.primary_associate_exists_unique h.1 h.2)
  else q

lemma primAssoc_associated {q : GaussianInt} (hq : q ≠ 0) (ho : Odd (Work.FIPlan.gnorm q)) :
    Associated (primAssoc q) q := by
  rw [primAssoc, dif_pos ⟨hq, ho⟩]
  exact (Classical.choose_spec
    (Commons.NumberTheory.GaussianInt.primary_associate_exists_unique hq ho)).1.1

lemma isPrimary_primAssoc {q : GaussianInt} (hq : q ≠ 0) (ho : Odd (Work.FIPlan.gnorm q)) :
    Work.FIPlan.IsPrimary (primAssoc q) := by
  rw [primAssoc, dif_pos ⟨hq, ho⟩]
  obtain ⟨⟨-, h1, h2, h3⟩, -⟩ := Classical.choose_spec
    (Commons.NumberTheory.GaussianInt.primary_associate_exists_unique hq ho)
  exact isPrimary_of_zmod h1 h2 h3

lemma primAssoc_dvd {q : GaussianInt} (hq : q ≠ 0) (ho : Odd (Work.FIPlan.gnorm q))
    {n : GaussianInt} (h : q ∣ n) : primAssoc q ∣ n :=
  (primAssoc_associated hq ho).dvd.trans h

lemma primAssoc_eq_self {q : GaussianInt} (hq : Work.FIPlan.IsPrimary q) : primAssoc q = q := by
  obtain ⟨-, huniq⟩ := Classical.choose_spec
    (Commons.NumberTheory.GaussianInt.primary_associate_exists_unique
      (isPrimary_ne_zero hq) (isPrimary_odd_gnorm hq))
  rw [primAssoc, dif_pos ⟨isPrimary_ne_zero hq, isPrimary_odd_gnorm hq⟩]
  exact (huniq q ⟨Associated.refl q, (isPrimary_iff_zmod q).mp hq⟩).symm

/-! ## 5. Products of primary primes -/

lemma isPrimary_prod_of_forall {S : Finset GaussianInt}
    (h : ∀ p ∈ S, Work.FIPlan.IsPrimary p) : Work.FIPlan.IsPrimary (∏ p ∈ S, p) := by
  induction S using Finset.induction_on with
  | empty => simpa using isPrimary_one
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact isPrimary_mul (h a (Finset.mem_insert_self a s))
      (ih (fun x hx => h x (Finset.mem_insert_of_mem hx)))

lemma squarefree_prod_of_forall {S : Finset GaussianInt}
    (hirr : ∀ p ∈ S, Irreducible p)
    (hpw : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → IsRelPrime p q) : Squarefree (∏ p ∈ S, p) := by
  refine Finset.squarefree_prod_of_pairwise_isCoprime ?_ ?_
  · intro a ha b hb hab
    exact hpw a ha b hb hab
  · intro a ha
    exact (hirr a ha).squarefree

lemma dvd_prod_of_forall {S : Finset GaussianInt} {n : GaussianInt}
    (hd : ∀ p ∈ S, p ∣ n)
    (hpw : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → IsRelPrime p q) : (∏ p ∈ S, p) ∣ n := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    refine IsRelPrime.mul_dvd ?_ (hd a (Finset.mem_insert_self a s))
      (ih (fun x hx => hd x (Finset.mem_insert_of_mem hx))
          (fun x hx y hy hxy =>
            hpw x (Finset.mem_insert_of_mem hx) y (Finset.mem_insert_of_mem hy) hxy))
    exact IsRelPrime.prod_right (fun i hi =>
      hpw a (Finset.mem_insert_self a s) i (Finset.mem_insert_of_mem hi) (fun h => ha (h ▸ hi)))

lemma moebius_prod_of_forall {S : Finset GaussianInt}
    (hirr : ∀ p ∈ S, Irreducible p)
    (hpw : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → IsRelPrime p q) :
    UniqueFactorizationMonoid.moebius (∏ p ∈ S, p) = (-1) ^ S.card := by
  induction S using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    have hrel : IsRelPrime a (∏ i ∈ s, i) :=
      IsRelPrime.prod_right (fun i hi =>
        hpw a (Finset.mem_insert_self a s) i (Finset.mem_insert_of_mem hi) (fun h => ha (h ▸ hi)))
    rw [Finset.prod_insert ha, IsRelPrime.moebius_mul hrel,
      (hirr a (Finset.mem_insert_self a s)).moebius_eq,
      ih (fun x hx => hirr x (Finset.mem_insert_of_mem hx))
         (fun x hx y hy hxy =>
            hpw x (Finset.mem_insert_of_mem hx) y (Finset.mem_insert_of_mem hy) hxy),
      Finset.card_insert_of_notMem ha, pow_succ]
    ring

lemma dvd_prod_iff_of_forall {S : Finset GaussianInt} {z : GaussianInt}
    (hpw : ∀ p ∈ S, ∀ q ∈ S, p ≠ q → IsRelPrime p q) :
    (∏ p ∈ S, p) ∣ z ↔ ∀ p ∈ S, p ∣ z := by
  refine ⟨fun h p hp => (Finset.dvd_prod_of_mem (fun p => p) hp).trans h, fun h => ?_⟩
  exact dvd_prod_of_forall h hpw

/-! ### Specialisations to subsets of `primPrimes w` -/

lemma prod_primPrimes_isPrimary {w : GaussianInt} {S : Finset GaussianInt}
    (hS : S ⊆ primPrimes w) : Work.FIPlan.IsPrimary (∏ p ∈ S, p) :=
  isPrimary_prod_of_forall (fun p hp => isPrimary_of_mem_primPrimes (hS hp))

lemma prod_primPrimes_squarefree {w : GaussianInt} {S : Finset GaussianInt}
    (hS : S ⊆ primPrimes w) : Squarefree (∏ p ∈ S, p) :=
  squarefree_prod_of_forall (fun p hp => irreducible_of_mem_primPrimes (hS hp))
    (fun p hp q hq hpq => isRelPrime_of_mem_primPrimes (hS hp) (hS hq) hpq)

lemma prod_primPrimes_dvd {w : GaussianInt} {S : Finset GaussianInt}
    (hS : S ⊆ primPrimes w) : (∏ p ∈ S, p) ∣ w :=
  dvd_prod_of_forall (fun p hp => dvd_of_mem_primPrimes (hS hp))
    (fun p hp q hq hpq => isRelPrime_of_mem_primPrimes (hS hp) (hS hq) hpq)

lemma prod_primPrimes_ne_zero {w : GaussianInt} {S : Finset GaussianInt}
    (hS : S ⊆ primPrimes w) : (∏ p ∈ S, p) ≠ 0 :=
  isPrimary_ne_zero (prod_primPrimes_isPrimary hS)

lemma moebius_prod_primPrimes {w : GaussianInt} {S : Finset GaussianInt}
    (hS : S ⊆ primPrimes w) : UniqueFactorizationMonoid.moebius (∏ p ∈ S, p) = (-1) ^ S.card :=
  moebius_prod_of_forall (fun p hp => irreducible_of_mem_primPrimes (hS hp))
    (fun p hp q hq hpq => isRelPrime_of_mem_primPrimes (hS hp) (hS hq) hpq)

lemma dvd_prod_primPrimes_iff {w : GaussianInt} {S : Finset GaussianInt} {z : GaussianInt}
    (hS : S ⊆ primPrimes w) : (∏ p ∈ S, p) ∣ z ↔ ∀ p ∈ S, p ∣ z :=
  dvd_prod_iff_of_forall
    (fun p hp q hq hpq => isRelPrime_of_mem_primPrimes (hS hp) (hS hq) hpq)


/-! ## 6. Structural lemmas -/

/-- For `S ⊆ primPrimes w`, the primary primes dividing `∏_{p ∈ S} p` are exactly `S`. -/
lemma filter_dvd_prod_primPrimes_eq {w : GaussianInt} {S : Finset GaussianInt}
    (hS : S ⊆ primPrimes w) :
    (primPrimes w).filter (fun p => p ∣ ∏ p' ∈ S, p') = S := by
  ext p
  rw [Finset.mem_filter]
  constructor
  · rintro ⟨hp, hdvd⟩
    have hprime : Prime p := UniqueFactorizationMonoid.irreducible_iff_prime.mp
      (irreducible_of_mem_primPrimes hp)
    obtain ⟨q, hq, hpq⟩ := hprime.exists_mem_finset_dvd (s := S) (f := fun x => x) hdvd
    have hassoc : Associated p q := associated_of_dvd_dvd hpq
      (Irreducible.dvd_symm (irreducible_of_mem_primPrimes hp)
        (irreducible_of_mem_primPrimes (hS hq)) hpq)
    have heq : p = q := isPrimary_associated_eq (isPrimary_of_mem_primPrimes hp)
      (isPrimary_of_mem_primPrimes (hS hq)) hassoc
    rwa [heq]
  · intro hp
    exact ⟨hS hp, Finset.dvd_prod_of_mem (fun x => x) hp⟩

/-- A primary `w` is coprime to `z` exactly when no *primary prime* dividing `w` divides `z`. -/
theorem isCoprime_iff_no_primPrime_dvd {w z : GaussianInt} (hw : Work.FIPlan.IsPrimary w) :
    IsCoprime z w ↔ ∀ p ∈ primPrimes w, ¬ p ∣ z := by
  rw [← isRelPrime_iff_isCoprime]
  constructor
  · intro h p hp hpz
    exact (irreducible_of_mem_primPrimes hp).not_isUnit (h hpz (dvd_of_mem_primPrimes hp))
  · intro h d hdz hdw
    by_contra hdnu
    have hw0 : w ≠ 0 := isPrimary_ne_zero hw
    have hd0 : d ≠ 0 := by
      rintro rfl
      obtain ⟨c, hc⟩ := hdw
      exact hw0 (by rw [hc, zero_mul])
    obtain ⟨q, hqirr, hqd⟩ := WfDvdMonoid.exists_irreducible_factor hdnu hd0
    have hq0 : q ≠ 0 := hqirr.ne_zero
    have hqw : q ∣ w := hqd.trans hdw
    have hqodd : Odd (Work.FIPlan.gnorm q) := odd_gnorm_of_dvd_of_primary hw hqw
    have hp : primAssoc q ∈ primPrimes w :=
      (mem_primPrimes hw).mpr
        ⟨(Associated.irreducible_iff (primAssoc_associated hq0 hqodd)).mpr hqirr,
          isPrimary_primAssoc hq0 hqodd, primAssoc_dvd hq0 hqodd hqw⟩
    exact h (primAssoc q) hp (primAssoc_dvd hq0 hqodd (hqd.trans hdz))


/-- The primary prime divisors of `w` that also divide `e`. -/
def primPrimeDivs (w e : GaussianInt) : Finset GaussianInt :=
  (primPrimes w).filter (fun p => p ∣ e)

@[simp] lemma mem_primPrimeDivs {w e p : GaussianInt} :
    p ∈ primPrimeDivs w e ↔ p ∈ primPrimes w ∧ p ∣ e := by
  simp [primPrimeDivs]


lemma primPrimeDivs_subset (w e : GaussianInt) : primPrimeDivs w e ⊆ primPrimes w := by
  intro p hp
  rw [mem_primPrimeDivs] at hp
  exact hp.1


end

end Work.FIArea7.KStarDivs
