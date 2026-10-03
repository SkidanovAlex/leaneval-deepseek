import Mathlib
import Submission.Commons.NumberTheory.GaussianInt.units_classification
import Submission.Commons.NumberTheory.GaussianInt.irreducible_norm_prime_pow
import Submission.Commons.NumberTheory.GaussianInt.irreducible_norm_eq_prime_or_sq
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Data.Nat.Factorization.Defs
import Submission.Commons.NumberTheory.Divisors.sum_divisors_eq_prod_primeFactors
import Submission.Commons.NumberTheory.Divisors.sum_chi4_divisors
import Submission.Commons.NumberTheory.Divisors.sum_range_chi4_pow
import Submission.Commons.NumberTheory.GaussianInt.ncard_assoc_irred_norm_prime
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.Normed.Ring.Lemmas
import Mathlib.Data.Int.Star
import Mathlib.NumberTheory.Zsqrtd.QuadraticReciprocity
import Submission.Commons.NumberTheory.GaussianInt.ncard_assoc_norm_prime_pow
import Submission.Commons.NumberTheory.GaussianInt.ncard_assoc_norm_mul
import Submission.Commons.NumberTheory.GaussianInt.ncard_units

namespace Commons.NumberTheory.GaussianInt

noncomputable section

open Finset
open Commons.NumberTheory.Divisors

local instance : DecidableEq (Associates GaussianInt) := Classical.decEq _

/-! ## The norm of an associate class -/

/-- The norm of an associate class of Gaussian integers: the (natural) norm of any
representative. -/
noncomputable def nc (κ : Associates GaussianInt) : ℕ :=
  Quotient.liftOn κ (fun z => z.norm.natAbs) (by
    intro a b hab
    have h : a.norm = b.norm := Zsqrtd.norm_eq_of_associated (by norm_num : (-1:ℤ) ≤ 0) hab
    rw [h])

@[simp] lemma nc_mk (z : GaussianInt) : nc (Associates.mk z) = z.norm.natAbs := rfl

lemma nc_mul (κ mu : Associates GaussianInt) : nc (κ * mu) = nc κ * nc mu := by
  obtain ⟨a, rfl⟩ := Associates.mk_surjective κ
  obtain ⟨b, rfl⟩ := Associates.mk_surjective mu
  rw [Associates.mk_mul_mk]
  show (a * b).norm.natAbs = a.norm.natAbs * b.norm.natAbs
  rw [Zsqrtd.norm_mul, Int.natAbs_mul]

@[simp] lemma nc_one : nc (1 : Associates GaussianInt) = 1 := rfl

lemma nc_prod_multiset (s : Multiset (Associates GaussianInt)) : nc s.prod = (s.map nc).prod := by
  induction s using Multiset.induction with
  | empty => simp
  | cons a s ih => rw [Multiset.prod_cons, nc_mul, ih, Multiset.map_cons, Multiset.prod_cons]

lemma nc_eq_zero_iff (κ : Associates GaussianInt) : nc κ = 0 ↔ κ = 0 := by
  constructor
  · intro h
    obtain ⟨z, rfl⟩ := Associates.mk_surjective κ
    rw [nc_mk] at h
    rw [Associates.mk_eq_zero]
    rw [← Zsqrtd.norm_eq_zero_iff (d := (-1)) (by norm_num : (-1:ℤ) < 0)]
    exact Int.natAbs_eq_zero.mp h
  · intro h; subst h; rfl

lemma nc_ne_zero {κ : Associates GaussianInt} (h : κ ≠ 0) : nc κ ≠ 0 :=
  fun hh => h ((nc_eq_zero_iff κ).mp hh)

/-! ## Counting elements and associate classes -/

/-- The finset of integer pairs `(x, y)` with `x ^ 2 + y ^ 2 = n`, `|x|, |y| ≤ n`. -/
noncomputable def targetF (n : ℕ) : Finset (ℤ × ℤ) :=
  (Finset.Icc (-(n : ℤ)) (n : ℤ) ×ˢ Finset.Icc (-(n : ℤ)) (n : ℤ)).filter
    (fun z => z.1 ^ 2 + z.2 ^ 2 = (n : ℤ))

/-- The same set, viewed as a finset of Gaussian integers. -/
noncomputable def elemF (n : ℕ) : Finset GaussianInt :=
  (targetF n).image (fun z => (⟨z.1, z.2⟩ : GaussianInt))

lemma norm_mk (a b : ℤ) : (show GaussianInt from ⟨a, b⟩).norm = a ^ 2 + b ^ 2 := by
  rw [Zsqrtd.norm_def]; ring

lemma norm_mk_natAbs (a b : ℤ) :
    (show GaussianInt from ⟨a, b⟩).norm.natAbs = (a ^ 2 + b ^ 2).natAbs := by
  rw [norm_mk]

lemma mem_Icc_of_sq_le {a : ℤ} {n : ℕ} (h : a ^ 2 ≤ (n : ℤ)) :
    a ∈ Finset.Icc (-(n : ℤ)) (n : ℤ) := by
  rw [Finset.mem_Icc]
  have h' : a.natAbs ≤ n := by
    have h1 : ((a.natAbs ^ 2 : ℕ) : ℤ) ≤ (n : ℤ) := by
      rw [Nat.cast_pow, Int.natAbs_sq]; exact h
    have h2 : a.natAbs ^ 2 ≤ n := by exact_mod_cast h1
    have h3 : a.natAbs ≤ Nat.sqrt n := Nat.le_sqrt'.mpr h2
    exact le_trans h3 (Nat.sqrt_le_self n)
  have h4 : |a| ≤ (n : ℤ) := by rw [Int.abs_eq_natAbs]; exact_mod_cast h'
  exact abs_le.mp h4

lemma mem_targetF {n : ℕ} (_hn : 1 ≤ n) (z : ℤ × ℤ) :
    z ∈ targetF n ↔ z.1 ^ 2 + z.2 ^ 2 = (n : ℤ) := by
  rw [targetF, Finset.mem_filter]
  constructor
  · rintro ⟨-, h⟩; exact h
  · intro h
    refine ⟨?_, h⟩
    rw [Finset.mem_product]
    exact ⟨mem_Icc_of_sq_le (by linarith [sq_nonneg z.2]),
           mem_Icc_of_sq_le (by linarith [sq_nonneg z.1])⟩

lemma targetF_card_eq_elemF_card (n : ℕ) : (targetF n).card = (elemF n).card := by
  rw [elemF, Finset.card_image_of_injective]
  intro a b h
  rw [Zsqrtd.ext_iff] at h
  exact Prod.ext h.1 h.2

lemma mem_elemF {n : ℕ} (hn : 1 ≤ n) (z : GaussianInt) :
    z ∈ elemF n ↔ z.norm.natAbs = n := by
  constructor
  · intro hz
    rw [elemF, Finset.mem_image] at hz
    obtain ⟨w, hw, hwz⟩ := hz
    have h1 : z = (⟨w.1, w.2⟩ : GaussianInt) := hwz.symm
    rw [h1, norm_mk_natAbs, (mem_targetF hn w).mp hw]
    rfl
  · intro hz
    rw [elemF, Finset.mem_image]
    refine ⟨(z.re, z.im), ?_, ?_⟩
    · rw [mem_targetF hn]
      have hnz : z.re ^ 2 + z.im ^ 2 = (n : ℤ) := by
        have hh : z.norm = z.re ^ 2 + z.im ^ 2 := norm_mk z.re z.im
        rw [← hh]
        have h2 : (0:ℤ) ≤ z.norm := Zsqrtd.norm_nonneg (by norm_num) z
        have := hz
        rw [Int.natAbs_eq_iff] at this
        rcases this with h | h
        · exact h
        · rw [h]; linarith
      exact hnz
    · exact Zsqrtd.ext_iff.mpr ⟨rfl, rfl⟩

/-- The number of associate classes of Gaussian integers of norm `n`. -/
noncomputable def A (n : ℕ) : ℕ := (Associates.mk '' ((elemF n) : Set GaussianInt)).ncard

/-- The set of associate classes of norm `n`. -/
noncomputable def Xset (n : ℕ) : Set (Associates GaussianInt) := {κ | nc κ = n}

lemma Xset_eq_image (n : ℕ) (hn : 1 ≤ n) :
    Xset n = Associates.mk '' ((elemF n) : Set GaussianInt) := by
  ext κ
  constructor
  · intro hκ
    obtain ⟨z, rfl⟩ := Associates.mk_surjective κ
    rw [Xset, Set.mem_ofPred_eq, nc_mk] at hκ
    exact (Set.mem_image _ _ _).mpr ⟨z, (mem_elemF hn z).mpr hκ, rfl⟩
  · intro hκ
    rw [Set.mem_image] at hκ
    obtain ⟨z, hz, rfl⟩ := hκ
    rw [Xset, Set.mem_ofPred_eq, nc_mk]
    exact (mem_elemF hn z).mp hz

lemma Xset_ncard (n : ℕ) (hn : 1 ≤ n) : (Xset n).ncard = A n := by
  rw [Xset_eq_image n hn]; rfl

/-! ## The number of units is four -/

lemma isUnit_norm_natAbs {u : GaussianInt} (hu : IsUnit u) : u.norm.natAbs = 1 :=
  Zsqrtd.norm_eq_one_iff.mpr hu

lemma mk_eq_one_of_isUnit {u : GaussianInt} (hu : IsUnit u) : Associates.mk u = 1 := by
  rw [show (1 : Associates GaussianInt) = Associates.mk 1 from rfl]
  exact Associates.mk_eq_mk_iff_associated.mpr (associated_one_iff_isUnit.mpr hu)

/-- The fibre of `Associates.mk` over the class of `z0`, among elements of norm `n`,
has exactly `4` elements (the four unit multiples of `z0`). -/
lemma elemF_fiber_card (n : ℕ) (hn : 1 ≤ n) {z0 : GaussianInt} (hz0 : z0 ∈ elemF n) :
    ((elemF n).filter (fun a => Associates.mk a = Associates.mk z0)).card = 4 := by
  classical
  have hz0n : z0.norm.natAbs = n := (mem_elemF hn z0).mp hz0
  have hz0ne : z0 ≠ 0 := by
    intro h; rw [h] at hz0n; simp at hz0n; omega
  have hset : ((elemF n).filter (fun a => Associates.mk a = Associates.mk z0) : Set GaussianInt)
      = {a : GaussianInt | a.norm.natAbs = n ∧ Associates.mk a = Associates.mk z0} := by
    ext a
    rw [Finset.mem_coe, Finset.mem_filter]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨(mem_elemF hn a).mp h1, h2⟩
    · rintro ⟨h1, h2⟩; exact ⟨(mem_elemF hn a).mpr h1, h2⟩
  have hbij : ({u : GaussianInt | IsUnit u}).ncard
      = ({a : GaussianInt | a.norm.natAbs = n ∧ Associates.mk a = Associates.mk z0}).ncard := by
    refine Set.ncard_congr (fun u _ => z0 * u) ?_ ?_ ?_
    · intro u hu
      rw [Set.mem_ofPred_eq]
      refine ⟨?_, ?_⟩
      · rw [Zsqrtd.norm_mul, Int.natAbs_mul, hz0n, isUnit_norm_natAbs hu, mul_one]
      · rw [← Associates.mk_mul_mk, mk_eq_one_of_isUnit hu, mul_one]
    · intro u hu v hv huv
      exact mul_left_cancel₀ hz0ne huv
    · intro a ha
      rw [Set.mem_ofPred_eq] at ha
      obtain ⟨-, hmk⟩ := ha
      rw [Associates.mk_eq_mk_iff_associated] at hmk
      obtain ⟨u, hu⟩ := hmk
      refine ⟨(↑u⁻¹ : GaussianInt), u⁻¹.isUnit, ?_⟩
      rw [← hu, mul_assoc, Units.mul_inv, mul_one]
  rw [← Set.ncard_coe_finset, hset, ← hbij, ncard_units]

/-- Every fibre of `Associates.mk` on the set of elements of norm `n` has `4` elements,
so the number of elements is four times the number of associate classes. -/
lemma elemF_card_eq_four_mul_A (n : ℕ) (hn : 1 ≤ n) : (elemF n).card = 4 * A n := by
  classical
  have hA : A n = ((elemF n).image Associates.mk).card := by
    unfold A
    rw [← Finset.coe_image]
    rw [Set.ncard_coe_finset]
  have hmaps : Set.MapsTo Associates.mk ((elemF n) : Set GaussianInt)
      (((elemF n).image Associates.mk) : Set (Associates GaussianInt)) := by
    intro a ha
    exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨a, Finset.mem_coe.mp ha, rfl⟩)
  have hcard := Finset.card_eq_sum_card_fiberwise hmaps
  have hfiber : ∀ b ∈ (elemF n).image Associates.mk,
      ((elemF n).filter (fun a => Associates.mk a = b)).card = 4 := by
    intro b hb
    rw [Finset.mem_image] at hb
    obtain ⟨z0, hz0, rfl⟩ := hb
    exact elemF_fiber_card n hn hz0
  calc (elemF n).card
      = ∑ b ∈ (elemF n).image Associates.mk,
          ((elemF n).filter (fun a => Associates.mk a = b)).card := hcard
    _ = ∑ _b ∈ (elemF n).image Associates.mk, 4 := Finset.sum_congr rfl hfiber
    _ = 4 * ((elemF n).image Associates.mk).card := by
          rw [Finset.sum_const, smul_eq_mul, mul_comm]
    _ = 4 * A n := by rw [hA]

/-- The number of pairs `(x,y)` of integers with `x ^ 2 + y ^ 2 = n` is `4 * A n`. -/
lemma targetF_card_eq_four_mul_A (n : ℕ) (hn : 1 ≤ n) : (targetF n).card = 4 * A n := by
  rw [targetF_card_eq_elemF_card, elemF_card_eq_four_mul_A n hn]

/-! ## Interaction with the character `χ₄` -/

lemma A_eq_ncard_image (n : ℕ) (hn : 1 ≤ n) :
    A n = (Associates.mk '' {z : GaussianInt | z.norm.natAbs = n}).ncard := by
  have h : ((elemF n) : Set GaussianInt) = {z : GaussianInt | z.norm.natAbs = n} := by
    ext z; simp only [Finset.mem_coe, mem_elemF hn, Set.mem_ofPred_eq]
  rw [← Xset_ncard n hn, Xset_eq_image n hn, h]

lemma mk_image_units : Associates.mk '' {z : GaussianInt | IsUnit z} = {1} := by
  ext κ
  constructor
  · rintro ⟨z, hz, rfl⟩
    rw [Set.mem_singleton_iff]
    exact mk_eq_one_of_isUnit hz
  · intro h
    rw [Set.mem_singleton_iff] at h
    subst h
    exact ⟨1, isUnit_one, Associates.mk_one⟩

lemma A_one : A 1 = 1 := by
  rw [A_eq_ncard_image 1 (by norm_num)]
  have hset : {z : GaussianInt | z.norm.natAbs = 1} = {z : GaussianInt | IsUnit z} := by
    ext z; rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, Zsqrtd.norm_eq_one_iff]
  rw [hset, mk_image_units, Set.ncard_singleton]

/-- The (completely multiplicative) character `χ₄` modulo `4`, as an integer-valued
function of a natural number. -/
def chi4 (d : ℕ) : ℤ := if d % 4 = 1 then 1 else if d % 4 = 3 then -1 else 0

lemma chi4_one : chi4 1 = 1 := by norm_num [chi4]

lemma chi4_mul (a b : ℕ) : chi4 (a * b) = chi4 a * chi4 b := by
  have ha : a % 4 < 4 := Nat.mod_lt _ (by norm_num)
  have hb : b % 4 < 4 := Nat.mod_lt _ (by norm_num)
  rw [chi4, chi4, chi4]
  rw [show (a * b) % 4 = ((a % 4) * (b % 4)) % 4 from Nat.mul_mod a b 4]
  interval_cases a % 4 <;> interval_cases b % 4 <;> simp

lemma A_mul_of_coprime (m n : ℕ) (hm : 1 ≤ m) (hn : 1 ≤ n) (hcop : Nat.Coprime m n) :
    A (m * n) = A m * A n := by
  have h1 : 1 ≤ m * n := Nat.one_le_iff_ne_zero.mpr (mul_ne_zero (by omega) (by omega))
  rw [A_eq_ncard_image (m * n) h1, A_eq_ncard_image m hm, A_eq_ncard_image n hn]
  exact ncard_assoc_norm_mul m n hm hn hcop

lemma A_prime_pow (p k : ℕ) (hp : p.Prime) :
    A (p ^ k) = (if p = 2 then 1 else if p % 4 = 1 then k + 1 else if Even k then 1 else 0) := by
  have h1 : 1 ≤ p ^ k := Nat.succ_le_iff.mpr (pow_pos hp.pos k)
  rw [A_eq_ncard_image (p ^ k) h1]
  exact ncard_assoc_norm_prime_pow p k hp

theorem two_squares_repr_count (n : ℕ) (hn : 1 ≤ n) :
    ((Finset.filter (fun z : ℤ × ℤ => z.1 ^ 2 + z.2 ^ 2 = (n : ℤ))
      (Finset.Icc (-(n : ℤ)) (n : ℤ) ×ˢ Finset.Icc (-(n : ℤ)) (n : ℤ))).card : ℤ)
      = 4 * (((n.divisors.filter (fun d => d % 4 = 1)).card : ℤ))
        - 4 * (((n.divisors.filter (fun d => d % 4 = 3)).card : ℤ)) := by
  have hn0 : n ≠ 0 := by omega
  have hmul : ∀ x y : ℕ, x.Coprime y → A (x * y) = A x * A y := by
    intro x y hxy
    rcases Nat.eq_zero_or_pos x with hx | hx
    · subst hx
      have hy : y = 1 := (Nat.coprime_zero_left y).mp hxy
      subst hy; simp [A_one]
    · rcases Nat.eq_zero_or_pos y with hy | hy
      · subst hy
        have hx1 : x = 1 := (Nat.coprime_zero_right x).mp hxy
        subst hx1; simp [A_one]
      · exact A_mul_of_coprime x y hx hy hxy
  have hprod : A n = ∏ p ∈ n.primeFactors, A (p ^ n.factorization p) := by
    rw [Nat.multiplicative_factorization A hmul A_one hn0]
    rw [Nat.prod_factorization_eq_prod_primeFactors]
  have hA : (A n : ℤ) = ∑ d ∈ n.divisors, chi4 d := by
    rw [hprod, Nat.cast_prod,
      Commons.NumberTheory.Divisors.sum_divisors_eq_prod_primeFactors chi4 chi4_one
        chi4_mul n hn0]
    refine Finset.prod_congr rfl (fun p hp => ?_)
    have hp' : p.Prime := Nat.prime_of_mem_primeFactors hp
    rw [A_prime_pow p (n.factorization p) hp']
    simp only [chi4]
    rw [Commons.NumberTheory.Divisors.sum_range_chi4_pow p (n.factorization p) hp']
    by_cases h2 : p = 2
    · subst h2; norm_num
    · rw [if_neg h2, if_neg h2]
      by_cases h41 : p % 4 = 1
      · rw [if_pos h41, if_pos h41]; push_cast; ring
      · rw [if_neg h41, if_neg h41]
        by_cases he : Even (n.factorization p)
        · rw [if_pos he, if_pos he]; norm_num
        · rw [if_neg he, if_neg he]; norm_num
  have hcard := targetF_card_eq_four_mul_A n hn
  change ((targetF n).card : ℤ) = _
  rw [hcard]
  push_cast
  rw [hA]
  simp only [chi4]
  rw [Commons.NumberTheory.Divisors.sum_chi4_divisors n]
  ring

end

end Commons.NumberTheory.GaussianInt
