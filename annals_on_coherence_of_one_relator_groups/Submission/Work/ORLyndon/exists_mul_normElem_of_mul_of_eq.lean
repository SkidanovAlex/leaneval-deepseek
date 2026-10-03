import Mathlib
import Submission.Work.ORLyndon.Magnus

/-!
# Divisibility by the norm element in a group algebra

For a group `G`, a field `K`, an element `w : G` and `b : K[G]` with `b * w = b`, the element `b`
is a right multiple of the norm element `N = 1 + w + ⋯ + w ^ (orderOf w - 1)`:

`b = c * N` for some `c : K[G]`.

Equivalently, the right annihilator in `K[G]` of `of G w - 1` is the principal right ideal generated
by `N` (the reverse inclusion being `N * (w - 1) = w ^ orderOf w - 1 = 0`).

The proof is a descent on the support of `b`: `b * w = b` says that the coefficients of `b` are
constant along the right cosets of `⟨w⟩`, so choosing `g` in the support and subtracting
`b g • (g * N)` — the contribution of the coset `g⟨w⟩` — strictly decreases the support, while
preserving the relation `b * w = b`.  When `w` has infinite order, the same constancy forces `b = 0`
(the `w ^ i` are distinct), and `N = 0`.
-/

set_option autoImplicit false

namespace Work.ORLyndon

open MonoidAlgebra

universe u v

variable {G : Type u} [Group G] [DecidableEq G] {K : Type v} [Field K]

/-- The norm element `1 + w + ⋯ + w ^ (n-1)` is fixed by right multiplication by `w`, whenever
`w ^ n = 1`. -/
private lemma normElem_mul_of_eq (n : ℕ) (w : G) (hw : w ^ n = 1) :
    normElem K n w * MonoidAlgebra.of K G w = normElem K n w := by
  have h0 : normElem K n w * (MonoidAlgebra.of K G w - 1) = 0 := by
    rw [normElem, geom_sum_mul, ← map_pow, hw, map_one, sub_self]
  rwa [mul_sub, mul_one, sub_eq_zero] at h0

/-- The coefficients of the norm element: `(1 + w + ⋯ + w ^ (n-1)).coeff y` is the number of
exponents `i < n` with `w ^ i = y`. -/
private lemma normElem_coeff (n : ℕ) (w y : G) :
    (normElem K n w).coeff y =
      ∑ i ∈ Finset.range n, if w ^ i = y then (1 : K) else 0 := by
  rw [normElem, MonoidAlgebra.coeff_sum, Finsupp.finsetSum_apply]
  exact Finset.sum_congr rfl fun i _ => by
    rw [← map_pow, MonoidAlgebra.of_apply, MonoidAlgebra.coeff_single, Finsupp.single_apply]

/-- A non-zero coefficient of the norm element forces the index to be a power of `w`. -/
private lemma exists_pow_of_coeff_normElem_ne_zero {n : ℕ} {w y : G}
    (h : (normElem K n w).coeff y ≠ 0) : ∃ i, i < n ∧ w ^ i = y := by
  by_contra hc
  apply h
  rw [normElem_coeff]
  refine Finset.sum_eq_zero fun i hi => ?_
  rw [if_neg (fun hwi => hc ⟨i, Finset.mem_range.mp hi, hwi⟩)]

/-- The coefficient of `z` in `(of g) * N` is the coefficient of `g⁻¹ * z` in `N`. -/
private lemma coeff_of_mul_normElem {w : G} (g z : G) (n : ℕ) :
    ((MonoidAlgebra.of K G g) * normElem K n w).coeff z =
      (normElem K n w).coeff (g⁻¹ * z) := by
  rw [MonoidAlgebra.of_apply, MonoidAlgebra.coeff_single_mul_apply, one_mul]

/-- The hypothesis `b * w = b` computes one coefficient of `b` from another. -/
private lemma coeff_mul_of {w : G} {b : MonoidAlgebra K G}
    (hb : b * MonoidAlgebra.of K G w = b) (x : G) :
    b.coeff (x * w) = b.coeff x := by
  have h := congrArg (fun z : MonoidAlgebra K G => z.coeff (x * w)) hb
  rw [MonoidAlgebra.of_apply, MonoidAlgebra.coeff_mul_single_apply] at h
  have hx : (x * w) * w⁻¹ = x := by rw [mul_assoc, mul_inv_cancel, mul_one]
  rw [hx] at h
  simpa using h.symm

/-- Iterated form of `coeff_mul_of`: the coefficients of `b` are constant along the right coset
`x⟨w⟩`. -/
private lemma coeff_mul_pow_of {w : G} {b : MonoidAlgebra K G}
    (hb : b * MonoidAlgebra.of K G w = b) (x : G) (i : ℕ) :
    b.coeff (x * w ^ i) = b.coeff x := by
  induction i with
  | zero => simp
  | succ i ih => rw [pow_succ, ← mul_assoc, coeff_mul_of hb, ih]

/-- **The finite-order case**: if `w` has finite order, every `b` with `b * w = b` is divisible on
the right by the norm element `1 + w + ⋯ + w ^ (orderOf w - 1)`.

The proof is a strong induction on the cardinality of the support of `b`. -/
private lemma exists_mul_normElem_of_finite {w : G} (hn : 0 < orderOf w) :
    ∀ k : ℕ, ∀ b : MonoidAlgebra K G, b.coeff.support.card ≤ k →
      b * MonoidAlgebra.of K G w = b →
      ∃ c : MonoidAlgebra K G, b = c * normElem K (orderOf w) w := by
  have hw : w ^ orderOf w = 1 := pow_orderOf_eq_one w
  intro k
  induction k with
  | zero =>
    intro b hk hb
    have hb0 : b = 0 := by
      have h1 : b.coeff.support = ∅ := Finset.card_eq_zero.mp (Nat.le_zero.mp hk)
      have h2 : b.coeff = 0 := Finsupp.support_eq_empty.mp h1
      rw [← MonoidAlgebra.coeff_inj]
      rw [h2, MonoidAlgebra.coeff_zero]
    exact ⟨0, by rw [hb0, zero_mul]⟩
  | succ k ih =>
    intro b hk hb
    by_cases hle : b.coeff.support.card ≤ k
    · exact ih b hle hb
    · have hpos : 0 < b.coeff.support.card := by omega
      obtain ⟨g, hg⟩ := Finset.card_pos.mp hpos
      have hbg : b.coeff g ≠ 0 := Finsupp.mem_support_iff.mp hg
      set N : MonoidAlgebra K G := normElem K (orderOf w) w with hN
      set a : MonoidAlgebra K G := b.coeff g • (MonoidAlgebra.of K G g * N) with ha
      have hNm : N * MonoidAlgebra.of K G w = N := by
        rw [hN]; exact normElem_mul_of_eq (orderOf w) w hw
      -- `a` is also fixed by right multiplication by `w`
      have ha_mul : a * MonoidAlgebra.of K G w = a := by
        rw [ha, smul_mul_assoc, mul_assoc, hNm]
      have hb'_mul : (b - a) * MonoidAlgebra.of K G w = b - a := by
        rw [sub_mul, hb, ha_mul]
      -- `a` does not change `b` in degree `g`
      have hagg : a.coeff g = b.coeff g := by
        rw [ha, MonoidAlgebra.coeff_smul_apply, smul_eq_mul, coeff_of_mul_normElem,
          inv_mul_cancel, normElem_coeff]
        rw [Finset.sum_eq_single 0]
        · simp
        · intro i hi hi0
          rw [if_neg (pow_ne_one_of_lt_orderOf hi0 (Finset.mem_range.mp hi))]
        · intro hmem
          exact absurd (Finset.mem_range.mpr hn) hmem
      -- the support of `a` is contained in the right coset `g⟨w⟩`, hence in the support of `b`
      have hsupp_a : a.coeff.support ⊆ b.coeff.support := by
        intro z hz
        rw [Finsupp.mem_support_iff] at hz ⊢
        have hNz : N.coeff (g⁻¹ * z) ≠ 0 := by
          intro h0
          apply hz
          rw [ha, MonoidAlgebra.coeff_smul_apply, smul_eq_mul, coeff_of_mul_normElem, h0,
            mul_zero]
        rw [hN] at hNz
        obtain ⟨i, _hi, hwi⟩ := exists_pow_of_coeff_normElem_ne_zero hNz
        have hz_eq : z = g * w ^ i := by rw [hwi, mul_inv_cancel_left]
        rw [hz_eq, coeff_mul_pow_of hb g i]
        exact hbg
      have hsupp_b' : (b - a).coeff.support ⊆ b.coeff.support := by
        intro z hz
        rw [MonoidAlgebra.coeff_sub] at hz
        rcases Finset.mem_union.mp (Finsupp.support_sub hz) with h | h
        · exact h
        · exact hsupp_a h
      have hg_notin : g ∉ (b - a).coeff.support := by
        have h0 : (b - a).coeff g = 0 := by
          rw [MonoidAlgebra.coeff_sub, Finsupp.sub_apply, hagg, sub_self]
        simpa [Finsupp.mem_support_iff] using h0
      have hcard : (b - a).coeff.support.card < b.coeff.support.card := by
        have hins : insert g (b - a).coeff.support ⊆ b.coeff.support := by
          intro z hz
          rcases Finset.mem_insert.mp hz with rfl | hz
          · exact hg
          · exact hsupp_b' hz
        calc (b - a).coeff.support.card
            < (insert g (b - a).coeff.support).card := by
              rw [Finset.card_insert_of_notMem hg_notin]
              exact Nat.lt_succ_self _
          _ ≤ b.coeff.support.card := Finset.card_le_card hins
      obtain ⟨c', hc'⟩ := ih (b - a) (by omega) hb'_mul
      refine ⟨c' + b.coeff g • MonoidAlgebra.of K G g, ?_⟩
      have h : (c' + b.coeff g • MonoidAlgebra.of K G g) * normElem K (orderOf w) w
          = c' * normElem K (orderOf w) w + a := by
        rw [add_mul, smul_mul_assoc, ← ha]
      rw [h, ← hc']
      exact (sub_add_cancel b a).symm

theorem exists_mul_normElem_of_mul_of_eq {G : Type*} [Group G] [DecidableEq G]
    {K : Type*} [Field K] {w : G} {b : MonoidAlgebra K G}
    (hb : b * MonoidAlgebra.of K G w = b) :
    ∃ c : MonoidAlgebra K G, b = c * Work.ORLyndon.normElem K (orderOf w) w := by
  classical
  by_cases hfin : orderOf w = 0
  · -- infinite order: the coefficients of `b` are constant on the infinite set `g⟨w⟩`, so `b = 0`
    have hb0 : b = 0 := by
      by_contra hne
      have hne' : b.coeff ≠ 0 := by
        intro h
        exact hne (by rw [← MonoidAlgebra.coeff_inj, h, MonoidAlgebra.coeff_zero])
      obtain ⟨g, hg⟩ := Finsupp.support_nonempty_iff.mpr hne'
      have hbg : b.coeff g ≠ 0 := Finsupp.mem_support_iff.mp hg
      have hwpow_one : ∀ m : ℕ, w ^ m = 1 → m = 0 := by
        intro m hm
        have hdvd : orderOf w ∣ m := orderOf_dvd_iff_pow_eq_one.mpr hm
        rw [hfin] at hdvd
        exact Nat.zero_dvd.mp hdvd
      have hinj : Function.Injective (fun i : ℕ => g * w ^ i) := by
        intro i j hij
        have hwij : w ^ i = w ^ j := mul_left_cancel hij
        rcases le_total i j with hle | hle
        · have hsub : w ^ (j - i) = 1 := by
            have h1 : w ^ j = w ^ i * w ^ (j - i) := by
              rw [← pow_add, Nat.add_sub_of_le hle]
            rw [hwij] at h1
            exact mul_left_cancel (h1.symm.trans (mul_one _).symm)
          have := hwpow_one (j - i) hsub
          omega
        · have hsub : w ^ (i - j) = 1 := by
            have h1 : w ^ i = w ^ j * w ^ (i - j) := by
              rw [← pow_add, Nat.add_sub_of_le hle]
            rw [← hwij] at h1
            exact mul_left_cancel (h1.symm.trans (mul_one _).symm)
          have := hwpow_one (i - j) hsub
          omega
      have hsub : (Finset.range (b.coeff.support.card + 1)).image (fun i => g * w ^ i)
          ⊆ b.coeff.support := by
        intro z hz
        rw [Finset.mem_image] at hz
        obtain ⟨i, _hi, rfl⟩ := hz
        rw [Finsupp.mem_support_iff, coeff_mul_pow_of hb g i]
        exact hbg
      have hcard := Finset.card_le_card hsub
      rw [Finset.card_image_of_injective _ hinj, Finset.card_range] at hcard
      omega
    exact ⟨0, by rw [hb0, zero_mul]⟩
  · -- finite order
    have hn : 0 < orderOf w := Nat.pos_of_ne_zero hfin
    exact exists_mul_normElem_of_finite hn b.coeff.support.card b le_rfl hb

end Work.ORLyndon
