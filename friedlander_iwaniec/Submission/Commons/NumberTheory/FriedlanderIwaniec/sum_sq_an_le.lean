import Mathlib
import Submission.Commons.NumberTheory.ArithmeticFunction.card_divisors_le_rpow
import Submission.Commons.Data.Finset.card_pullback_eq_sum_sq
import Submission.Commons.NumberTheory.Diophantine.card_sq_sub_sq_le_divisors

set_option maxHeartbeats 2000000

namespace Commons.NumberTheory.FriedlanderIwaniec

open Finset

/-! ## The counting box -/

private noncomputable def Ybox (x : ℕ) : Finset ℤ :=
  Finset.Icc (-((Nat.sqrt x : ℕ) : ℤ)) ((Nat.sqrt x : ℕ) : ℤ)

private noncomputable def Zbox (x : ℕ) : Finset ℤ :=
  Finset.Icc (-((Nat.sqrt (Nat.sqrt x) : ℕ) : ℤ)) ((Nat.sqrt (Nat.sqrt x) : ℕ) : ℤ)

private noncomputable def Bbox (x : ℕ) : Finset (ℤ × ℤ) := (Ybox x) ×ˢ (Zbox x)

/-- The function `(a,b) ↦ a² + b⁴`. -/
private def gfun (p : ℤ × ℤ) : ℤ := p.1 ^ 2 + p.2 ^ 4

/-- The fibre count at level `n`. -/
private noncomputable def bfc (x : ℕ) (n : ℤ) : ℕ := ((Bbox x).filter (fun p => gfun p = n)).card

/-- The off-diagonal / diagonal fibre count for fixed second coordinates. -/
private noncomputable def Mset (x : ℕ) (z1 z2 : ℤ) : Finset (ℤ × ℤ) :=
  ((Ybox x) ×ˢ (Ybox x)).filter (fun pq : ℤ × ℤ => pq.1 ^ 2 + z1 ^ 4 = pq.2 ^ 2 + z2 ^ 4)

private lemma abs_le_sq (z : ℤ) : |z| ≤ z ^ 2 := by
  have h : z.natAbs ≤ z.natAbs ^ 2 := Nat.le_self_pow (by norm_num) _
  rw [Int.abs_eq_natAbs]
  have hz : ((z.natAbs : ℤ)) ^ 2 = z ^ 2 := by
    rw [← Nat.cast_pow, ← Int.natAbs_pow, Int.natAbs_of_nonneg (by positivity)]
  rw [← hz]
  exact_mod_cast h

private lemma abs_le_pow_four (z : ℤ) : |z| ≤ z ^ 4 := by
  have h : z.natAbs ≤ z.natAbs ^ 4 := Nat.le_self_pow (by norm_num) _
  rw [Int.abs_eq_natAbs]
  have hz : ((z.natAbs : ℤ)) ^ 4 = z ^ 4 := by
    rw [← Nat.cast_pow, ← Int.natAbs_pow, Int.natAbs_of_nonneg (by positivity)]
  rw [← hz]
  exact_mod_cast h

private lemma int_natAbs_sq_cast (a : ℤ) : ((a.natAbs : ℕ) : ℤ) ^ 2 = a ^ 2 :=
  Int.natAbs_sq a

private lemma sqrt_sqrt_pow_four_le (x : ℕ) : (Nat.sqrt (Nat.sqrt x)) ^ 4 ≤ x := by
  have h1 : (Nat.sqrt (Nat.sqrt x)) ^ 2 ≤ Nat.sqrt x := Nat.sqrt_le' (Nat.sqrt x)
  have h2 : (Nat.sqrt x) ^ 2 ≤ x := Nat.sqrt_le' x
  have h3 : ((Nat.sqrt (Nat.sqrt x)) ^ 2) ^ 2 ≤ (Nat.sqrt x) ^ 2 :=
    Nat.pow_le_pow_left h1 2
  calc (Nat.sqrt (Nat.sqrt x)) ^ 4 = ((Nat.sqrt (Nat.sqrt x)) ^ 2) ^ 2 := by ring
    _ ≤ (Nat.sqrt x) ^ 2 := h3
    _ ≤ x := h2

/-- Membership in `Ybox`. -/
private lemma mem_Ybox_iff (x : ℕ) (a : ℤ) : a ∈ Ybox x ↔ |a| ≤ ((Nat.sqrt x : ℕ) : ℤ) := by
  rw [Ybox, Finset.mem_Icc, abs_le]

/-- Membership in `Zbox`. -/
private lemma mem_Zbox_iff (x : ℕ) (b : ℤ) :
    b ∈ Zbox x ↔ |b| ≤ ((Nat.sqrt (Nat.sqrt x) : ℕ) : ℤ) := by
  rw [Zbox, Finset.mem_Icc, abs_le]

/-- First coordinate bound: `a ^ 2 ≤ x` forces `a ∈ Ybox x`. -/
private lemma mem_Ybox_of_sq_le (x : ℕ) {a : ℤ} (ha : a ^ 2 ≤ (x : ℤ)) : a ∈ Ybox x := by
  rw [mem_Ybox_iff]
  have h2 : (a.natAbs : ℕ) ^ 2 ≤ x := by
    have h1 : ((a.natAbs : ℕ) : ℤ) ^ 2 ≤ (x : ℤ) := by rw [int_natAbs_sq_cast]; exact ha
    exact_mod_cast h1
  have h3 : (a.natAbs : ℕ) ≤ Nat.sqrt x := Nat.le_sqrt'.mpr h2
  have : |a| ≤ ((Nat.sqrt x : ℕ) : ℤ) := by
    rw [Int.abs_eq_natAbs]; exact_mod_cast h3
  exact this

/-- Second coordinate bound: `b ^ 4 ≤ x` forces `b ∈ Zbox x`. -/
private lemma mem_Zbox_of_pow_four_le (x : ℕ) {b : ℤ} (hb : b ^ 4 ≤ (x : ℤ)) : b ∈ Zbox x := by
  rw [mem_Zbox_iff]
  have hb' : (b ^ 2) ^ 2 ≤ (x : ℤ) := by
    have : b ^ 4 = (b ^ 2) ^ 2 := by ring
    rwa [this] at hb
  have h2 : ((b.natAbs : ℕ) ^ 2) ^ 2 ≤ x := by
    have h1 : (((b.natAbs : ℕ) : ℤ) ^ 2) ^ 2 ≤ (x : ℤ) := by rw [int_natAbs_sq_cast]; exact hb'
    exact_mod_cast h1
  have h3 : (b.natAbs : ℕ) ^ 2 ≤ Nat.sqrt x := Nat.le_sqrt'.mpr h2
  have h4 : (b.natAbs : ℕ) ≤ Nat.sqrt (Nat.sqrt x) := Nat.le_sqrt'.mpr h3
  have : |b| ≤ ((Nat.sqrt (Nat.sqrt x) : ℕ) : ℤ) := by
    rw [Int.abs_eq_natAbs]; exact_mod_cast h4
  exact this

/-- Every pair `(a,b)` with `a² + b⁴ ≤ x` lies in the box. -/
private lemma mem_Bbox_of_le (x : ℕ) {p : ℤ × ℤ} (hp : gfun p ≤ (x : ℤ)) : p ∈ Bbox x := by
  rw [Bbox, Finset.mem_product]
  refine ⟨?_, ?_⟩
  · apply mem_Ybox_of_sq_le x
    have : p.2 ^ 4 ≥ 0 := by positivity
    simp only [gfun] at hp
    linarith
  · apply mem_Zbox_of_pow_four_le x
    have : p.1 ^ 2 ≥ 0 := by positivity
    simp only [gfun] at hp
    linarith

/-- For `n ≤ x` the representation set of `n` is exactly the fibre of the box. -/
private lemma fiber_eq_Bbox (x : ℕ) (n : ℕ) (hn : n ≤ x) :
    ({p : ℤ × ℤ | p.1 ^ 2 + p.2 ^ 4 = (n : ℤ)} : Set (ℤ × ℤ))
      = ↑((Bbox x).filter (fun p => p.1 ^ 2 + p.2 ^ 4 = (n : ℤ))) := by
  ext p
  constructor
  · intro hp
    rw [Finset.mem_coe, Finset.mem_filter]
    refine ⟨mem_Bbox_of_le x ?_, hp⟩
    simp only [gfun]
    rw [hp]
    exact_mod_cast hn
  · intro hp
    rw [Finset.mem_coe, Finset.mem_filter] at hp
    exact hp.2

/-- For `n ≤ x`, the `ncard` of the representation set is the cardinality of the box fibre. -/
private lemma ncard_fiber_eq (x : ℕ) (n : ℕ) (hn : n ≤ x) :
    ({p : ℤ × ℤ | p.1 ^ 2 + p.2 ^ 4 = (n : ℤ)} : Set (ℤ × ℤ)).ncard = bfc x (n : ℤ) := by
  rw [fiber_eq_Bbox x n hn, Set.ncard_coe_finset]
  rfl

/-- Cardinality of `Ybox`. -/
private lemma Ybox_card (x : ℕ) : (Ybox x).card = 2 * Nat.sqrt x + 1 := by
  rw [Ybox, Int.card_Icc]
  have h : ((Nat.sqrt x : ℕ) : ℤ) + 1 - (-(((Nat.sqrt x : ℕ) : ℤ))) =
      2 * ((Nat.sqrt x : ℕ) : ℤ) + 1 := by ring
  rw [h]
  omega

/-- Cardinality of `Zbox`. -/
private lemma Zbox_card (x : ℕ) : (Zbox x).card = 2 * Nat.sqrt (Nat.sqrt x) + 1 := by
  rw [Zbox, Int.card_Icc]
  have h : ((Nat.sqrt (Nat.sqrt x) : ℕ) : ℤ) + 1 - (-(((Nat.sqrt (Nat.sqrt x) : ℕ) : ℤ))) =
      2 * ((Nat.sqrt (Nat.sqrt x) : ℕ) : ℤ) + 1 := by ring
  rw [h]
  omega

private lemma Ybox_card_le (x : ℕ) (hx : 1 ≤ x) :
    ((Ybox x).card : ℝ) ≤ 3 * (x : ℝ) ^ (1 / 2 : ℝ) := by
  rw [Ybox_card]
  have hxR : (0 : ℝ) ≤ (x : ℝ) := by positivity
  have hs : ((Nat.sqrt x : ℕ) : ℝ) ≤ Real.sqrt (x : ℝ) := by
    rw [Real.le_sqrt (by positivity) hxR]
    have := Nat.sqrt_le' x
    exact_mod_cast this
  have hs1 : (1 : ℝ) ≤ Real.sqrt (x : ℝ) := Real.one_le_sqrt.mpr (by exact_mod_cast hx)
  rw [show (x : ℝ) ^ (1 / 2 : ℝ) = Real.sqrt (x : ℝ) from (Real.sqrt_eq_rpow x).symm]
  push_cast
  linarith

private lemma Zbox_card_le (x : ℕ) (hx : 1 ≤ x) :
    ((Zbox x).card : ℝ) ≤ 3 * (x : ℝ) ^ (1 / 4 : ℝ) := by
  rw [Zbox_card]
  have hxR : (0 : ℝ) < (x : ℝ) := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hx)
  have hK4 : (((Nat.sqrt (Nat.sqrt x) : ℕ) : ℝ)) ^ 4 ≤ (x : ℝ) := by
    have := sqrt_sqrt_pow_four_le x
    push_cast
    exact_mod_cast this
  have hK : (((Nat.sqrt (Nat.sqrt x) : ℕ) : ℝ)) ≤ (x : ℝ) ^ (1 / 4 : ℝ) := by
    have hK0 : (0 : ℝ) ≤ ((Nat.sqrt (Nat.sqrt x) : ℕ) : ℝ) := by positivity
    have h4 : ((x : ℝ) ^ (1 / 4 : ℝ)) ^ 4 = (x : ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hxR)]
      rw [show (1 / 4 : ℝ) * ((4 : ℕ) : ℝ) = 1 by norm_num, Real.rpow_one]
    have : (((Nat.sqrt (Nat.sqrt x) : ℕ) : ℝ)) ^ 4 ≤ ((x : ℝ) ^ (1 / 4 : ℝ)) ^ 4 := by
      rw [h4]; exact hK4
    exact (pow_le_pow_iff_left₀ hK0 (Real.rpow_nonneg (le_of_lt hxR) _) (by norm_num)).mp this
  have hx1 : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
  have hx14 : (1 : ℝ) ≤ (x : ℝ) ^ (1 / 4 : ℝ) := Real.one_le_rpow hx1 (by norm_num)
  push_cast
  linarith

/-- `gfun` is bounded by `2x` on the box. -/
private lemma gfun_le_two_mul (x : ℕ) {a : ℤ × ℤ} (ha : a ∈ Bbox x) :
    gfun a ≤ 2 * (x : ℤ) := by
  rw [Bbox, Finset.mem_product] at ha
  obtain ⟨ha1, ha2⟩ := ha
  rw [mem_Ybox_iff] at ha1
  rw [mem_Zbox_iff] at ha2
  have h1 : a.1 ^ 2 ≤ (x : ℤ) := by
    have h : |a.1| ^ 2 ≤ ((Nat.sqrt x : ℕ) : ℤ) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) ha1 2
    rw [← abs_pow, abs_of_nonneg (by positivity : (0 : ℤ) ≤ a.1 ^ 2)] at h
    calc a.1 ^ 2 ≤ ((Nat.sqrt x : ℕ) : ℤ) ^ 2 := h
      _ = ((Nat.sqrt x ^ 2 : ℕ) : ℤ) := by push_cast; ring
      _ ≤ (x : ℤ) := by exact_mod_cast Nat.sqrt_le' x
  have h2 : a.2 ^ 4 ≤ (x : ℤ) := by
    have h : |a.2| ^ 4 ≤ ((Nat.sqrt (Nat.sqrt x) : ℕ) : ℤ) ^ 4 :=
      pow_le_pow_left₀ (abs_nonneg _) ha2 4
    rw [← abs_pow, abs_of_nonneg (by positivity : (0 : ℤ) ≤ a.2 ^ 4)] at h
    calc a.2 ^ 4 ≤ ((Nat.sqrt (Nat.sqrt x) : ℕ) : ℤ) ^ 4 := h
      _ = ((Nat.sqrt (Nat.sqrt x) ^ 4 : ℕ) : ℤ) := by push_cast; ring
      _ ≤ (x : ℤ) := by exact_mod_cast sqrt_sqrt_pow_four_le x
  simp only [gfun]
  linarith

/-- `e.natAbs ≤ x` for `e = z₂⁴ - z₁⁴` with `z₁, z₂` in `Zbox x`. -/
private lemma sub_pow_four_natAbs_le (x : ℕ) {z1 z2 : ℤ} (hz1 : z1 ∈ Zbox x)
    (hz2 : z2 ∈ Zbox x) : (z2 ^ 4 - z1 ^ 4).natAbs ≤ x := by
  have hmem : ∀ {z : ℤ}, z ∈ Zbox x → z ^ 4 ≤ (x : ℤ) := by
    intro z hz
    rw [mem_Zbox_iff] at hz
    have h : |z| ^ 4 ≤ ((Nat.sqrt (Nat.sqrt x) : ℕ) : ℤ) ^ 4 := pow_le_pow_left₀ (abs_nonneg _) hz 4
    rw [← abs_pow, abs_of_nonneg (by positivity : (0 : ℤ) ≤ z ^ 4)] at h
    calc z ^ 4 ≤ ((Nat.sqrt (Nat.sqrt x) : ℕ) : ℤ) ^ 4 := h
      _ = ((Nat.sqrt (Nat.sqrt x) ^ 4 : ℕ) : ℤ) := by push_cast; ring
      _ ≤ (x : ℤ) := by exact_mod_cast sqrt_sqrt_pow_four_le x
  have h1 := hmem hz1
  have h2 := hmem hz2
  have hz1nn : (0 : ℤ) ≤ z1 ^ 4 := by positivity
  have hz2nn : (0 : ℤ) ≤ z2 ^ 4 := by positivity
  have he : |z2 ^ 4 - z1 ^ 4| ≤ (x : ℤ) := by
    rw [abs_le]; constructor <;> linarith
  have hcast : (((z2 ^ 4 - z1 ^ 4).natAbs : ℕ) : ℤ) ≤ (x : ℤ) := by
    rw [← Int.abs_eq_natAbs]; exact he
  exact_mod_cast hcast

private lemma Mset_eq_sub (x : ℕ) (z1 z2 : ℤ) :
    Mset x z1 z2 = ((Ybox x) ×ˢ (Ybox x)).filter
      (fun pq : ℤ × ℤ => pq.1 ^ 2 - pq.2 ^ 2 = z2 ^ 4 - z1 ^ 4) := by
  rw [Mset]
  apply Finset.filter_congr
  intro pq _
  constructor <;> intro h <;> linarith

/-- Diagonal bound for the fibre count. -/
private lemma Mset_diag_le (x : ℕ) {z1 z2 : ℤ} (hz : z1 ^ 2 = z2 ^ 2) :
    (Mset x z1 z2).card ≤ 2 * (Ybox x).card := by
  set Y := Ybox x with hY
  have hz4 : z1 ^ 4 = z2 ^ 4 := by
    have h1 : z1 ^ 4 = (z1 ^ 2) ^ 2 := by ring
    have h2 : z2 ^ 4 = (z2 ^ 2) ^ 2 := by ring
    rw [h1, h2, hz]
  have hsub : (Mset x z1 z2) ⊆ ((Y ×ˢ Y).filter (fun pq : ℤ × ℤ => pq.2 = pq.1)) ∪
      ((Y ×ˢ Y).filter (fun pq : ℤ × ℤ => pq.2 = -pq.1)) := by
    intro pq hpq
    rw [Mset, Finset.mem_filter] at hpq
    obtain ⟨hmem, hcond⟩ := hpq
    have hsq : pq.1 ^ 2 = pq.2 ^ 2 := by linarith
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with h | h
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hmem, h.symm⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hmem, by linarith⟩)
  have hcard1 : (((Y ×ˢ Y).filter (fun pq : ℤ × ℤ => pq.2 = pq.1))).card ≤ Y.card := by
    apply Finset.card_le_card_of_injOn (fun pq : ℤ × ℤ => pq.1)
    · intro pq hpq
      rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at hpq
      exact hpq.1.1
    · intro pq hpq q hq heq
      rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at hpq hq
      simp only at heq
      exact Prod.ext heq (by rw [hpq.2, hq.2, heq])
  have hcard2 : (((Y ×ˢ Y).filter (fun pq : ℤ × ℤ => pq.2 = -pq.1))).card ≤ Y.card := by
    apply Finset.card_le_card_of_injOn (fun pq : ℤ × ℤ => pq.1)
    · intro pq hpq
      rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at hpq
      exact hpq.1.1
    · intro pq hpq q hq heq
      rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at hpq hq
      simp only at heq
      exact Prod.ext heq (by rw [hpq.2, hq.2, heq])
  calc (Mset x z1 z2).card
      ≤ (((Y ×ˢ Y).filter (fun pq : ℤ × ℤ => pq.2 = pq.1)) ∪
          ((Y ×ˢ Y).filter (fun pq : ℤ × ℤ => pq.2 = -pq.1))).card := Finset.card_le_card hsub
    _ ≤ (((Y ×ˢ Y).filter (fun pq : ℤ × ℤ => pq.2 = pq.1))).card +
          (((Y ×ˢ Y).filter (fun pq : ℤ × ℤ => pq.2 = -pq.1))).card := Finset.card_union_le _ _
    _ ≤ Y.card + Y.card := add_le_add hcard1 hcard2
    _ = 2 * (Ybox x).card := by rw [hY]; ring

/-- Off-diagonal bound for the fibre count. -/
private lemma Mset_offdiag_le (eps : ℝ) (heps : 0 < eps) (C0 : ℝ) (hC0pos : 0 < C0)
    (hC0 : ∀ n : ℕ, 1 ≤ n → ((n.divisors.card : ℕ) : ℝ) ≤ C0 * (n : ℝ) ^ eps)
    (x : ℕ) (hx : 1 ≤ x) {z1 z2 : ℤ} (hz1 : z1 ∈ Zbox x) (hz2 : z2 ∈ Zbox x)
    (hz : z1 ^ 2 ≠ z2 ^ 2) :
    ((Mset x z1 z2).card : ℝ) ≤ 2 * C0 * (x : ℝ) ^ eps := by
  have hz4 : z1 ^ 4 ≠ z2 ^ 4 := by
    intro h
    apply hz
    have h1 : z1 ^ 4 = (z1 ^ 2) ^ 2 := by ring
    have h2 : z2 ^ 4 = (z2 ^ 2) ^ 2 := by ring
    have h2' : (z1 ^ 2) ^ 2 = (z2 ^ 2) ^ 2 := by rw [← h1, ← h2]; exact h
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp h2' with hh | hh
    · exact hh
    · have hz1nn : (0 : ℤ) ≤ z1 ^ 2 := by positivity
      have hz2nn : (0 : ℤ) ≤ z2 ^ 2 := by positivity
      have h3 : z1 ^ 2 = 0 := by nlinarith
      have h4 : z2 ^ 2 = 0 := by nlinarith
      rw [h3, h4]
  have he : z2 ^ 4 - z1 ^ 4 ≠ 0 := sub_ne_zero.mpr (Ne.symm hz4)
  rw [Mset_eq_sub]
  have hbound := _root_.Commons.NumberTheory.Diophantine.card_sq_sub_sq_le_divisors (Ybox x) (z2 ^ 4 - z1 ^ 4) he
  have hNpos : 1 ≤ (z2 ^ 4 - z1 ^ 4).natAbs := by
    have := Int.natAbs_pos.mpr he; omega
  have hNx : (z2 ^ 4 - z1 ^ 4).natAbs ≤ x := sub_pow_four_natAbs_le x hz1 hz2
  have hdiv := hC0 (z2 ^ 4 - z1 ^ 4).natAbs hNpos
  have hpowx : ((((z2 ^ 4 - z1 ^ 4).natAbs : ℕ) : ℝ)) ^ eps ≤ (x : ℝ) ^ eps :=
    Real.rpow_le_rpow (by positivity) (by exact_mod_cast hNx) (le_of_lt heps)
  calc ((((Ybox x) ×ˢ (Ybox x)).filter
        (fun pq : ℤ × ℤ => pq.1 ^ 2 - pq.2 ^ 2 = z2 ^ 4 - z1 ^ 4)).card : ℝ)
      ≤ (2 * ((z2 ^ 4 - z1 ^ 4).natAbs).divisors.card : ℝ) := by exact_mod_cast hbound
    _ = 2 * ((((z2 ^ 4 - z1 ^ 4).natAbs).divisors.card : ℕ) : ℝ) := by push_cast; ring
    _ ≤ 2 * (C0 * ((((z2 ^ 4 - z1 ^ 4).natAbs : ℕ) : ℝ)) ^ eps) := by
        have h := mul_le_mul_of_nonneg_left hdiv (by norm_num : (0 : ℝ) ≤ 2)
        linarith
    _ ≤ 2 * (C0 * (x : ℝ) ^ eps) := by
        have : C0 * ((((z2 ^ 4 - z1 ^ 4).natAbs : ℕ) : ℝ)) ^ eps ≤ C0 * (x : ℝ) ^ eps :=
          mul_le_mul_of_nonneg_left hpowx (le_of_lt hC0pos)
        linarith
    _ = 2 * C0 * (x : ℝ) ^ eps := by ring

/-- Diagonal cardinality of `Zbox × Zbox`. -/
private lemma Zdiag_card_le (x : ℕ) :
    (((Zbox x) ×ˢ (Zbox x)).filter (fun z : ℤ × ℤ => z.1 ^ 2 = z.2 ^ 2)).card
      ≤ 2 * (Zbox x).card := by
  set Z := Zbox x with hZ
  have hsub : (((Z ×ˢ Z).filter (fun z : ℤ × ℤ => z.1 ^ 2 = z.2 ^ 2))) ⊆
      ((Z ×ˢ Z).filter (fun z : ℤ × ℤ => z.2 = z.1)) ∪
      ((Z ×ˢ Z).filter (fun z : ℤ × ℤ => z.2 = -z.1)) := by
    intro z hz
    rw [Finset.mem_filter] at hz
    obtain ⟨hmem, hcond⟩ := hz
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hcond with h | h
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hmem, h.symm⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hmem, by linarith⟩)
  have hcard1 : (((Z ×ˢ Z).filter (fun z : ℤ × ℤ => z.2 = z.1))).card ≤ Z.card := by
    apply Finset.card_le_card_of_injOn (fun z : ℤ × ℤ => z.1)
    · intro z hz
      rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at hz
      exact hz.1.1
    · intro z hz w hw heq
      rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at hz hw
      simp only at heq
      exact Prod.ext heq (by rw [hz.2, hw.2, heq])
  have hcard2 : (((Z ×ˢ Z).filter (fun z : ℤ × ℤ => z.2 = -z.1))).card ≤ Z.card := by
    apply Finset.card_le_card_of_injOn (fun z : ℤ × ℤ => z.1)
    · intro z hz
      rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at hz
      exact hz.1.1
    · intro z hz w hw heq
      rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_product] at hz hw
      simp only at heq
      exact Prod.ext heq (by rw [hz.2, hw.2, heq])
  calc (((Z ×ˢ Z).filter (fun z : ℤ × ℤ => z.1 ^ 2 = z.2 ^ 2))).card
      ≤ (((Z ×ˢ Z).filter (fun z : ℤ × ℤ => z.2 = z.1)) ∪
          ((Z ×ˢ Z).filter (fun z : ℤ × ℤ => z.2 = -z.1))).card := Finset.card_le_card hsub
    _ ≤ (((Z ×ˢ Z).filter (fun z : ℤ × ℤ => z.2 = z.1))).card +
          (((Z ×ˢ Z).filter (fun z : ℤ × ℤ => z.2 = -z.1))).card := Finset.card_union_le _ _
    _ ≤ Z.card + Z.card := add_le_add hcard1 hcard2
    _ = 2 * (Zbox x).card := by rw [hZ]; ring

/-- **Main bound.** -/
theorem sum_sq_an_le (eps : ℝ) (heps : 0 < eps) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℕ, 1 ≤ x →
      (∑ n ∈ Finset.range (x + 1),
          (({p : ℤ × ℤ | p.1 ^ 2 + p.2 ^ 4 = (n : ℤ)}).ncard : ℝ) ^ 2)
        ≤ C * (x : ℝ) ^ (3 / 4 : ℝ) * (x : ℝ) ^ eps := by
  classical
  obtain ⟨C0, hC0pos, hC0⟩ := ArithmeticFunction.card_divisors_le_rpow eps heps
  refine ⟨36 + 18 * C0, by positivity, ?_⟩
  intro x hx
  have hxR : (0 : ℝ) < (x : ℝ) := by exact_mod_cast (lt_of_lt_of_le zero_lt_one hx)
  -- Step 1: rewrite the target sum using the box fibre counts
  have hT1 : (∑ n ∈ Finset.range (x + 1),
        (({p : ℤ × ℤ | p.1 ^ 2 + p.2 ^ 4 = (n : ℤ)}).ncard : ℝ) ^ 2)
      = ∑ n ∈ Finset.range (x + 1), ((bfc x (n : ℤ) : ℕ) : ℝ) ^ 2 := by
    apply Finset.sum_congr rfl
    intro n hn
    rw [Finset.mem_range] at hn
    rw [ncard_fiber_eq x n (Nat.lt_succ_iff.mp hn)]
  -- Step 2: pullback identity
  set Wset : Finset ((ℤ × ℤ) × (ℤ × ℤ)) :=
    ((Bbox x) ×ˢ (Bbox x)).filter (fun pq => gfun pq.1 = gfun pq.2) with hWset
  have ht : ∀ a ∈ Bbox x, gfun a ∈ Finset.Icc (0 : ℤ) (2 * (x : ℤ)) := by
    intro a ha
    rw [Finset.mem_Icc]
    exact ⟨by simp only [gfun]; positivity, gfun_le_two_mul x ha⟩
  have hpull := _root_.Commons.Data.Finset.card_pullback_eq_sum_sq gfun (Bbox x)
    (Finset.Icc (0 : ℤ) (2 * (x : ℤ))) ht
  have hpullW : Wset.card = ∑ n ∈ Finset.Icc (0 : ℤ) (2 * (x : ℤ)), bfc x n ^ 2 := by
    rw [hWset]; exact hpull
  have hT2 : (∑ n ∈ Finset.range (x + 1), ((bfc x (n : ℤ) : ℕ) : ℝ) ^ 2)
      ≤ (Wset.card : ℝ) := by
    have hinj : Set.InjOn (fun m : ℕ => (m : ℤ)) ↑(Finset.range (x + 1)) := by
      intro a _ b _ hab
      change (a : ℤ) = (b : ℤ) at hab
      exact_mod_cast hab
    have hsumimg : (∑ n ∈ (Finset.range (x + 1)).image (fun m : ℕ => (m : ℤ)),
          ((bfc x n : ℕ) : ℝ) ^ 2)
        = ∑ m ∈ Finset.range (x + 1), ((bfc x (m : ℤ) : ℕ) : ℝ) ^ 2 :=
      Finset.sum_image hinj
    rw [← hsumimg]
    have hsub : (Finset.range (x + 1)).image (fun m : ℕ => (m : ℤ)) ⊆
        Finset.Icc (0 : ℤ) (2 * (x : ℤ)) := by
      intro n hn
      rw [Finset.mem_image] at hn
      obtain ⟨m, hm, rfl⟩ := hn
      rw [Finset.mem_range] at hm
      rw [Finset.mem_Icc]
      refine ⟨by positivity, ?_⟩
      have : m ≤ x := by omega
      have : (m : ℤ) ≤ (x : ℤ) := by exact_mod_cast this
      linarith
    calc ∑ n ∈ (Finset.range (x + 1)).image (fun m : ℕ => (m : ℤ)), ((bfc x n : ℕ) : ℝ) ^ 2
        ≤ ∑ n ∈ Finset.Icc (0 : ℤ) (2 * (x : ℤ)), ((bfc x n : ℕ) : ℝ) ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg hsub (by intro n _ _; positivity)
      _ = (Wset.card : ℝ) := by rw [hpullW]; push_cast; rfl
  have hTW : (∑ n ∈ Finset.range (x + 1),
        (({p : ℤ × ℤ | p.1 ^ 2 + p.2 ^ 4 = (n : ℤ)}).ncard : ℝ) ^ 2) ≤ (Wset.card : ℝ) :=
    hT1.trans_le hT2
  -- Step 3: decompose Wset over the second coordinates
  have hmap : Set.MapsTo (fun pq : (ℤ × ℤ) × (ℤ × ℤ) => (pq.1.2, pq.2.2)) ↑Wset
      ↑((Zbox x) ×ˢ (Zbox x)) := by
    intro pq hpq
    rw [Finset.mem_coe, hWset, Finset.mem_filter, Finset.mem_product] at hpq
    obtain ⟨⟨hp, hq⟩, _⟩ := hpq
    have hp2 : pq.1.2 ∈ Zbox x := by
      have := hp; rw [Bbox, Finset.mem_product] at this; exact this.2
    have hq2 : pq.2.2 ∈ Zbox x := by
      have := hq; rw [Bbox, Finset.mem_product] at this; exact this.2
    rw [Finset.mem_coe, Finset.mem_product]
    exact ⟨hp2, hq2⟩
  have hWsum := Finset.card_eq_sum_card_fiberwise hmap
  have hMle : ∀ z ∈ (Zbox x) ×ˢ (Zbox x),
      (Wset.filter (fun pq : (ℤ × ℤ) × (ℤ × ℤ) => (pq.1.2, pq.2.2) = z)).card
        ≤ (Mset x z.1 z.2).card := by
    intro z hz
    obtain ⟨z1, z2⟩ := z
    apply Finset.card_le_card_of_injOn (fun pq : (ℤ × ℤ) × (ℤ × ℤ) => (pq.1.1, pq.2.1))
    · intro pq hpq
      rw [Finset.mem_coe, Finset.mem_filter] at hpq
      obtain ⟨hpqW, hpqz⟩ := hpq
      rw [Finset.mem_coe, Mset, Finset.mem_filter]
      rw [hWset, Finset.mem_filter, Finset.mem_product] at hpqW
      obtain ⟨⟨hp, hq⟩, hgeq⟩ := hpqW
      have hp1 : pq.1.1 ∈ Ybox x := by
        have := hp; rw [Bbox, Finset.mem_product] at this; exact this.1
      have hq1 : pq.2.1 ∈ Ybox x := by
        have := hq; rw [Bbox, Finset.mem_product] at this; exact this.1
      have h1 : pq.1.2 = z1 := by simpa using congrArg Prod.fst hpqz
      have h2 : pq.2.2 = z2 := by simpa using congrArg Prod.snd hpqz
      refine ⟨Finset.mem_product.mpr ⟨hp1, hq1⟩, ?_⟩
      have hh := hgeq
      simp only [gfun] at hh
      rw [h1, h2] at hh
      exact hh
    · intro pq hpq q hq heq
      rw [Finset.mem_coe, Finset.mem_filter] at hpq hq
      obtain ⟨_, hpqz⟩ := hpq
      obtain ⟨_, hqz⟩ := hq
      have e1 : pq.1.2 = z1 := by simpa using congrArg Prod.fst hpqz
      have e1' : q.1.2 = z1 := by simpa using congrArg Prod.fst hqz
      have e2 : pq.2.2 = z2 := by simpa using congrArg Prod.snd hpqz
      have e2' : q.2.2 = z2 := by simpa using congrArg Prod.snd hqz
      have f1 : pq.1.1 = q.1.1 := by simpa using congrArg Prod.fst heq
      have f2 : pq.2.1 = q.2.1 := by simpa using congrArg Prod.snd heq
      exact Prod.ext (Prod.ext f1 (e1.trans e1'.symm)) (Prod.ext f2 (e2.trans e2'.symm))
  have hWle1 : (Wset.card : ℝ)
      ≤ ∑ z ∈ (Zbox x) ×ˢ (Zbox x), ((Mset x z.1 z.2).card : ℝ) := by
    rw [hWsum]
    push_cast
    apply Finset.sum_le_sum
    intro z hz
    exact_mod_cast hMle z hz
  -- Step 4: split the sum into diagonal and off-diagonal parts
  set ZZ : Finset (ℤ × ℤ) := (Zbox x) ×ˢ (Zbox x) with hZZ
  have hdiag : ∑ z ∈ ZZ.filter (fun z : ℤ × ℤ => z.1 ^ 2 = z.2 ^ 2),
        ((Mset x z.1 z.2).card : ℝ)
      ≤ ((ZZ.filter (fun z : ℤ × ℤ => z.1 ^ 2 = z.2 ^ 2)).card : ℝ)
          * (2 * ((Ybox x).card : ℝ)) := by
    calc ∑ z ∈ ZZ.filter (fun z : ℤ × ℤ => z.1 ^ 2 = z.2 ^ 2), ((Mset x z.1 z.2).card : ℝ)
        ≤ ∑ z ∈ ZZ.filter (fun z : ℤ × ℤ => z.1 ^ 2 = z.2 ^ 2),
            (2 * ((Ybox x).card : ℝ)) := by
          apply Finset.sum_le_sum
          intro z hz
          rw [Finset.mem_filter] at hz
          exact_mod_cast Mset_diag_le x hz.2
      _ = ((ZZ.filter (fun z : ℤ × ℤ => z.1 ^ 2 = z.2 ^ 2)).card : ℝ)
            * (2 * ((Ybox x).card : ℝ)) := by rw [Finset.sum_const, nsmul_eq_mul]
  have hoff : ∑ z ∈ ZZ.filter (fun z : ℤ × ℤ => ¬ z.1 ^ 2 = z.2 ^ 2),
        ((Mset x z.1 z.2).card : ℝ)
      ≤ (ZZ.card : ℝ) * (2 * C0 * (x : ℝ) ^ eps) := by
    calc ∑ z ∈ ZZ.filter (fun z : ℤ × ℤ => ¬ z.1 ^ 2 = z.2 ^ 2), ((Mset x z.1 z.2).card : ℝ)
        ≤ ∑ z ∈ ZZ.filter (fun z : ℤ × ℤ => ¬ z.1 ^ 2 = z.2 ^ 2),
            (2 * C0 * (x : ℝ) ^ eps) := by
          apply Finset.sum_le_sum
          intro z hz
          rw [Finset.mem_filter] at hz
          have hz1 : z.1 ∈ Zbox x := by
            have := hz.1; rw [hZZ, Finset.mem_product] at this; exact this.1
          have hz2 : z.2 ∈ Zbox x := by
            have := hz.1; rw [hZZ, Finset.mem_product] at this; exact this.2
          exact Mset_offdiag_le eps heps C0 hC0pos hC0 x hx hz1 hz2 hz.2
      _ = ((ZZ.filter (fun z : ℤ × ℤ => ¬ z.1 ^ 2 = z.2 ^ 2)).card : ℝ)
            * (2 * C0 * (x : ℝ) ^ eps) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (ZZ.card : ℝ) * (2 * C0 * (x : ℝ) ^ eps) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          exact_mod_cast Finset.card_filter_le ZZ (fun z : ℤ × ℤ => ¬ z.1 ^ (2:ℕ) = z.2 ^ (2:ℕ))
  have hWle2 : (Wset.card : ℝ)
      ≤ ((ZZ.filter (fun z : ℤ × ℤ => z.1 ^ 2 = z.2 ^ 2)).card : ℝ)
          * (2 * ((Ybox x).card : ℝ)) + (ZZ.card : ℝ) * (2 * C0 * (x : ℝ) ^ eps) := by
    calc (Wset.card : ℝ) ≤ ∑ z ∈ ZZ, ((Mset x z.1 z.2).card : ℝ) := hWle1
      _ = ∑ z ∈ ZZ.filter (fun z : ℤ × ℤ => z.1 ^ 2 = z.2 ^ 2), ((Mset x z.1 z.2).card : ℝ)
            + ∑ z ∈ ZZ.filter (fun z : ℤ × ℤ => ¬ z.1 ^ 2 = z.2 ^ 2),
                ((Mset x z.1 z.2).card : ℝ) :=
          (Finset.sum_filter_add_sum_filter_not ZZ (fun z : ℤ × ℤ => z.1 ^ 2 = z.2 ^ 2)
            (fun z => ((Mset x z.1 z.2).card : ℝ))).symm
      _ ≤ ((ZZ.filter (fun z : ℤ × ℤ => z.1 ^ 2 = z.2 ^ 2)).card : ℝ)
            * (2 * ((Ybox x).card : ℝ)) + (ZZ.card : ℝ) * (2 * C0 * (x : ℝ) ^ eps) :=
          add_le_add hdiag hoff
  -- Step 5: numeric bounds
  have hWnum : (Wset.card : ℝ)
      ≤ 36 * (x : ℝ) ^ (3 / 4 : ℝ) + 18 * C0 * ((x : ℝ) ^ (1 / 2 : ℝ) * (x : ℝ) ^ eps) := by
    set a : ℝ := (x : ℝ) ^ (1 / 4 : ℝ) with ha
    set b : ℝ := (x : ℝ) ^ (1 / 2 : ℝ) with hb
    set c : ℝ := (x : ℝ) ^ eps with hc
    have ha0 : 0 ≤ a := by rw [ha]; positivity
    have hb0 : 0 ≤ b := by rw [hb]; positivity
    have hc0 : 0 ≤ c := by rw [hc]; positivity
    have hYc : ((Ybox x).card : ℝ) ≤ 3 * b := by rw [hb]; exact Ybox_card_le x hx
    have hZc : ((Zbox x).card : ℝ) ≤ 3 * a := by rw [ha]; exact Zbox_card_le x hx
    have hY0 : (0 : ℝ) ≤ ((Ybox x).card : ℝ) := by positivity
    have hZ0 : (0 : ℝ) ≤ ((Zbox x).card : ℝ) := by positivity
    have hZD : ((ZZ.filter (fun z : ℤ × ℤ => z.1 ^ 2 = z.2 ^ 2)).card : ℝ)
        ≤ 2 * ((Zbox x).card : ℝ) := by
      rw [hZZ]; exact_mod_cast Zdiag_card_le x
    have hZZc : (ZZ.card : ℝ) = ((Zbox x).card : ℝ) * ((Zbox x).card : ℝ) := by
      rw [hZZ, Finset.card_product]; push_cast; ring
    have ha2b : a ^ 2 = b := by
      rw [ha, hb, ← Real.rpow_natCast, ← Real.rpow_mul (le_of_lt hxR)]
      rw [show (1 / 4 : ℝ) * ((2 : ℕ) : ℝ) = 1 / 2 by norm_num]
    have hab : a * b = (x : ℝ) ^ (3 / 4 : ℝ) := by
      rw [ha, hb, ← Real.rpow_add hxR]
      norm_num
    have hstep1 : ((ZZ.filter (fun z : ℤ × ℤ => z.1 ^ 2 = z.2 ^ 2)).card : ℝ)
          * (2 * ((Ybox x).card : ℝ)) ≤ (2 * (3 * a)) * (2 * (3 * b)) := by
      apply mul_le_mul
      · linarith [hZD, hZc]
      · linarith [hYc]
      · positivity
      · linarith [hZD, hZc]
    have hstep2 : (ZZ.card : ℝ) * (2 * C0 * c) ≤ ((3 * a) * (3 * a)) * (2 * C0 * c) := by
      rw [hZZc]
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul hZc hZc hZ0 (le_trans hZ0 hZc)
    calc (Wset.card : ℝ)
        ≤ ((ZZ.filter (fun z : ℤ × ℤ => z.1 ^ 2 = z.2 ^ 2)).card : ℝ)
            * (2 * ((Ybox x).card : ℝ)) + (ZZ.card : ℝ) * (2 * C0 * (x : ℝ) ^ eps) := hWle2
      _ ≤ (2 * (3 * a)) * (2 * (3 * b)) + ((3 * a) * (3 * a)) * (2 * C0 * c) := by
          have hh : (ZZ.card : ℝ) * (2 * C0 * c)
              = (ZZ.card : ℝ) * (2 * C0 * (x : ℝ) ^ eps) := by rw [hc]
          rw [← hc]
          exact add_le_add hstep1 hstep2
      _ = 36 * (a * b) + 18 * C0 * (b * c) := by rw [← ha2b]; ring
      _ = 36 * (x : ℝ) ^ (3 / 4 : ℝ)
            + 18 * C0 * ((x : ℝ) ^ (1 / 2 : ℝ) * (x : ℝ) ^ eps) := by rw [hab, hb, hc]
  -- Step 6: final assembly
  have hx1 : (1 : ℝ) ≤ (x : ℝ) := by exact_mod_cast hx
  have h34 : (0 : ℝ) ≤ (x : ℝ) ^ (3 / 4 : ℝ) := Real.rpow_nonneg (le_of_lt hxR) _
  have h12n : (0 : ℝ) ≤ (x : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_nonneg (le_of_lt hxR) _
  have hcn : (0 : ℝ) ≤ (x : ℝ) ^ eps := Real.rpow_nonneg (le_of_lt hxR) _
  have hc1 : (1 : ℝ) ≤ (x : ℝ) ^ eps := Real.one_le_rpow hx1 (le_of_lt heps)
  have h34le : (x : ℝ) ^ (3 / 4 : ℝ) ≤ (x : ℝ) ^ (3 / 4 : ℝ) * (x : ℝ) ^ eps :=
    le_mul_of_one_le_right h34 hc1
  have h12le : (x : ℝ) ^ (1 / 2 : ℝ) ≤ (x : ℝ) ^ (3 / 4 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num)
  calc (∑ n ∈ Finset.range (x + 1),
        (({p : ℤ × ℤ | p.1 ^ 2 + p.2 ^ 4 = (n : ℤ)}).ncard : ℝ) ^ 2)
      ≤ (Wset.card : ℝ) := hTW
    _ ≤ 36 * (x : ℝ) ^ (3 / 4 : ℝ) + 18 * C0 * ((x : ℝ) ^ (1 / 2 : ℝ) * (x : ℝ) ^ eps) := hWnum
    _ ≤ 36 * ((x : ℝ) ^ (3 / 4 : ℝ) * (x : ℝ) ^ eps)
          + 18 * C0 * ((x : ℝ) ^ (3 / 4 : ℝ) * (x : ℝ) ^ eps) := by
        apply add_le_add
        · apply mul_le_mul_of_nonneg_left h34le (by norm_num)
        · apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact mul_le_mul_of_nonneg_right h12le hcn
    _ = (36 + 18 * C0) * (x : ℝ) ^ (3 / 4 : ℝ) * (x : ℝ) ^ eps := by ring


end Commons.NumberTheory.FriedlanderIwaniec
