import Mathlib
import Submission.Work.WilC4.Defs
import Submission.Work.WilC4.valEq_iff_unitVal_div
import Submission.Work.WilC4.int_linDep_of_card_lt
import Submission.Work.WilC4.prod_zmono_zpow
import Submission.Work.WilC4.mem_prod_zpow
import Submission.Work.WilC4.prod_div_expand

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilC4
open WilkiesDesign WilkiesDesign.CG

/-! ### Arithmetic of `IsUnitVal` -/

private lemma isUnitVal_one' {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M] :
    IsUnitVal (1 : M) := by
  refine ⟨1, ?_, ?_⟩ <;> (rw [abs_one]; norm_num)

private lemma isUnitVal_mul' {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M]
    {x y : M} (hx : IsUnitVal x) (hy : IsUnitVal y) : IsUnitVal (x * y) := by
  obtain ⟨N, hN1, hN2⟩ := hx
  obtain ⟨K, hK1, hK2⟩ := hy
  have hcast : ((N * K + N + K : ℕ) : M) + 1 = ((N : M) + 1) * ((K : M) + 1) := by
    push_cast; ring
  refine ⟨N * K + N + K, ?_, ?_⟩
  · rw [abs_mul, hcast, mul_inv]
    exact mul_le_mul hN1 hK1 (by positivity) (abs_nonneg x)
  · rw [abs_mul, hcast]
    exact mul_le_mul hN2 hK2 (abs_nonneg y) (by positivity)

private lemma isUnitVal_inv' {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M]
    {x : M} (hx : IsUnitVal x) : IsUnitVal x⁻¹ := by
  obtain ⟨N, h1, h2⟩ := hx
  have hxpos : 0 < |x| := lt_of_lt_of_le (by positivity) h1
  refine ⟨N, ?_, ?_⟩
  · rw [abs_inv]
    exact (inv_le_inv₀ (by positivity) hxpos).mpr h2
  · rw [abs_inv]
    exact inv_le_of_inv_le₀ (by positivity) h1

private lemma isUnitVal_pow' {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M]
    {x : M} (hx : IsUnitVal x) : ∀ k : ℕ, IsUnitVal (x ^ k)
  | 0 => by simpa using isUnitVal_one'
  | k + 1 => by rw [pow_succ]; exact isUnitVal_mul' (isUnitVal_pow' hx k) hx

private lemma isUnitVal_zpow' {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M]
    {x : M} (hx : IsUnitVal x) (n : ℤ) : IsUnitVal (x ^ n) := by
  obtain ⟨k, hk | hk⟩ := Int.eq_nat_or_neg n
  · rw [hk, zpow_natCast]
    exact isUnitVal_pow' hx k
  · rw [hk, zpow_neg, zpow_natCast]
    exact isUnitVal_inv' (isUnitVal_pow' hx k)

private lemma isUnitVal_prod_zpow' {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M]
    {m : ℕ} {u : Fin m → M} {n : Fin m → ℤ} (h : ∀ j, IsUnitVal (u j)) :
    IsUnitVal (∏ j, u j ^ n j) := by
  have key : ∀ s : Finset (Fin m), IsUnitVal (∏ j ∈ s, u j ^ n j) := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using isUnitVal_one'
    | insert x s hx ih =>
        rw [Finset.prod_insert hx]
        exact isUnitVal_mul' (isUnitVal_zpow' (h x) (n x)) ih
  simpa using key Finset.univ

private lemma isUnitVal_ne_zero' {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M]
    {x : M} (h : IsUnitVal x) : x ≠ 0 := by
  obtain ⟨N, hN, -⟩ := h
  intro hx0
  rw [hx0, abs_zero] at hN
  have : (0 : M) < ((N : M) + 1)⁻¹ := by positivity
  linarith

private lemma valEq_refl' {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M]
    (x : M) : ValEq x x := by
  refine ⟨1, by norm_num, ?_, ?_⟩ <;> simp

/-! ### The main lemma -/

theorem valSpans_use {M : Type} [Field M] [LinearOrder M] [IsStrictOrderedRing M]
    {S V : Set M} {r m : ℕ} (b : Fin m → M) (hS : IsValBase S) (h : ValSpans S V r)
    (hV : ∀ j, ValOf V (b j)) (hind : ValIndep S b) : m ≤ r := by
  by_contra hcon
  have hlt : r < m := not_le.mp hcon
  obtain ⟨x, hx⟩ := h
  choose c hcV hc0 hceq using hV
  have hex : ∀ j, ∃ N : ℕ, ∃ q : Fin r → ℤ, ∃ d : M, d ∈ S ∧ d ≠ 0 ∧ N ≠ 0 ∧
      IsUnitVal (d * (c j) ^ N / zmono x q) := by
    intro j
    obtain ⟨N, hN, q, d, hdS, hd0, hu⟩ :=
      hx (c j) (hc0 j) ⟨c j, hcV j, hc0 j, valEq_refl' (c j)⟩
    exact ⟨N, q, d, hdS, hd0, hN, hu⟩
  choose N q d hdS hd0 hN hunit using hex
  have hz : ∀ j, zmono x (q j) ≠ 0 := by
    intro j h0
    have hz0 : d j * (c j) ^ (N j) / zmono x (q j) = 0 := by rw [h0, div_zero]
    exact isUnitVal_ne_zero' (hunit j) hz0
  have hsplit : ∀ i, x i ≠ 0 ∨ ∀ j, q j i = 0 := by
    intro i
    by_cases hxi : x i = 0
    · right
      intro j
      by_contra hq
      refine hz j ?_
      have hfac : x i ^ (q j i) = 0 := by rw [hxi]; exact zero_zpow (q j i) hq
      unfold zmono
      exact Finset.prod_eq_zero (Finset.mem_univ i) hfac
    · exact Or.inl hxi
  have hbc : ∀ j, IsUnitVal (b j / c j) := fun j =>
    (valEq_iff_unitVal_div (hc0 j)).mp (hceq j)
  have hkey : ∀ j, IsUnitVal (d j * (b j) ^ ((N j : ℤ)) / zmono x (q j)) := by
    intro j
    have huc : IsUnitVal (d j * (c j) ^ ((N j : ℤ)) / zmono x (q j)) := by
      simpa only [zpow_natCast] using hunit j
    have h1 : IsUnitVal
        ((b j / c j) ^ ((N j : ℤ)) * (d j * (c j) ^ ((N j : ℤ)) / zmono x (q j))) :=
      isUnitVal_mul' (isUnitVal_zpow' (hbc j) ((N j : ℤ))) huc
    have hc : (b j / c j) ^ ((N j : ℤ)) * (c j) ^ ((N j : ℤ)) = (b j) ^ ((N j : ℤ)) := by
      rw [← mul_zpow, div_mul_cancel₀ (b j) (hc0 j)]
    have heq : (b j / c j) ^ ((N j : ℤ)) * (d j * (c j) ^ ((N j : ℤ)) / zmono x (q j))
        = d j * (b j) ^ ((N j : ℤ)) / zmono x (q j) := by
      have h2 : (b j / c j) ^ ((N j : ℤ)) * (d j * (c j) ^ ((N j : ℤ)) / zmono x (q j))
          = d j * ((b j / c j) ^ ((N j : ℤ)) * (c j) ^ ((N j : ℤ))) / zmono x (q j) := by
        rw [div_eq_mul_inv, div_eq_mul_inv]
        ring
      rw [h2, hc]
    rwa [heq] at h1
  obtain ⟨a, ha0, haQ⟩ := int_linDep_of_card_lt hlt q
  have hU : IsUnitVal (∏ j, (d j * (b j) ^ ((N j : ℤ)) / zmono x (q j)) ^ (a j)) :=
    isUnitVal_prod_zpow' (u := fun j => d j * (b j) ^ ((N j : ℤ)) / zmono x (q j))
      (n := a) hkey
  have hxpart : (∏ j, (zmono x (q j)) ^ (a j)) = 1 := by
    rw [prod_zmono_zpow x q a hsplit]
    have hz0 : (fun i : Fin r => ∑ j, a j * q j i) = 0 := by
      funext i; exact haQ i
    rw [hz0]
    simp [zmono]
  rw [prod_div_expand d b (fun j => (N j : ℤ)) x q a] at hU
  rw [hxpart, inv_one, mul_one] at hU
  have hq0 : (fun j => (N j : ℤ) * a j) ≠ 0 := by
    intro hzero
    apply ha0
    funext j
    have hj : (N j : ℤ) * a j = 0 := by
      have := congrFun hzero j
      simpa using this
    exact (mul_eq_zero.mp hj).resolve_left (by exact_mod_cast hN j)
  have hmem := mem_prod_zpow hS d a hdS hd0
  exact hq0 (hind (fun j => (N j : ℤ) * a j) ⟨∏ j, d j ^ a j, hmem.1, hmem.2, hU⟩)

end Work.WilC4
