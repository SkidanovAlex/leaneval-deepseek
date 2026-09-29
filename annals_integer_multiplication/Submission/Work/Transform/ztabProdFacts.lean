import Mathlib
import Submission.Work.Transform.Defs
import Submission.Work.Transform.paramFacts

namespace Work.Transform

open HvdH

/-- `max a b` is a member of `a :: l` whenever `b` is a member of `l`. -/
lemma max_cons_mem {a b : ℕ} {l : List ℕ} (hb : b ∈ l) : max a b ∈ a :: l := by
  rcases le_total b a with h | h
  · rw [max_eq_left h]; simp
  · rw [max_eq_right h]; exact List.mem_cons_of_mem a hb

/-- The `foldr max 0` of a nonempty list is one of its entries. -/
lemma foldr_max_mem {ts : List ℕ} (hne : ts ≠ []) : List.foldr max 0 ts ∈ ts := by
  induction ts with
  | nil => exact absurd rfl hne
  | cons t ts ih =>
    cases ts with
    | nil => simp
    | cons u us =>
      rw [List.foldr_cons]
      exact max_cons_mem (ih (by simp))

/-- A positive `HvdH.lmax ts` is attained: it is one of the entries of `ts`. -/
lemma lmax_pos_mem {ts : List ℕ} (h : 0 < HvdH.lmax ts) : HvdH.lmax ts ∈ ts := by
  unfold HvdH.lmax at *
  by_cases hne : ts = []
  · subst hne; simp at h
  · exact foldr_max_mem hne

/-- List/product/size arithmetic needed for the `ζ`-table word `Work.Transform.ztabWord`.

`HvdH.lmax ts = r` is the key hypothesis (`r` is the largest dimension); `ts.prod` is the length `T`
of the stretched table; `HvdH.intList ts` is the list of the `ts` encoded as a `Val` (`HvdH.vsz` its
encoding size).  The facts (all with `r > 0` where needed):

1. if `HvdH.lmax ts = r` with `r > 0` then `r` is one of the entries (so `ts ≠ []`);
2. `r ∈ ts` divides `ts.prod` (`r * (ts without one r) = ts.prod`);
3. all entries positive and `HvdH.lmax ts = r` give `r ≤ ts.prod`;
4. with `HvdH.lmax ts = r`, `r > 0` and positive entries: `ts.prod / r * r = ts.prod`
   (conjunct 4 is FALSE without `0 < r`: `ts = []`, `r = 0` gives `1/0*0 = 0 ≠ 1 = ts.prod`);
5. a list of positive entries has product `≥ 1`;
6. `HvdH.isz (T) ≤ T + 2` for `T : ℕ`;
7. `Int.fdiv (T : ℤ) (r : ℤ) = (T / r : ℕ)` for `r > 0`;
8. `n < 2^p` gives `HvdH.isz (n : ℤ) ≤ p + 2`;
9. every entry of `ts` is `≤ HvdH.lmax ts` (already in `Work.Transform.le_lmax`, restated here);
10. `HvdH.lmax ts = r` with `r > 0` gives `ts ≠ []`. -/
theorem ztabProdFacts :
    (∀ (ts : List ℕ) (r : ℕ), HvdH.lmax ts = r → 0 < r → r ∈ ts) ∧
    (∀ (ts : List ℕ) (r : ℕ), r ∈ ts → r ∣ ts.prod) ∧
    (∀ (ts : List ℕ) (r : ℕ), HvdH.lmax ts = r → (∀ t ∈ ts, 0 < t) → r ≤ ts.prod) ∧
    (∀ (ts : List ℕ) (r : ℕ), HvdH.lmax ts = r → 0 < r → (∀ t ∈ ts, 0 < t) →
      ts.prod / r * r = ts.prod) ∧
    (∀ (ts : List ℕ), (∀ t ∈ ts, 0 < t) → 1 ≤ ts.prod) ∧
    (∀ (T : ℕ), HvdH.isz ((T : ℕ) : ℤ) ≤ T + 2) ∧
    (∀ (T r : ℕ), 0 < r → Int.fdiv (T : ℤ) (r : ℤ) = ((T / r : ℕ) : ℤ)) ∧
    (∀ (n p : ℕ), n < 2 ^ p → HvdH.isz ((n : ℕ) : ℤ) ≤ p + 2) ∧
    (∀ (ts : List ℕ) (t : ℕ), t ∈ ts → t ≤ HvdH.lmax ts) ∧
    (∀ (ts : List ℕ) (r : ℕ), HvdH.lmax ts = r → 0 < r → ts ≠ []) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- 1. `lmax ts = r > 0` ⟹ `r ∈ ts`
    intro ts r hr hpos
    rw [← hr]
    exact lmax_pos_mem (by rw [hr]; exact hpos)
  · -- 2. `r ∈ ts` ⟹ `r ∣ ts.prod`
    intro ts r hr
    exact List.dvd_prod hr
  · -- 3. positive entries ⟹ `r ≤ ts.prod`
    intro ts r hr hpos
    by_cases hne : ts = []
    · rw [hne] at hr ⊢
      simp [HvdH.lmax] at hr ⊢
      omega
    · have hmem : r ∈ ts := by rw [← hr]; exact foldr_max_mem hne
      exact Nat.le_of_dvd (by have := List.one_le_prod hpos; omega) (List.dvd_prod hmem)
  · -- 4. divisibility of `ts.prod` by the largest entry
    intro ts r hr hpos1 hpos
    have hmem : r ∈ ts := by
      rw [← hr]
      exact lmax_pos_mem (by rw [hr]; exact hpos1)
    exact Nat.div_mul_cancel (List.dvd_prod hmem)
  · -- 5. product of positive entries is `≥ 1`
    intro ts hpos
    exact List.one_le_prod hpos
  · -- 6. `isz T ≤ T + 2`
    intro T
    unfold HvdH.isz
    simp only [Int.natAbs_natCast]
    have h : T.size ≤ T := Nat.size_le.2 (Nat.lt_two_pow_self)
    omega
  · -- 7. `Int.fdiv` of naturals
    intro T r hr
    exact Eq.symm (Int.ofNat_fdiv T r)
  · -- 8. `n < 2^p` ⟹ `isz n ≤ p + 2`
    intro n p hp
    unfold HvdH.isz
    simp only [Int.natAbs_natCast]
    have h := (Nat.size_le).2 hp
    omega
  · -- 9. every entry is at most the largest
    intro ts t ht
    exact le_lmax ht
  · -- 10. `lmax ts = r > 0` ⟹ `ts ≠ []`
    intro ts r hr hpos
    have hmem : r ∈ ts := by
      rw [← hr]
      exact lmax_pos_mem (by rw [hr]; exact hpos)
    exact List.ne_nil_of_mem hmem

end Work.Transform
