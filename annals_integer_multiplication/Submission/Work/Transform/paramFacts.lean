import Mathlib
import Submission.Work.Transform.Defs
import Submission.Work.ConvR.basic

namespace Work.Transform

open HvdH

/-- `x ≤ lmax ts` for any member `x` of `ts`. -/
lemma le_lmax {ts : List ℕ} {x : ℕ} (hx : x ∈ ts) : x ≤ lmax ts :=
  List.le_max_of_le' 0 hx le_rfl

/-- `lmax ts` is at most any upper bound of the entries of `ts`. -/
lemma lmax_le_of_forall_le {ts : List ℕ} {a : ℕ} (h : ∀ x ∈ ts, x ≤ a) : lmax ts ≤ a := by
  unfold lmax
  induction ts with
  | nil => exact Nat.zero_le a
  | cons y t ih =>
    simp only [List.foldr]
    exact max_le (h y (by simp)) (ih fun x hx => h x (by simp [hx]))

/-- The largest entry of a nonempty ascending list is its last entry. -/
lemma lmax_eq_getLast {ts : List ℕ} (hne : ts ≠ []) (hs : ts.Pairwise (· ≤ ·)) :
    lmax ts = ts.getLast hne := by
  refine le_antisymm (lmax_le_of_forall_le fun x hx => hs.rel_getLast hx) ?_
  exact le_lmax (List.getLast_mem hne)

/-- The largest entry of a nonempty ascending list is one of its entries. -/
lemma lmax_mem {ts : List ℕ} (hne : ts ≠ []) (hs : ts.Pairwise (· ≤ ·)) : lmax ts ∈ ts := by
  rw [lmax_eq_getLast hne hs]
  exact List.getLast_mem hne

/-- A power of two is at least `2`. -/
lemma two_le_of_isPow2 {t : ℕ} (h : IsPow2 t) : 2 ≤ t := by
  obtain ⟨k, hk, rfl⟩ := h
  calc 2 = 2 ^ 1 := rfl
    _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk

/-- Powers of two divide each other according to their size: `t ∣ 2 * r` when `t ≤ r`. -/
lemma isPow2_dvd_two_mul {t r : ℕ} (ht : IsPow2 t) (hr : IsPow2 r) (h : t ≤ r) : t ∣ 2 * r := by
  obtain ⟨i, -, rfl⟩ := ht
  obtain ⟨j, -, rfl⟩ := hr
  rw [← pow_succ']
  refine pow_dvd_pow 2 ?_
  have h' : i ≤ j := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 h
  omega

/-- A nonempty list all of whose entries are at least `2` has product at least `2`. -/
lemma two_le_prod {l : List ℕ} (h : ∀ x ∈ l, 2 ≤ x) (hne : l ≠ []) : 2 ≤ l.prod := by
  cases l with
  | nil => exact absurd rfl hne
  | cons x t =>
    cases t with
    | nil => simpa using h x (by simp)
    | cons y t' =>
      have hx : 2 ≤ x := h x (by simp)
      have hy : 1 ≤ (y :: t').prod :=
        List.one_le_prod fun a ha => le_trans (by norm_num : 1 ≤ 2) (h a (by simp [ha]))
      calc 2 = 2 * 1 := by norm_num
        _ ≤ x * (y :: t').prod := Nat.mul_le_mul hx hy
        _ = (x :: y :: t').prod := (List.prod_cons (a := x) (l := y :: t')).symm

/-- Parameter arithmetic of Theorem 3.1 (`PowTwoParams p ts`): the list splits as
`ts = ts.dropLast ++ [lmax ts]`, the products multiply, `lmax ts` is the largest entry, the last
dimension `r = lmax ts` satisfies `2 ≤ r < 2^(p-1)` (because there are `D ≥ 2` entries, all `≥ 2`,
and `ts.prod < 2^p`), and `SynParams p r ts.dropLast` holds (i.e. `ts.dropLast` has length `D-1`,
all its entries are powers of two dividing `2r`). -/
theorem paramFacts (p : ℕ) (ts : List ℕ) (hdim : ts.length = HvdH.D)
    (hp2 : ∀ t ∈ ts, HvdH.IsPow2 t) (hpair : ts.Pairwise (· ≤ ·))
    (hT : ts.prod < 2 ^ p) (hp : 100 ≤ p) :
    ts = ts.dropLast ++ [HvdH.lmax ts] ∧
    ts.prod = ts.dropLast.prod * HvdH.lmax ts ∧
    2 ≤ ts.dropLast.prod ∧
    0 < HvdH.lmax ts ∧
    2 ≤ HvdH.lmax ts ∧
    HvdH.lmax ts < 2 ^ (p - 1) ∧
    HvdH.SynParams p (HvdH.lmax ts) ts.dropLast := by
  have hD : HvdH.D = 1729 := rfl
  have hne : ts ≠ [] := by
    intro h
    rw [h, hD] at hdim
    simp at hdim
  have hlmax : lmax ts = ts.getLast hne := lmax_eq_getLast hne hpair
  have hlmax_mem : lmax ts ∈ ts := by
    rw [hlmax]; exact List.getLast_mem hne
  have hsplit : ts = ts.dropLast ++ [lmax ts] := by
    rw [hlmax]; exact (List.dropLast_append_getLast hne).symm
  have hprod : ts.prod = ts.dropLast.prod * lmax ts := by
    conv_lhs => rw [hsplit]
    rw [List.prod_append, List.prod_singleton]
  have hdl_len : ts.dropLast.length = 1728 := by
    rw [List.length_dropLast, hdim, hD]
  have hdl_ne : ts.dropLast ≠ [] := by
    intro h
    rw [h] at hdl_len
    simp at hdl_len
  have h2prod : 2 ≤ ts.dropLast.prod :=
    two_le_prod (fun x hx => two_le_of_isPow2 (hp2 x (List.dropLast_subset ts hx))) hdl_ne
  have hlmax_ge2 : 2 ≤ lmax ts := two_le_of_isPow2 (hp2 _ hlmax_mem)
  have hlmax_pos : 0 < lmax ts := lt_of_lt_of_le (by norm_num) hlmax_ge2
  have hmul : 2 * lmax ts ≤ ts.prod := by
    rw [hprod]; exact Nat.mul_le_mul_right _ h2prod
  have hpow : 2 ^ p = 2 * 2 ^ (p - 1) := by
    rw [← pow_succ']; congr 1; omega
  have hlmax_lt : lmax ts < 2 ^ (p - 1) := by
    apply Nat.lt_of_mul_lt_mul_left
    rw [← hpow]
    exact lt_of_le_of_lt hmul hT
  have hsyn : SynParams p (lmax ts) ts.dropLast := by
    refine ⟨?_, hp2 _ hlmax_mem, ?_, ?_, hp⟩
    · rw [List.length_dropLast, hdim, hD]
    · intro t ht
      have ht_ts : t ∈ ts := List.dropLast_subset ts ht
      exact ⟨hp2 t ht_ts, isPow2_dvd_two_mul (hp2 t ht_ts) (hp2 _ hlmax_mem) (le_lmax ht_ts)⟩
    · rw [← hprod]; exact hT
  exact ⟨hsplit, hprod, h2prod, hlmax_pos, hlmax_ge2, hlmax_lt, hsyn⟩

end Work.Transform
