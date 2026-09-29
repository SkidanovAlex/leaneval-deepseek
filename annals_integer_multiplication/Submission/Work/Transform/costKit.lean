import Mathlib
import Submission.HvdH.Interfaces
import Submission.Work.ConvR.basic
import Submission.Work.Transform.SeqUtil
import Submission.Work.Transform.inDiscVecSizes

/-!
# Size bookkeeping for the cost bound of Theorem 3.1

Everything in the `Transform` pipeline is bounded in terms of `V := 100 * T * p ^ 2`, where
`T = ts.prod` is the transform length.  This file provides the elementary bounds:
`vsz` of the vectors/arrays/lists/int values occurring on the stack, and a generic bound for
`Σ vsz` over a prefix of a stack state.
-/

set_option autoImplicit false

namespace Work.Transform

open HvdH

/-- `2 ^ ts.length ≤ ts.prod` when every entry is at least `2`. -/
theorem pow_length_le_prod (ts : List ℕ) (h2 : ∀ t ∈ ts, 2 ≤ t) : 2 ^ ts.length ≤ ts.prod := by
  have h : (ts.map (fun _ => 2)).prod ≤ (ts.map id).prod :=
    List.prod_le_prod (fun i hi => by simpa using h2 i (by simpa using hi))
  simpa using h

/-- For an ascending list of `D` powers of two, `D ≤ log₂ (∏ tᵢ)`. -/
theorem D_le_log_two_prod (ts : List ℕ) (hlen : ts.length = HvdH.D) (h2 : ∀ t ∈ ts, 2 ≤ t) :
    HvdH.D ≤ Nat.log 2 ts.prod := by
  rw [← hlen]
  exact Nat.le_log_of_pow_le (by norm_num) (pow_length_le_prod ts h2)

/-- Sum of `vsz` over a prefix of a stack state `L ++ R`, when all entries of `L` are `≤ V`. -/
theorem sum_take_vsz_le {vs L R : List Val} {n V : ℕ} (hvs : vs = L ++ R) (hn : n ≤ L.length)
    (hL : ∀ v ∈ L, vsz v ≤ V) : ((vs.take n).map vsz).sum ≤ n * V := by
  subst hvs
  rw [List.take_append_of_le_length hn]
  calc ((L.take n).map vsz).sum
      ≤ ((L.take n).map (fun _ => V)).sum :=
        List.sum_le_sum (fun v hv => hL v (List.take_subset n L hv))
    _ = (L.take n).length * V := by
        rw [List.map_const']
        induction L.take n with
        | nil => simp
        | cons x xs ih =>
            rw [List.length_cons, List.replicate_succ, List.sum_cons, ih, Nat.succ_mul]
            omega
    _ ≤ n * V := Nat.mul_le_mul_right V (by rw [List.length_take]; exact Nat.min_le_left n L.length)

/-- `vsz` of a length-`T` disc vector is at most `100 * T * p ^ 2`. -/
theorem cvecVal_vsz_le_100 {p T : ℕ} {u : List (ℤ × ℤ)} (h : HvdH.InDiscVec p T u)
    (hp : 100 ≤ p) (hT : 1 ≤ T) : vsz (cvecVal u) ≤ 100 * T * p ^ 2 := by
  have h1 := (inDiscVecSizes h hp).2
  nlinarith [h1, hT, hp, Nat.zero_le (T * p ^ 2)]

/-- `vsz` of an `M × r` disc array is at most `100 * (M*r) * p ^ 2`. -/
theorem rarrVal_vsz_le_100 {p M r : ℕ} {A : List (List (ℤ × ℤ))} (h : HvdH.InDiscArr p M r A)
    (hp : 100 ≤ p) (hMr : 1 ≤ M * r) : vsz (rarrVal A) ≤ 100 * (M * r) * p ^ 2 := by
  have hr0 : 0 < r := by
    rcases Nat.eq_zero_or_pos r with h0 | h0
    · rw [h0, mul_zero] at hMr; omega
    · exact h0
  have h1 : M ≤ M * r := Nat.le_mul_of_pos_right (m := r) M hr0
  have h2 : vsz (rarrVal A) ≤ Work.ConvR.arrSz p M r := Work.ConvR.vsz_rarrVal_le h
  rw [Work.ConvR.arrSz, Work.ConvR.cvecSz, Work.ConvR.cfxSz] at h2
  nlinarith [h2, h1, hp, Nat.zero_le M, Nat.zero_le r]

/-- `vsz` of an encoded list of naturals below `2 ^ p`, of length at most `T`. -/
theorem intList_vsz_le_100 {p T : ℕ} {ts : List ℕ} (hlen : ts.length ≤ T)
    (hsz : ∀ t ∈ ts, t < 2 ^ p) (hp : 100 ≤ p) (hT : 1 ≤ T) :
    vsz (intList ts) ≤ 100 * T * p ^ 2 := by
  have h1 : vsz (intList ts) ≤ (ts.map (fun t => t.size + 3)).sum + ts.length + 2 :=
    Work.ConvR.vsz_intList_le ts
  have h2 : ∀ t ∈ ts, t.size + 3 ≤ p + 3 := by
    intro t ht
    have := (Nat.size_le).mpr (hsz t ht)
    omega
  have h3 : (ts.map (fun t => t.size + 3)).sum ≤ ts.length * (p + 3) := by
    calc (ts.map (fun t => t.size + 3)).sum
        ≤ (ts.map (fun _ => p + 3)).sum := List.sum_le_sum h2
      _ = ts.length * (p + 3) := Work.ConvR.sum_map_const ts (p + 3)
  nlinarith [h1, h3, hlen, hT, hp, Nat.zero_le (T * p ^ 2)]

/-- `isz n ≤ 100 * T * p ^ 2` when `n + 2 ≤ T * p`. -/
theorem isz_le_100 {n T p : ℕ} (hn : n + 2 ≤ T * p) (hp : 100 ≤ p) :
    isz (n : ℤ) ≤ 100 * T * p ^ 2 := by
  have h0 : ((n : ℤ)).natAbs.size = n.size := by rw [Int.natAbs_natCast]
  have h1 : n.size ≤ n := (Nat.size_le).mpr Nat.lt_two_pow_self
  have h2 : 2 ≤ T * p := le_trans (by omega : 2 ≤ n + 2) hn
  have h3 : T * p ≤ T * p * p := by
    calc T * p = T * p * 1 := (mul_one _).symm
      _ ≤ T * p * p := Nat.mul_le_mul_left _ (by omega)
  simp only [isz, h0]
  nlinarith [h1, hn, h2, h3, hp, Nat.zero_le (T * p ^ 2)]

end Work.Transform
