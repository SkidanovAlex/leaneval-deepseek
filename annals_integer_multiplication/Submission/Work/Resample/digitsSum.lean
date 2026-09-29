import Mathlib
import Submission.Work.Resample.defs

/-!
# Mixed-radix "Fubini" identity for `HvdH.digits`

This is the combinatorial heart of the tensor/Fubini bookkeeping of the Gaussian
resampling maps: summing an arbitrary function of the mixed-radix digits of `m`
over all `m < b.prod` is the same as summing independently over each digit.

`HvdH.digits ts m` is the big-endian mixed-radix expansion of `m` in the digit sizes
`ts` (`most significant digit first`), so for positive radices the map
`m ↦ (digits b m).getD i 0` realises the canonical bijection
`Fin b.prod ≃ Π i, Fin (bᵢ)`.

The identity is proved by induction on the digit list, peeling off the most significant
digit; the reindexing `Fin (t * d) ≃ Fin t × Fin d` is `finProdFinEquiv`.

The statement holds for *arbitrary* `b`: if some radix vanishes then both sides are `0`
(on the right because that factor sums over the empty type `Fin 0`).
-/

namespace Work.Resample

/-! ### Three elementary steps -/

/-- Splitting off the most significant digit of `digits (t :: ts) m`. -/
private lemma prod_digits_cons (t : ℕ) (ts : List ℕ) (h : ℕ → ℕ → ℂ) (m : ℕ) :
    ∏ i ∈ Finset.range (ts.length + 1), h i ((HvdH.digits (t :: ts) m).getD i 0)
      = (∏ i ∈ Finset.range ts.length, h (i+1) ((HvdH.digits ts (m % ts.prod)).getD i 0))
        * h 0 ((m / ts.prod) % t) := by
  rw [Finset.prod_range_succ']
  simp only [HvdH.digits, List.getD_cons_succ, List.getD_cons_zero]

/-- Reindexing a sum over `Fin (a * b)` as a double sum, via `Fin (a*b) ≃ Fin a × Fin b`. -/
private lemma sum_fin_mul_eq (a b : ℕ) (f : ℕ → ℂ) :
    ∑ m : Fin (a * b), f (m : ℕ) = ∑ q : Fin a, ∑ r : Fin b, f (b * q + r) := by
  rw [← Equiv.sum_comp finProdFinEquiv (fun m : Fin (a*b) => f (m:ℕ))]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun r _ => ?_
  congr 1
  simp [finProdFinEquiv, Nat.add_comm]

/-- The inductive step: after splitting off the leading digit, the sum factors. -/
private lemma cons_sum_step (t : ℕ) (ts : List ℕ) (h : ℕ → ℕ → ℂ) (hP : 0 < ts.prod) :
    (∑ m : Fin (t * ts.prod),
        (∏ i ∈ Finset.range ts.length, h (i+1) ((HvdH.digits ts (m % ts.prod)).getD i 0))
          * h 0 ((m / ts.prod) % t))
      = (∑ q : Fin t, h 0 q)
        * (∑ r : Fin ts.prod, ∏ i ∈ Finset.range ts.length, h (i+1) ((HvdH.digits ts r).getD i 0)) := by
  rw [sum_fin_mul_eq t ts.prod (fun m =>
    (∏ i ∈ Finset.range ts.length, h (i+1) ((HvdH.digits ts (m % ts.prod)).getD i 0))
      * h 0 ((m / ts.prod) % t))]
  rw [Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun r _ => ?_
  have hmod : (ts.prod * (q:ℕ) + (r:ℕ)) % ts.prod = (r:ℕ) := by
    have h1 : ts.prod * (q:ℕ) + (r:ℕ) = (r:ℕ) + (q:ℕ) * ts.prod := by ring
    rw [h1, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt r.isLt]
  have hdiv : (ts.prod * (q:ℕ) + (r:ℕ)) / ts.prod = (q:ℕ) := by
    have h1 : ts.prod * (q:ℕ) + (r:ℕ) = (r:ℕ) + (q:ℕ) * ts.prod := by ring
    rw [h1, Nat.add_mul_div_right _ _ hP, Nat.div_eq_of_lt r.isLt, Nat.zero_add]
  rw [hmod, hdiv, Nat.mod_eq_of_lt q.isLt]
  ring

/-! ### The identity for positive radices -/

private theorem pos_aux : ∀ b : List ℕ, (∀ x ∈ b, 0 < x) → ∀ h : ℕ → ℕ → ℂ,
    ∑ m : Fin b.prod, ∏ i ∈ Finset.range b.length, h i ((HvdH.digits b (m : ℕ)).getD i 0)
      = ∏ i ∈ Finset.range b.length, ∑ l : Fin (b.getD i 0), h i l := by
  intro b
  induction b with
  | nil =>
    intro _ h
    show (∑ m : Fin 1, ∏ i ∈ Finset.range 0, h i ((HvdH.digits [] (m : ℕ)).getD i 0))
        = ∏ i ∈ Finset.range 0, ∑ l : Fin (([].getD i 0)), h i l
    simp
  | cons t ts ih =>
    intro hpos h
    have hts_pos : ∀ x ∈ ts, 0 < x := fun x hx => hpos x (by simp [hx])
    have hP : 0 < ts.prod := List.prod_pos hts_pos
    have hlhs : (∑ m : Fin (t * ts.prod),
          ∏ i ∈ Finset.range (ts.length+1), h i ((HvdH.digits (t :: ts) (↑m)).getD i 0))
        = ∑ m : Fin (t * ts.prod),
            (∏ i ∈ Finset.range ts.length,
              h (i+1) ((HvdH.digits ts ((m:ℕ) % ts.prod)).getD i 0)) * h 0 (((m:ℕ) / ts.prod) % t) := by
      refine Finset.sum_congr rfl fun m _ => ?_
      exact prod_digits_cons t ts h (m:ℕ)
    have hr : (∏ i ∈ Finset.range (ts.length + 1), ∑ l : Fin ((t :: ts).getD i 0), h i l)
        = (∏ i ∈ Finset.range ts.length, ∑ l : Fin (ts.getD i 0), h (i+1) l)
          * (∑ l : Fin t, h 0 l) := by
      rw [Finset.prod_range_succ']
      rfl
    rw [List.prod_cons, List.length_cons, hlhs, cons_sum_step t ts h hP,
        ih hts_pos (fun i => h (i+1)), hr]
    exact mul_comm _ _

/-! ### The identity for arbitrary radices -/

theorem digitsSum (b : List ℕ) (h : ℕ → ℕ → ℂ) :
    ∑ m : Fin b.prod, ∏ i ∈ Finset.range b.length, h i ((HvdH.digits b (m : ℕ)).getD i 0)
      = ∏ i ∈ Finset.range b.length, ∑ l : Fin (b.getD i 0), h i l := by
  by_cases hmem : 0 ∈ b
  · -- a vanishing radix makes both sides `0`
    obtain ⟨i, hi, hget⟩ := List.mem_iff_getElem.mp hmem
    have hfac : (∑ l : Fin (b.getD i 0), h i l) = 0 := by
      rw [List.getD_eq_getElem b 0 hi, hget]
      simp
    rw [List.prod_eq_zero hmem, Finset.prod_eq_zero (Finset.mem_range.mpr hi) hfac]
    simp
  · exact pos_aux b (fun x hx => Nat.pos_of_ne_zero (fun h0 => hmem (h0 ▸ hx))) h

end Work.Resample
