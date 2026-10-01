import Mathlib
import Submission.Work.LinnikAreas.CorrAllR.Defs

namespace Work.LinnikAreas.CorrAllR

open Finset
open Work.LinnikAreas

/-- **Sum over tuples with one coordinate frozen.**

For a finite index type `ι`, a finite type `α` and a fixed index `i : ι`,
`∑_w ∏_{j ≠ i} G (w j) (w i) = ∑_u (∑_v G v u)^{card ι - 1}`:
freezing the `i`-th coordinate to `u`, the remaining coordinates range
independently over `α`, giving `card ι - 1` identical inner sums. -/
lemma sum_prod_erase_eq {ι α : Type*} [Fintype ι] [DecidableEq ι] [Fintype α]
    (i : ι) (G : α → α → ℝ) :
    (∑ w : ι → α, ∏ j ∈ Finset.univ.erase i, G (w j) (w i))
      = ∑ u : α, (∑ v : α, G v u) ^ (Fintype.card ι - 1) := by
  classical
  have h1 : ∀ w : ι → α, (∏ j ∈ Finset.univ.erase i, G (w j) (w i))
      = ∏ j : {j : ι // j ≠ i}, G (w j) (w i) := fun w =>
    Finset.prod_subtype (Finset.univ.erase i) (fun x => by simp) (fun j => G (w j) (w i))
  rw [Finset.sum_congr rfl (fun w _ => h1 w)]
  rw [← Equiv.sum_comp (Equiv.piSplitAt i (fun _ : ι => α)).symm
        (fun w : ι → α => ∏ j : {j : ι // j ≠ i}, G (w j) (w i))]
  rw [Fintype.sum_prod_type]
  have hcard : Fintype.card {j : ι // j ≠ i} = Fintype.card ι - 1 := by
    rw [Fintype.card_subtype]
    have hfil : (Finset.univ.filter (fun j : ι => j ≠ i)) = Finset.univ.erase i := by
      ext j; simp [Finset.mem_erase, and_comm]
    rw [hfil, Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ]
  refine Finset.sum_congr rfl fun u _ => ?_
  have hother : ∀ (c : {j : ι // j ≠ i} → α) (j : {j : ι // j ≠ i}),
      (Equiv.piSplitAt i (fun _ : ι => α)).symm (u, c) ↑j = c j := by
    intro c j
    rw [Equiv.piSplitAt_symm_apply]
    simp [j.2]
  have hself : ∀ c : {j : ι // j ≠ i} → α,
      (Equiv.piSplitAt i (fun _ : ι => α)).symm (u, c) i = u := by
    intro c
    rw [Equiv.piSplitAt_symm_apply]
    simp
  have key : ∀ (c : {j : ι // j ≠ i} → α),
      (∏ j : {j : ι // j ≠ i}, G ((Equiv.piSplitAt i (fun _ : ι => α)).symm (u, c) ↑j)
          ((Equiv.piSplitAt i (fun _ : ι => α)).symm (u, c) i))
        = ∏ j : {j : ι // j ≠ i}, G (c j) u := by
    intro c
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [hother c j, hself c]
  rw [Finset.sum_congr rfl (fun c _ => key c)]
  rw [← Fintype.prod_sum (fun (_ : {j : ι // j ≠ i}) (a : α) => G a u)]
  simp only [Finset.prod_const, Finset.card_univ, hcard]

/-- The `gcd`-weight with shifts `+1` can be rewritten symmetrically: shifting both arguments
by `1` does not change `|· - ·|`, and negation does not change `natAbs`. -/
lemma natAbs_shift {H r : ℕ} (w : Fin (r + r) → Fin H) (j i : Fin (r + r)) :
    (((pairVecH w j : ℤ) - (pairVecH w i : ℤ)).natAbs)
      = (((w i : ℤ) - (w j : ℤ)).natAbs) := by
  have h : ((pairVecH w j : ℤ) - (pairVecH w i : ℤ)) = -((w i : ℤ) - (w j : ℤ)) := by
    simp only [pairVecH]; push_cast; ring
  rw [h, Int.natAbs_neg]

/-- The single-terms weight appearing on the right-hand side of `sum_Ww_eq_pow`:
`G q a b = 0` when `b = a` and `gcd (q, |b - a|)` otherwise. -/
noncomputable def G (q : ℕ) {H : ℕ} (a b : Fin H) : ℝ :=
  if b = a then 0 else (Nat.gcd q (((b : ℤ) - (a : ℤ)).natAbs) : ℝ)

/-- One factor of `Ww` agrees with `G`: `w j = w i ↔ w i = w j` and the `+1` shifts cancel. -/
lemma Ww_factor (q : ℕ) {H r : ℕ} (w : Fin (r + r) → Fin H) (j i : Fin (r + r)) :
    (if w j = w i then 0
      else (Nat.gcd q (((pairVecH w j : ℤ) - (pairVecH w i : ℤ)).natAbs) : ℝ))
      = G q (w j) (w i) := by
  rw [G]
  by_cases h : w j = w i
  · rw [if_pos h, if_pos h.symm]
  · rw [if_neg h, if_neg (fun hh => h hh.symm), natAbs_shift]

theorem sum_Ww_eq_pow (q : ℕ) {H r : ℕ} (hr : 0 < r) (i : Fin (r + r)) :
    (∑ w : Fin (r + r) → Fin H, Work.LinnikAreas.Ww q w i)
      = ∑ u : Fin H,
          (∑ v : Fin H, (if u = v then 0 else (Nat.gcd q (((u : ℤ) - (v : ℤ)).natAbs) : ℝ)))
            ^ (2 * r - 1) := by
  classical
  have hstep : (∑ w : Fin (r + r) → Fin H, Work.LinnikAreas.Ww q w i)
      = ∑ w : Fin (r + r) → Fin H, ∏ j ∈ Finset.univ.erase i, G q (w j) (w i) := by
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [Work.LinnikAreas.Ww]
    exact Finset.prod_congr rfl fun j _ => Ww_factor q w j i
  rw [hstep, sum_prod_erase_eq i (G q)]
  refine Finset.sum_congr rfl fun u _ => ?_
  have hbase : (∑ v : Fin H, G q v u)
      = ∑ v : Fin H, (if u = v then 0 else (Nat.gcd q (((u : ℤ) - (v : ℤ)).natAbs) : ℝ)) := by
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [G]
  have hexp : Fintype.card (Fin (r + r)) - 1 = 2 * r - 1 := by
    rw [Fintype.card_fin]; omega
  rw [hbase, hexp]

end Work.LinnikAreas.CorrAllR
