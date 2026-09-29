import Mathlib
import Submission.Work.ZagC.defs
import Submission.Work.ZagC.coeff_id
import Submission.Work.ZagC.shift_up_sum
import Submission.Work.ZagC.shift_down_sum

/-!
# The binomial transfer of recurrence operators

For a sequence `u : ℕ → ℚ` let `Cfun u n = Σ_{m ≤ n} C(n,m) u m` be its binomial
transform.  The two recurrence operators of the Zagier/Franel story,

`LFop u m = (m+1)²u_{m+1} − (7m²+7m+2)u_m − 8m²u_{m−1}`  (Franel)
`LCop u m = (m+1)²u_{m+1} − (10m²+10m+3)u_m + 9m²u_{m−1}` (Zagier's C)

satisfy the intertwining identity

`LCop (Cfun u) n = Σ_{m ≤ n+1} C(n,m) · LFop u m`,

which is what lets one build a solution of the *inhomogeneous* Zagier recurrence
`LCop` from an explicit solution `g` of Franel's recurrence via `c_n = Σ_m C(n,m) g_m`
(cf. `Work.ZagC.zagier_c_integrality`).

The proof is a coefficient comparison.  Both sides are `Σ_j d_j · u_j` with

`d_j = (n+1)²C(n+1,j) − (10n²+10n+3)C(n,j) + 9n²C(n−1,j)`  (left side)

`d_j = j²C(n,j−1) − (7j²+7j+2)C(n,j) − 8(j+1)²C(n,j+1)`  (right side)

and the two expressions are equal (`Work.ZagC.coeff_id`).  The reindexings
`u_{m+1} ↔ u_j` and `u_{m−1} ↔ u_j` are the pure rewrite lemmas
`Work.ZagC.shift_up_sum` and `Work.ZagC.shift_down_sum`.
-/

namespace Work.ZagC

open Finset
open scoped BigOperators

noncomputable section

/-- `Cfun u n` is a sum over `range (n+1)`; pad it to `range (n+2)`. -/
lemma transfer_pad (v : ℕ → ℚ) (n : ℕ) :
    Cfun v n = ∑ m ∈ Finset.range (n+2), (n.choose m : ℚ) * v m := by
  unfold Cfun
  refine Finset.sum_subset (Finset.range_subset_range.mpr (by omega)) ?_
  intro x hx hxnot
  rw [Finset.mem_range] at hx hxnot
  rw [Nat.choose_eq_zero_of_lt (by omega : n < x)]
  norm_num

/-- Same padding for the index `n - 1`. -/
lemma transfer_pad_pred (v : ℕ → ℚ) (n : ℕ) :
    Cfun v (n-1) = ∑ m ∈ Finset.range (n+2), ((n-1).choose m : ℚ) * v m := by
  unfold Cfun
  refine Finset.sum_subset (Finset.range_subset_range.mpr (by omega)) ?_
  intro x hx hxnot
  rw [Finset.mem_range] at hx hxnot
  rw [Nat.choose_eq_zero_of_lt (by omega : n - 1 < x)]
  norm_num

/-- The left-hand side `LCop (Cfun v) n` written as `Σ_j d_j v_j`. -/
lemma transfer_NF_L (v : ℕ → ℚ) (n : ℕ) :
    LCop (fun t => Cfun v t) n
      = ∑ j ∈ Finset.range (n+2), ((((n:ℚ)+1)^2 * ((n+1).choose j : ℚ)
          - (10*(n:ℚ)^2 + 10*(n:ℚ) + 3) * (n.choose j : ℚ)
          + 9*(n:ℚ)^2 * ((n-1).choose j : ℚ)) * v j) := by
  simp only [LCop]
  rw [transfer_pad v n, transfer_pad_pred v n]
  have h3 : Cfun v (n+1) = ∑ m ∈ Finset.range (n+2), ((n+1).choose m : ℚ) * v m := rfl
  rw [h3]
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun j hj => ?_)
  push_cast
  ring

/-- The right-hand side `Σ_m C(n,m) LFop v m` (with `LFop` expanded) written as `Σ_j e_j v_j`. -/
lemma transfer_NF_R (v : ℕ → ℚ) (n : ℕ) :
    (∑ m ∈ Finset.range (n+2), (n.choose m : ℚ) *
        (((m:ℚ)+1)^2 * v (m+1) - (7*(m:ℚ)^2 + 7*(m:ℚ) + 2) * v m - 8*(m:ℚ)^2 * v (m-1)))
      = ∑ j ∈ Finset.range (n+2), ((j:ℚ)^2 * (n.choose (j-1) : ℚ)
          - (7*(j:ℚ)^2 + 7*(j:ℚ) + 2) * (n.choose j : ℚ)
          - 8*((j:ℚ)+1)^2 * (n.choose (j+1) : ℚ)) * v j := by
  rw [Finset.sum_congr rfl (fun m _ => by ring : ∀ m ∈ Finset.range (n+2),
    (n.choose m : ℚ) * (((m:ℚ)+1)^2 * v (m+1) - (7*(m:ℚ)^2 + 7*(m:ℚ) + 2) * v m - 8*(m:ℚ)^2 * v (m-1))
    = (n.choose m : ℚ) * ((m:ℚ)+1)^2 * v (m+1)
      - (n.choose m : ℚ) * (7*(m:ℚ)^2 + 7*(m:ℚ) + 2) * v m
      - (n.choose m : ℚ) * (8*(m:ℚ)^2) * v (m-1))]
  simp only [Finset.sum_sub_distrib]
  rw [shift_up_sum v n, shift_down_sum v n]
  rw [Finset.sum_congr rfl (fun j _ => by ring : ∀ j ∈ Finset.range (n+2),
    ((j:ℚ)^2 * (n.choose (j-1) : ℚ) - (7*(j:ℚ)^2 + 7*(j:ℚ) + 2) * (n.choose j : ℚ)
      - 8*((j:ℚ)+1)^2 * (n.choose (j+1) : ℚ)) * v j
    = (j:ℚ)^2 * (n.choose (j-1) : ℚ) * v j
      - (n.choose j : ℚ) * (7*(j:ℚ)^2 + 7*(j:ℚ) + 2) * v j
      - 8*((j:ℚ)+1)^2 * (n.choose (j+1) : ℚ) * v j)]
  simp only [Finset.sum_sub_distrib]

theorem transfer (u : ℕ → ℚ) (n : ℕ) : Work.ZagC.LCop (fun t : ℕ => Work.ZagC.Cfun u t) n = ∑ m ∈ Finset.range (n + 2), ((n.choose m : ℕ) : ℚ) * Work.ZagC.LFop u m := by
  have hR : (∑ m ∈ Finset.range (n+2), (n.choose m : ℚ) * LFop u m)
      = ∑ m ∈ Finset.range (n+2), (n.choose m : ℚ) *
          (((m:ℚ)+1)^2 * u (m+1) - (7*(m:ℚ)^2 + 7*(m:ℚ) + 2) * u m - 8*(m:ℚ)^2 * u (m-1)) := by
    refine Finset.sum_congr rfl (fun m _ => ?_)
    rw [LFop]
    push_cast
    ring
  rw [transfer_NF_L u n, hR, transfer_NF_R u n]
  refine Finset.sum_congr rfl (fun j hj => ?_)
  rw [Finset.mem_range] at hj
  rw [coeff_id n j (by omega)]

end

end Work.ZagC
