import Mathlib
import Submission.Work.Transform.Defs
import Submission.Work.ConvR.basic
import Submission.Work.ConvR.negaNorm

/-!
# The normalised synthetic convolution is a contraction

`convR r ts u v` (paper `M_ℝ`) is `1/(M r)` times the sum over the `M = ∏ tᵢ` shifts `k` of the
negacyclic product of `u k` with the `(j-k)`-th slice of `v`, in the synthetic ring
`ℝ = ℂ[y]/(y^r+1)`.  Each negacyclic product has sup norm at most `r ‖a‖ ‖b‖`
(`Work.ConvR.negaNorm`, the point being that the factor is `r` and not `r^2`), and each slice of
`v` has sup norm at most `‖v‖`; summing over the `M` shifts therefore gives at most
`M · r · ‖u‖ ‖v‖`, which the normalisation `1/(M r)` divides out.

The only hypothesis needed on `ts` is that its entries are positive, so that `M > 0`; the
degenerate case `r = 0` is handled separately (`Fin 0 → ℂ` is a zero space, so both sides
vanish).
-/

set_option autoImplicit false

namespace Work.Transform

open HvdH

/-- Each shifted slice `v_{j-k}` used by `convR` has sup norm at most `‖v‖` (the truncation to
`0` outside the range of `subIdx` cannot increase the norm). -/
theorem convR_slice_norm_le (r : ℕ) (ts : List ℕ) (v : Fin ts.prod → Fin r → ℂ)
    (j k : Fin ts.prod) :
    ‖(fun c' => if h : HvdH.subIdx ts (j : ℕ) (k : ℕ) < ts.prod then v ⟨_, h⟩ c' else 0)‖
      ≤ ‖v‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg v)).2 (fun c' => ?_)
  by_cases h : HvdH.subIdx ts (j : ℕ) (k : ℕ) < ts.prod
  · rw [dite_eq_left h]
    exact le_trans (norm_le_pi_norm (v ⟨_, h⟩) c') (norm_le_pi_norm v ⟨_, h⟩)
  · rw [dite_eq_right h]
    simp

/-- `∏ tᵢ > 0` when every `tᵢ > 0`. -/
theorem prod_pos_of_forall_pos (ts : List ℕ) (hpos : ∀ t ∈ ts, 0 < t) : 0 < ts.prod := by
  induction ts with
  | nil => simp
  | cons t ts ih =>
    have ht : 0 < t := hpos t (by simp)
    have hts : ∀ x ∈ ts, 0 < x := fun x hx => hpos x (by simp [hx])
    rw [List.prod_cons]
    exact Nat.mul_pos ht (ih hts)

/-- The normalised synthetic convolution is a contraction: `‖M_R(u,v)‖ ≤ ‖u‖‖v‖`
(sup norms; the paper observes `‖M_R‖ ≤ 1` just before Proposition 3.4). -/
theorem convR_norm (r : ℕ) (ts : List ℕ) (hpos : ∀ t ∈ ts, 0 < t)
    (u v : Fin ts.prod → Fin r → ℂ) : ‖HvdH.convR r ts u v‖ ≤ ‖u‖ * ‖v‖ := by
  rcases Nat.eq_zero_or_pos r with hr | hr
  · -- degenerate case `r = 0`: the coefficient space `Fin 0 → ℂ` is trivial
    subst hr
    refine le_trans ?_ (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    refine (pi_norm_le_iff_of_nonneg le_rfl).2 (fun j => ?_)
    exact (pi_norm_le_iff_of_nonneg le_rfl).2 (fun c => Fin.elim0 c)
  · have hM : 0 < ts.prod := prod_pos_of_forall_pos ts hpos
    have hMr : ((ts.prod * r : ℕ) : ℝ) ≠ 0 := by
      have h : (0 : ℝ) < (ts.prod * r : ℕ) := by exact_mod_cast Nat.mul_pos hM hr
      exact h.ne'
    have hnn : 0 ≤ ‖u‖ * ‖v‖ := mul_nonneg (norm_nonneg _) (norm_nonneg _)
    refine (pi_norm_le_iff_of_nonneg hnn).2 (fun j => ?_)
    refine (pi_norm_le_iff_of_nonneg hnn).2 (fun c => ?_)
    rw [HvdH.convR]
    have hsum : ‖∑ k : Fin ts.prod, HvdH.negaMul r (u k)
          (fun c' => if h : HvdH.subIdx ts (j : ℕ) (k : ℕ) < ts.prod then v ⟨_, h⟩ c' else 0) c‖
        ≤ (ts.prod : ℝ) * ((r : ℝ) * ‖u‖ * ‖v‖) := by
      calc ‖∑ k : Fin ts.prod, HvdH.negaMul r (u k)
            (fun c' => if h : HvdH.subIdx ts (j : ℕ) (k : ℕ) < ts.prod then v ⟨_, h⟩ c' else 0) c‖
          ≤ ∑ k : Fin ts.prod, ‖HvdH.negaMul r (u k)
              (fun c' => if h : HvdH.subIdx ts (j : ℕ) (k : ℕ) < ts.prod then v ⟨_, h⟩ c' else 0) c‖ :=
            norm_sum_le _ _
        _ ≤ ∑ _k : Fin ts.prod, (r : ℝ) * ‖u‖ * ‖v‖ := by
            apply Finset.sum_le_sum
            intro k _
            calc ‖HvdH.negaMul r (u k)
                  (fun c' => if h : HvdH.subIdx ts (j : ℕ) (k : ℕ) < ts.prod then v ⟨_, h⟩ c' else 0) c‖
                ≤ ‖HvdH.negaMul r (u k)
                  (fun c' => if h : HvdH.subIdx ts (j : ℕ) (k : ℕ) < ts.prod then v ⟨_, h⟩ c' else 0)‖ :=
                  norm_le_pi_norm _ c
              _ ≤ (r : ℝ) * ‖u k‖ *
                  ‖(fun c' => if h : HvdH.subIdx ts (j : ℕ) (k : ℕ) < ts.prod then v ⟨_, h⟩ c' else 0)‖ :=
                  Work.ConvR.negaNorm r _ _
              _ ≤ (r : ℝ) * ‖u‖ * ‖v‖ := by
                  have h1 : ‖u k‖ ≤ ‖u‖ := norm_le_pi_norm u k
                  have h2 : ‖(fun c' => if h : HvdH.subIdx ts (j : ℕ) (k : ℕ) < ts.prod then
                      v ⟨_, h⟩ c' else 0)‖ ≤ ‖v‖ := convR_slice_norm_le r ts v j k
                  have hu : (0 : ℝ) ≤ ‖u‖ := norm_nonneg _
                  calc (r : ℝ) * ‖u k‖ *
                        ‖(fun c' => if h : HvdH.subIdx ts (j : ℕ) (k : ℕ) < ts.prod then
                          v ⟨_, h⟩ c' else 0)‖
                      = (r : ℝ) * (‖u k‖ *
                        ‖(fun c' => if h : HvdH.subIdx ts (j : ℕ) (k : ℕ) < ts.prod then
                          v ⟨_, h⟩ c' else 0)‖) := by ring
                    _ ≤ (r : ℝ) * (‖u‖ * ‖v‖) :=
                        mul_le_mul_of_nonneg_left (mul_le_mul h1 h2 (norm_nonneg _) hu)
                          (Nat.cast_nonneg r)
                    _ = (r : ℝ) * ‖u‖ * ‖v‖ := by ring
        _ = (ts.prod : ℝ) * ((r : ℝ) * ‖u‖ * ‖v‖) := by
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    calc ‖1 / ((ts.prod * r : ℕ) : ℂ) * (∑ k : Fin ts.prod, HvdH.negaMul r (u k)
          (fun c' => if h : HvdH.subIdx ts (j : ℕ) (k : ℕ) < ts.prod then v ⟨_, h⟩ c' else 0) c)‖
        = ‖(1 / ((ts.prod * r : ℕ) : ℂ))‖ * ‖∑ k : Fin ts.prod, HvdH.negaMul r (u k)
          (fun c' => if h : HvdH.subIdx ts (j : ℕ) (k : ℕ) < ts.prod then v ⟨_, h⟩ c' else 0) c‖ :=
          norm_mul _ _
      _ = ((ts.prod * r : ℕ) : ℝ)⁻¹ * ‖∑ k : Fin ts.prod, HvdH.negaMul r (u k)
          (fun c' => if h : HvdH.subIdx ts (j : ℕ) (k : ℕ) < ts.prod then v ⟨_, h⟩ c' else 0) c‖ := by
          rw [one_div, norm_inv, Complex.norm_natCast]
      _ ≤ ((ts.prod * r : ℕ) : ℝ)⁻¹ * ((ts.prod : ℝ) * ((r : ℝ) * ‖u‖ * ‖v‖)) :=
          mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = ‖u‖ * ‖v‖ := by
          rw [Nat.cast_mul]
          field_simp

end Work.Transform
