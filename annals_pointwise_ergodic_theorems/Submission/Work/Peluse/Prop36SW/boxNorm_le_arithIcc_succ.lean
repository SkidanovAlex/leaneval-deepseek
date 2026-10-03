import Mathlib
import Submission.Work.Peluse.UControl.peluseLadder
import Submission.Work.Peluse.Prop36SW.boxNormPow_arithIcc_shrink

namespace Work.Peluse.Prop36SW

/-- **Passing from the direction family `q_i[H]` to `q_i[H+1]` costs only the constant
`(4^t)^{2^{-t}}`.**  The raw box quantity `rawPow t Q S f = (∏_i |Q i|²) · boxNormPow t Q S f` is
monotone in the direction sets, so with `Q i = arithIcc (q i) H ⊆ arithIcc (q i) (H+1) = Q' i` one
gets `(∏ |Q i|²) B(H) ≤ (∏ |Q' i|²) B(H+1)`.  Each direction set `arithIcc (q i) M` has cardinality
`M` when `q i ≠ 0` and cardinality `1` when `q i = 0`; in both cases
`|arithIcc (q i) (H+1)| ≤ 2 |arithIcc (q i) H|` for `H ≥ 1`, so `∏_i |Q' i|² ≤ 4^t ∏_i |Q i|²` and
`B(H) ≤ 4^t B(H+1)`.  Raising to the power `2^{-t}` (a monotone map on `ℝ_{≥0}`) and using
`(xy)^{2^{-t}} = x^{2^{-t}} y^{2^{-t}}` gives the claim, since `boxNorm = boxNormPow^{2^{-t}}`. -/
theorem boxNorm_le_arithIcc_succ {t : ℕ} (ht : 2 ≤ t) (q : Fin t → ℤ) {H : ℕ} (hH : 1 ≤ H)
    (S : Finset ℤ) {f : ℤ → ℂ} (hf : Work.Peluse.FinSuppZ f) :
    Work.Peluse.boxNorm t (fun i => Work.Peluse.arithIcc (q i) H) S f
      ≤ ((4 : ℝ) ^ t) ^ (1 / (2 : ℝ) ^ t)
        * Work.Peluse.boxNorm t (fun i => Work.Peluse.arithIcc (q i) (H + 1)) S f := by
  have hH2 : H + 1 ≤ 2 * H := by omega
  -- raw monotonicity of the box quantity in the direction sets
  have hraw := Work.Peluse.TransferUp.rawPow_mono_of_two_le (t := t) ht S hf
    (Q := fun i => Work.Peluse.arithIcc (q i) H)
    (Q' := fun i => Work.Peluse.arithIcc (q i) (H + 1))
    (fun i => arithIcc_subset_of_le (q i) (Nat.le_succ H))
  rw [Work.Peluse.TransferUp.rawPow, Work.Peluse.TransferUp.rawPow] at hraw
  -- the cardinality products differ by at most `4^t`
  have hprod : (∏ i : Fin t, (((Work.Peluse.arithIcc (q i) (H + 1)).card : ℝ)) ^ 2)
      ≤ (4 : ℝ) ^ t * ∏ i : Fin t, (((Work.Peluse.arithIcc (q i) H).card : ℝ)) ^ 2 := by
    have hper : ∀ i : Fin t, (((Work.Peluse.arithIcc (q i) (H + 1)).card : ℝ)) ^ 2
        ≤ 4 * (((Work.Peluse.arithIcc (q i) H).card : ℝ)) ^ 2 := by
      intro i
      have h3 := arithIcc_card_le_two (q i) hH hH2
      have h3' : ((Work.Peluse.arithIcc (q i) (H + 1)).card : ℝ)
          ≤ 2 * ((Work.Peluse.arithIcc (q i) H).card : ℝ) := by exact_mod_cast h3
      have h0a : (0 : ℝ) ≤ ((Work.Peluse.arithIcc (q i) (H + 1)).card : ℝ) := by positivity
      have h0b : (0 : ℝ) ≤ ((Work.Peluse.arithIcc (q i) H).card : ℝ) := by positivity
      nlinarith [h3', h0a, h0b]
    calc (∏ i : Fin t, (((Work.Peluse.arithIcc (q i) (H + 1)).card : ℝ)) ^ 2)
        ≤ ∏ i : Fin t, 4 * (((Work.Peluse.arithIcc (q i) H).card : ℝ)) ^ 2 :=
          Finset.prod_le_prod₀ (fun i _ => by positivity) (fun i _ => hper i)
      _ = (4 : ℝ) ^ t * ∏ i : Fin t, (((Work.Peluse.arithIcc (q i) H).card : ℝ)) ^ 2 := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have hpos : (0 : ℝ) < ∏ i : Fin t, (((Work.Peluse.arithIcc (q i) H).card : ℝ)) ^ 2 := by
    refine Finset.prod_pos (fun i _ => ?_)
    have h := arithIcc_card_pos (q i) hH
    have h' : (0 : ℝ) < ((Work.Peluse.arithIcc (q i) H).card : ℝ) := by exact_mod_cast h
    positivity
  have hBnn : (0 : ℝ) ≤ Work.Peluse.boxNormPow t (fun i => Work.Peluse.arithIcc (q i) (H + 1)) S f :=
    norm_nonneg _
  -- the core bound `B(H) ≤ 4^t B(H+1)`
  have hcore : Work.Peluse.boxNormPow t (fun i => Work.Peluse.arithIcc (q i) H) S f
      ≤ (4 : ℝ) ^ t
        * Work.Peluse.boxNormPow t (fun i => Work.Peluse.arithIcc (q i) (H + 1)) S f := by
    refine (mul_le_mul_iff_of_pos_left hpos).mp ?_
    calc (∏ i : Fin t, (((Work.Peluse.arithIcc (q i) H).card : ℝ)) ^ 2)
          * Work.Peluse.boxNormPow t (fun i => Work.Peluse.arithIcc (q i) H) S f
        ≤ (∏ i : Fin t, (((Work.Peluse.arithIcc (q i) (H + 1)).card : ℝ)) ^ 2)
          * Work.Peluse.boxNormPow t (fun i => Work.Peluse.arithIcc (q i) (H + 1)) S f := hraw
      _ ≤ ((4 : ℝ) ^ t * ∏ i : Fin t, (((Work.Peluse.arithIcc (q i) H).card : ℝ)) ^ 2)
          * Work.Peluse.boxNormPow t (fun i => Work.Peluse.arithIcc (q i) (H + 1)) S f :=
            mul_le_mul_of_nonneg_right hprod hBnn
      _ = (∏ i : Fin t, (((Work.Peluse.arithIcc (q i) H).card : ℝ)) ^ 2)
          * ((4 : ℝ) ^ t
              * Work.Peluse.boxNormPow t (fun i => Work.Peluse.arithIcc (q i) (H + 1)) S f) := by
            ring
  -- raise to the power `2^{-t}`
  have hexp : (0 : ℝ) ≤ 1 / (2 : ℝ) ^ t := by positivity
  have h4 : (0 : ℝ) ≤ (4 : ℝ) ^ t := by positivity
  have hx : (0 : ℝ) ≤ Work.Peluse.boxNormPow t (fun i => Work.Peluse.arithIcc (q i) H) S f :=
    norm_nonneg _
  calc Work.Peluse.boxNorm t (fun i => Work.Peluse.arithIcc (q i) H) S f
      = (Work.Peluse.boxNormPow t (fun i => Work.Peluse.arithIcc (q i) H) S f)
          ^ (1 / (2 : ℝ) ^ t) := rfl
    _ ≤ ((4 : ℝ) ^ t
          * Work.Peluse.boxNormPow t (fun i => Work.Peluse.arithIcc (q i) (H + 1)) S f)
          ^ (1 / (2 : ℝ) ^ t) := Real.rpow_le_rpow hx hcore hexp
    _ = ((4 : ℝ) ^ t) ^ (1 / (2 : ℝ) ^ t)
        * (Work.Peluse.boxNormPow t (fun i => Work.Peluse.arithIcc (q i) (H + 1)) S f)
            ^ (1 / (2 : ℝ) ^ t) := Real.mul_rpow h4 hBnn
    _ = ((4 : ℝ) ^ t) ^ (1 / (2 : ℝ) ^ t)
        * Work.Peluse.boxNorm t (fun i => Work.Peluse.arithIcc (q i) (H + 1)) S f := rfl

end Work.Peluse.Prop36SW
