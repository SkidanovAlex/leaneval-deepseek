import Mathlib
import Submission.Work.Peluse.TransferUp.RawPowDefs
import Submission.Work.Peluse.Concat.boxNormPow_succ_peel_gen

namespace Work.Peluse.TransferUp

/-- **Peeling the first coordinate of the raw box quantity.**  For `t ≥ 1`, `rawPow (t+1) Q S f`
(which is `boxNormPow (t+1) Q S f` multiplied by the normalising factor `∏_{i : Fin (t+1)} |Q i|²`)
is the honest (unweighted) sum over `h, h' ∈ Q 0` of `rawPow t` of the difference
`Δ'_{h,h'} f (u) = f (u + h) · conj (f (u + h'))` on the remaining direction sets `Q 1, …, Q t`:

`rawPow (t+1) Q S f = ∑_{h, h' ∈ Q 0} rawPow t (Q ∘ succ) S (Δ'_{h,h'} f)`.

This is `Work.Peluse.Concat.boxNormPow_succ_peel_gen` — the level-lowering recursion of Peluse's
Definition 2.1, whose right-hand side is the `|Q 0|⁻²`-weighted average of the box-norm powers —
read through the normalisation: multiplying by `∏_{i} |Q i|²` cancels the explicit `|Q 0|⁻²`, and
`∏_{i : Fin (t+1)} |Q i|² = |Q 0|² · ∏_{i : Fin t} |Q (i.succ)|²` splits off the first coordinate.
(When `Q 0 = ∅` both sides are `0`.) -/
theorem rawPow_succ_peel {t : ℕ} (ht : 1 ≤ t) (Q : Fin (t + 1) → Finset ℤ) (S : Finset ℤ) {f : ℤ → ℂ} (hf : Work.Peluse.FinSuppZ f) : Work.Peluse.TransferUp.rawPow (t + 1) Q S f = ∑ h ∈ Q 0, ∑ h' ∈ Q 0, Work.Peluse.TransferUp.rawPow t (fun i : Fin t => Q i.succ) S (fun u : ℤ => f (u + h) * star (f (u + h'))) := by
  classical
  simp only [rawPow]
  rw [Work.Peluse.Concat.boxNormPow_succ_peel_gen ht Q S hf]
  rw [Fin.prod_univ_succ]
  -- factor the (constant) normalising factor `∏_{i : Fin t} |Q (i.succ)|²` out of the double sum
  rw [show (∑ h ∈ Q 0, ∑ h' ∈ Q 0,
        (∏ i : Fin t, ((Q i.succ).card : ℝ) ^ 2) *
          Work.Peluse.boxNormPow t (fun i : Fin t => Q i.succ) S
            (fun u : ℤ => f (u + h) * star (f (u + h'))))
      = (∏ i : Fin t, ((Q i.succ).card : ℝ) ^ 2) *
        ∑ h ∈ Q 0, ∑ h' ∈ Q 0,
          Work.Peluse.boxNormPow t (fun i : Fin t => Q i.succ) S
            (fun u : ℤ => f (u + h) * star (f (u + h'))) from by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun h _ => ?_
    rw [Finset.mul_sum]]
  -- the remaining algebra: `|Q 0|² · |Q 0|⁻² = 1` (and both sides vanish when `Q 0 = ∅`)
  by_cases hc : (Q 0).card = 0
  · have hQ0 : Q 0 = ∅ := Finset.card_eq_zero.mp hc
    rw [hQ0]
    simp
  · have hcR : ((Q 0).card : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hc
    have hsq : (((Q 0).card : ℝ)) ^ 2 * ((((Q 0).card : ℝ)))⁻¹ ^ 2 = 1 := by
      rw [← mul_pow, mul_inv_cancel₀ hcR, one_pow]
    rw [show ((Q 0).card : ℝ) ^ 2 * (∏ i : Fin t, ((Q i.succ).card : ℝ) ^ 2) *
          ((((Q 0).card : ℝ))⁻¹ ^ 2 * ∑ h ∈ Q 0, ∑ h' ∈ Q 0, Work.Peluse.boxNormPow t (fun i : Fin t => Q i.succ) S
            (fun u : ℤ => f (u + h) * star (f (u + h'))))
        = (((Q 0).card : ℝ) ^ 2 * (((Q 0).card : ℝ))⁻¹ ^ 2) * ((∏ i : Fin t, ((Q i.succ).card : ℝ) ^ 2) *
            ∑ h ∈ Q 0, ∑ h' ∈ Q 0, Work.Peluse.boxNormPow t (fun i : Fin t => Q i.succ) S (fun u : ℤ => f (u + h) * star (f (u + h'))))
        from by ring]
    rw [hsq, one_mul]

end Work.Peluse.TransferUp
