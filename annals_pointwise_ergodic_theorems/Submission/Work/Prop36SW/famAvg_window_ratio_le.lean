import Mathlib
import Submission.Work.Peluse.UControl.peluseFamily
import Submission.Work.Prop36SW.boxNorm_symIcc_ratio_le

/-!
# Monotonicity of the family average in the ambient window

`D.famAvg l H c N f` is the average, over the parameter box `D.parBox l H`, of the level-`|I_{l-1}|`
box norm `D.famNorm l H c N a f`.  The box norm is taken over the ambient window `symIcc N`, and the
box sum `Work.Peluse.boxSumPow` sums its shift variable over all of `ℤ`; hence the window enters
`famNorm` only through the normalising factor `|symIcc N|⁻¹` (times the `1/2^t`-th root).  So
enlarging `N` can only help, up to the exact cardinality ratio:

    (|symIcc N| / |symIcc N'|) * D.famAvg l H c N f ≤ D.famAvg l H c N' f   (N ≤ N').

The per-direction-family inequality is `Work.Prop36SW.boxNorm_symIcc_ratio_le`; the passage to the
average over the parameter box is the fact that the normalising coefficient `|D.parBox l H|⁻¹` is
nonnegative.
-/

namespace Work.Prop36SW

theorem famAvg_window_ratio_le (D : Work.Peluse.UControl.IdxDatum) (l H : ℕ) (c : ℤ) (N N' : ℕ)
    (f : ℤ → ℂ) (hNN' : N ≤ N') :
    (((Work.Peluse.symIcc N).card : ℝ) / ((Work.Peluse.symIcc N').card : ℝ)) * D.famAvg l H c N f
      ≤ D.famAvg l H c N' f := by
  classical
  -- the direction family of the parameter `a` (independent of the ambient window)
  have hterm : ∀ a : D.Idx l,
      (((Work.Peluse.symIcc N).card : ℝ) / ((Work.Peluse.symIcc N').card : ℝ))
        * D.famNorm l H c N a f ≤ D.famNorm l H c N' a f := by
    intro a
    have h := boxNorm_symIcc_ratio_le
      (fun i : Fin (Fintype.card (D.I (l - 1))) =>
        Work.Peluse.arithIcc
          (D.dir l c (l - 1) ((Fintype.equivFin (D.I (l - 1))).symm i) (D.pad l a)) H)
      hNN' f
    simpa only [Work.Peluse.UControl.IdxDatum.famNorm] using h
  -- sum the per-parameter inequality over the parameter box
  have hsum : (∑ a ∈ D.parBox l H,
      (((Work.Peluse.symIcc N).card : ℝ) / ((Work.Peluse.symIcc N').card : ℝ))
        * D.famNorm l H c N a f)
      ≤ ∑ a ∈ D.parBox l H, D.famNorm l H c N' a f :=
    Finset.sum_le_sum fun a _ => hterm a
  simp only [Work.Peluse.UControl.IdxDatum.famAvg]
  rw [show (((Work.Peluse.symIcc N).card : ℝ) / ((Work.Peluse.symIcc N').card : ℝ))
        * (((D.parBox l H).card : ℝ)⁻¹ * ∑ a ∈ D.parBox l H, D.famNorm l H c N a f)
      = ((D.parBox l H).card : ℝ)⁻¹ * ∑ a ∈ D.parBox l H,
          (((Work.Peluse.symIcc N).card : ℝ) / ((Work.Peluse.symIcc N').card : ℝ))
            * D.famNorm l H c N a f by
      rw [mul_left_comm, Finset.mul_sum]]
  exact mul_le_mul_of_nonneg_left hsum (by positivity)

end Work.Prop36SW
