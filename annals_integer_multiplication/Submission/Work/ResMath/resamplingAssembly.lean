import Mathlib
import Submission.Work.ResMath.resamplingAux
import Submission.Work.ResMath.summable_gauss_FsZ
import Submission.Work.ResMath.gaussianPoisson

/-!
# Assembly lemmas for the resampling identity
-/

namespace Work.ResMath

open HvdH

/-- The left-hand side acting on `u`, computed. -/
theorem resT_permS_dft_mulVec (s t α : ℕ) (hs : 0 < s) (ht : 0 < t) (hα : 0 < α)
    (u : Fin s → ℂ) (k : Fin t) :
    ((HvdH.resTmat s t α * HvdH.permS s t * HvdH.dftMat s).mulVec u) k =
      ∑' n : ℤ, (Real.exp (-Real.pi * (α : ℝ) ^ 2 * (t : ℝ) ^ 2 *
        ((k : ℝ) / (t : ℝ) - (n : ℝ) / (s : ℝ)) ^ 2) : ℂ) * FsZ s u (t * n) := by
  have hsne : (s : ℝ) ≠ 0 := by positivity
  have hps : ∀ j : Fin s, (HvdH.permS s t).mulVec ((HvdH.dftMat s).mulVec u) j =
      FsZ s u (t * (j : ℤ)) := by
    intro j
    rw [permS_mulVec s t hs]
    rw [dftMat_mulVec_FsZ]
    simp only [Fin.val_mk]
    have hnat := Nat.mod_add_div (t * (j : ℕ)) s
    have h : ((t * (j : ℕ) % s : ℕ) : ℤ) + (s : ℤ) * (((t * (j : ℕ)) / s : ℕ) : ℤ) = t * (j : ℤ) := by
      have h2 := congrArg (fun x : ℕ => (x : ℤ)) hnat
      rw [Nat.cast_add, Nat.cast_mul] at h2
      have h3 : ((t * (j : ℕ) : ℕ) : ℤ) = t * (j : ℤ) := by push_cast; ring
      linarith [h2, h3]
    rw [← h, FsZ_period s hs u (((t * (j : ℕ) % s : ℕ)) : ℤ) (((t * (j : ℕ)) / s : ℕ))]
  have hmain : ((HvdH.resTmat s t α * HvdH.permS s t * HvdH.dftMat s).mulVec u) k
      = ∑ j : Fin s, HvdH.resTmat s t α k j * FsZ s u (t * (j : ℤ)) := by
    rw [← Matrix.mulVec_mulVec u (HvdH.resTmat s t α * HvdH.permS s t) (HvdH.dftMat s)]
    rw [← Matrix.mulVec_mulVec ((HvdH.dftMat s).mulVec u) (HvdH.resTmat s t α) (HvdH.permS s t)]
    rw [Matrix.mulVec_apply, dotProduct]
    simp only [Matrix.row_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hps j]
  have hsumm : Summable (fun n : ℤ => (Real.exp (-Real.pi * (α : ℝ) ^ 2 * (t : ℝ) ^ 2 *
        ((k : ℝ) / (t : ℝ) - (n : ℝ) / (s : ℝ)) ^ 2) : ℂ) * FsZ s u (t * n)) :=
    summable_gauss_FsZ s t α hs ht hα u ((k : ℝ) / (t : ℝ))
  rw [hmain]
  rw [tsum_int_residue s hs _ hsumm]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [resTmat_apply, ← tsum_mul_right]
  refine tsum_congr fun q => ?_
  have hrr : (-Real.pi * (α : ℝ) ^ 2 * (t : ℝ) ^ 2 *
      ((k : ℝ) / (t : ℝ) - (j : ℝ) / (s : ℝ) - (q : ℝ)) ^ 2)
      = (-Real.pi * (α : ℝ) ^ 2 * (t : ℝ) ^ 2 *
      ((k : ℝ) / (t : ℝ) - ((((j : ℤ) + (s : ℤ) * q : ℤ)) : ℝ) / (s : ℝ)) ^ 2) := by
    push_cast
    field_simp
    ring
  have hfs : FsZ s u (t * (j : ℤ)) = FsZ s u (t * ((j : ℤ) + (s : ℤ) * q)) := by
    rw [show t * ((j : ℤ) + (s : ℤ) * q) = t * (j : ℤ) + (s : ℤ) * (t * q) from by ring]
    rw [FsZ_period s hs u (t * (j : ℤ)) (t * q)]
  rw [hrr, hfs]

end Work.ResMath
