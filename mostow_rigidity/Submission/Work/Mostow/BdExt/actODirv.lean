import Mathlib
import Submission.Work.Mostow.poAux
import Submission.Work.Mostow.Hyper
import Submission.Work.Mostow.BdExt.Basic

/-!
# Direction of `actO A u`

`actO A u = tsign A • spat ((mat A) *ᵥ hlift u)` is the `tsign A`-signed scaling of the spatial
part of the matrix applied to the lift of `u`.  Since `dirv` is invariant under positive scalings
and flips sign under negative ones, `dirv (actO A u)` only depends on the *line* spanned by
`hlift u`.  In particular it is unchanged (up to the fixed sign `tsign A`) when `hlift u` is
rescaled by `‖u‖⁻¹`, which is the statement `actODirv`.

The proof is the elementary computation `dirv (c • w) = (c / |c|) • dirv w` together with
`|tsign A| = 1`.
-/

namespace Work.Mostow.BdExt

open Submission.Mostow Submission.Mostow.Hyper

variable {n : ℕ}

/-- `spat` is linear: it commutes with scalar multiplication. -/
lemma actODirv_spat_smul (c : ℝ) (z : Fin n ⊕ Fin 1 → ℝ) : spat (c • z) = c • spat z := by
  simp only [spat]
  ext i
  simp [Pi.smul_apply]

/-- `dirv` under a scalar multiple: `dirv (c • w) = (c / |c|) • dirv w`. -/
lemma actODirv_dirv_smul (c : ℝ) (w : E n) : dirv (c • w) = (c / |c|) • dirv w := by
  rw [dirv, dirv, norm_smul, Real.norm_eq_abs]
  rw [smul_smul, smul_smul]
  congr 1
  rw [mul_inv, div_eq_mul_inv]
  ring

/-- The sign `tsign A` is always `±1`, hence has absolute value `1`. -/
lemma actODirv_abs_tsign (A : O1 n) : |tsign A| = 1 := by
  unfold tsign
  split <;> simp

lemma actODirv_tsign_div_abs (A : O1 n) : tsign A / |tsign A| = tsign A := by
  rw [actODirv_abs_tsign, div_one]

/-- The defining computation of `actO`: it is `tsign A` times the spatial part of the matrix
applied to the lift of `u`. -/
lemma actODirv_actO_eq (A : O1 n) (u : E n) :
    actO A u = tsign A • spat (Matrix.mulVec (mat A) (hlift u)) := by
  simp only [actO, spat]
  ext i
  simp

theorem actODirv (n : ℕ) (A : Submission.Mostow.O1 n) (u : Submission.Mostow.E n) (hu : u ≠ 0) :
    Work.Mostow.BdExt.dirv (Submission.Mostow.actO A u)
      = Work.Mostow.BdExt.dirv (Submission.Mostow.tsign A •
          Submission.Mostow.Hyper.spat (Matrix.mulVec (Submission.Mostow.mat A)
            ((‖u‖)⁻¹ • Submission.Mostow.hlift u))) := by
  have hnorm : (‖u‖)⁻¹ ≠ 0 := inv_ne_zero (norm_ne_zero_iff.mpr hu)
  have hcoef : (tsign A * (‖u‖)⁻¹) / |tsign A * (‖u‖)⁻¹| = tsign A := by
    rw [abs_mul, actODirv_abs_tsign, one_mul,
      abs_of_nonneg (inv_nonneg.mpr (norm_nonneg u)), mul_div_assoc, div_self hnorm, mul_one]
  have hL : dirv (actO A u) = tsign A • dirv (spat (Matrix.mulVec (mat A) (hlift u))) := by
    rw [actODirv_actO_eq, actODirv_dirv_smul, actODirv_tsign_div_abs]
  have hR : dirv (tsign A • spat (Matrix.mulVec (mat A) ((‖u‖)⁻¹ • hlift u)))
      = tsign A • dirv (spat (Matrix.mulVec (mat A) (hlift u))) := by
    rw [Matrix.mulVec_smul, actODirv_spat_smul, smul_smul, actODirv_dirv_smul, hcoef]
  rw [hL, hR]

end Work.Mostow.BdExt
