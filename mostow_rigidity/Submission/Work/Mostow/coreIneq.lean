import Mathlib
import Submission.Work.Mostow.poAux
import Submission.Work.Mostow.StabHoroForm

/-!
# The core algebraic inequality of the level-scaling argument

Let `w` be the Minkowski form on `ℝ^{Fin n ⊕ Fin 1}` (`mform x y = xᵀ J y`, the time
coordinate being `Sum.inr 0`).  Suppose `pp`, `cc` are orthogonal vectors with
`mform pp pp = -PP`, `mform cc cc = CC`, `PP - CC = 1`, `CC > 0` — so `pp + cc` is a point
of the hyperboloid.  Suppose further that a linear map `M` acts on the plane spanned by
`pp, cc` with `mform pp (M pp) = -A`, `mform cc (M cc) = B`, `mform pp (M cc) = mform cc (M pp) = 0`,
and that `B ≤ CC`, `A - B > 1`.

Then for every `d > 0` such that the vector `pp + (1+d) cc` is timelike, the unit
normalisation of `pp + (1+d) cc` pairs with its image under `M` strictly below the value
attained at `pp + cc`:

`mform (w_d) (M w_d) < mform (pp + cc) (M (pp + cc))`.

This is the elementary estimate that drives the level-scaling (Prasad) argument for the
stabilizer of a horosphere.
-/

namespace Work.Mostow

open Matrix

lemma coreIneq {n : ℕ} (M : Matrix (Fin n ⊕ Fin 1) (Fin n ⊕ Fin 1) ℝ)
    (pp cc : Fin n ⊕ Fin 1 → ℝ) (PP CC A B : ℝ)
    (hpp : Work.Mostow.mform pp pp = -PP) (hcc : Work.Mostow.mform cc cc = CC)
    (hpc : Work.Mostow.mform pp cc = 0) (hPP : PP - CC = 1) (hCCpos : 0 < CC)
    (hAc : Work.Mostow.mform pp (M.mulVec pp) = -A) (hBc : Work.Mostow.mform cc (M.mulVec cc) = B)
    (hpMc : Work.Mostow.mform pp (M.mulVec cc) = 0) (hcMp : Work.Mostow.mform cc (M.mulVec pp) = 0)
    (hMM : Work.Mostow.mform (M.mulVec cc) (M.mulVec cc) = CC)
    (hB : B ≤ CC) (hA : 1 < A - B)
    (d : ℝ) (hd : 0 < d) (hden : 0 < PP - (1+d)^2 * CC) :
    Work.Mostow.mform ((Real.sqrt (PP - (1+d)^2 * CC))⁻¹ • (pp + (1+d) • cc))
        (M.mulVec ((Real.sqrt (PP - (1+d)^2*CC))⁻¹ • (pp + (1+d) • cc)))
      < Work.Mostow.mform (pp + cc) (M.mulVec (pp + cc)) := by
  -- `mform v (M v)` for `v = pp + (1+d) cc`
  have hv : Work.Mostow.mform (pp + (1 + d) • cc) (M.mulVec (pp + (1 + d) • cc))
      = -A + (1 + d)^2 * B := by
    simp only [Matrix.mulVec_add, Matrix.mulVec_smul, Work.Mostow.mform_add_left,
      Work.Mostow.mform_add_right, Work.Mostow.mform_smul_left, Work.Mostow.mform_smul_right,
      hAc, hpMc, hcMp, hBc]
    ring
  -- `mform w (M w)` for `w = pp + cc`
  have hw : Work.Mostow.mform (pp + cc) (M.mulVec (pp + cc)) = B - A := by
    simp only [Matrix.mulVec_add, Work.Mostow.mform_add_left, Work.Mostow.mform_add_right,
      hAc, hpMc, hcMp, hBc]
    ring
  -- scaling: `mform` is homogeneous of degree 2
  have h3 : Work.Mostow.mform ((Real.sqrt (PP - (1 + d)^2 * CC))⁻¹ • (pp + (1 + d) • cc))
      (M.mulVec ((Real.sqrt (PP - (1 + d)^2 * CC))⁻¹ • (pp + (1 + d) • cc)))
      = ((Real.sqrt (PP - (1 + d)^2 * CC))⁻¹)^2 * (-A + (1 + d)^2 * B) := by
    simp only [Matrix.mulVec_smul, Work.Mostow.mform_smul_left, Work.Mostow.mform_smul_right, hv]
    ring
  rw [h3, hw]
  have hDpos : (0:ℝ) < PP - (1 + d)^2 * CC := hden
  -- the elementary estimate: `((1+d)^2 - 1) * (B(1+CC) - A·CC) < 0`
  have hv1 : (0:ℝ) < (1 + d)^2 - 1 := by nlinarith [hd, sq_nonneg d]
  have hA1 : (0:ℝ) < (A - B - 1) * CC := mul_pos (by linarith [hA]) hCCpos
  have hu : B * (1 + CC) - A * CC < 0 := by nlinarith [hA1, hB]
  have hprod : ((1 + d)^2 - 1) * (B * (1 + CC) - A * CC) < 0 :=
    mul_neg_of_pos_of_neg hv1 hu
  have hX : -A + (1 + d)^2 * B < (B - A) * (1 - ((1 + d)^2 - 1) * CC) := by
    nlinarith [hprod]
  have hppD : PP - (1 + d)^2 * CC = 1 - ((1 + d)^2 - 1) * CC := by nlinarith [hPP]
  have hDpos' : (0:ℝ) < 1 - ((1 + d)^2 - 1) * CC := by rw [← hppD]; exact hDpos
  have hsq : ((Real.sqrt (PP - (1 + d)^2 * CC))⁻¹)^2 = (PP - (1 + d)^2 * CC)⁻¹ := by
    rw [inv_pow, Real.sq_sqrt (le_of_lt hDpos)]
  rw [hsq, inv_mul_eq_div, hppD]
  exact (div_lt_iff₀ hDpos').mpr hX

end Work.Mostow
