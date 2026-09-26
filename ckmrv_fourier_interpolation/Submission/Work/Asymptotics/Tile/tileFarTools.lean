/-
# Tools for the far-window work (reachable half of the workspace)

`tileWinDefs` (and thus every consumer of `TileBelowPoleFar`) lives on the `EtailE/Assembly`
side of the workspace's duplicate-declaration split, so several one-line bridges that exist in
the unreachable half must be re-stated here.  This file provides two of them:

* `Aexp_Gcusp_eq_Gfun'` — `Aexp (Gcusp ℓ d) τ t = Gfun d ℓ τ (i t)`, from
  `EtailE/Assembly.Aexp_Gcoef'` and `EtailE/Assembly.Gcusp_eq_Gcoef` (the unreachable
  `Asymptotics.ETailE_one.Aexp_Gcusp_eq_Gfun` is the same statement);
* `scale_S_smul_le_KEpsilon` — `scale (S • w) ≤ 3 * scale w` for `w ∈ E = KEpsilon`
  (the unreachable `Asymptotics.Epoly_scale_S_smul_le`).
-/
import Mathlib
import Submission.Work.Asymptotics.KEpsilon
import Submission.Work.Kernels.Kernels
import Submission.Work.Asymptotics.GcuspDefs
import Submission.Work.Asymptotics.Compact.tailDefs
import Submission.Work.Asymptotics.EtailE.Assembly

namespace Work.Asymptotics.Tile

open UpperHalfPlane ModularGroup
open scoped MatrixGroups UpperHalfPlane

noncomputable section

/-- **`Aexp (Gcusp ℓ d)` is the cusp model `Gfun` on the contour.** -/
theorem Aexp_Gcusp_eq_Gfun' (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    (τ : UpperHalfPlane) (t : ℝ) (ht : 0 < t) :
    Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t
      = Work.Asymptotics.Compact.Gfun d ℓ τ (Work.Kernels.imagAxis t ht) := by
  rw [Work.Asymptotics.Gcusp_eq_Gcoef ℓ d hd]
  exact Work.Asymptotics.Aexp_Gcoef' ℓ d τ t ht

/-- `‖S • τ‖ = 1 / ‖τ‖`. -/
lemma norm_coe_S_smul' (τ : ℍ) :
    ‖(((ModularGroup.S • τ : ℍ)) : ℂ)‖ = (‖(τ : ℂ)‖)⁻¹ := by
  rw [Work.Kernels.S_smul_coe, norm_neg, norm_inv]

/-- `Im (S • τ) = Im τ / ‖τ‖²`. -/
lemma im_S_smul' (τ : ℍ) : (ModularGroup.S • τ).im = τ.im / ‖(τ : ℂ)‖ ^ 2 := by
  rw [Work.Kernels.im_smul_eq]
  have hj : Work.Kernels.jFun ModularGroup.S (τ : ℂ) = (τ : ℂ) := by
    rw [Work.Kernels.jFun_apply]; simp
  rw [hj]

/-- **`scale (S • w) ≤ 3 scale w` on `E = KEpsilon`.** -/
theorem scale_S_smul_le_KEpsilon {w : UpperHalfPlane} (hw : w ∈ Work.Asymptotics.KEpsilon) :
    Work.Kernels.scale (ModularGroup.S • w) ≤ 3 * Work.Kernels.scale w := by
  have hspos : 0 < Work.Kernels.scale w := Work.Kernels.scale_pos w
  have h1s : (1 : ℝ) ≤ Work.Kernels.scale w := Work.Kernels.one_le_scale w
  have him : (ModularGroup.S • w).im = w.im / ‖(w : ℂ)‖ ^ 2 := im_S_smul' w
  have hnorm : ‖(((ModularGroup.S • w : ℍ)) : ℂ)‖ = (‖(w : ℂ)‖)⁻¹ := norm_coe_S_smul' w
  -- `|w| ≤ 1/2` from `2 ≤ Im (S • w) = Im w / |w|²`
  have hw2 : (2 : ℝ) ≤ (ModularGroup.S • w).im := hw.2
  have hnormpos : 0 < ‖(w : ℂ)‖ := by
    have := w.im_pos
    exact lt_of_lt_of_le this (Work.Kernels.im_le_coe_norm w)
  have hkey : 2 * ‖(w : ℂ)‖ ^ 2 ≤ w.im := by
    rw [him] at hw2
    rw [le_div_iff₀ (by positivity : (0:ℝ) < ‖(w : ℂ)‖ ^ 2)] at hw2
    linarith
  have hwle : ‖(w : ℂ)‖ ≤ 1 / 2 := by
    have himle : w.im ≤ ‖(w : ℂ)‖ := Work.Kernels.im_le_coe_norm w
    nlinarith [hnormpos, hkey, himle, sq_nonneg (‖(w : ℂ)‖ - 1 / 4)]
  have himpos : 0 < w.im := w.im_pos
  have hinv1 : (w.im)⁻¹ ≤ Work.Kernels.scale w := Work.Kernels.inv_im_le_scale w
  -- each summand of `scale (S • w) = 1 + (Im (S•w))⁻¹ + ‖S•w‖` is `≤ scale w`
  have hA : (1 : ℝ) ≤ Work.Kernels.scale w := h1s
  have hB : ((ModularGroup.S • w).im)⁻¹ ≤ Work.Kernels.scale w := by
    rw [him, inv_div, div_eq_mul_inv]
    have h1 : ‖(w : ℂ)‖ ^ 2 * (w.im)⁻¹ ≤ (1 / 2 : ℝ) * (w.im)⁻¹ := by
      refine mul_le_mul_of_nonneg_right ?_ (inv_nonneg.mpr himpos.le)
      nlinarith [hwle, hnormpos.le]
    have h2 : (1 / 2 : ℝ) * (w.im)⁻¹ ≤ (w.im)⁻¹ := by
      have := inv_nonneg.mpr himpos.le
      linarith
    linarith [h1, h2, hinv1]
  have hC : ‖(((ModularGroup.S • w : ℍ)) : ℂ)‖ ≤ Work.Kernels.scale w := by
    rw [hnorm]
    have h2 : (‖(w : ℂ)‖)⁻¹ ≤ (w.im)⁻¹ := inv_anti₀ himpos (Work.Kernels.im_le_coe_norm w)
    linarith [hinv1]
  calc Work.Kernels.scale (ModularGroup.S • w)
      = 1 + ((ModularGroup.S • w).im)⁻¹ + ‖(((ModularGroup.S • w : ℍ)) : ℂ)‖ := rfl
    _ ≤ Work.Kernels.scale w + Work.Kernels.scale w + Work.Kernels.scale w := by linarith
    _ = 3 * Work.Kernels.scale w := by ring

end

end Work.Asymptotics.Tile
