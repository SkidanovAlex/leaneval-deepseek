import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BoseBoxFock.chiChi_latPer3_eq_wLoc_add
import Submission.Work.BoseBoxFock.pairRowS2Row
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock

theorem K1lim_sub_chiChiImages {ℓ R : ℝ} (hℓ : 0 < ℓ) {W : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hW : ∀ z : EuclideanSpace ℝ (Fin 3), R < ‖z‖ → W z = 0) (w y : EuclideanSpace ℝ (Fin 3)) :
    Work.BoseBoxFock.K1lim ℓ W w y
        - Work.BoseBoxFock.chiChiImages ℓ (fun z => ((W z : ℝ) : ℂ)) w y
      = ((ℓ ^ 3 : ℝ)⁻¹ : ℂ) *
          ( ((ℓ ^ 3 : ℝ) : ℂ) * (((Submission.BoseGases.chiScale ℓ w : ℝ)) : ℂ)
              * ((W (w - y) : ℝ) : ℂ)
              * (((Submission.BoseGases.chiScale ℓ y : ℝ)) : ℂ)
            - (((Submission.BoseGases.chiScale ℓ w : ℝ)) : ℂ)
                * Work.BoseK15.corpusBox.thetaFun ℓ y * Work.BoseBoxFock.pinQBl ℓ W w
            - Work.BoseK15.corpusBox.thetaFun ℓ w
                * (((Submission.BoseGases.chiScale ℓ y : ℝ)) : ℂ) * Work.BoseBoxFock.pinQCl ℓ W y
            + Work.BoseK15.corpusBox.thetaFun ℓ w
                * Work.BoseK15.corpusBox.thetaFun ℓ y * Work.BoseBoxFock.pinQDl ℓ W) := by
  -- `K1lim` is `ℓ⁻³` times the four-term bracket; the `χχ` row of the bracket is
  -- `ℓ³ · Σ'_m W(w−y+ℓ•latVec m)` (the periodisation), and `chiChiImages` is the same
  -- series with its `m = 0` term removed.  Splitting off the `m = 0` term therefore leaves
  -- exactly `ℓ³ · W(w−y)` in the `χχ` row, which the outer `ℓ⁻³` turns into `W(w−y)`;
  -- the three `θ`-rows cancel against themselves, since `chiChiImages` has no `θ`-part.
  have hsum : Summable (fun m : Fin 3 → ℤ => ((W (w - y + ℓ • latVec m) : ℝ) : ℂ)) := by
    refine summable_of_hasFiniteSupport
      ((LatFourier.finite_latVec_norm_le ((R + ‖w - y‖) / ℓ)).subset ?_)
    intro m hm
    rw [Function.mem_support] at hm
    simp only [Set.mem_ofPred_eq]
    by_contra hcon
    rw [not_le] at hcon
    have hnorm : (R + ‖w - y‖) < ℓ * ‖latVec m‖ := by
      rw [div_lt_iff₀ hℓ] at hcon; linarith
    have hz : R < ‖w - y + ℓ • latVec m‖ := by
      have h1 : ℓ * ‖latVec m‖ ≤ ‖w - y + ℓ • latVec m‖ + ‖w - y‖ := by
        calc ℓ * ‖latVec m‖ = ‖ℓ • latVec m‖ := by rw [norm_smul, Real.norm_of_nonneg hℓ.le]
          _ = ‖(w - y + ℓ • latVec m) - (w - y)‖ := by congr 1; abel
          _ ≤ _ := norm_sub_le _ _
      linarith
    exact hm (by simp [hW _ hz])
  have hsplit := hsum.tsum_eq_add_tsum_ite (0 : Fin 3 → ℤ)
  -- the two spellings of `(ℓ³)⁻¹ : ℂ` (real inverse, then coercion vs. complex inverse)
  have hcoe : ((ℓ ^ 3 : ℝ)⁻¹ : ℂ) = (((ℓ ^ 3 : ℝ)⁻¹ : ℝ) : ℂ) := by
    rw [← Complex.ofReal_inv]
  have hce : (((ℓ ^ 3 : ℝ)⁻¹ : ℝ) : ℂ) * (((ℓ ^ 3 : ℝ)) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, inv_mul_cancel₀ (pow_ne_zero 3 (ne_of_gt hℓ)), Complex.ofReal_one]
  rw [K1lim, chiChiImages, latPer3, LatFourier.latPer, hsplit]
  simp only [LatFourier.latVec_zero, smul_zero, add_zero]
  rw [hcoe]
  linear_combination ((((Submission.BoseGases.chiScale ℓ w : ℝ) : ℂ)
      * ((Submission.BoseGases.chiScale ℓ y : ℝ) : ℂ)
      * (∑' m : Fin 3 → ℤ, if m = 0 then (0 : ℂ)
          else ((W (w - y + ℓ • latVec m) : ℝ) : ℂ)))) * hce

end Work.BoseBoxFock
