import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Submission.Work.BoseBoxFock.block13_Ksub_state
import Submission.Work.BoseBoxFock.err_aesm_bdd
import Submission.Work.BoseBoxFock.pairG21_bounded
import Submission.Work.BoseBoxFock.pairG21_kernel_integrable
import Submission.Work.BoseBoxFock.pairG21_measurable
import Submission.Work.BoseBoxFock.pairG23_bounded
import Submission.Work.BoseBoxFock.pairRowS2Row
import Submission.Work.BoseBoxFock.phi23_bound_support
import Submission.Work.BoseBoxFock.qVecFrameWeighted
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.K1exp_meas_bdd` — measurability and global boundedness of the
expanded pair kernel

`K1exp v μ N c` is the four-term expanded honest pair kernel of the FS `Q₂` row
(`pinQ_kernel_expansion`): its `χχ` row is the *finite* lattice sum `pinQA v μ N c (w - y)`,
the two `χ̂` rows are the finite sums `pinQB`/`pinQC` (`w`- and `y`-wise) and the `θθ` row the
constant `pinQD`, all four multiplied by the box cutoff `χ_ℓ` (`chiScale`) and the sharp box
indicator `θ_Λ` (`thetaFun`).

This file proves that the uncurried kernel `(w,y) ↦ K1exp v μ N c w y` is jointly measurable,
and globally bounded in `(w,y)`:

* measurability: each of the three cutoffs is measurable (`chiScale` is continuous,
  `thetaFun` is the indicator of the measurable box `boxL ℓ`) and each lattice row is continuous
  in its variable (`errBdd_pinQA_cont`, `errBdd_pinQB_cont`, `errBdd_pinQC_cont`); `pinQD` is
  constant.  The four products/subtractions are therefore measurable in `(w,y)`.
* boundedness: `|chiScale ℓ x| ≤ (√chiNormSq)⁻¹` (`abs_chiScale_le`), `‖thetaFun ℓ x‖ ≤ 1`
  (`norm_thetaFun_le`), and the three `χ̂`-rows are bounded by the finite row count
  (`errBdd_pinQA_bdd`, `errBdd_pinQB_bdd`, `errBdd_pinQC_bdd`, `errBdd_pinQD_bdd`); the phases
  `e^{±i⟪κ_k,·⟫}` are unimodular.  No compact support or a.e.-argument is needed — the sums are
  finite.
-/

namespace Work.BoseBoxFock

open MeasureTheory
open scoped BigOperators

local notation "E3" => EuclideanSpace ℝ (Fin 3)

theorem K1exp_meas_bdd {v : EuclideanSpace ℝ (Fin 3) → ℝ} {μ : ℝ} {N : ℕ}
    (c : Work.BoseBoxFock.Lab N → ℝ) :
    Measurable (Function.uncurry (Work.BoseBoxFock.K1exp v μ N c))
      ∧ ∃ C : ℝ, ∀ w y : EuclideanSpace ℝ (Fin 3),
          ‖Work.BoseBoxFock.K1exp v μ N c w y‖ ≤ C := by
  constructor
  · show Measurable (fun p : E3 × E3 => K1exp v μ N c p.1 p.2)
    simp only [K1exp]
    refine measurable_const.mul ?_
    have hchi1 : Measurable (fun p : E3 × E3 =>
        (((Submission.BoseGases.chiScale (ellH v μ) p.1 : ℝ)) : ℂ)) :=
      Complex.continuous_ofReal.measurable.comp
        ((Submission.BoseGases.chiScale_continuous (ellH v μ)).measurable.comp
          continuous_fst.measurable)
    have hchi2 : Measurable (fun p : E3 × E3 =>
        (((Submission.BoseGases.chiScale (ellH v μ) p.2 : ℝ)) : ℂ)) :=
      Complex.continuous_ofReal.measurable.comp
        ((Submission.BoseGases.chiScale_continuous (ellH v μ)).measurable.comp
          continuous_snd.measurable)
    have hth1 : Measurable (fun p : E3 × E3 =>
        Work.BoseK15.corpusBox.thetaFun (ellH v μ) p.1) :=
      (measurable_thetaFun (ellH v μ)).comp continuous_fst.measurable
    have hth2 : Measurable (fun p : E3 × E3 =>
        Work.BoseK15.corpusBox.thetaFun (ellH v μ) p.2) :=
      (measurable_thetaFun (ellH v μ)).comp continuous_snd.measurable
    have hQA : Measurable (fun p : E3 × E3 => pinQA v μ N c (p.1 - p.2)) :=
      (errBdd_pinQA_cont c).measurable.comp (continuous_fst.sub continuous_snd).measurable
    have hQB : Measurable (fun p : E3 × E3 => pinQB v μ N c p.1) :=
      (errBdd_pinQB_cont c).measurable.comp continuous_fst.measurable
    have hQC : Measurable (fun p : E3 × E3 => pinQC v μ N c p.2) :=
      (errBdd_pinQC_cont c).measurable.comp continuous_snd.measurable
    have hQD : Measurable (fun _ : E3 × E3 => pinQD v μ N c) := measurable_const
    exact ((((hchi1.mul hchi2).mul hQA).sub ((hchi1.mul hth2).mul hQB)).sub
      ((hth1.mul hchi2).mul hQC)).add ((hth1.mul hth2).mul hQD)
  · -- boundedness: a uniform bound for `|c k|`, then the four row bounds
    obtain ⟨B, hB0, hB⟩ : ∃ B : ℝ, 0 ≤ B ∧ ∀ k : Lab N, |c k| ≤ B := by
      refine ⟨∑ k : Lab N, |c k|, Finset.sum_nonneg (fun k _ => abs_nonneg _), ?_⟩
      intro k
      exact Finset.single_le_sum (f := fun k : Lab N => |c k|) (fun j _ => abs_nonneg _)
        (Finset.mem_univ k)
    obtain ⟨CA, hCA0, hCA⟩ := errBdd_pinQA_bdd (v := v) (μ := μ) (N := N) (c := c) hB0 hB
    obtain ⟨CB, hCB0, hCB⟩ := errBdd_pinQB_bdd (v := v) (μ := μ) (N := N) (c := c) hB0 hB
    obtain ⟨CC, hCC0, hCC⟩ := errBdd_pinQC_bdd (v := v) (μ := μ) (N := N) (c := c) hB0 hB
    obtain ⟨CD, hCD0, hCD⟩ := errBdd_pinQD_bdd (v := v) (μ := μ) (N := N) (c := c) hB0 hB
    set M : ℝ := (Real.sqrt Submission.BoseGases.chiNormSq)⁻¹ with hMdef
    have hM0 : 0 ≤ M := by
      rw [hMdef]; exact inv_nonneg.mpr (Real.sqrt_nonneg _)
    have hchi : ∀ x : E3, ‖(((Submission.BoseGases.chiScale (ellH v μ) x : ℝ)) : ℂ)‖ ≤ M := by
      intro x
      rw [hMdef, errBdd_norm_ofReal]
      exact Submission.BoseGases.abs_chiScale_le (ellH v μ) x
    have hth : ∀ x : E3, ‖Work.BoseK15.corpusBox.thetaFun (ellH v μ) x‖ ≤ 1 :=
      fun x => norm_thetaFun_le (ellH v μ) x
    refine ⟨|((ellH v μ) ^ 3)⁻¹| * (((M * M * CA + M * 1 * CB) + 1 * M * CC)
      + 1 * 1 * CD), fun w y => ?_⟩
    rw [K1exp, norm_mul, errBdd_norm_ofReal]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    have hA : ‖(((Submission.BoseGases.chiScale (ellH v μ) w : ℝ)) : ℂ)
        * (((Submission.BoseGases.chiScale (ellH v μ) y : ℝ)) : ℂ)
        * pinQA v μ N c (w - y)‖ ≤ M * M * CA := by
      rw [norm_mul, norm_mul]
      exact mul_le_mul (mul_le_mul (hchi w) (hchi y) (norm_nonneg _) hM0) (hCA (w - y))
        (norm_nonneg _) (mul_nonneg hM0 hM0)
    have hB' : ‖(((Submission.BoseGases.chiScale (ellH v μ) w : ℝ)) : ℂ)
        * Work.BoseK15.corpusBox.thetaFun (ellH v μ) y * pinQB v μ N c w‖ ≤ M * 1 * CB := by
      rw [norm_mul, norm_mul]
      exact mul_le_mul (mul_le_mul (hchi w) (hth y) (norm_nonneg _) hM0) (hCB w)
        (norm_nonneg _) (mul_nonneg hM0 zero_le_one)
    have hC' : ‖Work.BoseK15.corpusBox.thetaFun (ellH v μ) w
        * (((Submission.BoseGases.chiScale (ellH v μ) y : ℝ)) : ℂ)
        * pinQC v μ N c y‖ ≤ 1 * M * CC := by
      rw [norm_mul, norm_mul]
      exact mul_le_mul (mul_le_mul (hth w) (hchi y) (norm_nonneg _) zero_le_one) (hCC y)
        (norm_nonneg _) (mul_nonneg zero_le_one hM0)
    have hD' : ‖Work.BoseK15.corpusBox.thetaFun (ellH v μ) w
        * Work.BoseK15.corpusBox.thetaFun (ellH v μ) y * pinQD v μ N c‖ ≤ 1 * 1 * CD := by
      rw [norm_mul, norm_mul]
      exact mul_le_mul (mul_le_mul (hth w) (hth y) (norm_nonneg _) zero_le_one) hCD
        (norm_nonneg _) (mul_nonneg zero_le_one zero_le_one)
    have h1 : ‖(((Submission.BoseGases.chiScale (ellH v μ) w : ℝ)) : ℂ)
          * (((Submission.BoseGases.chiScale (ellH v μ) y : ℝ)) : ℂ)
          * pinQA v μ N c (w - y)
        - (((Submission.BoseGases.chiScale (ellH v μ) w : ℝ)) : ℂ)
          * Work.BoseK15.corpusBox.thetaFun (ellH v μ) y * pinQB v μ N c w‖
        ≤ M * M * CA + M * 1 * CB := by
      linarith [norm_sub_le ((((Submission.BoseGases.chiScale (ellH v μ) w : ℝ)) : ℂ)
          * (((Submission.BoseGases.chiScale (ellH v μ) y : ℝ)) : ℂ)
          * pinQA v μ N c (w - y))
        ((((Submission.BoseGases.chiScale (ellH v μ) w : ℝ)) : ℂ)
          * Work.BoseK15.corpusBox.thetaFun (ellH v μ) y * pinQB v μ N c w), hA, hB']
    have h2 : ‖(((Submission.BoseGases.chiScale (ellH v μ) w : ℝ)) : ℂ)
          * (((Submission.BoseGases.chiScale (ellH v μ) y : ℝ)) : ℂ)
          * pinQA v μ N c (w - y)
        - (((Submission.BoseGases.chiScale (ellH v μ) w : ℝ)) : ℂ)
          * Work.BoseK15.corpusBox.thetaFun (ellH v μ) y * pinQB v μ N c w
        - Work.BoseK15.corpusBox.thetaFun (ellH v μ) w
          * (((Submission.BoseGases.chiScale (ellH v μ) y : ℝ)) : ℂ) * pinQC v μ N c y‖
        ≤ (M * M * CA + M * 1 * CB) + 1 * M * CC := by
      linarith [norm_sub_le ((((Submission.BoseGases.chiScale (ellH v μ) w : ℝ)) : ℂ)
          * (((Submission.BoseGases.chiScale (ellH v μ) y : ℝ)) : ℂ)
          * pinQA v μ N c (w - y)
        - (((Submission.BoseGases.chiScale (ellH v μ) w : ℝ)) : ℂ)
          * Work.BoseK15.corpusBox.thetaFun (ellH v μ) y * pinQB v μ N c w)
        (Work.BoseK15.corpusBox.thetaFun (ellH v μ) w
          * (((Submission.BoseGases.chiScale (ellH v μ) y : ℝ)) : ℂ) * pinQC v μ N c y),
        h1, hC']
    linarith [norm_add_le ((((Submission.BoseGases.chiScale (ellH v μ) w : ℝ)) : ℂ)
          * (((Submission.BoseGases.chiScale (ellH v μ) y : ℝ)) : ℂ)
          * pinQA v μ N c (w - y)
        - (((Submission.BoseGases.chiScale (ellH v μ) w : ℝ)) : ℂ)
          * Work.BoseK15.corpusBox.thetaFun (ellH v μ) y * pinQB v μ N c w
        - Work.BoseK15.corpusBox.thetaFun (ellH v μ) w
          * (((Submission.BoseGases.chiScale (ellH v μ) y : ℝ)) : ℂ) * pinQC v μ N c y)
        (Work.BoseK15.corpusBox.thetaFun (ellH v μ) w
          * Work.BoseK15.corpusBox.thetaFun (ellH v μ) y * pinQD v μ N c), h2, hD']

end Work.BoseBoxFock
