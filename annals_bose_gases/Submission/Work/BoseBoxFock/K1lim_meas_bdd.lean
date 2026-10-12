import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Topology.UniformSpace.Uniformizable
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Constructions.BorelSpace.Complex
import Mathlib.MeasureTheory.Constructions.Polish.Basic
import Submission.Work.BoseBoxFock.err_aesm_bdd
import Submission.Work.BoseBoxFock.latPer_bdd_global
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.K1lim_meas_bdd` — measurability and global boundedness of the limit kernel

`K1lim ℓ W` is the four-term limit pair kernel of the FS `Q₂` row (`pinQLimDefs`): the `χχ`-row
carries the periodisation `latPer3 ℓ W (w − y)`, the three `χ̂`-rows the absolutely convergent
lattice series `pinQBl/pinQCl/pinQDl`, and all four are multiplied by the box cutoff `χ_ℓ`
(`chiScale`) and the sharp box indicator `θ_Λ` (`thetaFun`).

This file proves that the *uncurried* kernel

    `(w,y) ↦ K1lim ℓ W w y`

is (jointly) measurable when `W` is, and that it is bounded uniformly in `(w,y)` when `W` is
bounded with compact support.  The two ingredients of the bound are:

* `latPer_bdd_global` — the periodisation of a bounded, compactly supported weight is bounded on
  *all* of `ℝ³` (not only on the box cube); the three `χ̂`-series are bounded for *every* `W` by
  `errBdd_pinQBl_bdd` / `errBdd_pinQCl_bdd` / `errBdd_pinQDl_bdd` (their summands decay like
  `(1+‖n‖²)^{-52}` because `χ̂` is Schwartz), so only `W`'s boundedness and support enter;
* `|chiScale ℓ x| ≤ (√chiNormSq)⁻¹` and `‖thetaFun ℓ x‖ ≤ 1` are the two pointwise bounds on the
  cutoffs.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## 1. Measurability -/

/-- The sharp box indicator `θ_Λ` is measurable (it is the indicator of the measurable box
`boxL ℓ`). -/
private lemma thetaFun_measurable_loc (ℓ : ℝ) :
    Measurable (Work.BoseK15.corpusBox.thetaFun ℓ) := by
  have h : Work.BoseK15.corpusBox.thetaFun ℓ
      = Set.indicator (Work.BoseK15.corpusBox.boxL ℓ) (fun _ : E3 => (1 : ℂ)) := by
    funext z
    rw [Work.BoseB4.BoxData.thetaFun_apply]
    by_cases hz : z ∈ Work.BoseK15.corpusBox.boxL ℓ <;> simp [hz]
  rw [h]
  exact measurable_const.indicator (Work.BoseB4.BoxData.boxL_measurableSet _ ℓ)

/-- The periodisation, as a function of the *pair* `(w,y) ↦ latPer ℓ W (w − y)`, is measurable
whenever `W` is: each lattice translate of `W` is measurable, and `Measurable.tsum` needs no
summability. -/
private lemma measurable_latPer_uncurry {ℓ : ℝ} {W : E3 → ℝ} (hWm : Measurable W) :
    Measurable (fun p : E3 × E3 => LatFourier.latPer ℓ W (p.1 - p.2)) := by
  have hterm : ∀ m : Fin 3 → ℤ,
      Measurable (fun p : E3 × E3 => (W (p.1 - p.2 + ℓ • latVec m) : ℂ)) := by
    intro m
    have hg : Continuous (fun p : E3 × E3 => p.1 - p.2 + ℓ • latVec m) := by fun_prop
    exact Complex.continuous_ofReal.measurable.comp (hWm.comp hg.measurable)
  have h := Measurable.tsum (L := SummationFilter.unconditional (Fin 3 → ℤ)) hterm
  simpa only [LatFourier.latPer] using h

/-- The `χχ`-row `latPer3 ℓ W (w − y)` is measurable in the pair `(w,y)`. -/
private lemma measurable_latPer3_uncurry {ℓ : ℝ} {W : E3 → ℝ} (hWm : Measurable W) :
    Measurable (fun p : E3 × E3 => latPer3 ℓ W (p.1 - p.2)) := by
  have h : Measurable (fun p : E3 × E3 =>
      (((ℓ ^ 3 : ℝ)) : ℂ) * LatFourier.latPer ℓ W (p.1 - p.2)) :=
    measurable_const.mul (measurable_latPer_uncurry hWm)
  simpa only [latPer3] using h

/-- A `tsum` of the form `∑' n, F n · e^{i⟪kmomInt ℓ n, w⟫}` is measurable in `w` (each summand is
continuous). -/
private lemma measurable_tsum_exp_phase (ℓ : ℝ) (F : (Fin 3 → ℤ) → ℂ) :
    Measurable (fun w : E3 => ∑' n : Fin 3 → ℤ,
      F n * Complex.exp (Complex.I * ((inner ℝ (kmomInt ℓ n) w : ℝ) : ℂ))) := by
  refine Measurable.tsum (L := SummationFilter.unconditional (Fin 3 → ℤ)) (fun n => ?_)
  have hcont : Continuous (fun w : E3 =>
      F n * Complex.exp (Complex.I * ((inner ℝ (kmomInt ℓ n) w : ℝ) : ℂ))) :=
    Continuous.mul continuous_const (Complex.continuous_exp.comp (Continuous.mul continuous_const
      (Complex.continuous_ofReal.comp (Continuous.inner continuous_const continuous_id))))
  exact hcont.measurable

/-- The `−i`-phase variant of the previous lemma. -/
private lemma measurable_tsum_neg_exp_phase (ℓ : ℝ) (F : (Fin 3 → ℤ) → ℂ) :
    Measurable (fun y : E3 => ∑' n : Fin 3 → ℤ,
      F n * Complex.exp (-(Complex.I * ((inner ℝ (kmomInt ℓ n) y : ℝ) : ℂ)))) := by
  refine Measurable.tsum (L := SummationFilter.unconditional (Fin 3 → ℤ)) (fun n => ?_)
  have hcont : Continuous (fun y : E3 =>
      F n * Complex.exp (-(Complex.I * ((inner ℝ (kmomInt ℓ n) y : ℝ) : ℂ)))) :=
    Continuous.mul continuous_const (Complex.continuous_exp.comp (Continuous.neg
      (Continuous.mul continuous_const (Complex.continuous_ofReal.comp
        (Continuous.inner continuous_const continuous_id)))))
  exact hcont.measurable

/-- `pinQBl ℓ W` is measurable (for every `W`). -/
private lemma measurable_pinQBl (ℓ : ℝ) (W : E3 → ℝ) : Measurable (pinQBl ℓ W) := by
  change Measurable (fun w : E3 => pinQBl ℓ W w)
  have h := measurable_tsum_exp_phase ℓ (fun n : Fin 3 → ℤ =>
      ((Work.BoseFixR.chat W (kmomInt ℓ n) : ℝ) : ℂ)
        * ((Work.BoseK15.corpusBox.hatChi (ℓ • kmomInt ℓ n) : ℝ) : ℂ))
  simpa only [pinQBl] using h

/-- `pinQCl ℓ W` is measurable (for every `W`). -/
private lemma measurable_pinQCl (ℓ : ℝ) (W : E3 → ℝ) : Measurable (pinQCl ℓ W) := by
  change Measurable (fun y : E3 => pinQCl ℓ W y)
  have h := measurable_tsum_neg_exp_phase ℓ (fun n : Fin 3 → ℤ =>
      ((Work.BoseFixR.chat W (kmomInt ℓ n) : ℝ) : ℂ)
        * ((Work.BoseK15.corpusBox.hatChi (ℓ • kmomInt ℓ n) : ℝ) : ℂ))
  simpa only [pinQCl] using h

/-! ## 2. The main theorem -/

theorem K1lim_meas_bdd {ℓ : ℝ} (hℓ : 0 < ℓ) {W : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hWm : Measurable W)
    (hWb : ∃ C : ℝ, ∀ x, ‖W x‖ ≤ C) (hWs : HasCompactSupport W) :
    Measurable (Function.uncurry (Work.BoseBoxFock.K1lim ℓ W))
      ∧ ∃ C : ℝ, ∀ w y : EuclideanSpace ℝ (Fin 3),
          ‖Work.BoseBoxFock.K1lim ℓ W w y‖ ≤ C := by
  constructor
  · -- measurability: each of the four rows is a product of a measurable function of `w`, a
    -- measurable function of `y` and a measurable function of `w - y` (or a `tsum` in one variable)
    have hlat : Measurable (fun p : E3 × E3 => latPer3 ℓ W (p.1 - p.2)) :=
      measurable_latPer3_uncurry hWm
    have hchi1 : Measurable (fun p : E3 × E3 =>
        (((Submission.BoseGases.chiScale ℓ p.1 : ℝ)) : ℂ)) :=
      Complex.continuous_ofReal.measurable.comp
        ((Submission.BoseGases.chiScale_continuous ℓ).measurable.comp continuous_fst.measurable)
    have hchi2 : Measurable (fun p : E3 × E3 =>
        (((Submission.BoseGases.chiScale ℓ p.2 : ℝ)) : ℂ)) :=
      Complex.continuous_ofReal.measurable.comp
        ((Submission.BoseGases.chiScale_continuous ℓ).measurable.comp continuous_snd.measurable)
    have hth1 : Measurable (fun p : E3 × E3 =>
        Work.BoseK15.corpusBox.thetaFun ℓ p.1) :=
      (thetaFun_measurable_loc ℓ).comp continuous_fst.measurable
    have hth2 : Measurable (fun p : E3 × E3 =>
        Work.BoseK15.corpusBox.thetaFun ℓ p.2) :=
      (thetaFun_measurable_loc ℓ).comp continuous_snd.measurable
    have hB : Measurable (fun p : E3 × E3 => pinQBl ℓ W p.1) :=
      (measurable_pinQBl ℓ W).comp continuous_fst.measurable
    have hC : Measurable (fun p : E3 × E3 => pinQCl ℓ W p.2) :=
      (measurable_pinQCl ℓ W).comp continuous_snd.measurable
    have hD : Measurable (fun _ : E3 × E3 => pinQDl ℓ W) := measurable_const
    have h1 : Measurable (fun p : E3 × E3 =>
        (((Submission.BoseGases.chiScale ℓ p.1 : ℝ)) : ℂ)
          * (((Submission.BoseGases.chiScale ℓ p.2 : ℝ)) : ℂ)
          * latPer3 ℓ W (p.1 - p.2)) := (hchi1.mul hchi2).mul hlat
    have h2 : Measurable (fun p : E3 × E3 =>
        (((Submission.BoseGases.chiScale ℓ p.1 : ℝ)) : ℂ)
          * Work.BoseK15.corpusBox.thetaFun ℓ p.2 * pinQBl ℓ W p.1) :=
      (hchi1.mul hth2).mul hB
    have h3 : Measurable (fun p : E3 × E3 =>
        Work.BoseK15.corpusBox.thetaFun ℓ p.1
          * (((Submission.BoseGases.chiScale ℓ p.2 : ℝ)) : ℂ) * pinQCl ℓ W p.2) :=
      (hth1.mul hchi2).mul hC
    have h4 : Measurable (fun p : E3 × E3 =>
        Work.BoseK15.corpusBox.thetaFun ℓ p.1
          * Work.BoseK15.corpusBox.thetaFun ℓ p.2 * pinQDl ℓ W) :=
      (hth1.mul hth2).mul hD
    have hmain : Measurable (fun p : E3 × E3 =>
        (((Submission.BoseGases.chiScale ℓ p.1 : ℝ)) : ℂ)
            * (((Submission.BoseGases.chiScale ℓ p.2 : ℝ)) : ℂ)
            * latPer3 ℓ W (p.1 - p.2)
          - (((Submission.BoseGases.chiScale ℓ p.1 : ℝ)) : ℂ)
            * Work.BoseK15.corpusBox.thetaFun ℓ p.2 * pinQBl ℓ W p.1
          - Work.BoseK15.corpusBox.thetaFun ℓ p.1
            * (((Submission.BoseGases.chiScale ℓ p.2 : ℝ)) : ℂ) * pinQCl ℓ W p.2
          + Work.BoseK15.corpusBox.thetaFun ℓ p.1
            * Work.BoseK15.corpusBox.thetaFun ℓ p.2 * pinQDl ℓ W) :=
      ((h1.sub h2).sub h3).add h4
    have hprod : Measurable (fun p : E3 × E3 =>
        (((ℓ ^ 3)⁻¹ : ℝ) : ℂ) *
          ((((Submission.BoseGases.chiScale ℓ p.1 : ℝ)) : ℂ)
              * (((Submission.BoseGases.chiScale ℓ p.2 : ℝ)) : ℂ)
              * latPer3 ℓ W (p.1 - p.2)
            - (((Submission.BoseGases.chiScale ℓ p.1 : ℝ)) : ℂ)
              * Work.BoseK15.corpusBox.thetaFun ℓ p.2 * pinQBl ℓ W p.1
            - Work.BoseK15.corpusBox.thetaFun ℓ p.1
              * (((Submission.BoseGases.chiScale ℓ p.2 : ℝ)) : ℂ) * pinQCl ℓ W p.2
            + Work.BoseK15.corpusBox.thetaFun ℓ p.1
              * Work.BoseK15.corpusBox.thetaFun ℓ p.2 * pinQDl ℓ W)) :=
      measurable_const.mul hmain
    have hun : Function.uncurry (K1lim ℓ W)
        = fun p : E3 × E3 => K1lim ℓ W p.1 p.2 := rfl
    rw [hun]
    simpa only [K1lim] using hprod
  · -- boundedness
    -- pointwise vanishing of `W` outside a ball, from the compactness of its support
    obtain ⟨R, hR⟩ : ∃ R : ℝ, ∀ x : E3, R < ‖x‖ → W x = 0 := by
      obtain ⟨K, hKc, hK⟩ := exists_compact_iff_hasCompactSupport.mpr hWs
      obtain ⟨R, hR⟩ := hKc.isBounded.subset_closedBall (0 : E3)
      refine ⟨R, fun x hx => hK x fun hxK => ?_⟩
      have hx' : ‖x‖ ≤ R := by
        have := hR hxK
        rwa [Metric.mem_closedBall, dist_eq_norm, sub_zero] at this
      exact absurd hx' (not_le.mpr hx)
    obtain ⟨D, hD0, hD⟩ := latPer_bdd_global hℓ hWb hR
    have hD3 : ∀ z : E3, ‖latPer3 ℓ W z‖ ≤ ‖(((ℓ ^ 3 : ℝ)) : ℂ)‖ * D := by
      intro z
      rw [latPer3, norm_mul]
      exact mul_le_mul_of_nonneg_left (hD z) (norm_nonneg _)
    obtain ⟨CB, hCB0, hCB⟩ := errBdd_pinQBl_bdd hℓ W
    obtain ⟨CC, hCC0, hCC⟩ := errBdd_pinQCl_bdd hℓ W
    obtain ⟨CD, hCD0, hCD⟩ := errBdd_pinQDl_bdd hℓ W
    -- bounds on the two cutoffs
    obtain ⟨Mchi, hMchi0, hchi⟩ : ∃ M : ℝ, 0 ≤ M ∧ ∀ w : E3,
        ‖(((Submission.BoseGases.chiScale ℓ w : ℝ)) : ℂ)‖ ≤ M := by
      refine ⟨(Real.sqrt Submission.BoseGases.chiNormSq)⁻¹,
        inv_nonneg.mpr (Real.sqrt_nonneg _), fun w => ?_⟩
      have hnn : 0 ≤ Submission.BoseGases.chiScale ℓ w :=
        Submission.BoseGases.chi_nonneg ((ℓ⁻¹) • w)
      rw [errBdd_norm_ofReal, abs_of_nonneg hnn]
      exact Submission.BoseGases.chi_le_sqrt_inv ((ℓ⁻¹) • w)
    have hth : ∀ z : E3, ‖Work.BoseK15.corpusBox.thetaFun ℓ z‖ ≤ 1 := by
      intro z
      rw [Work.BoseB4.BoxData.thetaFun_apply]
      split <;> simp
    refine ⟨|(ℓ ^ 3)⁻¹| * (((Mchi * Mchi * (‖(((ℓ ^ 3 : ℝ)) : ℂ)‖ * D) + Mchi * 1 * CB)
      + 1 * Mchi * CC) + 1 * 1 * CD), fun w y => ?_⟩
    have hA : ‖(((Submission.BoseGases.chiScale ℓ w : ℝ)) : ℂ)
        * (((Submission.BoseGases.chiScale ℓ y : ℝ)) : ℂ)
        * latPer3 ℓ W (w - y)‖ ≤ Mchi * Mchi * (‖(((ℓ ^ 3 : ℝ)) : ℂ)‖ * D) := by
      rw [norm_mul, norm_mul]
      exact mul_le_mul (mul_le_mul (hchi w) (hchi y) (norm_nonneg _) hMchi0)
        (hD3 (w - y)) (norm_nonneg _) (mul_nonneg hMchi0 hMchi0)
    have hB : ‖(((Submission.BoseGases.chiScale ℓ w : ℝ)) : ℂ)
        * Work.BoseK15.corpusBox.thetaFun ℓ y * pinQBl ℓ W w‖ ≤ Mchi * 1 * CB := by
      rw [norm_mul, norm_mul]
      exact mul_le_mul (mul_le_mul (hchi w) (hth y) (norm_nonneg _) hMchi0)
        (hCB w) (norm_nonneg _) (mul_nonneg hMchi0 zero_le_one)
    have hC : ‖Work.BoseK15.corpusBox.thetaFun ℓ w
        * (((Submission.BoseGases.chiScale ℓ y : ℝ)) : ℂ) * pinQCl ℓ W y‖
        ≤ 1 * Mchi * CC := by
      rw [norm_mul, norm_mul]
      exact mul_le_mul (mul_le_mul (hth w) (hchi y) (norm_nonneg _) zero_le_one)
        (hCC y) (norm_nonneg _) (mul_nonneg zero_le_one hMchi0)
    have hD' : ‖Work.BoseK15.corpusBox.thetaFun ℓ w
        * Work.BoseK15.corpusBox.thetaFun ℓ y * pinQDl ℓ W‖ ≤ 1 * 1 * CD := by
      rw [norm_mul, norm_mul]
      exact mul_le_mul (mul_le_mul (hth w) (hth y) (norm_nonneg _) zero_le_one)
        hCD (norm_nonneg _) (mul_nonneg zero_le_one zero_le_one)
    have hbody : ‖(((Submission.BoseGases.chiScale ℓ w : ℝ)) : ℂ)
          * (((Submission.BoseGases.chiScale ℓ y : ℝ)) : ℂ) * latPer3 ℓ W (w - y)
        - (((Submission.BoseGases.chiScale ℓ w : ℝ)) : ℂ)
          * Work.BoseK15.corpusBox.thetaFun ℓ y * pinQBl ℓ W w
        - Work.BoseK15.corpusBox.thetaFun ℓ w
          * (((Submission.BoseGases.chiScale ℓ y : ℝ)) : ℂ) * pinQCl ℓ W y
        + Work.BoseK15.corpusBox.thetaFun ℓ w
          * Work.BoseK15.corpusBox.thetaFun ℓ y * pinQDl ℓ W‖
        ≤ ((Mchi * Mchi * (‖(((ℓ ^ 3 : ℝ)) : ℂ)‖ * D) + Mchi * 1 * CB)
            + 1 * Mchi * CC) + 1 * 1 * CD := by
      have h5 : ‖(((Submission.BoseGases.chiScale ℓ w : ℝ)) : ℂ)
            * (((Submission.BoseGases.chiScale ℓ y : ℝ)) : ℂ) * latPer3 ℓ W (w - y)
          - (((Submission.BoseGases.chiScale ℓ w : ℝ)) : ℂ)
            * Work.BoseK15.corpusBox.thetaFun ℓ y * pinQBl ℓ W w
          - Work.BoseK15.corpusBox.thetaFun ℓ w
            * (((Submission.BoseGases.chiScale ℓ y : ℝ)) : ℂ) * pinQCl ℓ W y‖
          ≤ (Mchi * Mchi * (‖(((ℓ ^ 3 : ℝ)) : ℂ)‖ * D) + Mchi * 1 * CB)
            + 1 * Mchi * CC := by
        have h6 : ‖(((Submission.BoseGases.chiScale ℓ w : ℝ)) : ℂ)
              * (((Submission.BoseGases.chiScale ℓ y : ℝ)) : ℂ) * latPer3 ℓ W (w - y)
            - (((Submission.BoseGases.chiScale ℓ w : ℝ)) : ℂ)
              * Work.BoseK15.corpusBox.thetaFun ℓ y * pinQBl ℓ W w‖
            ≤ Mchi * Mchi * (‖(((ℓ ^ 3 : ℝ)) : ℂ)‖ * D) + Mchi * 1 * CB := by
          linarith [norm_sub_le ((((Submission.BoseGases.chiScale ℓ w : ℝ)) : ℂ)
              * (((Submission.BoseGases.chiScale ℓ y : ℝ)) : ℂ) * latPer3 ℓ W (w - y))
            ((((Submission.BoseGases.chiScale ℓ w : ℝ)) : ℂ)
              * Work.BoseK15.corpusBox.thetaFun ℓ y * pinQBl ℓ W w), hA, hB]
        linarith [norm_sub_le ((((Submission.BoseGases.chiScale ℓ w : ℝ)) : ℂ)
            * (((Submission.BoseGases.chiScale ℓ y : ℝ)) : ℂ) * latPer3 ℓ W (w - y)
          - (((Submission.BoseGases.chiScale ℓ w : ℝ)) : ℂ)
            * Work.BoseK15.corpusBox.thetaFun ℓ y * pinQBl ℓ W w)
          (Work.BoseK15.corpusBox.thetaFun ℓ w
            * (((Submission.BoseGases.chiScale ℓ y : ℝ)) : ℂ) * pinQCl ℓ W y), h6, hC]
      linarith [norm_add_le ((((Submission.BoseGases.chiScale ℓ w : ℝ)) : ℂ)
            * (((Submission.BoseGases.chiScale ℓ y : ℝ)) : ℂ) * latPer3 ℓ W (w - y)
          - (((Submission.BoseGases.chiScale ℓ w : ℝ)) : ℂ)
            * Work.BoseK15.corpusBox.thetaFun ℓ y * pinQBl ℓ W w
          - Work.BoseK15.corpusBox.thetaFun ℓ w
            * (((Submission.BoseGases.chiScale ℓ y : ℝ)) : ℂ) * pinQCl ℓ W y)
          (Work.BoseK15.corpusBox.thetaFun ℓ w
            * Work.BoseK15.corpusBox.thetaFun ℓ y * pinQDl ℓ W), h5, hD']
    calc ‖Work.BoseBoxFock.K1lim ℓ W w y‖
        = ‖(((ℓ ^ 3)⁻¹ : ℝ) : ℂ)‖ * ‖(((Submission.BoseGases.chiScale ℓ w : ℝ)) : ℂ)
            * (((Submission.BoseGases.chiScale ℓ y : ℝ)) : ℂ) * latPer3 ℓ W (w - y)
          - (((Submission.BoseGases.chiScale ℓ w : ℝ)) : ℂ)
            * Work.BoseK15.corpusBox.thetaFun ℓ y * pinQBl ℓ W w
          - Work.BoseK15.corpusBox.thetaFun ℓ w
            * (((Submission.BoseGases.chiScale ℓ y : ℝ)) : ℂ) * pinQCl ℓ W y
          + Work.BoseK15.corpusBox.thetaFun ℓ w
            * Work.BoseK15.corpusBox.thetaFun ℓ y * pinQDl ℓ W‖ := by
          rw [K1lim, norm_mul]
      _ ≤ |(ℓ ^ 3)⁻¹| * (((Mchi * Mchi * (‖(((ℓ ^ 3 : ℝ)) : ℂ)‖ * D) + Mchi * 1 * CB)
            + 1 * Mchi * CC) + 1 * 1 * CD) := by
          rw [errBdd_norm_ofReal]
          exact mul_le_mul_of_nonneg_left hbody (abs_nonneg _)

end Work.BoseBoxFock
