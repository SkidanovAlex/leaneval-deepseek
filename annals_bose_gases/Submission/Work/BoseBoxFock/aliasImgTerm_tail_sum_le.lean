import Mathlib.Tactic.Have
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.AliasClosedTermAux
import Submission.Work.BoseBoxFock.lattice_sum_inv_fourth_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.aliasImgTerm_tail_sum_le` — the *tail* of the image series

The image series of the closed-ball aliasing chapter,

    ∑_m ∫⁻_u ofReal(‖𝒢(u)‖ · imgW ℓ m u) ,    𝒢 = aliasKernel g ,  imgW ℓ m u = ‖u − ℓ•latVec m‖⁻⁴,

is split into the *low* indices (`‖m‖ ≤ 1`, the 27 translates that can meet the ball `B(0,ℓ)`,
where the autocorrelation vanishes only at a single touching point and the lens bound
`‖𝒢(u)‖ ≤ C(ℓ² − ‖u‖²)^{3/2}` is needed) and the *far* indices (`‖m‖ ≥ 2`).  This file bounds the
**far part**: for an arbitrary finite set `s` of indices with `‖m‖ ≥ 2`,

    ∑_{m ∈ s} aliasImgTerm ℓ g m ≤ ofReal((∫_x ‖g x‖²) · ℓ⁻⁴ · 200) · vol (closedBall 0 ℓ) .

The two ingredients are:

* the **pointwise lattice bound** `aliasImgTerm_imgW_sum_le_aux`: for `‖u‖ ≤ ℓ` and `‖m‖ ≥ 2` the
  reverse triangle inequality gives `‖u − ℓ•latVec m‖ ≥ ℓ(‖m‖ − 1)`, hence
  `∑_{m ∈ s} imgW ℓ m u ≤ ℓ⁻⁴ ∑_{m ∈ s} (‖m‖ − 1)⁻⁴ ≤ 200 ℓ⁻⁴`
  (`Work.BoseBoxFock.lattice_sum_inv_fourth_le`);
* the **pointwise bound on the kernel** `‖𝒢(u)‖ ≤ ∫_x ‖g x‖²` (`AliasAux.autocorr_norm_le`,
  Cauchy–Schwarz) together with the closed-ball vanishing `𝒢(u) = 0` for `ℓ ≤ ‖u‖`
  (`AliasClosedAux.autocorr_eq_zero_of_le_norm_closed`), which confines the `u`-integral to the
  ball `closedBall 0 ℓ`.
-/

noncomputable section

open MeasureTheory
open scoped Real BigOperators ENNReal

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- Measurability of the Riesz weight of an image. -/
lemma measurable_imgW (ℓ : ℝ) (m : Fin 3 → ℤ) : Measurable (fun u : E3 => imgW ℓ m u) := by
  by_cases hm : m = 0
  · subst hm
    have : (fun u : E3 => imgW ℓ 0 u) = fun _ => (0 : ℝ) := by
      funext u; simp [imgW]
    rw [this]; exact measurable_const
  · have hfun : (fun u : E3 => imgW ℓ m u) = fun u => (‖u - ℓ • latVec m‖ ^ 4)⁻¹ := by
      funext u; exact imgW_ne_zero hm u
    rw [hfun]
    fun_prop

/-- **Pointwise lattice bound.**  For `‖u‖ ≤ ℓ` and indices `m` with `‖m‖ ≥ 2`, the sum of the
Riesz weights of the images `ℓ • latVec m` is at most `200 ℓ⁻⁴`: the reverse triangle inequality
gives `‖u − ℓ•latVec m‖ ≥ ℓ‖m‖ − ℓ = ℓ(‖m‖ − 1)`, so each weight is `≤ ℓ⁻⁴(‖m‖ − 1)⁻⁴`, and
`∑_{‖m‖ ≥ 2} (‖m‖ − 1)⁻⁴ ≤ 200` (`lattice_sum_inv_fourth_le`). -/
theorem aliasImgTerm_imgW_sum_le_aux {ℓ : ℝ} (hℓ : 0 < ℓ) (s : Finset (Fin 3 → ℤ))
    (hs : ∀ m ∈ s, 2 ≤ ‖m‖) {u : E3} (hu : ‖u‖ ≤ ℓ) :
    ∑ m ∈ s, imgW ℓ m u ≤ 200 * ℓ ^ (-(4 : ℝ)) := by
  have hterm : ∀ m ∈ s, imgW ℓ m u ≤ ℓ ^ (-(4:ℝ)) * (‖m‖ - 1) ^ (-(4:ℝ)) := by
    intro m hm
    have hm0 : m ≠ 0 := by
      intro h0
      have h2 := hs m hm
      rw [h0] at h2
      norm_num at h2
    rw [imgW_ne_zero hm0]
    have hK1 : 1 ≤ ‖m‖ - 1 := by linarith [hs m hm]
    have hKpos : 0 < ‖m‖ - 1 := lt_of_lt_of_le one_pos hK1
    have hY : (‖m‖ - 1) * ℓ ≤ ‖u - ℓ • latVec m‖ := by
      calc (‖m‖ - 1) * ℓ = ℓ * ‖m‖ - ℓ := by ring
        _ ≤ ℓ * ‖latVec m‖ - ℓ := by
              have := norm_le_norm_latVec m
              nlinarith [hℓ]
        _ = ‖ℓ • latVec m‖ - ℓ := by rw [norm_smul, Real.norm_of_nonneg hℓ.le]
        _ ≤ ‖ℓ • latVec m‖ - ‖u‖ := by linarith
        _ ≤ ‖ℓ • latVec m - u‖ := norm_sub_norm_le _ _
        _ = ‖u - ℓ • latVec m‖ := by rw [norm_sub_rev]
    have hYpos : 0 < ‖u - ℓ • latVec m‖ := lt_of_lt_of_le (by positivity) hY
    have hY4 : (‖u - ℓ • latVec m‖ ^ 4)⁻¹ = ‖u - ℓ • latVec m‖ ^ (-(4:ℝ)) := by
      rw [Real.rpow_neg (le_of_lt hYpos) (4:ℝ), Real.rpow_ofNat]
    have hkey := Real.rpow_le_rpow_of_nonpos (by positivity : (0:ℝ) < (‖m‖ - 1) * ℓ) hY
        (by norm_num : (-(4:ℝ)) ≤ 0)
    calc (‖u - ℓ • latVec m‖ ^ 4)⁻¹ = ‖u - ℓ • latVec m‖ ^ (-(4:ℝ)) := hY4
      _ ≤ ((‖m‖ - 1) * ℓ) ^ (-(4:ℝ)) := hkey
      _ = ℓ ^ (-(4:ℝ)) * (‖m‖ - 1) ^ (-(4:ℝ)) := by
            rw [Real.mul_rpow hKpos.le hℓ.le, mul_comm]
  calc ∑ m ∈ s, imgW ℓ m u
      ≤ ∑ m ∈ s, ℓ ^ (-(4:ℝ)) * (‖m‖ - 1) ^ (-(4:ℝ)) := Finset.sum_le_sum hterm
    _ = ℓ ^ (-(4:ℝ)) * ∑ m ∈ s, (‖m‖ - 1) ^ (-(4:ℝ)) := by
          rw [Finset.mul_sum]
    _ = ℓ ^ (-(4:ℝ)) * ∑ m ∈ s, (if 2 ≤ ‖m‖ then (‖m‖ - 1) ^ (-(4:ℝ)) else 0) := by
          congr 1
          refine Finset.sum_congr rfl fun m hm => ?_
          rw [if_pos (hs m hm)]
    _ ≤ ℓ ^ (-(4:ℝ)) * 200 := by
          apply mul_le_mul_of_nonneg_left (lattice_sum_inv_fourth_le s)
          exact (Real.rpow_pos_of_pos hℓ _).le
    _ = 200 * ℓ ^ (-(4:ℝ)) := by ring

theorem aliasImgTerm_tail_sum_le {ℓ : ℝ} (hℓ : 0 < ℓ)
    {g : EuclideanSpace ℝ (Fin 3) → ℂ} (hg : ContDiff ℝ (⊤ : ENat) g)
    (hgsupp : tsupport g ⊆ Metric.closedBall 0 (ℓ / 2))
    (s : Finset (Fin 3 → ℤ)) (hs : ∀ m ∈ s, 2 ≤ ‖m‖) :
    (∑ m ∈ s, Work.BoseBoxFock.aliasImgTerm ℓ g m)
      ≤ ENNReal.ofReal ((∫ x : EuclideanSpace ℝ (Fin 3), ‖g x‖ ^ 2) * ℓ ^ (-(4 : ℝ)) * 200)
        * (MeasureTheory.volume (Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) ℓ)) := by
  have hgc : HasCompactSupport g := hasCompactSupport_of_closedBall hgsupp
  have hGcont : Continuous (fun u : E3 => aliasKernel g u) :=
    Complex.continuous_re.comp (autocorr_continuous hg hgc)
  set A : ℝ := ∫ x : E3, ‖g x‖ ^ 2 with hA
  have hA0 : 0 ≤ A := by rw [hA]; exact integral_nonneg (fun x => by positivity)
  set t : ℝ := ℓ ^ (-(4 : ℝ)) with ht
  have ht0 : 0 ≤ t := by rw [ht]; exact (Real.rpow_pos_of_pos hℓ _).le
  set S : Set E3 := Metric.closedBall 0 ℓ with hS
  have hSmeas : MeasurableSet S := by rw [hS]; exact measurableSet_closedBall
  have hG : ∀ u : E3, ‖aliasKernel g u‖ ≤ A := by
    intro u
    calc ‖aliasKernel g u‖ = |(autocorr g u).re| := by rw [aliasKernel, Real.norm_eq_abs]
      _ ≤ ‖autocorr g u‖ := Complex.abs_re_le_norm _
      _ ≤ A := by rw [hA]; exact autocorr_norm_le hg hgc u
  have hmeas : ∀ m ∈ s, Measurable (fun u : E3 =>
      ENNReal.ofReal (‖aliasKernel g u‖ * imgW ℓ m u)) := by
    intro m hm
    exact ENNReal.measurable_ofReal.comp ((hGcont.norm.measurable).mul (measurable_imgW ℓ m))
  have hpoint : ∀ u : E3, ∑ m ∈ s, ENNReal.ofReal (‖aliasKernel g u‖ * imgW ℓ m u)
      ≤ ENNReal.ofReal (A * (200 * t)) * S.indicator (fun _ => (1 : ℝ≥0∞)) u := by
    intro u
    by_cases hu : u ∈ S
    · have huℓ : ‖u‖ ≤ ℓ := by
        rw [hS, Metric.mem_closedBall, dist_zero_right] at hu; exact hu
      have hsum : ∑ m ∈ s, imgW ℓ m u ≤ 200 * t := by
        rw [ht]; exact aliasImgTerm_imgW_sum_le_aux hℓ s hs huℓ
      rw [Set.indicator_of_mem hu, mul_one]
      have hexp : ∑ m ∈ s, ENNReal.ofReal (‖aliasKernel g u‖ * imgW ℓ m u)
          = ENNReal.ofReal (‖aliasKernel g u‖ * ∑ m ∈ s, imgW ℓ m u) := by
        rw [← ENNReal.ofReal_sum_of_nonneg
          (fun m _ => mul_nonneg (norm_nonneg _) (imgW_nonneg ℓ m u))]
        congr 1
        rw [Finset.mul_sum]
      rw [hexp]
      exact ENNReal.ofReal_le_ofReal
        (mul_le_mul (hG u) hsum (Finset.sum_nonneg (fun m _ => imgW_nonneg ℓ m u)) hA0)
    · rw [Set.indicator_of_notMem hu]
      have hle : ℓ ≤ ‖u‖ := by
        rw [hS, Metric.mem_closedBall, dist_zero_right] at hu
        exact le_of_lt (not_le.mp hu)
      have hz : aliasKernel g u = 0 := by
        rw [aliasKernel, autocorr_eq_zero_of_le_norm_closed hℓ hg hgsupp hle, Complex.zero_re]
      simp [hz]
  calc ∑ m ∈ s, aliasImgTerm ℓ g m
      = ∫⁻ u : E3, ∑ m ∈ s, ENNReal.ofReal (‖aliasKernel g u‖ * imgW ℓ m u) := by
        have h := MeasureTheory.lintegral_finsetSum (μ := (volume : Measure E3)) s
          (f := fun m (u : E3) => ENNReal.ofReal (‖aliasKernel g u‖ * imgW ℓ m u)) hmeas
        rw [h]
        simp [aliasImgTerm]
    _ ≤ ∫⁻ u : E3, ENNReal.ofReal (A * (200 * t)) * S.indicator (fun _ => (1 : ℝ≥0∞)) u :=
        MeasureTheory.lintegral_mono hpoint
    _ = ENNReal.ofReal (A * (200 * t)) * MeasureTheory.volume S := by
        rw [MeasureTheory.lintegral_const_mul (ENNReal.ofReal (A * (200 * t)))
          (measurable_const.indicator hSmeas)]
        rw [MeasureTheory.lintegral_indicator_const hSmeas (1 : ℝ≥0∞), one_mul]
    _ = ENNReal.ofReal ((∫ x : E3, ‖g x‖ ^ 2) * ℓ ^ (-(4 : ℝ)) * 200)
          * MeasureTheory.volume (Metric.closedBall (0 : E3) ℓ) := by
        have harith : A * (200 * t) = (∫ x : E3, ‖g x‖ ^ 2) * ℓ ^ (-(4 : ℝ)) * 200 := by
          rw [hA, ht]; ring
        rw [harith, hS]

end Work.BoseBoxFock
