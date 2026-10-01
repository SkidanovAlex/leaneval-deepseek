import Mathlib
import Submission.Work.ZeroDensity.Ingham.perronIntDeps
import Submission.Work.ZeroDensity.Ingham.perronHDifferentiableSelf
import Submission.Work.ZeroDensity.Ingham.mkStripBound
import Submission.Work.ZeroDensity.Ingham.gammaLineBound
import Submission.Work.ZeroDensity.Ingham.zetaLineBound

/-!
# Integrability of the Perron integrand on a vertical line

For `Y > 0`, a zero `ρ ≠ 1` of `ζ` and a real `c` with `-1 < c ≤ 3`, subject to the shifted strip
condition `-1 ≤ Re ρ + c ≤ 3` and to the vertical line `Re w = c` avoiding the pole `w = 1 - ρ`
of `ζ(ρ + ·)` (that is `c ≠ Re (1 - ρ)`), the Perron integrand

`perronInt K Y ρ w = Γ(w) * Y^w * ζ(ρ+w) * M_K(ρ+w)`

is Bochner integrable on that line.

On the line the integrand agrees, off the single point with `w = 0`, with the continuous function
`perronM K Y ρ w / (w - (1-ρ))`: the quotient removes the pole of `Γ` at `w = 0` against the zero
of `ζ` at `ρ` (`perronInt_eq_perronM_div`), `perronM` is holomorphic on `{Re > -1}`
(`differentiableOn_perronM` in `perronH_differentiable`), and the denominator has real part
`c - Re (1-ρ) ≠ 0` on the whole line.  Hence the integrand is bounded on the compact piece
`|t| ≤ |Im ρ| + 1` of the line, and a single point does not affect integrability.  On the
remaining piece `|t| ≥ |Im ρ| + 1` the four factors are estimated separately (exponential decay of
`Γ` on `Re = c`, `gammaLineBound`; quartic growth of `ζ` in the strip, `zetaLineBound`; the
polynomial bound for the mollifier, `mkStripBound`; and `‖Y^w‖ = Y^{Re w} ≤ max (Y^3) Y^{-1}`),
which produces the integrable majorant `(1 + |t|)^10 * exp (-(π/2) * |t|)`.
-/

namespace Work.ZeroDensity.Ingham

open MeasureTheory

theorem perronIntIntegrableSelf (K : ℕ) (Y : ℝ) (hY : 0 < Y) (ρ : ℂ)
    (hζ : riemannZeta ρ = 0) (hρ1 : ρ ≠ 1) {c : ℝ}
    (hc1 : -1 ≤ ρ.re + c) (hc2 : ρ.re + c ≤ 3) (hc3 : c ≠ (1 - ρ).re)
    (hc4 : -1 < c) (hc5 : c ≤ 3) :
    MeasureTheory.Integrable (fun t : ℝ => Work.ZeroDensity.Ingham.perronInt K Y ρ
      ((c : ℂ) + (t : ℂ) * Complex.I)) := by
  set T₀ : ℝ := |ρ.im| + 1 with hT₀
  have hT₀1 : (1 : ℝ) ≤ T₀ := by
    rw [hT₀]; have := abs_nonneg ρ.im; linarith
  have hcontM : Continuous (fun t : ℝ => perronM K Y ρ ((c : ℂ) + (t : ℂ) * Complex.I)) := by
    have hlin : Continuous (fun t : ℝ => (c : ℂ) + (t : ℂ) * Complex.I) := by fun_prop
    have hmem : ∀ t : ℝ, ((c : ℂ) + (t : ℂ) * Complex.I) ∈ {w : ℂ | -1 < w.re} := by
      intro t
      show (-1 : ℝ) < ((c : ℂ) + (t : ℂ) * Complex.I).re
      have hre : ((c : ℂ) + (t : ℂ) * Complex.I).re = c := by simp
      rw [hre]; exact hc4
    have hcontOn : ContinuousOn (fun z : ℂ => perronM K Y ρ z) {w : ℂ | -1 < w.re} :=
      (differentiableOn_perronM K Y hY ρ).continuousOn
    have h := hcontOn.comp_continuous hlin hmem
    simpa [Function.comp_def] using h
  have hden : ∀ t : ℝ, ((c : ℂ) + (t : ℂ) * Complex.I) ≠ 1 - ρ := by
    intro t h
    have hre := congrArg Complex.re h
    have h1 : ((c : ℂ) + (t : ℂ) * Complex.I).re = c := by simp
    have h2 : (1 - ρ).re = 1 - ρ.re := by simp
    rw [h1, h2] at hre
    exact hc3 (by linarith)
  have hconth : Continuous (fun t : ℝ =>
      perronM K Y ρ ((c : ℂ) + (t : ℂ) * Complex.I) /
        (((c : ℂ) + (t : ℂ) * Complex.I) - (1 - ρ))) := by
    refine hcontM.div ?_ ?_
    · fun_prop
    · intro t
      exact sub_ne_zero.mpr (hden t)
  have heq_off : ∀ t : ℝ, ((c : ℂ) + (t : ℂ) * Complex.I) ≠ 0 →
      perronInt K Y ρ ((c : ℂ) + (t : ℂ) * Complex.I) =
        perronM K Y ρ ((c : ℂ) + (t : ℂ) * Complex.I) /
          (((c : ℂ) + (t : ℂ) * Complex.I) - (1 - ρ)) :=
    fun t hw => perronInt_eq_perronM_div K Y ρ hζ hρ1 hw (hden t)
  have hwae : ∀ᵐ t : ℝ, ((c : ℂ) + (t : ℂ) * Complex.I) ≠ 0 := by
    rw [MeasureTheory.ae_iff]
    refine MeasureTheory.measure_mono_null ?_ (MeasureTheory.measure_singleton (0 : ℝ))
    intro t ht
    simp only [Set.mem_singleton_iff]
    push Not at ht
    have him := congrArg Complex.im ht
    simpa using him
  have hae : (fun t : ℝ => perronInt K Y ρ ((c : ℂ) + (t : ℂ) * Complex.I)) =ᵐ[volume]
      (fun t : ℝ => perronM K Y ρ ((c : ℂ) + (t : ℂ) * Complex.I) /
        (((c : ℂ) + (t : ℂ) * Complex.I) - (1 - ρ))) :=
    hwae.mono fun t ht => heq_off t ht
  have hbound_cpt : ∃ B0 : ℝ, 0 < B0 ∧ ∀ t : ℝ, |t| ≤ T₀ →
      ‖perronInt K Y ρ ((c : ℂ) + (t : ℂ) * Complex.I)‖ ≤ B0 := by
    have hcontOn : ContinuousOn (fun t : ℝ => perronM K Y ρ ((c : ℂ) + (t : ℂ) * Complex.I) /
        (((c : ℂ) + (t : ℂ) * Complex.I) - (1 - ρ))) (Set.Icc (-T₀) T₀) :=
      hconth.continuousOn.mono (Set.subset_univ _)
    obtain ⟨Ch, hCh⟩ := isCompact_Icc.exists_bound_of_continuousOn hcontOn
    refine ⟨max Ch 1, lt_of_lt_of_le one_pos (le_max_right _ _), ?_⟩
    intro t ht
    have htI : t ∈ Set.Icc (-T₀) T₀ := by
      rw [Set.mem_Icc]
      exact ⟨by linarith [neg_abs_le t], by linarith [le_abs_self t]⟩
    by_cases hw : ((c : ℂ) + (t : ℂ) * Complex.I) = 0
    · have hzero : perronInt K Y ρ ((c : ℂ) + (t : ℂ) * Complex.I) = 0 := by
        rw [hw]
        simp [perronInt, hζ]
      rw [hzero, norm_zero]
      exact le_of_lt (lt_of_lt_of_le one_pos (le_max_right _ _))
    · rw [heq_off t hw]
      exact le_trans (hCh t htI) (le_max_left _ _)
  obtain ⟨Cγ, hCγpos, hCγ⟩ := gammaLineBound c hc4 hc5
  obtain ⟨Cζ, hCζpos, hCζ⟩ := zetaLineBound ρ c hc1 hc2
  set CY : ℝ := max (Y ^ (3 : ℝ)) (Y ^ (-1 : ℝ)) with hCY
  have hCYpos : 0 < CY :=
    lt_of_lt_of_le (Real.rpow_pos_of_pos hY 3) (le_max_left _ _)
  set CMK : ℝ := ∑ n ∈ Finset.Icc 1 K, (n : ℝ) ^ 3 with hCMK
  have hCMKnn : 0 ≤ CMK := by rw [hCMK]; positivity
  set Cbig : ℝ := Cγ * CY * Cζ * CMK with hCbig
  have hCbig0 : 0 ≤ Cbig := by rw [hCbig]; positivity
  have hbound_large : ∀ t : ℝ, T₀ ≤ |t| →
      ‖perronInt K Y ρ ((c : ℂ) + (t : ℂ) * Complex.I)‖ ≤
        Cbig * ((1 + |t|) ^ 10 * Real.exp (-(Real.pi / 2) * |t|)) := by
    intro t ht
    have ht1 : (1 : ℝ) ≤ |t| := le_trans hT₀1 ht
    have hlt : |ρ.im| + 1 ≤ |t| := by rw [hT₀] at ht; exact ht
    have hΓ : ‖Complex.Gamma ((c : ℂ) + (t : ℂ) * Complex.I)‖ ≤
        Cγ * (1 + |t|) ^ 6 * Real.exp (-(Real.pi / 2) * |t|) := hCγ t ht1
    have hζb : ‖riemannZeta (ρ + ((c : ℂ) + (t : ℂ) * Complex.I))‖ ≤
        Cζ * (1 + |t|) ^ 4 := hCζ t hlt
    have hMKb : ‖MK K (ρ + ((c : ℂ) + (t : ℂ) * Complex.I))‖ ≤ CMK := by
      rw [hCMK]
      refine mkStripBound K ?_
      have hre : (ρ + ((c : ℂ) + (t : ℂ) * Complex.I)).re = ρ.re + c := by simp
      rw [hre]; linarith
    have hYb : ‖(Y : ℂ) ^ ((c : ℂ) + (t : ℂ) * Complex.I)‖ ≤ CY := by
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hY]
      have hre : ((c : ℂ) + (t : ℂ) * Complex.I).re = c := by simp
      rw [hre, hCY]
      rcases le_or_gt 1 Y with h1 | h1
      · exact le_trans (Real.rpow_le_rpow_of_exponent_le h1 hc5) (le_max_left _ _)
      · exact le_trans (Real.rpow_le_rpow_of_exponent_ge hY h1.le (by linarith : (-1 : ℝ) ≤ c))
          (le_max_right _ _)
    have hnormeq : ‖perronInt K Y ρ ((c : ℂ) + (t : ℂ) * Complex.I)‖
        = ‖Complex.Gamma ((c : ℂ) + (t : ℂ) * Complex.I)‖
          * ‖(Y : ℂ) ^ ((c : ℂ) + (t : ℂ) * Complex.I)‖
          * ‖riemannZeta (ρ + ((c : ℂ) + (t : ℂ) * Complex.I))‖
          * ‖MK K (ρ + ((c : ℂ) + (t : ℂ) * Complex.I))‖ := by
      unfold perronInt
      simp only [norm_mul]
    rw [hnormeq]
    have hstep : ‖Complex.Gamma ((c : ℂ) + (t : ℂ) * Complex.I)‖
          * ‖(Y : ℂ) ^ ((c : ℂ) + (t : ℂ) * Complex.I)‖
          * ‖riemannZeta (ρ + ((c : ℂ) + (t : ℂ) * Complex.I))‖
          * ‖MK K (ρ + ((c : ℂ) + (t : ℂ) * Complex.I))‖
        ≤ (Cγ * (1 + |t|) ^ 6 * Real.exp (-(Real.pi / 2) * |t|)) * CY
          * (Cζ * (1 + |t|) ^ 4) * CMK := by
      have h1 : ‖Complex.Gamma ((c : ℂ) + (t : ℂ) * Complex.I)‖
            * ‖(Y : ℂ) ^ ((c : ℂ) + (t : ℂ) * Complex.I)‖
          ≤ (Cγ * (1 + |t|) ^ 6 * Real.exp (-(Real.pi / 2) * |t|)) * CY :=
        mul_le_mul hΓ hYb (norm_nonneg _) (by positivity)
      have h2 : ‖Complex.Gamma ((c : ℂ) + (t : ℂ) * Complex.I)‖
            * ‖(Y : ℂ) ^ ((c : ℂ) + (t : ℂ) * Complex.I)‖
            * ‖riemannZeta (ρ + ((c : ℂ) + (t : ℂ) * Complex.I))‖
          ≤ ((Cγ * (1 + |t|) ^ 6 * Real.exp (-(Real.pi / 2) * |t|)) * CY)
            * (Cζ * (1 + |t|) ^ 4) :=
        mul_le_mul h1 hζb (norm_nonneg _) (by positivity)
      exact mul_le_mul h2 hMKb (norm_nonneg _) (by positivity)
    have hpow : (1 + |t|) ^ 6 * (1 + |t|) ^ 4 = (1 + |t|) ^ 10 := by
      rw [← pow_add]
    refine le_trans hstep (le_of_eq ?_)
    rw [hCbig, ← hpow]
    ring
  obtain ⟨B0, hB0pos, hB0⟩ := hbound_cpt
  set M : ℝ := max (B0 * Real.exp (Real.pi / 2 * T₀)) Cbig with hM
  have hM0 : 0 ≤ M :=
    le_trans (mul_nonneg hB0pos.le (Real.exp_pos _).le) (le_max_left _ _)
  have hpoint : ∀ t : ℝ, ‖perronInt K Y ρ ((c : ℂ) + (t : ℂ) * Complex.I)‖ ≤
      M * ((1 + |t|) ^ 10 * Real.exp (-(Real.pi / 2) * |t|)) := by
    intro t
    rcases le_total |t| T₀ with hle | hge
    · have hb := hB0 t hle
      have hX : Real.exp (-(Real.pi / 2) * T₀) ≤
          (1 + |t|) ^ 10 * Real.exp (-(Real.pi / 2) * |t|) := by
        have ha : (1 : ℝ) ≤ (1 + |t|) ^ 10 :=
          one_le_pow₀ (by linarith [abs_nonneg t] : (1 : ℝ) ≤ 1 + |t|)
        have hb' : Real.exp (-(Real.pi / 2) * T₀) ≤ Real.exp (-(Real.pi / 2) * |t|) := by
          apply Real.exp_le_exp.mpr
          have h2 : (Real.pi / 2) * |t| ≤ (Real.pi / 2) * T₀ := by nlinarith [Real.pi_pos]
          linarith
        calc Real.exp (-(Real.pi / 2) * T₀) ≤ 1 * Real.exp (-(Real.pi / 2) * |t|) := by
              rw [one_mul]; exact hb'
          _ ≤ (1 + |t|) ^ 10 * Real.exp (-(Real.pi / 2) * |t|) :=
              mul_le_mul_of_nonneg_right ha (Real.exp_pos _).le
      have hMge : B0 * Real.exp (Real.pi / 2 * T₀) ≤ M := le_max_left _ _
      have hexpB0 : B0 * Real.exp (Real.pi / 2 * T₀) * Real.exp (-(Real.pi / 2) * T₀) = B0 := by
        rw [mul_assoc, ← Real.exp_add,
          show Real.pi / 2 * T₀ + -(Real.pi / 2) * T₀ = 0 by ring, Real.exp_zero, mul_one]
      refine le_trans hb ?_
      calc B0 = B0 * Real.exp (Real.pi / 2 * T₀) * Real.exp (-(Real.pi / 2) * T₀) := hexpB0.symm
        _ ≤ M * Real.exp (-(Real.pi / 2) * T₀) :=
            mul_le_mul_of_nonneg_right hMge (Real.exp_pos _).le
        _ ≤ M * ((1 + |t|) ^ 10 * Real.exp (-(Real.pi / 2) * |t|)) :=
            mul_le_mul_of_nonneg_left hX hM0
    · have hb := hbound_large t hge
      have hCbigM : Cbig ≤ M := le_max_right _ _
      exact le_trans hb (mul_le_mul_of_nonneg_right hCbigM (by positivity))
  have hbase : Integrable
      (fun t : ℝ => (1 + |t|) ^ 10 * Real.exp (-(Real.pi / 2) * |t|)) := by
    have h := Work.LinnikAreas.Density4.integrable_one_add_abs_rpow_exp ((10 : ℕ) : ℝ)
      (Real.pi / 2) (by positivity)
    simpa only [Real.rpow_natCast, neg_mul] using h
  refine Integrable.mono' (hbase.const_mul M) ?_ ?_
  · exact hconth.aestronglyMeasurable.congr hae.symm
  · exact Filter.Eventually.of_forall hpoint

end Work.ZeroDensity.Ingham
