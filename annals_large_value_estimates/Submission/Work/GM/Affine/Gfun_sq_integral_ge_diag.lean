import Mathlib
import Submission.Work.GM.Affine.region_II_defs
import Submission.Work.GM.Affine.smoothed_properties
import Submission.Work.GM.Affine.smoothed_psiSmooth_fourier
import Submission.Work.GM.Affine.Gfun_le_gSum
import Submission.Work.GM.Affine.cauchy_base
import Submission.Work.GM.Affine.asgs_aux

/-!
# `Work.GM.Affine.Gfun_sq_integral_ge_diag` (GM §9, region II: the diagonal lower bound)

The honest affine sum of GM §9 region II is

`Gfun C₀ T M₂ f u = Σ_{m₂ ∈ R2 M₂} Σ_{m₂' ∈ R2 M₂} Σ_{|j| ≤ ⌊2C₀M₂⌋} f̃((m₂u + j)/m₂')`,
`f̃ = smoothed psiSmooth T f`.

Since `f̃ ≥ 0`, dropping the cross terms in `(Σ_t f̃_t)²` gives `Σ_t f̃_t² ≤ Gfun²`; each single
term integrates (change of variables) to `(m₂'/m₂) ∫ f̃²`, and `m₂'/m₂ ≥ 1/2` on `R2 M₂` because
`M₂ < m₂'` and `m₂ ≤ 2M₂`.  Summing over the `|R2|² (2⌊2C₀M₂⌋+1)` terms yields

`(1/2) |R2 M₂|² (2⌊2C₀M₂⌋+1) ∫ f̃² ≤ ∫ Gfun²`.
-/

open Complex MeasureTheory Finset
open scoped BigOperators FourierTransform

set_option autoImplicit false
set_option maxHeartbeats 1000000

namespace Work.GM.Affine

noncomputable section

theorem Gfun_sq_integral_ge_diag {C₀ T M₂ : ℝ} (hC₀ : 1 ≤ C₀) (hT : 0 < T) (hM₂ : 1 ≤ M₂)
    {f : ℝ → ℝ} (hf : Continuous f) (hfnn : ∀ u, 0 ≤ f u) (hcs : HasCompactSupport f) :
    (1 / 2 : ℝ) * ((R2 M₂).card : ℝ) ^ 2 * ((2 * ⌊2 * C₀ * M₂⌋ + 1 : ℤ) : ℝ) *
        (∫ u, (smoothed psiSmooth T f u) ^ 2)
      ≤ ∫ u, (Gfun C₀ T M₂ f u) ^ 2 := by
  have hM₂pos : (0 : ℝ) < M₂ := lt_of_lt_of_le zero_lt_one hM₂
  obtain ⟨hFcont0, hFcs0, -⟩ := smoothed_psiSmooth_fourier hT hf hcs
  set F : ℝ → ℝ := smoothed psiSmooth T f with hFdef
  set n : ℤ := ⌊2 * C₀ * M₂⌋ with hn_def
  set J : Finset ℤ := Finset.Icc (-n) n with hJdef
  have hFcont : Continuous F := by simpa only [hFdef] using hFcont0
  have hFcs : HasCompactSupport F := by simpa only [hFdef] using hFcs0
  have hFnn : ∀ u, 0 ≤ F u := by
    intro u
    rw [hFdef]
    exact smoothed_psiSmooth_nonneg hT hfnn u
  have hnn_nonneg : (0 : ℤ) ≤ n := by
    rw [hn_def]
    exact Int.floor_nonneg.mpr (by nlinarith)
  have hJcard : ((J.card : ℕ) : ℝ) = ((2 * n + 1 : ℤ) : ℝ) := by
    have h : (J.card : ℤ) = 2 * n + 1 := by
      rw [hJdef, Int.card_Icc]
      rw [Int.toNat_of_nonneg (by omega : (0 : ℤ) ≤ n + 1 - -n)]
      ring
    exact_mod_cast h
  -- the honest sum in terms of the local abbreviations
  have hGfun_eq : ∀ u, Gfun C₀ T M₂ f u
      = ∑ m₂ ∈ R2 M₂, ∑ m₂' ∈ R2 M₂, ∑ j ∈ J,
          F (((m₂ : ℝ) * u + (j : ℝ)) / (m₂' : ℝ)) := by
    intro u
    rw [Gfun]
  -- pointwise: the sum of the squares is bounded by the square of the sum
  have hpt : ∀ u, (∑ m₂ ∈ R2 M₂, ∑ m₂' ∈ R2 M₂, ∑ j ∈ J,
        (F (((m₂ : ℝ) * u + (j : ℝ)) / (m₂' : ℝ))) ^ 2)
      ≤ (Gfun C₀ T M₂ f u) ^ 2 := by
    intro u
    rw [hGfun_eq u]
    have hnn2 : ∀ m₂ ∈ R2 M₂, 0 ≤ ∑ m₂' ∈ R2 M₂, ∑ j ∈ J,
        F (((m₂ : ℝ) * u + (j : ℝ)) / (m₂' : ℝ)) :=
      fun m₂ _ => Finset.sum_nonneg fun m₂' _ => Finset.sum_nonneg fun j _ => hFnn _
    have hstep1 : ∀ m₂ ∈ R2 M₂,
        (∑ m₂' ∈ R2 M₂, ∑ j ∈ J, (F (((m₂ : ℝ) * u + (j : ℝ)) / (m₂' : ℝ))) ^ 2)
        ≤ (∑ m₂' ∈ R2 M₂, ∑ j ∈ J, F (((m₂ : ℝ) * u + (j : ℝ)) / (m₂' : ℝ))) ^ 2 := by
      intro m₂ _
      have hnn3 : ∀ m₂' ∈ R2 M₂, 0 ≤ ∑ j ∈ J, F (((m₂ : ℝ) * u + (j : ℝ)) / (m₂' : ℝ)) :=
        fun m₂' _ => Finset.sum_nonneg fun j _ => hFnn _
      have hstep2 : ∀ m₂' ∈ R2 M₂,
          (∑ j ∈ J, (F (((m₂ : ℝ) * u + (j : ℝ)) / (m₂' : ℝ))) ^ 2)
          ≤ (∑ j ∈ J, F (((m₂ : ℝ) * u + (j : ℝ)) / (m₂' : ℝ))) ^ 2 :=
        fun m₂' _ => asgs_sq_sum_ge_sum_sq J (fun j _ => hFnn _)
      calc (∑ m₂' ∈ R2 M₂, ∑ j ∈ J, (F (((m₂ : ℝ) * u + (j : ℝ)) / (m₂' : ℝ))) ^ 2)
          ≤ ∑ m₂' ∈ R2 M₂, (∑ j ∈ J, F (((m₂ : ℝ) * u + (j : ℝ)) / (m₂' : ℝ))) ^ 2 :=
            Finset.sum_le_sum hstep2
        _ ≤ (∑ m₂' ∈ R2 M₂, ∑ j ∈ J, F (((m₂ : ℝ) * u + (j : ℝ)) / (m₂' : ℝ))) ^ 2 :=
            asgs_sq_sum_ge_sum_sq (R2 M₂) hnn3
    calc (∑ m₂ ∈ R2 M₂, ∑ m₂' ∈ R2 M₂, ∑ j ∈ J,
          (F (((m₂ : ℝ) * u + (j : ℝ)) / (m₂' : ℝ))) ^ 2)
        ≤ ∑ m₂ ∈ R2 M₂,
            (∑ m₂' ∈ R2 M₂, ∑ j ∈ J, F (((m₂ : ℝ) * u + (j : ℝ)) / (m₂' : ℝ))) ^ 2 :=
          Finset.sum_le_sum hstep1
      _ ≤ (∑ m₂ ∈ R2 M₂, ∑ m₂' ∈ R2 M₂, ∑ j ∈ J,
            F (((m₂ : ℝ) * u + (j : ℝ)) / (m₂' : ℝ))) ^ 2 :=
          asgs_sq_sum_ge_sum_sq (R2 M₂) hnn2
  -- integrability of one squared term and its integral
  have hpiece_int : ∀ m₂ ∈ R2 M₂, ∀ m₂' ∈ R2 M₂, ∀ j ∈ J,
      Integrable (fun u : ℝ => (F (((m₂ : ℝ) * u + (j : ℝ)) / (m₂' : ℝ))) ^ 2) :=
    fun m₂ hm₂ m₂' hm₂' j _ =>
      integrable_affine_sq hFcont hFcs (ne_of_gt (R2_pos hM₂pos hm₂))
        (ne_of_gt (R2_pos hM₂pos hm₂'))
  have hpiece_val : ∀ m₂ ∈ R2 M₂, ∀ m₂' ∈ R2 M₂, ∀ j ∈ J,
      (∫ u, (F (((m₂ : ℝ) * u + (j : ℝ)) / (m₂' : ℝ))) ^ 2)
        = ((m₂' : ℝ) / (m₂ : ℝ)) * ∫ u, (F u) ^ 2 := by
    intro m₂ hm₂ m₂' hm₂' j _
    have h := integral_affine_sq (f := F) (c := (m₂ : ℝ)) (d := (m₂' : ℝ)) (e := (j : ℝ))
      (ne_of_gt (R2_pos hM₂pos hm₂)) (R2_pos hM₂pos hm₂')
    rw [h, abs_of_pos (R2_pos hM₂pos hm₂)]
  -- the integral of the sum of squares
  have hIntEval : (∫ u, (∑ m₂ ∈ R2 M₂, ∑ m₂' ∈ R2 M₂, ∑ j ∈ J,
        (F (((m₂ : ℝ) * u + (j : ℝ)) / (m₂' : ℝ))) ^ 2))
      = (∑ m₂ ∈ R2 M₂, ∑ m₂' ∈ R2 M₂, ∑ j ∈ J, ((m₂' : ℝ) / (m₂ : ℝ)))
        * ∫ u, (F u) ^ 2 := by
    have hsumfac : (∑ m₂ ∈ R2 M₂, ∑ m₂' ∈ R2 M₂, ∑ j ∈ J,
          ((m₂' : ℝ) / (m₂ : ℝ)) * ∫ u, (F u) ^ 2)
        = (∑ m₂ ∈ R2 M₂, ∑ m₂' ∈ R2 M₂, ∑ j ∈ J, ((m₂' : ℝ) / (m₂ : ℝ)))
          * ∫ u, (F u) ^ 2 := by
      simp only [Finset.sum_mul]
    rw [← hsumfac]
    rw [MeasureTheory.integral_finsetSum _ (fun m₂ hm₂ =>
      integrable_finsetSum _ (fun m₂' hm₂' =>
        integrable_finsetSum _ (fun j hj => hpiece_int m₂ hm₂ m₂' hm₂' j hj)))]
    apply Finset.sum_congr rfl; intro m₂ hm₂
    rw [MeasureTheory.integral_finsetSum _ (fun m₂' hm₂' =>
      integrable_finsetSum _ (fun j hj => hpiece_int m₂ hm₂ m₂' hm₂' j hj))]
    apply Finset.sum_congr rfl; intro m₂' hm₂'
    rw [MeasureTheory.integral_finsetSum _ (fun j hj => hpiece_int m₂ hm₂ m₂' hm₂' j hj)]
    apply Finset.sum_congr rfl; intro j hj
    exact hpiece_val m₂ hm₂ m₂' hm₂' j hj
  -- integrability of the sum of squares and of `Gfun²`
  have hsumsq_int : Integrable (fun u : ℝ => ∑ m₂ ∈ R2 M₂, ∑ m₂' ∈ R2 M₂, ∑ j ∈ J,
      (F (((m₂ : ℝ) * u + (j : ℝ)) / (m₂' : ℝ))) ^ 2) :=
    integrable_finsetSum _ (fun m₂ hm₂ => integrable_finsetSum _ (fun m₂' hm₂' =>
      integrable_finsetSum _ (fun j hj => hpiece_int m₂ hm₂ m₂' hm₂' j hj)))
  have hGcont : Continuous (fun u => Gfun C₀ T M₂ f u) := by
    rw [show (fun u => Gfun C₀ T M₂ f u) = fun u => ∑ m₂ ∈ R2 M₂, ∑ m₂' ∈ R2 M₂, ∑ j ∈ J,
        F (((m₂ : ℝ) * u + (j : ℝ)) / (m₂' : ℝ)) from funext hGfun_eq]
    refine continuous_finsetSum _ (fun m₂ _ => ?_)
    refine continuous_finsetSum _ (fun m₂' _ => ?_)
    refine continuous_finsetSum _ (fun j _ => ?_)
    exact hFcont.comp (((continuous_const.mul continuous_id).add continuous_const).div_const _)
  have hGint : Integrable (fun u => (Gfun C₀ T M₂ f u) ^ 2) := by
    have hmaj : Integrable (fun u : ℝ =>
        ((R2 M₂).card : ℝ) * ((R2 M₂).card : ℝ) * ((J.card : ℕ) : ℝ)
          * (∑ m₂ ∈ R2 M₂, ∑ m₂' ∈ R2 M₂, ∑ j ∈ J,
              (F (((m₂ : ℝ) * u + (j : ℝ)) / (m₂' : ℝ))) ^ 2)) :=
      hsumsq_int.const_mul _
    refine Integrable.mono_nonneg hmaj (hGcont.pow 2).aestronglyMeasurable
      (Filter.Eventually.of_forall fun u => sq_nonneg _) (Filter.Eventually.of_forall fun u => ?_)
    rw [hGfun_eq u]
    exact sq_sum_sum_le (R2 M₂) (R2 M₂) J
      (fun m₂ m₂' j => F (((m₂ : ℝ) * u + (j : ℝ)) / (m₂' : ℝ)))
  have hmono : (∫ u, (∑ m₂ ∈ R2 M₂, ∑ m₂' ∈ R2 M₂, ∑ j ∈ J,
        (F (((m₂ : ℝ) * u + (j : ℝ)) / (m₂' : ℝ))) ^ 2))
      ≤ ∫ u, (Gfun C₀ T M₂ f u) ^ 2 :=
    integral_mono_of_nonneg
      (Filter.Eventually.of_forall fun u => Finset.sum_nonneg fun m₂ _ =>
        Finset.sum_nonneg fun m₂' _ => Finset.sum_nonneg fun j _ => sq_nonneg _)
      hGint (Filter.Eventually.of_forall hpt)
  -- the coefficient bound
  have hterm : ∀ m₂ ∈ R2 M₂, ∀ m₂' ∈ R2 M₂, ∀ j ∈ J,
      (1 / 2 : ℝ) ≤ ((m₂' : ℝ) / (m₂ : ℝ)) := by
    intro m₂ hm₂ m₂' hm₂' j _
    have h1 : M₂ < (m₂' : ℝ) := (Finset.mem_filter.mp hm₂').2
    have h2 : (m₂ : ℝ) ≤ 2 * M₂ := R2_le hm₂
    have h3 : 0 < (m₂ : ℝ) := R2_pos hM₂pos hm₂
    rw [le_div_iff₀ h3]
    linarith
  have hcoef : (1 / 2 : ℝ) * ((R2 M₂).card : ℝ) * ((R2 M₂).card : ℝ) * ((J.card : ℕ) : ℝ)
      ≤ ∑ m₂ ∈ R2 M₂, ∑ m₂' ∈ R2 M₂, ∑ j ∈ J, ((m₂' : ℝ) / (m₂ : ℝ)) := by
    calc (1 / 2 : ℝ) * ((R2 M₂).card : ℝ) * ((R2 M₂).card : ℝ) * ((J.card : ℕ) : ℝ)
        = ∑ m₂ ∈ R2 M₂, ∑ m₂' ∈ R2 M₂, ∑ j ∈ J, (1 / 2 : ℝ) := by
          simp only [Finset.sum_const, nsmul_eq_mul]
          ring
      _ ≤ ∑ m₂ ∈ R2 M₂, ∑ m₂' ∈ R2 M₂, ∑ j ∈ J, ((m₂' : ℝ) / (m₂ : ℝ)) :=
          Finset.sum_le_sum fun m₂ hm₂ => Finset.sum_le_sum fun m₂' hm₂' =>
            Finset.sum_le_sum fun j hj => hterm m₂ hm₂ m₂' hm₂' j hj
  have hF2nn : (0 : ℝ) ≤ ∫ u, (F u) ^ 2 := integral_nonneg fun u => sq_nonneg _
  calc (1 / 2 : ℝ) * ((R2 M₂).card : ℝ) ^ 2 * ((2 * n + 1 : ℤ) : ℝ) * (∫ u, (F u) ^ 2)
      = (1 / 2 : ℝ) * ((R2 M₂).card : ℝ) * ((R2 M₂).card : ℝ) * ((J.card : ℕ) : ℝ)
          * (∫ u, (F u) ^ 2) := by
        rw [← hJcard]; ring
    _ ≤ (∑ m₂ ∈ R2 M₂, ∑ m₂' ∈ R2 M₂, ∑ j ∈ J, ((m₂' : ℝ) / (m₂ : ℝ)))
          * (∫ u, (F u) ^ 2) := mul_le_mul_of_nonneg_right hcoef hF2nn
    _ = ∫ u, (∑ m₂ ∈ R2 M₂, ∑ m₂' ∈ R2 M₂, ∑ j ∈ J,
          (F (((m₂ : ℝ) * u + (j : ℝ)) / (m₂' : ℝ))) ^ 2) := hIntEval.symm
    _ ≤ ∫ u, (Gfun C₀ T M₂ f u) ^ 2 := hmono

end

end Work.GM.Affine
