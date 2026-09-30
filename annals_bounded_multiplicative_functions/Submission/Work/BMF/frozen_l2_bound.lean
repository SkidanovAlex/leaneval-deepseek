import Mathlib
import Submission.Work.BMF.parseval.Defs
import Submission.Work.BMF.frozen_l2_sq_expand
import Submission.Work.BMF.frozen_l2_cpow
import Submission.Work.BMF.frozen_l2_schur
import Submission.Work.BMF.frozen_l2_cont

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory intervalIntegral
open scoped ComplexConjugate

namespace Work.BMF

lemma frozen_l2_core (X L C0 : ℝ) (hC0 : 0 < C0) (hX : 0 < X) (hL : 0 ≤ L)
    (w : ℝ → ℝ) (a : ℝ → ℂ)
    (hcont : ContinuousOn (fun z : ℝ × ℝ × ℝ =>
        (w z.1 : ℂ) * ((a z.2.1 * conj (a z.2.2)) * (z.1:ℂ)^(4 + Complex.I*((z.2.1 - z.2.2 : ℝ):ℂ))))
      (Set.Icc (X * Real.exp (-1)) (X * Real.exp 3) ×ˢ (Set.Icc (-L) L ×ˢ Set.Icc (-L) L)))
    (htrans : ∀ Δ : ℝ, ‖∫ x in X * Real.exp (-1)..X * Real.exp 3,
        (w x : ℂ) * (x:ℂ)^(4 + Complex.I*(Δ:ℂ))‖ ≤ C0 * X^5/(1+Δ^2))
    (ha : Continuous a) :
    (∫ x in X * Real.exp (-1)..X * Real.exp 3, w x * ‖∫ t in (-L)..L, a t * (x:ℂ)^(2 + Complex.I*(t:ℂ))‖^2)
      ≤ C0 * X^5 * Real.pi * (∫ t in (-L)..L, ‖a t‖^2) := by
  have hab : X * Real.exp (-1) ≤ X * Real.exp 3 :=
    mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr (by norm_num)) hX.le
  have hlohi : (-L) ≤ L := by linarith
  have hxa_pos : (0:ℝ) < X * Real.exp (-1) := by positivity
  have hsubI : Set.uIoc (X * Real.exp (-1)) (X * Real.exp 3) ⊆ Set.Icc (X * Real.exp (-1)) (X * Real.exp 3) := by
    rw [← Set.uIcc_of_le hab]; exact Set.uIoc_subset_uIcc
  have hsubJ : Set.uIoc (-L) L ⊆ Set.Icc (-L) L := by
    rw [← Set.uIcc_of_le hlohi]; exact Set.uIoc_subset_uIcc
  set μI : Measure ℝ := volume.restrict (Set.uIoc (X * Real.exp (-1)) (X * Real.exp 3)) with hμI
  set μJ : Measure ℝ := volume.restrict (Set.uIoc (-L) L) with hμJ
  set Z : ℝ → ℂ := fun Δ => ∫ x in X * Real.exp (-1)..X * Real.exp 3,
      (w x : ℂ) * (x:ℂ)^(4 + Complex.I*(Δ:ℂ)) with hZ
  have hconv : ∀ g : ℝ → ℂ, (∫ t, g t ∂μJ) = ∫ t in (-L)..L, g t := by
    intro g
    show (∫ t, g t ∂(volume.restrict (Set.uIoc (-L) L))) = ∫ t in (-L)..L, g t
    rw [Set.uIoc_of_le hlohi, intervalIntegral.integral_of_le hlohi]
  have hconvI : ∀ g : ℝ → ℂ, (∫ t in (-L)..L, g t) = ∫ t, g t ∂μJ := by
    intro g
    show (∫ t in (-L)..L, g t) = ∫ t, g t ∂(volume.restrict (Set.uIoc (-L) L))
    rw [intervalIntegral.integral_of_le hlohi, ← Set.uIoc_of_le hlohi]
  have hconvIR : ∀ g : ℝ → ℝ, (∫ t in (-L)..L, g t) = ∫ t, g t ∂μJ := by
    intro g
    show (∫ t in (-L)..L, g t) = ∫ t, g t ∂(volume.restrict (Set.uIoc (-L) L))
    rw [intervalIntegral.integral_of_le hlohi, ← Set.uIoc_of_le hlohi]
  have hconvX : ∀ g : ℝ → ℂ, (∫ x in X * Real.exp (-1)..X * Real.exp 3, g x) = ∫ x, g x ∂μI := by
    intro g
    show (∫ x in X * Real.exp (-1)..X * Real.exp 3, g x)
        = ∫ x, g x ∂(volume.restrict (Set.uIoc (X * Real.exp (-1)) (X * Real.exp 3)))
    rw [intervalIntegral.integral_of_le hab, ← Set.uIoc_of_le hab]
  have hJint : ∀ g : ℝ → ℝ, Continuous g →
      Integrable (fun p : ℝ × ℝ => ‖a p.1‖ * ‖a p.2‖ * g (p.1 - p.2)) (μJ.prod μJ) := by
    intro g hg
    show Integrable (fun p : ℝ × ℝ => ‖a p.1‖ * ‖a p.2‖ * g (p.1 - p.2))
      ((volume.restrict (Set.uIoc (-L) L)).prod (volume.restrict (Set.uIoc (-L) L)))
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod ℝ ℝ]
    change IntegrableOn (fun p : ℝ × ℝ => ‖a p.1‖ * ‖a p.2‖ * g (p.1 - p.2))
      (Set.uIoc (-L) L ×ˢ Set.uIoc (-L) L) volume
    refine (ContinuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc) ?_).mono_set
      (Set.prod_mono hsubJ hsubJ)
    fun_prop
  -- integrability of the triple integrand
  have hInt3 : Integrable (fun z : ℝ × ℝ × ℝ =>
      (w z.1 : ℂ) * ((a z.2.1 * conj (a z.2.2)) * (z.1:ℂ)^(4 + Complex.I*((z.2.1 - z.2.2 : ℝ):ℂ))))
      (μI.prod (μJ.prod μJ)) := by
    have hcpt : IsCompact (Set.Icc (X * Real.exp (-1)) (X * Real.exp 3) ×ˢ (Set.Icc (-L) L ×ˢ Set.Icc (-L) L)) :=
      isCompact_Icc.prod (isCompact_Icc.prod isCompact_Icc)
    have hboxInt : IntegrableOn (fun z : ℝ × ℝ × ℝ =>
        (w z.1 : ℂ) * ((a z.2.1 * conj (a z.2.2)) * (z.1:ℂ)^(4 + Complex.I*((z.2.1 - z.2.2 : ℝ):ℂ))))
        (Set.Icc (X * Real.exp (-1)) (X * Real.exp 3) ×ˢ (Set.Icc (-L) L ×ˢ Set.Icc (-L) L)) volume :=
      ContinuousOn.integrableOn_compact hcpt hcont
    have hboxInt' : Integrable (fun z : ℝ × ℝ × ℝ =>
        (w z.1 : ℂ) * ((a z.2.1 * conj (a z.2.2)) * (z.1:ℂ)^(4 + Complex.I*((z.2.1 - z.2.2 : ℝ):ℂ))))
        (volume.restrict (Set.uIoc (X * Real.exp (-1)) (X * Real.exp 3) ×ˢ (Set.uIoc (-L) L ×ˢ Set.uIoc (-L) L))) :=
      hboxInt.mono_set (Set.prod_mono hsubI (Set.prod_mono hsubJ hsubJ))
    have hmeas : (μI.prod (μJ.prod μJ)) = volume.restrict (Set.uIoc (X * Real.exp (-1)) (X * Real.exp 3) ×ˢ (Set.uIoc (-L) L ×ˢ Set.uIoc (-L) L)) := by
      show (volume.restrict (Set.uIoc (X * Real.exp (-1)) (X * Real.exp 3))).prod
          ((volume.restrict (Set.uIoc (-L) L)).prod (volume.restrict (Set.uIoc (-L) L)))
          = volume.restrict (Set.uIoc (X * Real.exp (-1)) (X * Real.exp 3) ×ˢ (Set.uIoc (-L) L ×ˢ Set.uIoc (-L) L))
      rw [Measure.prod_restrict, Measure.prod_restrict, ← Measure.volume_eq_prod ℝ ℝ,
        ← Measure.volume_eq_prod ℝ (ℝ × ℝ)]
    exact hmeas ▸ hboxInt'
  have hMargB : Integrable (fun p : ℝ × ℝ => ∫ x, (fun z : ℝ × ℝ × ℝ =>
      (w z.1 : ℂ) * ((a z.2.1 * conj (a z.2.2)) * (z.1:ℂ)^(4 + Complex.I*((z.2.1 - z.2.2 : ℝ):ℂ)))) (x, p)
      ∂μI) (μJ.prod μJ) :=
    hInt3.integral_prod_right
  have hsliceD : ∀ p : ℝ × ℝ, (∫ x, (fun z : ℝ × ℝ × ℝ =>
      (w z.1 : ℂ) * ((a z.2.1 * conj (a z.2.2)) * (z.1:ℂ)^(4 + Complex.I*((z.2.1 - z.2.2 : ℝ):ℂ)))) (x, p) ∂μI)
      = (a p.1 * conj (a p.2)) * Z (p.1 - p.2) := by
    intro p
    have h1 : ∀ x : ℝ, (w x : ℂ) * ((a p.1 * conj (a p.2)) * (x:ℂ)^(4 + Complex.I*((p.1 - p.2 : ℝ):ℂ)))
        = (a p.1 * conj (a p.2)) * ((w x : ℂ) * (x:ℂ)^(4 + Complex.I*((p.1 - p.2 : ℝ):ℂ))) := by
      intro x; ring
    simp only []
    simp_rw [h1]
    rw [MeasureTheory.integral_const_mul]
    show (a p.1 * conj (a p.2)) * (∫ x, (w x : ℂ) * (x:ℂ)^(4 + Complex.I*((p.1 - p.2 : ℝ):ℂ)) ∂μI)
        = (a p.1 * conj (a p.2)) * Z (p.1 - p.2)
    congr 1
    show (∫ x, (w x : ℂ) * (x:ℂ)^(4 + Complex.I*((p.1 - p.2 : ℝ):ℂ)) ∂μI)
        = ∫ x in X * Real.exp (-1)..X * Real.exp 3, (w x : ℂ) * (x:ℂ)^(4 + Complex.I*((p.1 - p.2 : ℝ):ℂ))
    show (∫ x, (w x : ℂ) * (x:ℂ)^(4 + Complex.I*((p.1 - p.2 : ℝ):ℂ)) ∂(volume.restrict (Set.uIoc (X * Real.exp (-1)) (X * Real.exp 3))))
        = ∫ x in X * Real.exp (-1)..X * Real.exp 3, (w x : ℂ) * (x:ℂ)^(4 + Complex.I*((p.1 - p.2 : ℝ):ℂ))
    rw [Set.uIoc_of_le hab, intervalIntegral.integral_of_le hab]
  have hH : Integrable (fun p : ℝ × ℝ => (a p.1 * conj (a p.2)) * Z (p.1 - p.2)) (μJ.prod μJ) :=
    hMargB.congr (Filter.Eventually.of_forall hsliceD)
  have hMargA : Integrable (fun x => ∫ p, (fun z : ℝ × ℝ × ℝ =>
      (w z.1 : ℂ) * ((a z.2.1 * conj (a z.2.2)) * (z.1:ℂ)^(4 + Complex.I*((z.2.1 - z.2.2 : ℝ):ℂ)))) (x, p)
      ∂(μJ.prod μJ)) μI :=
    hInt3.integral_prod_left
  have hsliceG : ∀ x : ℝ, 0 < x → (∫ p : ℝ × ℝ, (fun z : ℝ × ℝ × ℝ =>
      (w z.1 : ℂ) * ((a z.2.1 * conj (a z.2.2)) * (z.1:ℂ)^(4 + Complex.I*((z.2.1 - z.2.2 : ℝ):ℂ)))) (x, p) ∂(μJ.prod μJ))
      = (w x : ℂ) * (∫ t in (-L)..L, ∫ s in (-L)..L, (a t * conj (a s)) * (x:ℂ)^(4 + Complex.I*((t - s : ℝ):ℂ))) := by
    intro x hx
    set f1 : ℝ → ℂ := fun t => a t * (x:ℂ)^(2 + Complex.I*(t:ℂ)) with hf1
    set f2 : ℝ → ℂ := fun s => conj (a s * (x:ℂ)^(2 + Complex.I*(s:ℂ))) with hf2
    have hpt : ∀ t s : ℝ, f1 t * f2 s = (a t * conj (a s)) * (x:ℂ)^(4 + Complex.I*((t - s : ℝ):ℂ)) := by
      intro t s
      simp only [hf1, hf2]
      exact frozen_l2_cpow hx a t s
    have hA : (∫ p : ℝ × ℝ, (a p.1 * conj (a p.2)) * (x:ℂ)^(4 + Complex.I*((p.1 - p.2 : ℝ):ℂ)) ∂(μJ.prod μJ))
        = (∫ t, f1 t ∂μJ) * (∫ s, f2 s ∂μJ) := by
      rw [show (fun p : ℝ × ℝ => (a p.1 * conj (a p.2)) * (x:ℂ)^(4 + Complex.I*((p.1 - p.2 : ℝ):ℂ)))
          = fun p : ℝ × ℝ => f1 p.1 * f2 p.2 from funext (fun p => (hpt p.1 p.2).symm)]
      exact MeasureTheory.integral_prod_mul f1 f2
    have hB : (∫ t in (-L)..L, ∫ s in (-L)..L, (a t * conj (a s)) * (x:ℂ)^(4 + Complex.I*((t - s : ℝ):ℂ)))
        = (∫ t, f1 t ∂μJ) * (∫ s, f2 s ∂μJ) := by
      have hinner : ∀ t : ℝ, (∫ s in (-L)..L, (a t * conj (a s)) * (x:ℂ)^(4 + Complex.I*((t - s : ℝ):ℂ)))
          = f1 t * (∫ s in (-L)..L, f2 s) := by
        intro t
        rw [← intervalIntegral.integral_const_mul]
        exact intervalIntegral.integral_congr (fun s _ => (hpt t s).symm)
      rw [show (fun t : ℝ => ∫ s in (-L)..L, (a t * conj (a s)) * (x:ℂ)^(4 + Complex.I*((t - s : ℝ):ℂ)))
          = fun t : ℝ => f1 t * (∫ s in (-L)..L, f2 s) from funext hinner]
      rw [intervalIntegral.integral_mul_const, hconv f1, hconv f2]
    simp only []
    rw [MeasureTheory.integral_const_mul]
    congr 1
    rw [hA, hB]
  have hIntG : Integrable (fun x : ℝ => (w x : ℂ) *
      (∫ t in (-L)..L, ∫ s in (-L)..L, (a t * conj (a s)) * (x:ℂ)^(4 + Complex.I*((t - s : ℝ):ℂ)))) μI := by
    refine hMargA.congr ?_
    have hμI' : μI = volume.restrict (Set.uIoc (X * Real.exp (-1)) (X * Real.exp 3)) := hμI
    rw [hμI']
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_uIoc] with x hx
    have hx' : x ∈ Set.Icc (X * Real.exp (-1)) (X * Real.exp 3) := by
      have h := Set.uIoc_subset_uIcc hx
      rwa [Set.uIcc_of_le hab] at h
    exact hsliceG x (lt_of_lt_of_le hxa_pos hx'.1)
  have hintG : IntervalIntegrable (fun x : ℝ => (w x : ℂ) *
      (∫ t in (-L)..L, ∫ s in (-L)..L, (a t * conj (a s)) * (x:ℂ)^(4 + Complex.I*((t - s : ℝ):ℂ))))
      volume (X * Real.exp (-1)) (X * Real.exp 3) := by
    rw [intervalIntegrable_iff]
    change Integrable _ (volume.restrict (Set.uIoc (X * Real.exp (-1)) (X * Real.exp 3)))
    rw [← hμI]
    exact hIntG
  have hre : (∫ x in X * Real.exp (-1)..X * Real.exp 3,
        w x * ‖∫ t in (-L)..L, a t * (x:ℂ)^(2 + Complex.I*(t:ℂ))‖^2)
      = (∫ x in X * Real.exp (-1)..X * Real.exp 3, (w x : ℂ) *
          (∫ t in (-L)..L, ∫ s in (-L)..L, (a t * conj (a s)) * (x:ℂ)^(4 + Complex.I*((t - s : ℝ):ℂ)))).re := by
    have hpt : ∀ x ∈ Set.uIcc (X * Real.exp (-1)) (X * Real.exp 3),
        w x * ‖∫ t in (-L)..L, a t * (x:ℂ)^(2 + Complex.I*(t:ℂ))‖^2
          = ((w x : ℂ) * (∫ t in (-L)..L, ∫ s in (-L)..L, (a t * conj (a s)) * (x:ℂ)^(4 + Complex.I*((t - s : ℝ):ℂ)))).re := by
      intro x hx
      have hxpos : 0 < x := by
        rw [Set.uIcc_of_le hab] at hx
        exact lt_of_lt_of_le hxa_pos hx.1
      have hfcont : Continuous (fun t : ℝ => a t * (x:ℂ)^(2 + Complex.I*(t:ℂ))) := by
        refine Continuous.mul ha ?_
        rw [show (fun t : ℝ => (x:ℂ)^(2 + Complex.I*(t:ℂ)))
            = fun t : ℝ => Complex.exp (Complex.log (x:ℂ) * (2 + Complex.I*(t:ℂ))) from by
              funext t; rw [Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hxpos.ne')]]
        fun_prop
      have hsq := frozen_l2_sq_expand (-L) L (fun t : ℝ => a t * (x:ℂ)^(2 + Complex.I*(t:ℂ))) hfcont
      have hdouble : (∫ t in (-L)..L, ∫ s in (-L)..L, (a t * (x:ℂ)^(2 + Complex.I*(t:ℂ))) * conj (a s * (x:ℂ)^(2 + Complex.I*(s:ℂ))))
          = (∫ t in (-L)..L, ∫ s in (-L)..L, (a t * conj (a s)) * (x:ℂ)^(4 + Complex.I*((t - s : ℝ):ℂ))) := by
        refine intervalIntegral.integral_congr (fun t _ => ?_)
        refine intervalIntegral.integral_congr (fun s _ => ?_)
        exact frozen_l2_cpow hxpos a t s
      rw [hsq, hdouble, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
      ring
    rw [intervalIntegral.integral_congr hpt]
    exact ContinuousLinearMap.intervalIntegral_comp_comm Complex.reCLM hintG
  have hFub' : (∫ x in X * Real.exp (-1)..X * Real.exp 3, (w x : ℂ) *
        (∫ t in (-L)..L, ∫ s in (-L)..L, (a t * conj (a s)) * (x:ℂ)^(4 + Complex.I*((t - s : ℝ):ℂ))))
      = ∫ t in (-L)..L, ∫ s in (-L)..L, (a t * conj (a s)) * Z (t - s) := by
    have hstep1 : (∫ x in X * Real.exp (-1)..X * Real.exp 3, (w x : ℂ) *
          (∫ t in (-L)..L, ∫ s in (-L)..L, (a t * conj (a s)) * (x:ℂ)^(4 + Complex.I*((t - s : ℝ):ℂ))))
        = ∫ x, (∫ p : ℝ × ℝ, (fun z : ℝ × ℝ × ℝ =>
            (w z.1 : ℂ) * ((a z.2.1 * conj (a z.2.2)) * (z.1:ℂ)^(4 + Complex.I*((z.2.1 - z.2.2 : ℝ):ℂ)))) (x, p)
            ∂(μJ.prod μJ)) ∂μI := by
      rw [hconvX (fun x => (w x : ℂ) *
          (∫ t in (-L)..L, ∫ s in (-L)..L, (a t * conj (a s)) * (x:ℂ)^(4 + Complex.I*((t - s : ℝ):ℂ))))]
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_uIoc] with x hx
      have hx' : x ∈ Set.Icc (X * Real.exp (-1)) (X * Real.exp 3) := by
        have h := Set.uIoc_subset_uIcc hx
        rwa [Set.uIcc_of_le hab] at h
      exact (hsliceG x (lt_of_lt_of_le hxa_pos hx'.1)).symm
    have hstep2 : (∫ x, (∫ p : ℝ × ℝ, (fun z : ℝ × ℝ × ℝ =>
            (w z.1 : ℂ) * ((a z.2.1 * conj (a z.2.2)) * (z.1:ℂ)^(4 + Complex.I*((z.2.1 - z.2.2 : ℝ):ℂ)))) (x, p)
            ∂(μJ.prod μJ)) ∂μI)
        = ∫ p, (∫ x, (fun z : ℝ × ℝ × ℝ =>
            (w z.1 : ℂ) * ((a z.2.1 * conj (a z.2.2)) * (z.1:ℂ)^(4 + Complex.I*((z.2.1 - z.2.2 : ℝ):ℂ)))) (x, p)
            ∂μI) ∂(μJ.prod μJ) :=
      MeasureTheory.integral_integral_swap (f := fun x (p : ℝ × ℝ) => (fun z : ℝ × ℝ × ℝ =>
            (w z.1 : ℂ) * ((a z.2.1 * conj (a z.2.2)) * (z.1:ℂ)^(4 + Complex.I*((z.2.1 - z.2.2 : ℝ):ℂ)))) (x, p)) hInt3
    have hstep3 : (∫ p, (∫ x, (fun z : ℝ × ℝ × ℝ =>
            (w z.1 : ℂ) * ((a z.2.1 * conj (a z.2.2)) * (z.1:ℂ)^(4 + Complex.I*((z.2.1 - z.2.2 : ℝ):ℂ)))) (x, p)
            ∂μI) ∂(μJ.prod μJ))
        = ∫ p, ((a p.1 * conj (a p.2)) * Z (p.1 - p.2)) ∂(μJ.prod μJ) := by
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall (fun p => ?_))
      simp only []
      exact hsliceD p
    have hstep4 : (∫ p, ((a p.1 * conj (a p.2)) * Z (p.1 - p.2)) ∂(μJ.prod μJ))
        = ∫ t, ∫ s, (a t * conj (a s)) * Z (t - s) ∂μJ ∂μJ :=
      MeasureTheory.integral_prod (fun p : ℝ × ℝ => (a p.1 * conj (a p.2)) * Z (p.1 - p.2)) hH
    have hstep5 : (∫ t, ∫ s, (a t * conj (a s)) * Z (t - s) ∂μJ ∂μJ)
        = ∫ t in (-L)..L, ∫ s in (-L)..L, (a t * conj (a s)) * Z (t - s) := by
      rw [← hconvI (fun t => ∫ s, (a t * conj (a s)) * Z (t - s) ∂μJ)]
      refine intervalIntegral.integral_congr (fun t _ => ?_)
      rw [← hconvI (fun s => (a t * conj (a s)) * Z (t - s))]
    rw [hstep1, hstep2, hstep3, hstep4, hstep5]
  have hmain : (∫ x in X * Real.exp (-1)..X * Real.exp 3, w x * ‖∫ t in (-L)..L, a t * (x:ℂ)^(2 + Complex.I*(t:ℂ))‖^2)
      = (∫ t in (-L)..L, ∫ s in (-L)..L, (a t * conj (a s)) * Z (t - s)).re := by
    rw [hre, hFub']
  have hS_eq : (∫ t in (-L)..L, ∫ s in (-L)..L, (a t * conj (a s)) * Z (t - s))
      = ∫ p : ℝ × ℝ, (a p.1 * conj (a p.2)) * Z (p.1 - p.2) ∂(μJ.prod μJ) := by
    have hIP : (∫ p : ℝ × ℝ, (a p.1 * conj (a p.2)) * Z (p.1 - p.2) ∂(μJ.prod μJ))
        = ∫ t, ∫ s, (a t * conj (a s)) * Z (t - s) ∂μJ ∂μJ :=
      MeasureTheory.integral_prod (fun p : ℝ × ℝ => (a p.1 * conj (a p.2)) * Z (p.1 - p.2)) hH
    rw [hconvI (fun t => ∫ s in (-L)..L, (a t * conj (a s)) * Z (t - s))]
    rw [show (fun t : ℝ => ∫ s in (-L)..L, (a t * conj (a s)) * Z (t - s))
        = fun t : ℝ => ∫ s, (a t * conj (a s)) * Z (t - s) ∂μJ from
        funext (fun t => hconvI (fun s => (a t * conj (a s)) * Z (t - s)))]
    exact hIP.symm
  have hcont1 : Continuous (fun u : ℝ => C0 * X^5/(1+u^2)) := by
    rw [show (fun u : ℝ => C0 * X^5/(1+u^2)) = fun u : ℝ => (C0*X^5) * (1+u^2)⁻¹ from by
      funext u; rw [div_eq_mul_inv]]
    exact ((by fun_prop : Continuous (fun u : ℝ => (1:ℝ) + u^2)).inv₀ (fun u => by positivity)).const_mul _
  have hcont2 : Continuous (fun u : ℝ => (1+u^2)⁻¹) :=
    (by fun_prop : Continuous (fun u : ℝ => (1:ℝ) + u^2)).inv₀ (fun u => by positivity)
  have hintg2 : Integrable (fun p : ℝ × ℝ => ‖a p.1‖ * ‖a p.2‖ * (C0 * X^5/(1 + (p.1 - p.2)^2))) (μJ.prod μJ) :=
    hJint (fun u => C0 * X^5/(1+u^2)) hcont1
  have hint2 : Integrable (fun p : ℝ × ℝ => ‖a p.1‖ * ‖a p.2‖ * (1 + (p.1 - p.2)^2)⁻¹) (μJ.prod μJ) :=
    hJint (fun u => (1+u^2)⁻¹) hcont2
  have hinner2 : (∫ p : ℝ × ℝ, ‖a p.1‖ * ‖a p.2‖ * (1 + (p.1 - p.2)^2)⁻¹ ∂(μJ.prod μJ))
      = ∫ t in (-L)..L, ∫ s in (-L)..L, ‖a t‖ * ‖a s‖ * (1 + (t - s)^2)⁻¹ := by
    have hIP2 : (∫ p : ℝ × ℝ, ‖a p.1‖ * ‖a p.2‖ * (1 + (p.1 - p.2)^2)⁻¹ ∂(μJ.prod μJ))
        = ∫ t, ∫ s, ‖a t‖ * ‖a s‖ * (1 + (t - s)^2)⁻¹ ∂μJ ∂μJ :=
      MeasureTheory.integral_prod (fun p : ℝ × ℝ => ‖a p.1‖ * ‖a p.2‖ * (1 + (p.1 - p.2)^2)⁻¹) hint2
    rw [hIP2]
    rw [hconvIR (fun t => ∫ s in (-L)..L, ‖a t‖ * ‖a s‖ * (1 + (t - s)^2)⁻¹)]
    rw [show (fun t : ℝ => ∫ s in (-L)..L, ‖a t‖ * ‖a s‖ * (1 + (t - s)^2)⁻¹)
        = fun t : ℝ => ∫ s, ‖a t‖ * ‖a s‖ * (1 + (t - s)^2)⁻¹ ∂μJ from
        funext (fun t => hconvIR (fun s => ‖a t‖ * ‖a s‖ * (1 + (t - s)^2)⁻¹))]
  have hbound : ‖∫ p : ℝ × ℝ, (a p.1 * conj (a p.2)) * Z (p.1 - p.2) ∂(μJ.prod μJ)‖
      ≤ C0 * X^5 * Real.pi * (∫ t in (-L)..L, ‖a t‖^2) := by
    calc ‖∫ p : ℝ × ℝ, (a p.1 * conj (a p.2)) * Z (p.1 - p.2) ∂(μJ.prod μJ)‖
        ≤ ∫ p, ‖(a p.1 * conj (a p.2)) * Z (p.1 - p.2)‖ ∂(μJ.prod μJ) :=
          MeasureTheory.norm_integral_le_integral_norm _
      _ = ∫ p, ‖a p.1‖ * ‖a p.2‖ * ‖Z (p.1 - p.2)‖ ∂(μJ.prod μJ) := by
          rw [show (fun p : ℝ × ℝ => ‖(a p.1 * conj (a p.2)) * Z (p.1 - p.2)‖)
              = fun p : ℝ × ℝ => ‖a p.1‖ * ‖a p.2‖ * ‖Z (p.1 - p.2)‖ from by
            funext p; rw [norm_mul, norm_mul, Complex.norm_conj]]
      _ ≤ ∫ p, ‖a p.1‖ * ‖a p.2‖ * (C0 * X^5/(1 + (p.1 - p.2)^2)) ∂(μJ.prod μJ) := by
          have hHn : Integrable (fun p : ℝ × ℝ => ‖a p.1‖ * ‖a p.2‖ * ‖Z (p.1 - p.2)‖) (μJ.prod μJ) :=
            hH.norm.congr (Filter.Eventually.of_forall (fun p => by
              simp only []
              rw [norm_mul, norm_mul, Complex.norm_conj]))
          refine MeasureTheory.integral_mono_ae hHn hintg2 ?_
          filter_upwards with p
          gcongr
          exact htrans (p.1 - p.2)
      _ = C0 * X^5 * ∫ p, ‖a p.1‖ * ‖a p.2‖ * (1 + (p.1 - p.2)^2)⁻¹ ∂(μJ.prod μJ) := by
          rw [show (fun p : ℝ × ℝ => ‖a p.1‖ * ‖a p.2‖ * (C0 * X^5/(1 + (p.1 - p.2)^2)))
              = fun p : ℝ × ℝ => C0 * X^5 * (‖a p.1‖ * ‖a p.2‖ * (1 + (p.1 - p.2)^2)⁻¹) from by
                funext p; rw [div_eq_mul_inv]; ring]
          rw [MeasureTheory.integral_const_mul]
      _ = C0 * X^5 * (∫ t in (-L)..L, ∫ s in (-L)..L, ‖a t‖ * ‖a s‖ * (1 + (t - s)^2)⁻¹) := by
          rw [hinner2]
      _ ≤ C0 * X^5 * (Real.pi * ∫ t in (-L)..L, ‖a t‖^2) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact frozen_l2_schur (fun t => ‖a t‖) ha.norm (fun t => norm_nonneg _) (-L) L hlohi
      _ = C0 * X^5 * Real.pi * (∫ t in (-L)..L, ‖a t‖^2) := by ring
  calc (∫ x in X * Real.exp (-1)..X * Real.exp 3, w x * ‖∫ t in (-L)..L, a t * (x:ℂ)^(2 + Complex.I*(t:ℂ))‖^2)
      = (∫ t in (-L)..L, ∫ s in (-L)..L, (a t * conj (a s)) * Z (t - s)).re := hmain
    _ = (∫ p : ℝ × ℝ, (a p.1 * conj (a p.2)) * Z (p.1 - p.2) ∂(μJ.prod μJ)).re := by rw [hS_eq]
    _ ≤ C0 * X^5 * Real.pi * (∫ t in (-L)..L, ‖a t‖^2) := le_trans (Complex.re_le_norm _) hbound


/-- The frozen `L²` bound: the target lemma. -/
theorem frozen_l2_bound (X L : ℝ) (C0 : ℝ) (hC0 : 0 < C0) (hX : 1 ≤ X) (hL : 0 ≤ L)
    (htrans : ∀ Δ : ℝ, ‖∫ x in X * Real.exp (-1)..X * Real.exp 3,
        (mwt X x : ℂ) * (x:ℂ)^(4 + Complex.I*(Δ:ℂ))‖ ≤ C0 * X^5/(1+Δ^2))
    (a : ℝ → ℂ) (ha : Continuous a) :
    (1/X) * (∫ x in X * Real.exp (-1)..X * Real.exp 3,
        mwt X x * ‖∫ t in (-L)..L, a t * (x:ℂ)^(2 + Complex.I*(t:ℂ))‖^2)
      ≤ C0 * Real.pi * X^4 * (∫ t in (-L)..L, ‖a t‖^2) := by
  have hXpos : 0 < X := lt_of_lt_of_le one_pos hX
  have hcore := frozen_l2_core X L C0 hC0 hXpos hL (fun x => mwt X x) a
    (frozen_l2_cont X L hXpos a ha) htrans ha
  have hXne : X ≠ 0 := hXpos.ne'
  calc (1/X) * (∫ x in X * Real.exp (-1)..X * Real.exp 3,
          mwt X x * ‖∫ t in (-L)..L, a t * (x:ℂ)^(2 + Complex.I*(t:ℂ))‖^2)
      ≤ (1/X) * (C0 * X^5 * Real.pi * (∫ t in (-L)..L, ‖a t‖^2)) :=
        mul_le_mul_of_nonneg_left hcore (by positivity)
    _ = C0 * Real.pi * X^4 * (∫ t in (-L)..L, ‖a t‖^2) := by
        have hpow : (1/X : ℝ) * X^5 = X^4 := by
          rw [one_div, inv_mul_eq_div, div_eq_iff hXne]
          ring
        rw [show (1/X) * (C0 * X^5 * Real.pi * (∫ t in (-L)..L, ‖a t‖^2))
            = C0 * Real.pi * ((1/X) * X^5) * (∫ t in (-L)..L, ‖a t‖^2) by ring]
        rw [hpow]

end Work.BMF
