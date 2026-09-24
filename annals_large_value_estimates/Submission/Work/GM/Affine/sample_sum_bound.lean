import Mathlib
import Submission.Work.GM.Affine.setup
import Submission.Work.GM.Affine.periodization_identity
import Submission.Work.GM.Affine.card_int_in_interval_le
import Submission.Commons.Analysis.Integration.integral_cexp_two_pi_mul_int
import Submission.Commons.Analysis.Integration.integral_mul_sq_le

/-!
# Sampling / large-sieve bound for the affine sums of GM §9

For a continuous `H : ℝ → ℂ` vanishing off `[-R,R]`, and complex coefficients `c k`, the
trigonometric polynomial `u ↦ ∑ k ∈ s, c k * e_{-k}(u)` (with `e_{-k}(u) = exp(-2πi u k)`) is
`1`-periodic up to a unimodular factor, so the sampling inequality

`∫_{[-R,R]} ‖∑_k c k e_{-k}‖² ≤ (2R+2) ∑_k ‖c k‖²`

holds (one period on `[0,1]` gives `∑_k ‖c k‖²` by orthogonality of the characters).  Feeding this
into Cauchy–Schwarz gives the adjoint ("dual") estimate, from which the sampling sum bound for the
frequencies `k + α` follows by duality.
-/

namespace Work.GM.Affine

open Complex MeasureTheory Finset
open scoped BigOperators

set_option autoImplicit false

noncomputable section

@[fun_prop] lemma continuous_efun : Continuous efun := by unfold efun; fun_prop

lemma conj_efun (t : ℝ) : (starRingEnd ℂ) (efun t) = efun (-t) := by
  unfold efun
  rw [← Complex.exp_conj]
  congr 1
  push_cast
  simp only [map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I]
  ring

lemma integral_efun_int (a : ℤ) :
    (∫ u in (0:ℝ)..1, efun (-(u * (a:ℝ)))) = if a = 0 then 1 else 0 := by
  have hpt : ∀ u : ℝ, efun (-(u * (a:ℝ)))
      = Complex.exp (↑(2 * Real.pi * u * ((-a:ℤ):ℝ)) * Complex.I) := by
    intro u
    unfold efun
    congr 1
    push_cast
    ring
  simp_rw [hpt]
  rw [Commons.Analysis.Integration.integral_cexp_two_pi_mul_int (-a)]
  by_cases h : a = 0
  · subst h; simp
  · rw [if_neg h, if_neg (by omega)]

lemma integral_efun_mul_conj (k l : ℤ) :
    (∫ u in (0:ℝ)..1, efun (-(u*(k:ℝ))) * (starRingEnd ℂ) (efun (-(u*(l:ℝ)))))
      = if k = l then 1 else 0 := by
  have hpt : ∀ u : ℝ, efun (-(u*(k:ℝ))) * (starRingEnd ℂ) (efun (-(u*(l:ℝ))))
      = efun (-(u*((k-l:ℤ):ℝ))) := by
    intro u
    rw [conj_efun, ← efun_add]
    congr 1
    push_cast
    ring
  simp_rw [hpt]
  rw [integral_efun_int (k-l)]
  by_cases h : k = l
  · subst h; simp
  · rw [if_neg h, if_neg (by omega)]

lemma efun_int (j : ℤ) : efun (j:ℝ) = 1 := by
  unfold efun
  push_cast
  rw [show 2 * (Real.pi : ℂ) * Complex.I * (j:ℂ)
      = (j:ℂ) * (2 * (Real.pi : ℂ) * Complex.I) by ring]
  exact Complex.exp_int_mul_two_pi_mul_I j

lemma efun_neg_int (k : ℤ) : efun (-(k:ℝ)) = 1 := by
  simpa using efun_int (-k)

lemma integral_finsum_mul_conj (s : Finset ℤ) (c : ℤ → ℂ) (m : ℤ) :
    (∫ u in (0:ℝ)..1, (∑ k ∈ s, c k * efun (-(u*(k:ℝ))))
        * (starRingEnd ℂ) (efun (-(u*(m:ℝ)))))
      = if m ∈ s then c m else 0 := by
  have hpt : ∀ u : ℝ, (∑ k ∈ s, c k * efun (-(u*(k:ℝ))))
        * (starRingEnd ℂ) (efun (-(u*(m:ℝ))))
      = ∑ k ∈ s, c k * (efun (-(u*(k:ℝ))) * (starRingEnd ℂ) (efun (-(u*(m:ℝ))))) := by
    intro u
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl (fun k _ => by ring)
  rw [show (∫ u in (0:ℝ)..1, (∑ k ∈ s, c k * efun (-(u*(k:ℝ))))
          * (starRingEnd ℂ) (efun (-(u*(m:ℝ)))))
      = ∫ u in (0:ℝ)..1, ∑ k ∈ s,
          c k * (efun (-(u*(k:ℝ))) * (starRingEnd ℂ) (efun (-(u*(m:ℝ))))) from
        intervalIntegral.integral_congr (fun u _ => hpt u)]
  rw [intervalIntegral.integral_finsetSum
      (fun k _ => Continuous.intervalIntegrable (by fun_prop) 0 1)]
  simp only [intervalIntegral.integral_const_mul, integral_efun_mul_conj]
  rw [show (∑ k ∈ s, c k * (if k = m then (1:ℂ) else 0))
      = ∑ k ∈ s, (if k = m then c k else 0) from
        Finset.sum_congr rfl (fun k _ => by by_cases hk : k = m <;> simp [hk])]
  rw [Finset.sum_ite_eq']

lemma integral_normSq_finsum (s : Finset ℤ) (c : ℤ → ℂ) :
    (∫ u in (0:ℝ)..1, ‖(∑ k ∈ s, c k * efun (-(u*(k:ℝ))))‖^2) = ∑ k ∈ s, ‖c k‖^2 := by
  have key : (∫ u in (0:ℝ)..1, ((‖(∑ k ∈ s, c k * efun (-(u*(k:ℝ))))‖^2 : ℝ) : ℂ))
      = ∫ u in (0:ℝ)..1, (∑ k ∈ s, c k * efun (-(u*(k:ℝ))))
          * (starRingEnd ℂ) (∑ k ∈ s, c k * efun (-(u*(k:ℝ)))) := by
    refine intervalIntegral.integral_congr (fun u _ => ?_)
    rw [← Complex.normSq_eq_norm_sq]
    exact (Complex.mul_conj _).symm
  rw [intervalIntegral.integral_ofReal] at key
  have key2 : (∫ u in (0:ℝ)..1, (∑ k ∈ s, c k * efun (-(u*(k:ℝ))))
        * (starRingEnd ℂ) (∑ k ∈ s, c k * efun (-(u*(k:ℝ)))))
      = ((∑ k ∈ s, ‖c k‖^2 : ℝ) : ℂ) := by
    have hpt : ∀ u : ℝ, (∑ k ∈ s, c k * efun (-(u*(k:ℝ))))
          * (starRingEnd ℂ) (∑ k ∈ s, c k * efun (-(u*(k:ℝ))))
        = ∑ l ∈ s, (starRingEnd ℂ) (c l)
            * ((∑ k ∈ s, c k * efun (-(u*(k:ℝ))))
                * (starRingEnd ℂ) (efun (-(u*(l:ℝ))))) := by
      intro u
      have hsum : (starRingEnd ℂ) (∑ k ∈ s, c k * efun (-(u*(k:ℝ))))
          = ∑ k ∈ s, (starRingEnd ℂ) (c k) * (starRingEnd ℂ) (efun (-(u*(k:ℝ)))) := by
        rw [map_sum]
        exact Finset.sum_congr rfl (fun k _ => by rw [map_mul])
      rw [hsum, Finset.mul_sum]
      exact Finset.sum_congr rfl (fun l _ => by ring)
    rw [show (∫ u in (0:ℝ)..1, (∑ k ∈ s, c k * efun (-(u*(k:ℝ))))
            * (starRingEnd ℂ) (∑ k ∈ s, c k * efun (-(u*(k:ℝ)))))
        = ∫ u in (0:ℝ)..1, ∑ l ∈ s, (starRingEnd ℂ) (c l)
            * ((∑ k ∈ s, c k * efun (-(u*(k:ℝ))))
                * (starRingEnd ℂ) (efun (-(u*(l:ℝ))))) from
          intervalIntegral.integral_congr (fun u _ => hpt u)]
    rw [intervalIntegral.integral_finsetSum
        (fun l _ => Continuous.intervalIntegrable (by fun_prop) 0 1)]
    simp only [intervalIntegral.integral_const_mul, integral_finsum_mul_conj]
    rw [show (∑ l ∈ s, (starRingEnd ℂ) (c l) * (if l ∈ s then c l else 0))
        = ∑ l ∈ s, ((‖c l‖^2 : ℝ) : ℂ) from
          Finset.sum_congr rfl (fun l hl => by
            rw [if_pos hl, ← Complex.normSq_eq_norm_sq, ← Complex.mul_conj]; ring)]
    exact (Complex.ofReal_sum s (fun l => ‖c l‖^2)).symm
  exact Complex.ofReal_injective (key.trans key2)

lemma periodic_normSq_finsum (s : Finset ℤ) (c : ℤ → ℂ) :
    Function.Periodic (fun u : ℝ => ‖(∑ k ∈ s, c k * efun (-(u*(k:ℝ))))‖^2) 1 := by
  intro u
  have hQ : (∑ k ∈ s, c k * efun (-((u+1)*(k:ℝ)))) = ∑ k ∈ s, c k * efun (-(u*(k:ℝ))) := by
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [show -((u+1)*(k:ℝ)) = -(u*(k:ℝ)) + (-(k:ℝ)) by ring, efun_add, efun_neg_int]
    ring
  change ‖(∑ k ∈ s, c k * efun (-((u+1)*(k:ℝ))))‖^2
      = ‖(∑ k ∈ s, c k * efun (-(u*(k:ℝ))))‖^2
  rw [hQ]

lemma interval_integral_normSq_finsum_le {R : ℝ} (hR₀ : 0 ≤ R) (s : Finset ℤ) (c : ℤ → ℂ) :
    (∫ u in (-R)..R, ‖(∑ k ∈ s, c k * efun (-(u*(k:ℝ))))‖^2)
      ≤ (2*R+2) * ∑ k ∈ s, ‖c k‖^2 := by
  set m : ℕ := Nat.ceil R with hm
  have hmR : R ≤ (m:ℝ) := Nat.le_ceil R
  have hmlt : (m:ℝ) < R + 1 := Nat.ceil_lt_add_one hR₀
  have hcont : Continuous (fun u : ℝ => ‖(∑ k ∈ s, c k * efun (-(u*(k:ℝ))))‖^2) := by fun_prop
  have hint : ∀ a b : ℝ,
      IntervalIntegrable (fun u : ℝ => ‖(∑ k ∈ s, c k * efun (-(u*(k:ℝ))))‖^2) volume a b :=
    fun a b => hcont.intervalIntegrable a b
  have hper : Function.Periodic (fun u : ℝ => ‖(∑ k ∈ s, c k * efun (-(u*(k:ℝ))))‖^2) 1 :=
    periodic_normSq_finsum s c
  have hstep1 : (∫ u in (-R)..R, ‖(∑ k ∈ s, c k * efun (-(u*(k:ℝ))))‖^2)
      ≤ ∫ u in (-(m:ℝ))..(m:ℝ), ‖(∑ k ∈ s, c k * efun (-(u*(k:ℝ))))‖^2 := by
    refine intervalIntegral.integral_mono_interval (by linarith) (by linarith) (by linarith)
      (Filter.Eventually.of_forall (fun x => by positivity)) (hint _ _)
  have hstep2 : (∫ u in (-(m:ℝ))..(m:ℝ), ‖(∑ k ∈ s, c k * efun (-(u*(k:ℝ))))‖^2)
      = (2*(m:ℝ)) * ∫ u in (0:ℝ)..1, ‖(∑ k ∈ s, c k * efun (-(u*(k:ℝ))))‖^2 := by
    have h := hper.intervalIntegral_add_zsmul_eq (2*(m:ℤ)) (-(m:ℝ)) hint
    rw [show (-(m:ℝ) + (2*(m:ℤ)) • (1:ℝ)) = (m:ℝ) by
      rw [zsmul_eq_mul]; push_cast; try ring] at h
    rw [h, hper.intervalIntegral_add_eq (-(m:ℝ)) 0, zero_add, zsmul_eq_mul]
    push_cast
    try ring
  have h01 := integral_normSq_finsum s c
  have hsum_nonneg : (0:ℝ) ≤ ∑ k ∈ s, ‖c k‖^2 := Finset.sum_nonneg (fun k _ => by positivity)
  calc (∫ u in (-R)..R, ‖(∑ k ∈ s, c k * efun (-(u*(k:ℝ))))‖^2)
      ≤ ∫ u in (-(m:ℝ))..(m:ℝ), ‖(∑ k ∈ s, c k * efun (-(u*(k:ℝ))))‖^2 := hstep1
    _ = (2*(m:ℝ)) * ∫ u in (0:ℝ)..1, ‖(∑ k ∈ s, c k * efun (-(u*(k:ℝ))))‖^2 := hstep2
    _ = (2*(m:ℝ)) * ∑ k ∈ s, ‖c k‖^2 := by rw [h01]
    _ ≤ (2*R+2) * ∑ k ∈ s, ‖c k‖^2 :=
        mul_le_mul_of_nonneg_right (by linarith) hsum_nonneg

lemma norm_finsum_shift (s : Finset ℤ) (c : ℤ → ℂ) (α : ℝ) (u : ℝ) :
    ‖∑ k ∈ s, c k * efun (-(u*((k:ℝ)+α)))‖ = ‖∑ k ∈ s, c k * efun (-(u*(k:ℝ)))‖ := by
  have hshift : (∑ k ∈ s, c k * efun (-(u*((k:ℝ)+α))))
      = (∑ k ∈ s, c k * efun (-(u*(k:ℝ)))) * efun (-(u*α)) := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [show -(u*((k:ℝ)+α)) = -(u*(k:ℝ)) + (-(u*α)) by ring, efun_add]
    ring
  rw [hshift, norm_mul, norm_efun, mul_one]

/-- **Dual (adjoint) form of the sampling bound.**  For any coefficients `c : ℤ → ℂ`,

`‖∑_k c k * ∫ H(u) e_{-k-α}(u) du‖² ≤ (2R+2) (∑_k ‖c k‖²) ∫ ‖H‖²`.

This is Cauchy–Schwarz applied to `∫ (∑_k c k e_{-k-α}) H`, together with the one-period
orthogonality bound `interval_integral_normSq_finsum_le` for the trigonometric polynomial. -/
lemma dual_bound {H : ℝ → ℂ} (hH : Continuous H) {R : ℝ} (hR₀ : 0 ≤ R)
    (hR : ∀ y : ℝ, R < |y| → H y = 0) (α : ℝ) (s : Finset ℤ) (c : ℤ → ℂ) :
    ‖∑ k ∈ s, c k * (∫ u : ℝ, efun (-(u*((k:ℝ)+α))) * H u)‖^2
      ≤ (2*R+2) * (∑ k ∈ s, ‖c k‖^2) * (∫ u : ℝ, ‖H u‖^2) := by
  have hRle : -R ≤ R := by linarith
  have hzero : ∀ x : ℝ, x ∉ Set.Icc (-R) R → H x = 0 := by
    intro x hx
    apply hR
    rw [Set.mem_Icc, not_and_or] at hx
    rcases hx with hx | hx
    · rw [not_le] at hx
      rw [abs_of_neg (by linarith)]; linarith
    · rw [not_le] at hx
      rw [abs_of_pos (by linarith)]; linarith
  set G : ℝ → ℂ := fun u => ∑ k ∈ s, c k * efun (-(u*((k:ℝ)+α))) with hG
  set Q : ℝ → ℂ := fun u => ∑ k ∈ s, c k * efun (-(u*(k:ℝ))) with hQ
  have hGcont : Continuous G := by rw [hG]; fun_prop
  have hQcont : Continuous Q := by rw [hQ]; fun_prop
  have hGnQ : ∀ u : ℝ, ‖G u‖ = ‖Q u‖ := fun u => by
    simp only [hG, hQ]; exact norm_finsum_shift s c α u
  have hfin : (volume : Measure ℝ) (Set.Icc (-R) R) < ⊤ := isCompact_Icc.measure_lt_top
  have hIn : ∀ᵐ x ∂(volume.restrict (Set.Icc (-R) R)), x ∈ Set.Icc (-R) R :=
    ae_restrict_mem measurableSet_Icc
  obtain ⟨CG, hCG⟩ := isCompact_Icc.exists_bound_of_continuousOn (f := G) hGcont.continuousOn
  obtain ⟨CH, hCH⟩ := isCompact_Icc.exists_bound_of_continuousOn (f := H) hH.continuousOn
  -- integrability of each summand on the finite measure `volume.restrict (Icc (-R) R)`
  have hIntegrand : ∀ k : ℤ, IntegrableOn (fun u => c k * (efun (-(u*((k:ℝ)+α))) * H u))
      (Set.Icc (-R) R) := by
    intro k
    refine IntegrableOn.of_bound hfin (by fun_prop : Continuous
      (fun u => c k * (efun (-(u*((k:ℝ)+α))) * H u))).aestronglyMeasurable (‖c k‖ * CH) ?_
    filter_upwards [hIn] with x hx
    have h1 : ‖efun (-(x*((k:ℝ)+α)))‖ = 1 := norm_efun _
    simp only [norm_mul, h1, one_mul]
    exact mul_le_mul_of_nonneg_left (hCH x hx) (norm_nonneg _)
  -- the sum of integrals is the integral of `G * H`
  have hsum_eq : (∑ k ∈ s, c k * (∫ u : ℝ, efun (-(u*((k:ℝ)+α))) * H u))
      = ∫ u in Set.Icc (-R) R, G u * H u := by
    have hterm : ∀ k : ℤ, (∫ u : ℝ, efun (-(u*((k:ℝ)+α))) * H u)
        = ∫ u in Set.Icc (-R) R, efun (-(u*((k:ℝ)+α))) * H u := fun k =>
      (MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
        (fun x hx => by rw [hzero x hx, mul_zero])).symm
    have hcongr1 : ∀ u ∈ Set.Icc (-R) R, G u * H u
        = ∑ k ∈ s, c k * (efun (-(u*((k:ℝ)+α))) * H u) := by
      intro u _
      simp only [hG, Finset.sum_mul]
      exact Finset.sum_congr rfl (fun k _ => by ring)
    calc (∑ k ∈ s, c k * (∫ u : ℝ, efun (-(u*((k:ℝ)+α))) * H u))
        = ∑ k ∈ s, c k * (∫ u in Set.Icc (-R) R, efun (-(u*((k:ℝ)+α))) * H u) :=
          Finset.sum_congr rfl (fun k _ => by rw [hterm k])
      _ = ∑ k ∈ s, ∫ u in Set.Icc (-R) R, c k * (efun (-(u*((k:ℝ)+α))) * H u) :=
          Finset.sum_congr rfl (fun k _ => (MeasureTheory.integral_const_mul (c k) _).symm)
      _ = ∫ u in Set.Icc (-R) R, ∑ k ∈ s, c k * (efun (-(u*((k:ℝ)+α))) * H u) :=
          (MeasureTheory.integral_finsetSum s
            (f := fun k u => c k * (efun (-(u*((k:ℝ)+α))) * H u))
            (fun k _ => hIntegrand k)).symm
      _ = ∫ u in Set.Icc (-R) R, G u * H u :=
          (MeasureTheory.setIntegral_congr_fun measurableSet_Icc hcongr1).symm
  -- Cauchy–Schwarz on `Icc (-R) R`
  have hInt1 : IntegrableOn (fun x => ‖G x‖ * ‖H x‖) (Set.Icc (-R) R) := by
    refine IntegrableOn.of_bound hfin (hGcont.norm.mul hH.norm).aestronglyMeasurable (CG*CH) ?_
    filter_upwards [hIn] with x hx
    rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
    exact mul_le_mul (hCG x hx) (hCH x hx) (norm_nonneg _) (le_trans (norm_nonneg _) (hCG x hx))
  have hInt2 : IntegrableOn (fun x => ‖G x‖^2) (Set.Icc (-R) R) := by
    refine IntegrableOn.of_bound hfin (hGcont.norm.pow 2).aestronglyMeasurable (CG^2) ?_
    filter_upwards [hIn] with x hx
    rw [Real.norm_of_nonneg (by positivity)]
    nlinarith [hCG x hx, norm_nonneg (G x)]
  have hInt3 : IntegrableOn (fun x => ‖H x‖^2) (Set.Icc (-R) R) := by
    refine IntegrableOn.of_bound hfin (hH.norm.pow 2).aestronglyMeasurable (CH^2) ?_
    filter_upwards [hIn] with x hx
    rw [Real.norm_of_nonneg (by positivity)]
    nlinarith [hCH x hx, norm_nonneg (H x)]
  have hCS := Commons.Analysis.Integration.integral_mul_sq_le_of_integrable
      (μ := volume.restrict (Set.Icc (-R) R)) (u := fun x => ‖G x‖) (v := fun x => ‖H x‖)
      hInt1 hInt2 hInt3
  have hnorm : ‖∫ u in Set.Icc (-R) R, G u * H u‖ ≤ ∫ x in Set.Icc (-R) R, ‖G x‖ * ‖H x‖ := by
    have h := MeasureTheory.norm_integral_le_integral_norm (fun x => G x * H x)
      (μ := volume.restrict (Set.Icc (-R) R))
    simpa only [norm_mul] using h
  have hI : 0 ≤ ∫ u : ℝ, ‖H u‖^2 := integral_nonneg (fun u => by positivity)
  have hHsq : (∫ x in Set.Icc (-R) R, ‖H x‖^2) = ∫ u : ℝ, ‖H u‖^2 :=
    (MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
      (f := fun x => ‖H x‖^2) (s := Set.Icc (-R) R) (μ := volume)
      (fun x hx => by rw [hzero x hx]; simp))
  have hGsq : (∫ x in Set.Icc (-R) R, ‖G x‖^2) ≤ (2*R+2) * (∑ k ∈ s, ‖c k‖^2) := by
    have heq : (∫ x in Set.Icc (-R) R, ‖G x‖^2) = ∫ x in Set.Icc (-R) R, ‖Q x‖^2 :=
      MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun x _ => by rw [hGnQ x])
    rw [heq, integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hRle]
    simp only [hQ]
    exact interval_integral_normSq_finsum_le hR₀ s c
  calc ‖∑ k ∈ s, c k * (∫ u : ℝ, efun (-(u*((k:ℝ)+α))) * H u)‖^2
      = ‖∫ u in Set.Icc (-R) R, G u * H u‖^2 := by rw [hsum_eq]
    _ ≤ (∫ x in Set.Icc (-R) R, ‖G x‖ * ‖H x‖)^2 :=
        pow_le_pow_left₀ (norm_nonneg _) hnorm 2
    _ ≤ (∫ x in Set.Icc (-R) R, ‖G x‖^2) * (∫ x in Set.Icc (-R) R, ‖H x‖^2) := hCS
    _ ≤ ((2*R+2) * (∑ k ∈ s, ‖c k‖^2)) * (∫ u : ℝ, ‖H u‖^2) := by
        rw [← hHsq]
        exact mul_le_mul_of_nonneg_right hGsq (by rw [hHsq]; exact hI)

theorem sample_sum_bound {H : ℝ → ℂ} (hH : Continuous H) {R : ℝ} (hR₀ : 0 ≤ R)
    (hR : ∀ y : ℝ, R < |y| → H y = 0) (α : ℝ) :
    ∀ s : Finset ℤ, ∑ k ∈ s, ‖∫ u : ℝ, efun (-(u * ((k : ℝ) + α))) * H u‖ ^ 2
      ≤ (2 * R + 2) * ∫ u : ℝ, ‖H u‖ ^ 2 := by
  intro s
  set m : ℝ := ∑ k ∈ s, ‖∫ u : ℝ, efun (-(u * ((k : ℝ) + α))) * H u‖ ^ 2 with hm
  have hm_nonneg : 0 ≤ m := by
    rw [hm]; exact Finset.sum_nonneg (fun k _ => by positivity)
  have hI : 0 ≤ ∫ u : ℝ, ‖H u‖ ^ 2 := integral_nonneg (fun u => by positivity)
  have hdual := dual_bound hH hR₀ hR α s
      (fun k => (starRingEnd ℂ) (∫ u : ℝ, efun (-(u * ((k : ℝ) + α))) * H u))
  have h1 : (∑ k ∈ s, (starRingEnd ℂ) (∫ u : ℝ, efun (-(u * ((k : ℝ) + α))) * H u)
        * (∫ u : ℝ, efun (-(u * ((k : ℝ) + α))) * H u)) = (m : ℂ) := by
    rw [hm, Complex.ofReal_sum]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [← Complex.normSq_eq_norm_sq, ← Complex.mul_conj]
    ring
  have h2 : (∑ k ∈ s,
      ‖(starRingEnd ℂ) (∫ u : ℝ, efun (-(u * ((k : ℝ) + α))) * H u)‖ ^ 2) = m := by
    rw [hm]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Complex.norm_conj]
  rw [h1, h2] at hdual
  have hm2 : ‖(m : ℂ)‖ ^ 2 = m ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_ofReal]; ring
  rw [hm2] at hdual
  rcases eq_or_lt_of_le hm_nonneg with h0 | hpos
  · rw [← h0]; exact mul_nonneg (by linarith) hI
  · have hkey : m * m ≤ ((2 * R + 2) * (∫ u : ℝ, ‖H u‖ ^ 2)) * m := by nlinarith [hdual]
    exact le_of_mul_le_mul_right hkey hpos

end

end Work.GM.Affine
