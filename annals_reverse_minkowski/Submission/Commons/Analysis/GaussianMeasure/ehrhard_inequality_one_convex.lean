import Mathlib.Topology.UniformSpace.Uniformizable
import Submission.Commons.Analysis.GaussianMeasure.ehrhard_functional_1d
import Submission.Commons.Measure.Analytic.analyticSet_exists_measurable_hull

/-!
# The one-dimensional Ehrhard inequality (one convex set)

This file proves

`ehrhard_inequality_one_convex` : for measurable `A`, convex measurable `B` in `ℝⁿ`,
the Gaussian measure of the Minkowski combination `(1-λ)A + λB` dominates the Gaussian
measure of the corresponding interval in `ℝ`.

The proof is a reduction to the *functional* form of Ehrhard's inequality, applied to
indicator functions. The `n`-dimensional functional inequality is obtained from the
one-dimensional one (`Commons.Analysis.GaussianMeasure.ehrhard_functional_1d`) by a
Fubini/induction argument on the product structure of the standard Gaussian measure.
-/

open MeasureTheory Set
open scoped Real Pointwise BigOperators ENNReal
set_option autoImplicit false

namespace Commons.Analysis.GaussianMeasure

private noncomputable def gauss1 : Measure ℝ :=
  volume.withDensity fun x : ℝ => ENNReal.ofReal (Real.exp (-Real.pi * x ^ 2))

private lemma gauss1_apply (s : Set ℝ) :
    gauss1 s = ∫⁻ x in s, ENNReal.ofReal (Real.exp (-Real.pi * x ^ 2)) := by
  rw [gauss1, withDensity_apply' _ s]

private lemma integral_exp_pi_sq : (∫ x : ℝ, Real.exp (-Real.pi * x ^ 2)) = 1 := by
  rw [integral_gaussian]
  rw [div_self (ne_of_gt Real.pi_pos), Real.sqrt_one]

private lemma gauss1_univ : gauss1 univ = 1 := by
  rw [gauss1_apply, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (integrable_exp_neg_mul_sq Real.pi_pos)
      (ae_of_all _ (fun x => (Real.exp_pos _).le)),
    integral_exp_pi_sq, ENNReal.ofReal_one]

instance : IsProbabilityMeasure gauss1 where
  measure_univ := gauss1_univ

private noncomputable def gaussN (n : ℕ) : Measure (Fin n → ℝ) := Measure.pi fun _ => gauss1

instance (n : ℕ) : IsProbabilityMeasure (gaussN n) :=
  Measure.pi.instIsProbabilityMeasure (fun _ : Fin n => gauss1)

/-- Lebesgue integral against the one-dimensional Gaussian measure. -/
private lemma integral_gauss1 (H : ℝ → ℝ) :
    ∫ s, H s ∂gauss1 = ∫ s, H s * Real.exp (-Real.pi * s ^ 2) := by
  have hf : Measurable fun x : ℝ => ENNReal.ofReal (Real.exp (-Real.pi * x ^ 2)) := by
    fun_prop
  have h := integral_withDensity_eq_integral_toReal_smul (μ := (volume : Measure ℝ)) hf
    (ae_of_all _ (fun x => ENNReal.ofReal_lt_top)) H
  simp only [gauss1]
  rw [h]
  refine integral_congr_ae (ae_of_all _ fun s => ?_)
  simp only [ENNReal.toReal_ofReal (Real.exp_pos _).le, smul_eq_mul, mul_comm]

/-- Fubini for the product Gaussian measure, peeling off the first coordinate. -/
private lemma gaussN_fubini_succ (n : ℕ) (G : (Fin (n + 1) → ℝ) → ℝ)
    (hG : Measurable G) (hG1 : ∀ x, ‖G x‖ ≤ 1) :
    ∫ x, G x ∂(gaussN (n + 1)) = ∫ s, (∫ y, G (Fin.cons s y) ∂(gaussN n)) ∂gauss1 := by
  set e : (Fin (n + 1) → ℝ) ≃ᵐ (ℝ × (Fin n → ℝ)) :=
    MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0 with he
  have hmp : MeasurePreserving e (gaussN (n + 1)) (gauss1.prod (gaussN n)) := by
    rw [he]
    simpa [gaussN] using
      measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => gauss1) (0 : Fin (n + 1))
  have hGint : Integrable G (gaussN (n + 1)) :=
    Integrable.of_bound hG.aestronglyMeasurable 1 (ae_of_all _ hG1)
  have hge : Measurable fun z : ℝ × (Fin n → ℝ) => G (e.symm z) :=
    hG.comp e.symm.measurable
  have hesymm : ∀ (s : ℝ) (y : Fin n → ℝ), e.symm (s, y) = Fin.cons s y := by
    intro s y
    rw [he]
    simp [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNth_zero', Fin.insertNthEquiv]
  have hint2 : Integrable (fun z : ℝ × (Fin n → ℝ) => G (e.symm z)) (gauss1.prod (gaussN n)) := by
    rw [← hmp.integrable_comp hge.aestronglyMeasurable]
    convert hGint using 2
    ext x
    apply congrArg G
    ext j
    simp [e, Fin.consEquiv_apply]
  calc ∫ x, G x ∂(gaussN (n + 1))
      = ∫ z, G (e.symm z) ∂(gauss1.prod (gaussN n)) := by
        rw [← hmp.integral_comp' (fun z => G (e.symm z))]
        refine integral_congr_ae (ae_of_all _ fun x => ?_)
        apply congrArg G
        ext j
        simp [e, Fin.consEquiv_apply]
    _ = ∫ s, ∫ y, G (e.symm (s, y)) ∂(gaussN n) ∂gauss1 := integral_prod _ hint2
    _ = ∫ s, ∫ y, G (Fin.cons s y) ∂(gaussN n) ∂gauss1 := by
        simp only [hesymm]

/-- The density of the product Gaussian measure. -/
private noncomputable abbrev rhoN (n : ℕ) (y : Fin n → ℝ) : ℝ≥0∞ :=
  ∏ i, ENNReal.ofReal (Real.exp (-Real.pi * y i ^ 2))

private lemma measurable_rhoN (n : ℕ) : Measurable (rhoN n) := by
  refine Finset.measurable_prod _ fun i _ => ?_
  fun_prop

private lemma measurable_ofReal_gauss :
    Measurable fun t : ℝ => ENNReal.ofReal (Real.exp (-Real.pi * t ^ 2)) := by fun_prop

private lemma measurable_cons_fst (n : ℕ) :
    Measurable fun p : ℝ × (Fin n → ℝ) => Fin.cons (α := fun _ : Fin (n + 1) => ℝ) p.1 p.2 := by
  rw [measurable_pi_iff]
  intro j
  refine Fin.cases ?_ ?_ j
  · simpa using measurable_fst
  · intro k
    exact (measurable_pi_apply k).comp measurable_snd

private lemma measurable_cons_apply (n : ℕ) (s : ℝ) :
    Measurable fun y : Fin n → ℝ => Fin.cons (α := fun _ : Fin (n + 1) => ℝ) s y := by
  rw [measurable_pi_iff]
  intro j
  refine Fin.cases ?_ ?_ j
  · simp
  · intro k
    simpa using (measurable_pi_apply k)

private lemma lintegral_gaussN (n : ℕ) (G : (Fin n → ℝ) → ℝ≥0∞) (hG : Measurable G) :
    ∫⁻ y, G y ∂(gaussN n) = ∫⁻ y, G y * rhoN n y ∂volume := by
  induction n with
  | zero =>
    have hγ0 : gaussN 0 = Measure.dirac (0 : Fin 0 → ℝ) := by
      rw [gaussN, Measure.pi_of_empty (fun _ : Fin 0 => gauss1) (0 : Fin 0 → ℝ)]
    have hvol : (volume : Measure (Fin 0 → ℝ)) = Measure.dirac (0 : Fin 0 → ℝ) := by
      rw [volume_pi,
        Measure.pi_of_empty (fun _ : Fin 0 => (volume : Measure ℝ)) (0 : Fin 0 → ℝ)]
    rw [hγ0, hvol, lintegral_dirac, lintegral_dirac]
    simp [rhoN]
  | succ n ih =>
    set e : (Fin (n + 1) → ℝ) ≃ᵐ (ℝ × (Fin n → ℝ)) :=
      MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) 0 with he
    have hmp : MeasurePreserving e (gaussN (n + 1)) (gauss1.prod (gaussN n)) := by
      rw [he]
      simpa [gaussN] using
        measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => gauss1) (0 : Fin (n + 1))
    have hmpvol : MeasurePreserving e (volume : Measure (Fin (n + 1) → ℝ))
        ((volume : Measure ℝ).prod (volume : Measure (Fin n → ℝ))) := by
      have h := measurePreserving_piFinSuccAbove
        (fun _ : Fin (n + 1) => (volume : Measure ℝ)) (0 : Fin (n + 1))
      rw [he]
      rw [← volume_pi] at h
      exact h
    have hesymm : ∀ (s : ℝ) (y : Fin n → ℝ), e.symm (s, y) = Fin.cons s y := by
      intro s y
      rw [he]
      simp [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNth_zero', Fin.insertNthEquiv]
    have hmeas1 : Measurable fun z : ℝ × (Fin n → ℝ) => G (e.symm z) := hG.comp e.symm.measurable
    have stepA : ∫⁻ y, G y ∂(gaussN (n + 1)) =
        ∫⁻ z : ℝ × (Fin n → ℝ), G (e.symm z) ∂(gauss1.prod (gaussN n)) :=
      (hmp.symm.lintegral_comp hG).symm
    have stepB : ∫⁻ z : ℝ × (Fin n → ℝ), G (e.symm z) ∂(gauss1.prod (gaussN n)) =
        ∫⁻ s, ∫⁻ y, G (e.symm (s, y)) ∂(gaussN n) ∂gauss1 :=
      lintegral_prod _ hmeas1.aemeasurable
    have stepC : ∫⁻ s, ∫⁻ y, G (e.symm (s, y)) ∂(gaussN n) ∂gauss1 =
        ∫⁻ s, ∫⁻ y, G (Fin.cons (α := fun _ : Fin (n + 1) => ℝ) s y) * rhoN n y ∂volume
          ∂gauss1 := by
      refine lintegral_congr fun s => ?_
      simp only [hesymm]
      exact ih (fun y => G (Fin.cons (α := fun _ : Fin (n + 1) => ℝ) s y))
        (hG.comp (measurable_cons_apply n s))
    have hHmeas : Measurable fun s : ℝ =>
        ∫⁻ y, G (Fin.cons (α := fun _ : Fin (n + 1) => ℝ) s y) * rhoN n y ∂volume :=
      ((hG.comp (measurable_cons_fst n)).mul ((measurable_rhoN n).comp measurable_snd)).lintegral_prod_right'
    have hKmeas : Measurable fun y : Fin n → ℝ =>
        G (Fin.cons (α := fun _ : Fin (n + 1) => ℝ) 0 y) * rhoN n y :=
      (hG.comp (measurable_cons_apply n 0)).mul (measurable_rhoN n)
    have stepD : ∫⁻ s, (∫⁻ y, G (Fin.cons (α := fun _ : Fin (n + 1) => ℝ) s y) * rhoN n y
          ∂volume) ∂gauss1 =
        ∫⁻ s, ENNReal.ofReal (Real.exp (-Real.pi * s ^ 2)) *
          (∫⁻ y, G (Fin.cons (α := fun _ : Fin (n + 1) => ℝ) s y) * rhoN n y ∂volume)
          ∂volume :=
      lintegral_withDensity_eq_lintegral_mul volume (by fun_prop) hHmeas
    have stepE : ∫⁻ s, ENNReal.ofReal (Real.exp (-Real.pi * s ^ 2)) *
          (∫⁻ y, G (Fin.cons (α := fun _ : Fin (n + 1) => ℝ) s y) * rhoN n y ∂volume)
          ∂volume =
        ∫⁻ s, ∫⁻ y, ENNReal.ofReal (Real.exp (-Real.pi * s ^ 2)) *
          (G (Fin.cons (α := fun _ : Fin (n + 1) => ℝ) s y) * rhoN n y) ∂volume ∂volume := by
      refine lintegral_congr fun s => ?_
      rw [lintegral_const_mul]
      exact (hG.comp (measurable_cons_apply n s)).mul (measurable_rhoN n)
    have hFmeas : Measurable fun z : ℝ × (Fin n → ℝ) =>
        ENNReal.ofReal (Real.exp (-Real.pi * z.1 ^ 2)) *
          (G (Fin.cons (α := fun _ : Fin (n + 1) => ℝ) z.1 z.2) * rhoN n z.2) :=
      (measurable_ofReal_gauss.comp measurable_fst).mul
        ((hG.comp (measurable_cons_fst n)).mul ((measurable_rhoN n).comp measurable_snd))
    have stepF : ∫⁻ s, ∫⁻ y, ENNReal.ofReal (Real.exp (-Real.pi * s ^ 2)) *
          (G (Fin.cons (α := fun _ : Fin (n + 1) => ℝ) s y) * rhoN n y) ∂volume ∂volume =
        ∫⁻ z : ℝ × (Fin n → ℝ), ENNReal.ofReal (Real.exp (-Real.pi * z.1 ^ 2)) *
          (G (Fin.cons (α := fun _ : Fin (n + 1) => ℝ) z.1 z.2) * rhoN n z.2)
          ∂(volume.prod volume) :=
      (lintegral_prod _ hFmeas.aemeasurable).symm
    have htail : Measurable fun x : Fin (n + 1) → ℝ => Fin.tail x := by
      rw [measurable_pi_iff]
      intro i
      exact measurable_pi_apply _
    have hPhi : Measurable fun x : Fin (n + 1) → ℝ =>
        ENNReal.ofReal (Real.exp (-Real.pi * x 0 ^ 2)) * (G x * rhoN n (Fin.tail x)) :=
      (measurable_ofReal_gauss.comp (measurable_pi_apply 0)).mul
        (hG.mul ((measurable_rhoN n).comp htail))
    have stepG : ∫⁻ z : ℝ × (Fin n → ℝ), ENNReal.ofReal (Real.exp (-Real.pi * z.1 ^ 2)) *
          (G (Fin.cons (α := fun _ : Fin (n + 1) => ℝ) z.1 z.2) * rhoN n z.2)
          ∂(volume.prod volume) =
        ∫⁻ x : Fin (n + 1) → ℝ, ENNReal.ofReal (Real.exp (-Real.pi * x 0 ^ 2)) *
          (G x * rhoN n (Fin.tail x)) ∂volume := by
      rw [← hmpvol.symm.lintegral_comp hPhi]
      refine lintegral_congr fun z => ?_
      have hz : e.symm z = Fin.cons (α := fun _ : Fin (n + 1) => ℝ) z.1 z.2 := hesymm z.1 z.2
      rw [hz]
      simp
    have stepH : ∫⁻ x : Fin (n + 1) → ℝ, ENNReal.ofReal (Real.exp (-Real.pi * x 0 ^ 2)) *
          (G x * rhoN n (Fin.tail x)) ∂volume =
        ∫⁻ x, G x * rhoN (n + 1) x ∂volume := by
      refine lintegral_congr fun x => ?_
      simp only [rhoN, Fin.prod_univ_succ, Fin.tail]
      ac_rfl
    rw [stepA, stepB, stepC, stepD, stepE, stepF, stepG, stepH]

end Commons.Analysis.GaussianMeasure

namespace Commons.Analysis.GaussianMeasure

private lemma measurable_rhoR (n : ℕ) :
    Measurable fun y : Fin n → ℝ => ∏ i, Real.exp (-Real.pi * y i ^ 2) := by
  refine Finset.measurable_prod _ fun i _ => ?_
  fun_prop

/-- The real form of the density of the product Gaussian measure. -/
private lemma integral_gaussN_real (n : ℕ) (u : (Fin n → ℝ) → ℝ) (hum : Measurable u)
    (hu0 : ∀ y, 0 ≤ u y) (hu1 : ∀ y, u y ≤ 1) :
    ∫ y, u y ∂(gaussN n) = ∫ y, u y * ∏ i, Real.exp (-Real.pi * y i ^ 2) ∂volume := by
  have hρint : Integrable (fun y : Fin n → ℝ => ∏ i, Real.exp (-Real.pi * y i ^ 2)) volume := by
    rw [volume_pi]
    exact Integrable.fintype_prod (fun _ => integrable_exp_neg_mul_sq Real.pi_pos)
  have hρ0 : ∀ y : Fin n → ℝ, 0 ≤ ∏ i, Real.exp (-Real.pi * y i ^ 2) :=
    fun y => Finset.prod_nonneg fun i _ => (Real.exp_pos _).le
  have huρint : Integrable (fun y : Fin n → ℝ => u y * ∏ i, Real.exp (-Real.pi * y i ^ 2))
      volume :=
    Integrable.mono' hρint (hum.mul (measurable_rhoR n)).aestronglyMeasurable
      (ae_of_all _ fun y => by
        rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hu0 y) (hρ0 y))]
        exact mul_le_of_le_one_left (hρ0 y) (hu1 y))
  calc ∫ y, u y ∂(gaussN n)
      = (∫⁻ y, ENNReal.ofReal (u y) ∂(gaussN n)).toReal :=
        integral_eq_lintegral_of_nonneg_ae (μ := gaussN n) (ae_of_all _ hu0)
          hum.aestronglyMeasurable
    _ = (∫⁻ y, ENNReal.ofReal (u y) * rhoN n y ∂volume).toReal := by
        rw [lintegral_gaussN n (fun y => ENNReal.ofReal (u y)) hum.ennreal_ofReal]
    _ = (∫⁻ y, ENNReal.ofReal (u y * ∏ i, Real.exp (-Real.pi * y i ^ 2)) ∂volume).toReal := by
        congr 1
        refine lintegral_congr fun y => ?_
        simp only [rhoN]
        rw [ENNReal.ofReal_mul (hu0 y), ENNReal.ofReal_prod_of_nonneg fun i _ => (Real.exp_pos _).le]
    _ = ∫ y, u y * ∏ i, Real.exp (-Real.pi * y i ^ 2) ∂volume :=
        (integral_eq_lintegral_of_nonneg_ae (μ := volume)
          (ae_of_all _ fun y => mul_nonneg (hu0 y) (hρ0 y)) huρint.1).symm

/-- Bridge between the product Gaussian measure on `Fin n → ℝ` and the Gaussian integral on
`EuclideanSpace ℝ (Fin n)`. -/
private lemma integral_toLp_gaussN (n : ℕ) (u : EuclideanSpace ℝ (Fin n) → ℝ) (hum : Measurable u)
    (hu0 : ∀ x, 0 ≤ u x) (hu1 : ∀ x, u x ≤ 1) :
    ∫ y : Fin n → ℝ, u (WithLp.toLp 2 y) ∂(gaussN n)
      = ∫ x : EuclideanSpace ℝ (Fin n), u x * Real.exp (-Real.pi * ‖x‖ ^ 2) := by
  have hsum : ∀ y : Fin n → ℝ, (∏ i, Real.exp (-Real.pi * y i ^ 2))
      = Real.exp (-(Real.pi * ∑ i, y i ^ 2)) := by
    intro y
    rw [← Real.exp_sum]
    congr 1
    rw [← Finset.mul_sum]
    ring
  have hnorm : ∀ x : EuclideanSpace ℝ (Fin n), ‖x‖ ^ 2 = ∑ i, (WithLp.ofLp x) i ^ 2 := by
    intro x
    rw [EuclideanSpace.norm_sq_eq]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Real.norm_eq_abs, sq_abs]
  have hmp : MeasurePreserving (WithLp.ofLp : EuclideanSpace ℝ (Fin n) → Fin n → ℝ)
      volume volume := PiLp.volume_preserving_ofLp (Fin n)
  have hemb : MeasurableEmbedding (WithLp.ofLp : EuclideanSpace ℝ (Fin n) → Fin n → ℝ) :=
    (MeasurableEquiv.toLp 2 (Fin n → ℝ)).symm.measurableEmbedding
  have hcc := hmp.integral_comp hemb
    (fun y : Fin n → ℝ => u (WithLp.toLp 2 y) * Real.exp (-(Real.pi * ∑ i, y i ^ 2)))
  rw [integral_gaussN_real n (fun y => u (WithLp.toLp 2 y))
    (hum.comp (MeasurableEquiv.toLp 2 (Fin n → ℝ)).measurable) (fun y => hu0 _) (fun y => hu1 _)]
  calc ∫ y, u (WithLp.toLp 2 y) * ∏ i, Real.exp (-Real.pi * y i ^ 2) ∂volume
      = ∫ y, u (WithLp.toLp 2 y) * Real.exp (-(Real.pi * ∑ i, y i ^ 2)) ∂volume := by
        refine integral_congr_ae (ae_of_all _ fun y => ?_)
        simp only [hsum y]
    _ = ∫ x : EuclideanSpace ℝ (Fin n),
          u (WithLp.toLp 2 (WithLp.ofLp x)) * Real.exp (-(Real.pi * ∑ i, (WithLp.ofLp x) i ^ 2)) :=
        hcc.symm
    _ = ∫ x : EuclideanSpace ℝ (Fin n), u x * Real.exp (-Real.pi * ‖x‖ ^ 2) := by
        refine integral_congr_ae (ae_of_all _ fun x => ?_)
        simp only [WithLp.toLp_ofLp, hnorm x, neg_mul]


private noncomputable abbrev Phi (c : ℝ) : ℝ := ∫ u in Set.Iic c, Real.exp (-Real.pi * u ^ 2)

private noncomputable abbrev marg (n : ℕ) (u : (Fin (n + 1) → ℝ) → ℝ) (s : ℝ) : ℝ :=
  ∫ y, u (Fin.cons (α := fun _ : Fin (n + 1) => ℝ) s y) ∂(gaussN n)

private lemma fin_cons_smul_add {n : ℕ} (lam s t : ℝ) (x y : Fin n → ℝ) :
    lam • (Fin.cons (α := fun _ : Fin (n + 1) => ℝ) s x) +
        (1 - lam) • (Fin.cons (α := fun _ : Fin (n + 1) => ℝ) t y)
      = Fin.cons (α := fun _ : Fin (n + 1) => ℝ) (lam * s + (1 - lam) * t)
          (lam • x + (1 - lam) • y) := by
  have h := (Fin.consLinearEquiv ℝ (fun _ : Fin (n + 1) => ℝ)).map_add
    (lam • (s, x)) ((1 - lam) • (t, y))
  simp only [map_smul] at h
  exact h.symm

/-- Measurability of the marginal of a function of the first coordinate. -/
private lemma marginal_measurable (n : ℕ) (u : (Fin (n + 1) → ℝ) → ℝ) (hu : Measurable u) :
    Measurable (marg n u) := by
  have h : StronglyMeasurable (marg n u) :=
    (hu.comp (measurable_cons_fst n)).stronglyMeasurable.integral_prod_right'
  exact h.measurable

private lemma marginal_nonneg (n : ℕ) (u : (Fin (n + 1) → ℝ) → ℝ) (hu0 : ∀ x, 0 ≤ u x)
    (s : ℝ) : 0 ≤ marg n u s :=
  integral_nonneg fun _ => hu0 _

private lemma marginal_le_one (n : ℕ) (u : (Fin (n + 1) → ℝ) → ℝ) (hu : Measurable u)
    (hu0 : ∀ x, 0 ≤ u x) (hu1 : ∀ x, u x ≤ 1) (s : ℝ) : marg n u s ≤ 1 := by
  have h1 : Integrable (fun y : Fin n → ℝ =>
      u (Fin.cons (α := fun _ : Fin (n + 1) => ℝ) s y)) (gaussN n) :=
    Integrable.of_bound ((hu.comp (measurable_cons_apply n s)).aestronglyMeasurable) 1
      (ae_of_all _ fun y => by
        rw [Real.norm_eq_abs, abs_of_nonneg (hu0 _)]; exact hu1 _)
  refine (integral_mono h1 (integrable_const 1) fun _ => hu1 _).trans_eq ?_
  simp

/-- The `n`-dimensional functional Ehrhard inequality for the product Gaussian measure on
`Fin n → ℝ`. -/
private def EhrhardPi (n : ℕ) : Prop :=
  ∀ (f g h : (Fin n → ℝ) → ℝ),
    Measurable f → Measurable g → Measurable h →
    (∀ x, 0 ≤ f x) → (∀ x, f x ≤ 1) →
    (∀ x, 0 ≤ g x) → (∀ x, g x ≤ 1) →
    (∀ x, 0 ≤ h x) → (∀ x, h x ≤ 1) →
    ∀ lam : ℝ, 0 ≤ lam → lam ≤ 1 →
    (∀ a b x y, Phi a ≤ f x → Phi b ≤ g y →
      Phi (lam * a + (1 - lam) * b) ≤ h (lam • x + (1 - lam) • y)) →
    ∀ a b, Phi a ≤ ∫ x, f x ∂(gaussN n) → Phi b ≤ ∫ x, g x ∂(gaussN n) →
      Phi (lam * a + (1 - lam) * b) ≤ ∫ x, h x ∂(gaussN n)

private lemma ehrhardPi_zero : EhrhardPi 0 := by
  intro f g h hfm hgm hhm hf0 hf1 hg0 hg1 hh0 hh1 lam hl0 hl1 hcond a b ha hb
  have hγ0 : gaussN 0 = Measure.dirac (0 : Fin 0 → ℝ) := by
    rw [gaussN, Measure.pi_of_empty (fun _ : Fin 0 => gauss1) (0 : Fin 0 → ℝ)]
  have hfint : ∫ x : Fin 0 → ℝ, f x ∂(gaussN 0) = f 0 := by
    rw [hγ0, integral_dirac]
  have hgint : ∫ x : Fin 0 → ℝ, g x ∂(gaussN 0) = g 0 := by
    rw [hγ0, integral_dirac]
  have hhint : ∫ x : Fin 0 → ℝ, h x ∂(gaussN 0) = h 0 := by
    rw [hγ0, integral_dirac]
  rw [hfint] at ha
  rw [hgint] at hb
  rw [hhint]
  simpa using hcond a b 0 0 ha hb

private lemma ehrhardPi_succ (n : ℕ) (ih : EhrhardPi n) : EhrhardPi (n + 1) := by
  intro f g h hfm hgm hhm hf0 hf1 hg0 hg1 hh0 hh1 lam hl0 hl1 hcond a b ha hb
  have hfN : ∀ x, ‖f x‖ ≤ 1 := fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (hf0 x)]; exact hf1 x
  have hgN : ∀ x, ‖g x‖ ≤ 1 := fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (hg0 x)]; exact hg1 x
  have hhN : ∀ x, ‖h x‖ ≤ 1 := fun x => by
    rw [Real.norm_eq_abs, abs_of_nonneg (hh0 x)]; exact hh1 x
  have hfub : ∫ x, f x ∂(gaussN (n + 1)) = ∫ s, marg n f s ∂gauss1 :=
    gaussN_fubini_succ n f hfm hfN
  have hgub : ∫ x, g x ∂(gaussN (n + 1)) = ∫ s, marg n g s ∂gauss1 :=
    gaussN_fubini_succ n g hgm hgN
  have hhub : ∫ x, h x ∂(gaussN (n + 1)) = ∫ s, marg n h s ∂gauss1 :=
    gaussN_fubini_succ n h hhm hhN
  have hFeq : (∫ s, marg n f s * Real.exp (-Real.pi * s ^ 2)) = ∫ x, f x ∂(gaussN (n + 1)) := by
    rw [← integral_gauss1 (marg n f), ← hfub]
  have hGeq : (∫ s, marg n g s * Real.exp (-Real.pi * s ^ 2)) = ∫ x, g x ∂(gaussN (n + 1)) := by
    rw [← integral_gauss1 (marg n g), ← hgub]
  have hHeq : (∫ s, marg n h s * Real.exp (-Real.pi * s ^ 2)) = ∫ x, h x ∂(gaussN (n + 1)) := by
    rw [← integral_gauss1 (marg n h), ← hhub]
  have hcond1 : ∀ a b s t, Phi a ≤ marg n f s → Phi b ≤ marg n g t →
      Phi (lam * a + (1 - lam) * b) ≤ marg n h (lam * s + (1 - lam) * t) := by
    intro a b s t hs ht
    exact ih (fun y => f (Fin.cons (α := fun _ : Fin (n + 1) => ℝ) s y))
      (fun y => g (Fin.cons (α := fun _ : Fin (n + 1) => ℝ) t y))
      (fun y => h (Fin.cons (α := fun _ : Fin (n + 1) => ℝ) (lam * s + (1 - lam) * t) y))
      (hfm.comp (measurable_cons_apply n s)) (hgm.comp (measurable_cons_apply n t))
      (hhm.comp (measurable_cons_apply n _))
      (fun _ => hf0 _) (fun _ => hf1 _) (fun _ => hg0 _) (fun _ => hg1 _)
      (fun _ => hh0 _) (fun _ => hh1 _)
      lam hl0 hl1 (fun a' b' x y hx hy => by
        have hc := hcond a' b' (Fin.cons (α := fun _ : Fin (n + 1) => ℝ) s x)
          (Fin.cons (α := fun _ : Fin (n + 1) => ℝ) t y) hx hy
        rwa [fin_cons_smul_add] at hc)
      a b hs ht
  have key := ehrhard_functional_1d (marg n f) (marg n g) (marg n h)
    (marginal_measurable n f hfm) (marginal_measurable n g hgm) (marginal_measurable n h hhm)
    (marginal_nonneg n f hf0) (marginal_le_one n f hfm hf0 hf1)
    (marginal_nonneg n g hg0) (marginal_le_one n g hgm hg0 hg1)
    (marginal_nonneg n h hh0) (marginal_le_one n h hhm hh0 hh1)
    lam hl0 hl1 hcond1 a b (by rw [hFeq]; exact ha) (by rw [hGeq]; exact hb)
  rwa [hHeq] at key

private theorem ehrhardPi (n : ℕ) : EhrhardPi n :=
  Nat.rec ehrhardPi_zero (fun n ih => ehrhardPi_succ n ih) n



/-- **Functional Ehrhard inequality in `n` dimensions** (for the standard Gaussian measure
on `EuclideanSpace ℝ (Fin n)`). -/
private theorem ehrhard_functional_nd {n : ℕ} (f g h : EuclideanSpace ℝ (Fin n) → ℝ)
    (hfm : Measurable f) (hgm : Measurable g) (hhm : Measurable h)
    (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1)
    (hg0 : ∀ x, 0 ≤ g x) (hg1 : ∀ x, g x ≤ 1)
    (hh0 : ∀ x, 0 ≤ h x) (hh1 : ∀ x, h x ≤ 1)
    (lam : ℝ) (hl0 : 0 ≤ lam) (hl1 : lam ≤ 1)
    (hcond : ∀ a b x y, Phi a ≤ f x → Phi b ≤ g y →
      Phi (lam * a + (1 - lam) * b) ≤ h (lam • x + (1 - lam) • y)) :
    ∀ a b, Phi a ≤ ∫ x, f x * Real.exp (-Real.pi * ‖x‖ ^ 2) →
      Phi b ≤ ∫ x, g x * Real.exp (-Real.pi * ‖x‖ ^ 2) →
      Phi (lam * a + (1 - lam) * b) ≤ ∫ x, h x * Real.exp (-Real.pi * ‖x‖ ^ 2) := by
  have htoLp : Measurable (WithLp.toLp 2 : (Fin n → ℝ) → EuclideanSpace ℝ (Fin n)) :=
    (MeasurableEquiv.toLp 2 (Fin n → ℝ)).measurable
  set F : (Fin n → ℝ) → ℝ := fun y => f (WithLp.toLp 2 y) with hF
  set G : (Fin n → ℝ) → ℝ := fun y => g (WithLp.toLp 2 y) with hG
  set H : (Fin n → ℝ) → ℝ := fun y => h (WithLp.toLp 2 y) with hH
  have hFm : Measurable F := hfm.comp htoLp
  have hGm : Measurable G := hgm.comp htoLp
  have hHm : Measurable H := hhm.comp htoLp
  have hFeq : (∫ y, F y ∂(gaussN n)) = ∫ x, f x * Real.exp (-Real.pi * ‖x‖ ^ 2) := by
    rw [hF]; exact integral_toLp_gaussN n f hfm hf0 hf1
  have hGeq : (∫ y, G y ∂(gaussN n)) = ∫ x, g x * Real.exp (-Real.pi * ‖x‖ ^ 2) := by
    rw [hG]; exact integral_toLp_gaussN n g hgm hg0 hg1
  have hHeq : (∫ y, H y ∂(gaussN n)) = ∫ x, h x * Real.exp (-Real.pi * ‖x‖ ^ 2) := by
    rw [hH]; exact integral_toLp_gaussN n h hhm hh0 hh1
  have hlin : ∀ (x y : Fin n → ℝ), WithLp.toLp 2 (lam • x + (1 - lam) • y)
      = lam • WithLp.toLp 2 x + (1 - lam) • WithLp.toLp 2 y := by
    intro x y
    simp
  have hcond' : ∀ a b x y, Phi a ≤ F x → Phi b ≤ G y →
      Phi (lam * a + (1 - lam) * b) ≤ H (lam • x + (1 - lam) • y) := by
    intro a b x y hx hy
    simp only [hH, hlin x y]
    exact hcond a b (WithLp.toLp 2 x) (WithLp.toLp 2 y) hx hy
  intro a b ha hb
  have key := ehrhardPi n F G H hFm hGm hHm
    (fun y => hf0 _) (fun y => hf1 _) (fun y => hg0 _) (fun y => hg1 _)
    (fun y => hh0 _) (fun y => hh1 _) lam hl0 hl1 hcond' a b
    (by rw [hFeq]; exact ha) (by rw [hGeq]; exact hb)
  rwa [hHeq] at key

/-- The one-dimensional Gaussian CDF `c ↦ ∫_{u ≤ c} exp (-π u²)` is strictly positive. -/
private lemma phi_pos (c : ℝ) : 0 < Phi c := by
  have hfi : IntegrableOn (fun u : ℝ => Real.exp (-Real.pi * u ^ 2)) (Set.Iic c) :=
    (integrable_exp_neg_mul_sq Real.pi_pos).integrableOn
  have hf : 0 ≤ᵐ[volume.restrict (Set.Iic c)] (fun u : ℝ => Real.exp (-Real.pi * u ^ 2)) :=
    Filter.Eventually.of_forall (fun u => (Real.exp_pos _).le)
  rw [setIntegral_pos_iff_support_of_nonneg_ae hf hfi]
  have : Function.support (fun u : ℝ => Real.exp (-Real.pi * u ^ 2)) = Set.univ := by
    ext u; simp [Function.mem_support]
  rw [this, Set.univ_inter, Real.volume_Iic]
  exact ENNReal.zero_lt_top

/-- The one-dimensional Gaussian CDF is at most `1`. -/
private lemma phi_le_one (c : ℝ) : Phi c ≤ 1 := by
  rw [← integral_exp_pi_sq]
  exact MeasureTheory.setIntegral_le_integral (integrable_exp_neg_mul_sq Real.pi_pos)
    (Filter.Eventually.of_forall (fun u => (Real.exp_pos _).le))

theorem ehrhard_inequality_one_convex {n : ℕ} (A B : Set (EuclideanSpace ℝ (Fin n)))
    (hA : MeasurableSet A) (hBcvx : Convex ℝ B) (hB : MeasurableSet B)
    (lam : ℝ) (hl0 : 0 ≤ lam) (hl1 : lam ≤ 1) (s t : ℝ)
    (hAγ : (∫ x : ℝ in {x : ℝ | x ≤ s}, Real.exp (-Real.pi * x ^ 2)) ≤
            ∫ x in A, Real.exp (-Real.pi * ‖x‖ ^ 2))
    (hBγ : (∫ x : ℝ in {x : ℝ | x ≤ t}, Real.exp (-Real.pi * x ^ 2)) ≤
            ∫ x in B, Real.exp (-Real.pi * ‖x‖ ^ 2)) :
    (∫ x : ℝ in {x : ℝ | x ≤ (1-lam)*s + lam*t}, Real.exp (-Real.pi * x ^ 2)) ≤
      ∫ x in {x : EuclideanSpace ℝ (Fin n) | ∃ a ∈ A, ∃ b ∈ B, x = (1-lam) • a + lam • b},
        Real.exp (-Real.pi * ‖x‖ ^ 2) := by
  set M : Set (EuclideanSpace ℝ (Fin n)) := {x | ∃ a ∈ A, ∃ b ∈ B, x = (1-lam) • a + lam • b} with hMdef
  -- The Minkowski combination of a measurable set and a convex set is analytic.
  have hMan : AnalyticSet M := by
    rw [hMdef]
    have hcont : Continuous (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
        (1-lam) • p.1 + lam • p.2) := by fun_prop
    have himg : {x : EuclideanSpace ℝ (Fin n) | ∃ a ∈ A, ∃ b ∈ B, x = (1-lam) • a + lam • b}
        = (fun p : EuclideanSpace ℝ (Fin n) × EuclideanSpace ℝ (Fin n) =>
            (1-lam) • p.1 + lam • p.2) '' (A ×ˢ B) := by
      ext x; constructor
      · rintro ⟨a, ha, b, hb, rfl⟩
        exact ⟨(a, b), ⟨ha, hb⟩, rfl⟩
      · rintro ⟨p, hp, rfl⟩
        exact ⟨p.1, hp.1, p.2, hp.2, rfl⟩
    rw [himg]
    exact (hA.prod hB).analyticSet_image hcont.measurable
  -- Enlarge it to a Borel set differing by a null set.
  obtain ⟨M', hM'meas, hM'sub, hM'null⟩ :=
    Commons.Measure.Analytic.analyticSet_exists_measurable_hull volume hMan
  have hFmeas : Measurable (B.indicator (fun _ => (1:ℝ))) := measurable_const.indicator hB
  have hGmeas : Measurable (A.indicator (fun _ => (1:ℝ))) := measurable_const.indicator hA
  have hHmeas : Measurable (M'.indicator (fun _ => (1:ℝ))) := measurable_const.indicator hM'meas
  -- The pointwise hypothesis of the functional Ehrhard inequality.
  have hcond : ∀ a b x y,
       (∫ u in Set.Iic a, Real.exp (-Real.pi * u ^ 2)) ≤ (B.indicator (fun _ => (1:ℝ))) x →
       (∫ u in Set.Iic b, Real.exp (-Real.pi * u ^ 2)) ≤ (A.indicator (fun _ => (1:ℝ))) y →
       (∫ u in Set.Iic (lam * a + (1 - lam) * b), Real.exp (-Real.pi * u ^ 2)) ≤
         (M'.indicator (fun _ => (1:ℝ))) (lam • x + (1 - lam) • y) := by
    intro a b x y hx hy
    have hxB : x ∈ B := by
      by_contra hc
      rw [Set.indicator_of_notMem hc] at hx
      exact absurd hx (not_le.mpr (phi_pos a))
    have hyA : y ∈ A := by
      by_contra hc
      rw [Set.indicator_of_notMem hc] at hy
      exact absurd hy (not_le.mpr (phi_pos b))
    have hmemM : lam • x + (1 - lam) • y ∈ M := by
      rw [hMdef]
      exact ⟨y, hyA, x, hxB, by rw [add_comm]⟩
    rw [Set.indicator_of_mem (hM'sub hmemM)]
    exact phi_le_one _
  -- Apply the functional Ehrhard inequality (with the roles of `A` and `B` swapped).
  have key := ehrhard_functional_nd (B.indicator (fun _ => (1:ℝ))) (A.indicator (fun _ => (1:ℝ)))
      (M'.indicator (fun _ => (1:ℝ))) hFmeas hGmeas hHmeas
      (fun z => Set.indicator_nonneg (fun x _ => zero_le_one) z)
      (fun z => Set.indicator_le_self' (fun x _ => zero_le_one) z)
      (fun z => Set.indicator_nonneg (fun x _ => zero_le_one) z)
      (fun z => Set.indicator_le_self' (fun x _ => zero_le_one) z)
      (fun z => Set.indicator_nonneg (fun x _ => zero_le_one) z)
      (fun z => Set.indicator_le_self' (fun x _ => zero_le_one) z)
      lam hl0 hl1 hcond t s
  have hFB : (∫ x, (B.indicator (fun _ => (1:ℝ))) x * Real.exp (-Real.pi * ‖x‖ ^ 2))
      = ∫ x in B, Real.exp (-Real.pi * ‖x‖ ^ 2) := by
    rw [← integral_indicator hB]
    apply integral_congr_ae
    filter_upwards with x
    by_cases hx : x ∈ B <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, hx]
  have hGA : (∫ x, (A.indicator (fun _ => (1:ℝ))) x * Real.exp (-Real.pi * ‖x‖ ^ 2))
      = ∫ x in A, Real.exp (-Real.pi * ‖x‖ ^ 2) := by
    rw [← integral_indicator hA]
    apply integral_congr_ae
    filter_upwards with x
    by_cases hx : x ∈ A <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, hx]
  have hkey2 := key (by rw [hFB]; exact hBγ) (by rw [hGA]; exact hAγ)
  have hHM' : (∫ x, (M'.indicator (fun _ => (1:ℝ))) x * Real.exp (-Real.pi * ‖x‖ ^ 2))
      = ∫ x in M', Real.exp (-Real.pi * ‖x‖ ^ 2) := by
    rw [← integral_indicator hM'meas]
    apply integral_congr_ae
    filter_upwards with x
    by_cases hx : x ∈ M' <;> simp [Set.indicator_of_mem, Set.indicator_of_notMem, hx]
  rw [hHM'] at hkey2
  suffices h : (∫ x in M, Real.exp (-Real.pi * ‖x‖ ^ 2)) = ∫ x in M', Real.exp (-Real.pi * ‖x‖ ^ 2) by
    rw [h]
    have harg : (1-lam)*s + lam*t = lam*t + (1-lam)*s := by ring
    rw [harg]
    exact hkey2
  have hae : M =ᵐ[volume] M' := by
    rw [MeasureTheory.ae_eq_set]
    exact ⟨by rw [Set.diff_eq_empty.mpr hM'sub, measure_empty], hM'null⟩
  exact MeasureTheory.setIntegral_congr_set hae

end Commons.Analysis.GaussianMeasure