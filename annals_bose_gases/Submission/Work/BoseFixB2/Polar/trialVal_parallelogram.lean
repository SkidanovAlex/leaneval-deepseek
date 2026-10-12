import Mathlib.Tactic.Have
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB2.Polar.BoxAux
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal
open Work.BoseKinLoc Work.BoseKinLoc.Kinetic

namespace Work.BoseFixB2.Polar

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The moving box is compact for every `ℓ` -/

/-- **The centred cube `acube ℓ` is compact for every `ℓ`** (not only for `0 < ℓ`): it is the
intersection of the coordinate strips `{y | y m ∈ Icc (−ℓ/2) (ℓ/2)}` (closed) and is contained
in the ball of radius `√3·|ℓ|/2`.  For `ℓ ≤ 0` it is empty or a single point, which the same
estimate covers. -/
lemma isCompact_acube_all (ℓ : ℝ) : IsCompact (Submission.BoseGases.acube ℓ) := by
  rw [Metric.isCompact_iff_isClosed_bounded]
  constructor
  · rw [show Submission.BoseGases.acube ℓ
        = ⋂ m : Fin 3, (fun y : ℝ³ => y m) ⁻¹' (Set.Icc (-ℓ / 2) (ℓ / 2)) by
      ext y
      simp [Submission.BoseGases.acube]]
    exact isClosed_iInter (fun m =>
      IsClosed.preimage (by fun_prop : Continuous fun y : ℝ³ => y m) isClosed_Icc)
  · rw [Metric.isBounded_iff_subset_closedBall (c := (0 : ℝ³))]
    refine ⟨Real.sqrt 3 * (|ℓ| / 2), ?_⟩
    intro y hy
    rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
    have hcoord : ∀ m : Fin 3, |y m| ≤ |ℓ| / 2 := by
      intro m
      have hm : y m ∈ Set.Icc (-ℓ / 2) (ℓ / 2) := hy m
      refine abs_le.mpr ⟨?_, ?_⟩
      · have := hm.1; nlinarith [le_abs_self ℓ, neg_abs_le ℓ]
      · have := hm.2; nlinarith [le_abs_self ℓ, neg_abs_le ℓ]
    have hsq : ‖y‖ ^ 2 ≤ (Real.sqrt 3 * (|ℓ| / 2)) ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      calc ∑ m : Fin 3, (y m) ^ 2 ≤ ∑ m : Fin 3, (|ℓ| / 2) ^ 2 := by
            refine Finset.sum_le_sum (fun m _ => ?_)
            rw [← sq_abs (y m)]
            exact pow_le_pow_left₀ (abs_nonneg _) (hcoord m) 2
        _ = (Real.sqrt 3 * (|ℓ| / 2)) ^ 2 := by
            rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
            norm_num
    exact le_of_sq_le_sq hsq (by positivity)

/-- **The moving box `lamBox ℓ u = ℓu + acube ℓ` is compact for every `ℓ`**: it is the image
of the compact centred cube under the translation `z ↦ ℓu + z`. -/
lemma isCompact_lamBox_all (ℓ : ℝ) (u : ℝ³) : IsCompact (lamBox ℓ u) := by
  have himg : lamBox ℓ u =
      (fun z : ℝ³ => ℓ • u + z) '' Submission.BoseGases.acube ℓ := by
    ext x
    simp only [lamBox, Work.BSKinetic.bsBox, Set.mem_setOf_eq, Set.mem_image]
    constructor
    · intro hx; exact ⟨x - ℓ • u, hx, by rw [add_sub_cancel]⟩
    · rintro ⟨z, hz, rfl⟩; simpa using hz
  rw [himg]
  exact (isCompact_acube_all ℓ).image (continuous_const.add continuous_id)

/-- **Every continuous function is integrable over the moving box** (for every `ℓ`): the box
is compact and Lebesgue measure is finite on compacta. -/
lemma integrableOn_lamBox_of_continuous (ℓ : ℝ) (u : ℝ³) {F : ℝ³ → ℝ}
    (hF : Continuous F) : IntegrableOn F (lamBox ℓ u) :=
  ContinuousOn.integrableOn_compact (isCompact_lamBox_all ℓ u) hF.continuousOn

/-! ## The two scalar parallelogram identities -/

/-- **Parallelogram identity for squares of continuous functions on the box.**
`∫_Λ (p+q)² + ∫_Λ (p−q)² = 2∫_Λ p² + 2∫_Λ q²`. -/
lemma integral_sq_parallelogram (ℓ : ℝ) (u : ℝ³) {p q : ℝ³ → ℝ}
    (hp : Continuous p) (hq : Continuous q) :
    (∫ z in lamBox ℓ u, (p z + q z) ^ 2) + (∫ z in lamBox ℓ u, (p z - q z) ^ 2)
      = 2 * (∫ z in lamBox ℓ u, (p z) ^ 2) + 2 * (∫ z in lamBox ℓ u, (q z) ^ 2) := by
  have h1 : IntegrableOn (fun z : ℝ³ => (p z + q z) ^ 2) (lamBox ℓ u) :=
    integrableOn_lamBox_of_continuous ℓ u ((hp.add hq).pow 2)
  have h2 : IntegrableOn (fun z : ℝ³ => (p z - q z) ^ 2) (lamBox ℓ u) :=
    integrableOn_lamBox_of_continuous ℓ u ((hp.sub hq).pow 2)
  have h3 : IntegrableOn (fun z : ℝ³ => 2 * (p z) ^ 2) (lamBox ℓ u) :=
    (integrableOn_lamBox_of_continuous ℓ u (hp.pow 2)).const_mul 2
  have h4 : IntegrableOn (fun z : ℝ³ => 2 * (q z) ^ 2) (lamBox ℓ u) :=
    (integrableOn_lamBox_of_continuous ℓ u (hq.pow 2)).const_mul 2
  calc (∫ z in lamBox ℓ u, (p z + q z) ^ 2) + (∫ z in lamBox ℓ u, (p z - q z) ^ 2)
      = ∫ z in lamBox ℓ u, ((p z + q z) ^ 2 + (p z - q z) ^ 2) := (integral_add h1 h2).symm
    _ = ∫ z in lamBox ℓ u, (2 * (p z) ^ 2 + 2 * (q z) ^ 2) := by
        apply integral_congr_ae
        filter_upwards with z
        ring
    _ = (∫ z in lamBox ℓ u, 2 * (p z) ^ 2) + (∫ z in lamBox ℓ u, 2 * (q z) ^ 2) :=
        integral_add h3 h4
    _ = 2 * (∫ z in lamBox ℓ u, (p z) ^ 2) + 2 * (∫ z in lamBox ℓ u, (q z) ^ 2) := by
        rw [integral_const_mul, integral_const_mul]

/-- **Parallelogram identity for products of continuous functions on the box.**
`∫_Λ (p+q)(r+s) + ∫_Λ (p−q)(r−s) = 2∫_Λ pr + 2∫_Λ qs`. -/
lemma integral_mul_parallelogram (ℓ : ℝ) (u : ℝ³) {p q r s : ℝ³ → ℝ}
    (hp : Continuous p) (hq : Continuous q) (hr : Continuous r) (hs : Continuous s) :
    (∫ z in lamBox ℓ u, (p z + q z) * (r z + s z))
      + (∫ z in lamBox ℓ u, (p z - q z) * (r z - s z))
      = 2 * (∫ z in lamBox ℓ u, p z * r z) + 2 * (∫ z in lamBox ℓ u, q z * s z) := by
  have h1 : IntegrableOn (fun z : ℝ³ => (p z + q z) * (r z + s z)) (lamBox ℓ u) :=
    integrableOn_lamBox_of_continuous ℓ u ((hp.add hq).mul (hr.add hs))
  have h2 : IntegrableOn (fun z : ℝ³ => (p z - q z) * (r z - s z)) (lamBox ℓ u) :=
    integrableOn_lamBox_of_continuous ℓ u ((hp.sub hq).mul (hr.sub hs))
  have h3 : IntegrableOn (fun z : ℝ³ => 2 * (p z * r z)) (lamBox ℓ u) :=
    (integrableOn_lamBox_of_continuous ℓ u (hp.mul hr)).const_mul 2
  have h4 : IntegrableOn (fun z : ℝ³ => 2 * (q z * s z)) (lamBox ℓ u) :=
    (integrableOn_lamBox_of_continuous ℓ u (hq.mul hs)).const_mul 2
  calc (∫ z in lamBox ℓ u, (p z + q z) * (r z + s z))
        + (∫ z in lamBox ℓ u, (p z - q z) * (r z - s z))
      = ∫ z in lamBox ℓ u, ((p z + q z) * (r z + s z) + (p z - q z) * (r z - s z)) :=
        (integral_add h1 h2).symm
    _ = ∫ z in lamBox ℓ u, (2 * (p z * r z) + 2 * (q z * s z)) := by
        apply integral_congr_ae
        filter_upwards with z
        ring
    _ = (∫ z in lamBox ℓ u, 2 * (p z * r z)) + (∫ z in lamBox ℓ u, 2 * (q z * s z)) :=
        integral_add h3 h4
    _ = 2 * (∫ z in lamBox ℓ u, p z * r z) + 2 * (∫ z in lamBox ℓ u, q z * s z) := by
        rw [integral_const_mul, integral_const_mul]

/-! ## The polarisation identity for `trialVal` -/

theorem trialVal_parallelogram {ℓ a2 : ℝ} (u : EuclideanSpace ℝ (Fin 3))
    {f g A B : EuclideanSpace ℝ (Fin 3) → ℝ} (hf : ContDiff ℝ (⊤ : ENat) f)
    (hg : ContDiff ℝ (⊤ : ENat) g) (hA : ContDiff ℝ (⊤ : ENat) A)
    (hAs : HasCompactSupport A) (hB : ContDiff ℝ (⊤ : ENat) B)
    (hBs : HasCompactSupport B) :
    Work.BoseKinLoc.Kinetic.trialVal ℓ a2 u (f + g) (A + B)
      + Work.BoseKinLoc.Kinetic.trialVal ℓ a2 u (f - g) (A - B)
      = 2 * (Work.BoseKinLoc.Kinetic.trialVal ℓ a2 u f A
          + Work.BoseKinLoc.Kinetic.trialVal ℓ a2 u g B) := by
  classical
  have hfc : Continuous f := hf.continuous
  have hgc : Continuous g := hg.continuous
  have hAc : Continuous A := hA.continuous
  have hBc : Continuous B := hB.continuous
  have hdA : ∀ k : Fin 3,
      Continuous (fun z : ℝ³ => fderiv ℝ A z (Submission.BoseGases.kcStdBasis k)) :=
    fun k => (hA.continuous_fderiv (by simp)).clm_apply continuous_const
  have hdB : ∀ k : Fin 3,
      Continuous (fun z : ℝ³ => fderiv ℝ B z (Submission.BoseGases.kcStdBasis k)) :=
    fun k => (hB.continuous_fderiv (by simp)).clm_apply continuous_const
  -- the `φ²`-row, solved for `∫_Λ (f+g)²`
  have hP1 : (∫ z in lamBox ℓ u, (f z + g z) ^ 2)
      = 2 * (∫ z in lamBox ℓ u, (f z) ^ 2) + 2 * (∫ z in lamBox ℓ u, (g z) ^ 2)
        - (∫ z in lamBox ℓ u, (f z - g z) ^ 2) := by
    linarith [integral_sq_parallelogram ℓ u hfc hgc]
  -- the cross row, solved for `∫_Λ (f+g)(A+B)`
  have hC1 : (∫ z in lamBox ℓ u, (f z + g z) * (A z + B z))
      = 2 * (∫ z in lamBox ℓ u, f z * A z) + 2 * (∫ z in lamBox ℓ u, g z * B z)
        - (∫ z in lamBox ℓ u, (f z - g z) * (A z - B z)) := by
    linarith [integral_mul_parallelogram ℓ u hfc hgc hAc hBc]
  -- the `A²`-row, solved for `∫_Λ (A+B)²`
  have hQ1 : (∫ z in lamBox ℓ u, (A z + B z) ^ 2)
      = 2 * (∫ z in lamBox ℓ u, (A z) ^ 2) + 2 * (∫ z in lamBox ℓ u, (B z) ^ 2)
        - (∫ z in lamBox ℓ u, (A z - B z) ^ 2) := by
    linarith [integral_sq_parallelogram ℓ u hAc hBc]
  -- the kinetic row, via `∂_k(A±B) = ∂_k A ± ∂_k B`
  have hK : (∑ k : Fin 3, ∫ z in lamBox ℓ u,
        (fderiv ℝ (A + B) z (Submission.BoseGases.kcStdBasis k)) ^ 2)
      + (∑ k : Fin 3, ∫ z in lamBox ℓ u,
        (fderiv ℝ (A - B) z (Submission.BoseGases.kcStdBasis k)) ^ 2)
      = 2 * (∑ k : Fin 3, ∫ z in lamBox ℓ u,
          (fderiv ℝ A z (Submission.BoseGases.kcStdBasis k)) ^ 2)
        + 2 * (∑ k : Fin 3, ∫ z in lamBox ℓ u,
          (fderiv ℝ B z (Submission.BoseGases.kcStdBasis k)) ^ 2) := by
    have hk : ∀ k : Fin 3,
        (∫ z in lamBox ℓ u, (fderiv ℝ (A + B) z (Submission.BoseGases.kcStdBasis k)) ^ 2)
        + (∫ z in lamBox ℓ u, (fderiv ℝ (A - B) z (Submission.BoseGases.kcStdBasis k)) ^ 2)
        = 2 * (∫ z in lamBox ℓ u, (fderiv ℝ A z (Submission.BoseGases.kcStdBasis k)) ^ 2)
          + 2 * (∫ z in lamBox ℓ u, (fderiv ℝ B z (Submission.BoseGases.kcStdBasis k)) ^ 2) := by
      intro k
      have hpt₁ : ∀ z : ℝ³, fderiv ℝ (A + B) z (Submission.BoseGases.kcStdBasis k)
          = fderiv ℝ A z (Submission.BoseGases.kcStdBasis k)
            + fderiv ℝ B z (Submission.BoseGases.kcStdBasis k) := by
        intro z
        rw [fderiv_add ((hA.differentiable (by simp)).differentiableAt)
          ((hB.differentiable (by simp)).differentiableAt)]
        simp
      have hpt₂ : ∀ z : ℝ³, fderiv ℝ (A - B) z (Submission.BoseGases.kcStdBasis k)
          = fderiv ℝ A z (Submission.BoseGases.kcStdBasis k)
            - fderiv ℝ B z (Submission.BoseGases.kcStdBasis k) := by
        intro z
        rw [fderiv_sub ((hA.differentiable (by simp)).differentiableAt)
          ((hB.differentiable (by simp)).differentiableAt)]
        simp
      have hEq₁ : (∫ z in lamBox ℓ u,
            (fderiv ℝ (A + B) z (Submission.BoseGases.kcStdBasis k)) ^ 2)
          = ∫ z in lamBox ℓ u,
              (fderiv ℝ A z (Submission.BoseGases.kcStdBasis k)
                + fderiv ℝ B z (Submission.BoseGases.kcStdBasis k)) ^ 2 := by
        apply integral_congr_ae
        filter_upwards with z
        rw [hpt₁ z]
      have hEq₂ : (∫ z in lamBox ℓ u,
            (fderiv ℝ (A - B) z (Submission.BoseGases.kcStdBasis k)) ^ 2)
          = ∫ z in lamBox ℓ u,
              (fderiv ℝ A z (Submission.BoseGases.kcStdBasis k)
                - fderiv ℝ B z (Submission.BoseGases.kcStdBasis k)) ^ 2 := by
        apply integral_congr_ae
        filter_upwards with z
        rw [hpt₂ z]
      rw [hEq₁, hEq₂]
      exact integral_sq_parallelogram ℓ u (hdA k) (hdB k)
    calc (∑ k : Fin 3, ∫ z in lamBox ℓ u,
            (fderiv ℝ (A + B) z (Submission.BoseGases.kcStdBasis k)) ^ 2)
          + (∑ k : Fin 3, ∫ z in lamBox ℓ u,
            (fderiv ℝ (A - B) z (Submission.BoseGases.kcStdBasis k)) ^ 2)
        = ∑ k : Fin 3,
            ((∫ z in lamBox ℓ u,
                (fderiv ℝ (A + B) z (Submission.BoseGases.kcStdBasis k)) ^ 2)
             + (∫ z in lamBox ℓ u,
                (fderiv ℝ (A - B) z (Submission.BoseGases.kcStdBasis k)) ^ 2)) :=
          Finset.sum_add_distrib.symm
      _ = ∑ k : Fin 3,
            (2 * (∫ z in lamBox ℓ u,
                (fderiv ℝ A z (Submission.BoseGases.kcStdBasis k)) ^ 2)
             + 2 * (∫ z in lamBox ℓ u,
                (fderiv ℝ B z (Submission.BoseGases.kcStdBasis k)) ^ 2)) :=
          Finset.sum_congr rfl (fun k _ => hk k)
      _ = (∑ k : Fin 3, 2 * (∫ z in lamBox ℓ u,
              (fderiv ℝ A z (Submission.BoseGases.kcStdBasis k)) ^ 2))
          + (∑ k : Fin 3, 2 * (∫ z in lamBox ℓ u,
              (fderiv ℝ B z (Submission.BoseGases.kcStdBasis k)) ^ 2)) :=
          Finset.sum_add_distrib
      _ = 2 * (∑ k : Fin 3, ∫ z in lamBox ℓ u,
              (fderiv ℝ A z (Submission.BoseGases.kcStdBasis k)) ^ 2)
          + 2 * (∑ k : Fin 3, ∫ z in lamBox ℓ u,
              (fderiv ℝ B z (Submission.BoseGases.kcStdBasis k)) ^ 2) := by
          rw [Finset.mul_sum, Finset.mul_sum]
  have hK1 : (∑ k : Fin 3, ∫ z in lamBox ℓ u,
        (fderiv ℝ (A + B) z (Submission.BoseGases.kcStdBasis k)) ^ 2)
      = 2 * (∑ k : Fin 3, ∫ z in lamBox ℓ u,
          (fderiv ℝ A z (Submission.BoseGases.kcStdBasis k)) ^ 2)
        + 2 * (∑ k : Fin 3, ∫ z in lamBox ℓ u,
          (fderiv ℝ B z (Submission.BoseGases.kcStdBasis k)) ^ 2)
        - (∑ k : Fin 3, ∫ z in lamBox ℓ u,
          (fderiv ℝ (A - B) z (Submission.BoseGases.kcStdBasis k)) ^ 2) := by
    linarith [hK]
  -- unfold `trialVal` in its four occurrences and substitute the four row identities
  simp only [Work.BoseKinLoc.Kinetic.trialVal, Pi.add_apply, Pi.sub_apply]
  rw [hP1, hC1, hK1, hQ1]
  ring

end Work.BoseFixB2.Polar
