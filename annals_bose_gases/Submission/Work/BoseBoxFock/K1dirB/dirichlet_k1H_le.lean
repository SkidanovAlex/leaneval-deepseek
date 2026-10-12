import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseBoxFock.K1dirB.continuous_partialFderiv_chiG
import Submission.Work.BoseBoxFock.K1dirB.fderiv_chiG_eq_zero_of_notMem_boxL
import Submission.Work.BoseBoxFock.K1dirB.k1H_integrand_eq
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section
open MeasureTheory Filter
open scoped BigOperators

set_option maxHeartbeats 1000000

namespace Work.BoseBoxFock.K1dirB
local notation "E3" => EuclideanSpace ℝ (Fin 3)

-- ===== local definitions (uncurried!) =====

private noncomputable def dirS (ℓ : ℝ) (G : E3 → E3 → ℂ) : E3 × E3 → ℝ :=
  fun p => ∑ j : Fin 3,
    ‖fderiv ℝ (fun w' => chiB ℓ w' * G w' p.2) p.1 (EuclideanSpace.single j (1 : ℝ))‖ ^ 2

private noncomputable def dirM (ℓ : ℝ) (G : E3 → E3 → ℂ) : E3 × E3 → ℝ :=
  fun p => (ℓ ^ 2)⁻¹ * ‖chiB ℓ p.1 * G p.1 p.2‖ ^ 2

private lemma dirS_nonneg (ℓ : ℝ) (G : E3 → E3 → ℂ) (p : E3 × E3) : 0 ≤ dirS ℓ G p := by
  simp only [dirS]; positivity

private lemma dirM_nonneg (ℓ : ℝ) (G : E3 → E3 → ℂ) (p : E3 × E3) : 0 ≤ dirM ℓ G p := by
  simp only [dirM]; positivity

private lemma continuous_dirS_curry {ℓ : ℝ} {G : E3 → E3 → ℂ} (w : E3)
    (h : Continuous (dirS ℓ G)) : Continuous (fun y : E3 => dirS ℓ G (w, y)) :=
  h.comp (continuous_const.prodMk continuous_id)

private lemma continuous_dirM_curry {ℓ : ℝ} {G : E3 → E3 → ℂ} (w : E3)
    (h : Continuous (dirM ℓ G)) : Continuous (fun y : E3 => dirM ℓ G (w, y)) :=
  h.comp (continuous_const.prodMk continuous_id)

private lemma setIntegral_setIntegral_const_mul {s : Set E3} (c : ℝ) (f : E3 → E3 → ℝ) :
    (∫ w in s, ∫ y in s, c * f w y) = c * ∫ w in s, ∫ y in s, f w y := by
  have h1 : ∀ w : E3, (∫ y in s, c * f w y) = c * ∫ y in s, f w y :=
    fun w => integral_const_mul c _
  rw [integral_congr_ae (Filter.Eventually.of_forall h1), integral_const_mul]

private lemma continuous_snd_sq (ℓ : ℝ) :
    Continuous (fun p : E3 × E3 => (Submission.BoseGases.chiScale ℓ p.2) ^ 2) :=
  (((Work.BoseBoxFock.L1Tails.contDiff_chiScale ℓ).continuous).comp continuous_snd).pow 2

private lemma continuous_curry_sq {ℓ : ℝ} (w : E3) :
    Continuous (fun y : E3 => (Submission.BoseGases.chiScale ℓ y) ^ 2) :=
  (((Work.BoseBoxFock.L1Tails.contDiff_chiScale ℓ).continuous).pow 2)

theorem dirichlet_k1H_le {ℓ : ℝ} (hℓ : 0 < ℓ)
    {G : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℂ}
    (hG : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry G)) :
    (∫ w : EuclideanSpace ℝ (Fin 3), ∫ y : EuclideanSpace ℝ (Fin 3), ∑ j : Fin 3,
        ‖fderiv ℝ (fun w' => Work.BoseBoxFock.K1dirB.k1H ℓ G w' y) w
          (EuclideanSpace.single j (1 : ℝ))‖ ^ 2)
      ≤ Work.BoseBoxFock.k1Chi * ((ℓ ^ 3)⁻¹) ^ 2 * Work.BoseBoxFock.L1Tails.pairEnergy ℓ G := by
  classical
  set B : Set E3 := Work.BoseK15.corpusBox.boxL ℓ with hBdef
  have hBmeas : MeasurableSet B := Work.BoseB4.BoxData.boxL_measurableSet Work.BoseK15.corpusBox ℓ
  have hBcomp : IsCompact B := Work.BoseBoxFock.L1Tails.isCompact_boxL ℓ
  have hBfin : (volume : Measure E3) B < ⊤ := hBcomp.measure_lt_top
  -- pointwise identity
  have hF : ∀ w y : E3, (∑ j : Fin 3,
        ‖fderiv ℝ (fun w' => k1H ℓ G w' y) w (EuclideanSpace.single j (1 : ℝ))‖ ^ 2)
      = ((ℓ ^ 3)⁻¹) ^ 2 * (Submission.BoseGases.chiScale ℓ y) ^ 2 * dirS ℓ G (w, y) := by
    intro w y
    simpa only [dirS] using k1H_integrand_eq hℓ hG w y
  -- the window vanishes off the box
  have hχ0 : ∀ {y : E3}, y ∉ B → Submission.BoseGases.chiScale ℓ y = 0 := by
    intro y hy
    by_contra hne
    refine hy ?_
    rw [hBdef]
    exact Work.BoseBoxFock.L1Tails.mem_boxL_of_norm_le hℓ
      (le_of_lt ((Work.BoseFixB1.chiScale_ne_zero_iff hℓ y).mp hne))
  -- the Dirichlet integrand vanishes off the box in the first variable
  have hS0 : ∀ {w : E3}, w ∉ B → ∀ y : E3, dirS ℓ G (w, y) = 0 := by
    intro w hw y
    have hw' : w ∉ Work.BoseK15.corpusBox.boxL ℓ := by rwa [hBdef] at hw
    simp only [dirS]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [fderiv_chiG_eq_zero_of_notMem_boxL hℓ hG hw' y]
    simp
  have hM0 : ∀ {w : E3}, w ∉ B → ∀ y : E3, dirM ℓ G (w, y) = 0 := by
    intro w hw y
    have hw' : w ∉ Work.BoseK15.corpusBox.boxL ℓ := by rwa [hBdef] at hw
    simp only [dirM]
    rw [chiB_eq_zero_of_notMem_boxL hℓ hw']
    simp
  -- continuity on the product
  have hcontS : Continuous (dirS ℓ G) := continuous_partialFderiv_chiG (ℓ := ℓ) hG
  have hcontM : Continuous (dirM ℓ G) := by
    have hχ : Continuous (fun p : E3 × E3 => chiB ℓ p.1 * G p.1 p.2) :=
      ((chiB_contDiff (ne_of_gt hℓ)).continuous.comp continuous_fst).mul hG.continuous
    exact continuous_const.mul ((hχ.norm).pow 2)
  -- step 1 : pull out the constant
  have hstep1 : (∫ w : E3, ∫ y : E3, ∑ j : Fin 3,
        ‖fderiv ℝ (fun w' => k1H ℓ G w' y) w (EuclideanSpace.single j (1 : ℝ))‖ ^ 2)
      = ((ℓ ^ 3)⁻¹) ^ 2 * ∫ w : E3, ∫ y : E3,
          (Submission.BoseGases.chiScale ℓ y) ^ 2 * dirS ℓ G (w, y) := by
    have hcongr : ∀ w : E3, (∫ y : E3, ∑ j : Fin 3,
          ‖fderiv ℝ (fun w' => k1H ℓ G w' y) w (EuclideanSpace.single j (1 : ℝ))‖ ^ 2)
        = ((ℓ ^ 3)⁻¹) ^ 2 * ∫ y : E3,
            (Submission.BoseGases.chiScale ℓ y) ^ 2 * dirS ℓ G (w, y) := by
      intro w
      have hfun : (fun y : E3 => ∑ j : Fin 3,
            ‖fderiv ℝ (fun w' => k1H ℓ G w' y) w (EuclideanSpace.single j (1 : ℝ))‖ ^ 2)
          = fun y : E3 => ((ℓ ^ 3)⁻¹) ^ 2 *
              ((Submission.BoseGases.chiScale ℓ y) ^ 2 * dirS ℓ G (w, y)) := by
        funext y; rw [hF w y]; ring
      rw [hfun, integral_const_mul]
    calc (∫ w : E3, ∫ y : E3, ∑ j : Fin 3,
          ‖fderiv ℝ (fun w' => k1H ℓ G w' y) w (EuclideanSpace.single j (1 : ℝ))‖ ^ 2)
        = ∫ w : E3, ((ℓ ^ 3)⁻¹) ^ 2 * ∫ y : E3,
            (Submission.BoseGases.chiScale ℓ y) ^ 2 * dirS ℓ G (w, y) :=
          integral_congr_ae (Filter.Eventually.of_forall hcongr)
      _ = ((ℓ ^ 3)⁻¹) ^ 2 * ∫ w : E3, ∫ y : E3,
            (Submission.BoseGases.chiScale ℓ y) ^ 2 * dirS ℓ G (w, y) := integral_const_mul _ _
  -- step 2 : restrict to the box
  have hstep2 : (∫ w : E3, ∫ y : E3, (Submission.BoseGases.chiScale ℓ y) ^ 2 * dirS ℓ G (w, y))
      = ∫ w in B, ∫ y in B, (Submission.BoseGases.chiScale ℓ y) ^ 2 * dirS ℓ G (w, y) := by
    have hi : ∀ w : E3, (∫ y : E3, (Submission.BoseGases.chiScale ℓ y) ^ 2 * dirS ℓ G (w, y))
        = ∫ y in B, (Submission.BoseGases.chiScale ℓ y) ^ 2 * dirS ℓ G (w, y) := by
      intro w
      refine (setIntegral_eq_integral_of_forall_compl_eq_zero (s := B)
        (f := fun y : E3 => (Submission.BoseGases.chiScale ℓ y) ^ 2 * dirS ℓ G (w, y))
        (fun y hy => ?_)).symm
      rw [hχ0 hy]; ring
    rw [integral_congr_ae (Filter.Eventually.of_forall hi)]
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero (s := B)
      (f := fun w : E3 => ∫ y in B, (Submission.BoseGases.chiScale ℓ y) ^ 2 * dirS ℓ G (w, y))
      (fun w hw => ?_)).symm
    have hzero : (fun y : E3 => (Submission.BoseGases.chiScale ℓ y) ^ 2 * dirS ℓ G (w, y))
        = fun _ => (0 : ℝ) := by
      funext y; rw [hS0 hw y]; ring
    rw [hzero]
    simp
  -- step 3 : the comparison on the box
  have hpt : ∀ w y : E3, (Submission.BoseGases.chiScale ℓ y) ^ 2 * dirS ℓ G (w, y)
      ≤ k1Chi * (dirS ℓ G (w, y) + dirM ℓ G (w, y)) := by
    intro w y
    have h1 : (Submission.BoseGases.chiScale ℓ y) ^ 2 ≤ k1Chi := chiScale_sq_le_k1Chi ℓ y
    have h2 : 0 ≤ dirS ℓ G (w, y) := dirS_nonneg ℓ G _
    have h3 : 0 ≤ dirM ℓ G (w, y) := dirM_nonneg ℓ G _
    calc (Submission.BoseGases.chiScale ℓ y) ^ 2 * dirS ℓ G (w, y)
        ≤ k1Chi * dirS ℓ G (w, y) := mul_le_mul_of_nonneg_right h1 h2
      _ ≤ k1Chi * (dirS ℓ G (w, y) + dirM ℓ G (w, y)) :=
          mul_le_mul_of_nonneg_left (by linarith) k1Chi_pos.le
  have hinner : ∀ w : E3, (∫ y in B, (Submission.BoseGases.chiScale ℓ y) ^ 2 * dirS ℓ G (w, y))
      ≤ ∫ y in B, k1Chi * (dirS ℓ G (w, y) + dirM ℓ G (w, y)) := by
    intro w
    refine setIntegral_mono_on ?_ ?_ hBmeas (fun y hy => hpt w y)
    · exact ((continuous_curry_sq w).mul (continuous_dirS_curry w hcontS)).continuousOn.integrableOn_compact hBcomp
    · exact (continuous_const.mul ((continuous_dirS_curry w hcontS).add
        (continuous_dirM_curry w hcontM))).continuousOn.integrableOn_compact hBcomp
  -- bounds on the box for the outer integrability
  obtain ⟨CS, hCS⟩ := (hBcomp.prod hBcomp).exists_bound_of_continuousOn hcontS.continuousOn
  obtain ⟨CM, hCM⟩ := (hBcomp.prod hBcomp).exists_bound_of_continuousOn hcontM.continuousOn
  have hbndS : ∀ w : E3, ‖∫ y in B, (Submission.BoseGases.chiScale ℓ y) ^ 2 * dirS ℓ G (w, y)‖
      ≤ (max CS 0 * k1Chi) * (volume : Measure E3).real B := by
    intro w
    refine norm_setIntegral_le_of_norm_le_const hBfin (fun y hy => ?_)
    rw [norm_mul, Real.norm_of_nonneg (by positivity : (0 : ℝ) ≤ (Submission.BoseGases.chiScale ℓ y) ^ 2)]
    have hSle : ‖dirS ℓ G (w, y)‖ ≤ max CS 0 := by
      by_cases hw : w ∈ B
      · exact le_max_of_le_left (hCS (w, y) ⟨hw, hy⟩)
      · rw [hS0 hw y, norm_zero]; exact le_max_right _ _
    calc (Submission.BoseGases.chiScale ℓ y) ^ 2 * ‖dirS ℓ G (w, y)‖
        ≤ k1Chi * max CS 0 :=
          mul_le_mul (chiScale_sq_le_k1Chi ℓ y) hSle (norm_nonneg _) k1Chi_pos.le
      _ = max CS 0 * k1Chi := by ring
  have hbndT : ∀ w : E3, ‖∫ y in B, k1Chi * (dirS ℓ G (w, y) + dirM ℓ G (w, y))‖
      ≤ (k1Chi * (max CS 0 + max CM 0)) * (volume : Measure E3).real B := by
    intro w
    refine norm_setIntegral_le_of_norm_le_const hBfin (fun y hy => ?_)
    rw [norm_mul, Real.norm_of_nonneg k1Chi_pos.le]
    have hSle : ‖dirS ℓ G (w, y)‖ ≤ max CS 0 := by
      by_cases hw : w ∈ B
      · exact le_max_of_le_left (hCS (w, y) ⟨hw, hy⟩)
      · rw [hS0 hw y, norm_zero]; exact le_max_right _ _
    have hMle : ‖dirM ℓ G (w, y)‖ ≤ max CM 0 := by
      by_cases hw : w ∈ B
      · exact le_max_of_le_left (hCM (w, y) ⟨hw, hy⟩)
      · rw [hM0 hw y, norm_zero]; exact le_max_right _ _
    have h1 : ‖dirS ℓ G (w, y) + dirM ℓ G (w, y)‖ ≤ max CS 0 + max CM 0 :=
      le_trans (norm_add_le _ _) (add_le_add hSle hMle)
    exact mul_le_mul_of_nonneg_left h1 k1Chi_pos.le
  have houter : (∫ w in B, ∫ y in B, (Submission.BoseGases.chiScale ℓ y) ^ 2 * dirS ℓ G (w, y))
      ≤ ∫ w in B, ∫ y in B, k1Chi * (dirS ℓ G (w, y) + dirM ℓ G (w, y)) := by
    refine setIntegral_mono_on ?_ ?_ hBmeas (fun w _ => hinner w)
    · refine IntegrableOn.of_bound hBfin ?_
        ((max CS 0 * k1Chi) * (volume : Measure E3).real B) (Filter.Eventually.of_forall hbndS)
      have hsm : StronglyMeasurable (fun w : E3 => ∫ y in B,
          (Submission.BoseGases.chiScale ℓ y) ^ 2 * dirS ℓ G (w, y)) :=
        StronglyMeasurable.integral_prod_right (ν := (volume : Measure E3).restrict B)
          (f := fun w y => (Submission.BoseGases.chiScale ℓ y) ^ 2 * dirS ℓ G (w, y))
          ((continuous_snd_sq ℓ).mul hcontS).stronglyMeasurable
      simpa using hsm.aestronglyMeasurable
    · refine IntegrableOn.of_bound hBfin ?_
        ((k1Chi * (max CS 0 + max CM 0)) * (volume : Measure E3).real B)
        (Filter.Eventually.of_forall hbndT)
      have hsm : StronglyMeasurable (fun w : E3 => ∫ y in B,
          k1Chi * (dirS ℓ G (w, y) + dirM ℓ G (w, y))) :=
        StronglyMeasurable.integral_prod_right (ν := (volume : Measure E3).restrict B)
          (f := fun w y => k1Chi * (dirS ℓ G (w, y) + dirM ℓ G (w, y)))
          (continuous_const.mul (hcontS.add hcontM)).stronglyMeasurable
      simpa using hsm.aestronglyMeasurable
  -- step 4 : identify pairEnergy
  have hpair : Work.BoseBoxFock.L1Tails.pairEnergy ℓ G
      = ∫ w in B, ∫ y in B, (dirS ℓ G (w, y) + dirM ℓ G (w, y)) := by
    rw [Work.BoseBoxFock.L1Tails.pairEnergy]
    refine setIntegral_congr_fun hBmeas (fun w _ => ?_)
    refine setIntegral_congr_fun hBmeas (fun y _ => ?_)
    simp only [dirS, dirM, chiB]
  -- assembly
  calc (∫ w : E3, ∫ y : E3, ∑ j : Fin 3,
        ‖fderiv ℝ (fun w' => k1H ℓ G w' y) w (EuclideanSpace.single j (1 : ℝ))‖ ^ 2)
      = ((ℓ ^ 3)⁻¹) ^ 2 * ∫ w : E3, ∫ y : E3,
          (Submission.BoseGases.chiScale ℓ y) ^ 2 * dirS ℓ G (w, y) := hstep1
    _ = ((ℓ ^ 3)⁻¹) ^ 2 * ∫ w in B, ∫ y in B,
          (Submission.BoseGases.chiScale ℓ y) ^ 2 * dirS ℓ G (w, y) := by rw [hstep2]
    _ ≤ ((ℓ ^ 3)⁻¹) ^ 2 * ∫ w in B, ∫ y in B,
          k1Chi * (dirS ℓ G (w, y) + dirM ℓ G (w, y)) :=
        mul_le_mul_of_nonneg_left houter (by positivity)
    _ = ((ℓ ^ 3)⁻¹) ^ 2 * (k1Chi * ∫ w in B, ∫ y in B, (dirS ℓ G (w, y) + dirM ℓ G (w, y))) := by
        rw [setIntegral_setIntegral_const_mul]
    _ = k1Chi * ((ℓ ^ 3)⁻¹) ^ 2 * Work.BoseBoxFock.L1Tails.pairEnergy ℓ G := by
        rw [hpair]; ring

end Work.BoseBoxFock.K1dirB
