import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.FDeriv.Measurable
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.Spaces.Defs
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.FTS.LocData.angMaj_mem
import Submission.Work.Elliptic.WtoH_IntZ
import Submission.Work.FTS.StrongPersist.L3Aux.bcoefPoint
import Submission.Work.FTS.StrongPersist.L3Aux.bcoefRadBound

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.StrongPersist.L3Aux

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## F. Angular integral, radial integral, and the assembly -/

/-- Integrability and the bound of the angular majorant. -/
theorem radAngInt_bound : ∃ M : ℝ, 0 < M ∧ ∀ (α : ℝ), 0 < α → α ≤ 1 →
    MeasureTheory.IntegrableOn (radAngInt α) Work.Spaces.Iθ ∧
    (∫ θ in Work.Spaces.Iθ, radAngInt α θ) ≤ M := by
  refine ⟨10500, by norm_num, fun α hα hα1 => ?_⟩
  have hsin2 : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ Real.sin (2 * θ) :=
    fun θ hθ => sin_two_nonneg_of_mem_Iθ hθ
  -- the `η`-term
  have hA : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) Work.Spaces.Iθ ∧
      (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) ≤ 10000 := by
    obtain ⟨h1, h2⟩ := Work.Spaces.sin_two_rpow (-(Work.Spaces.eta))
      (by rw [Work.Spaces.eta]; norm_num) (by rw [Work.Spaces.eta]; norm_num)
    refine ⟨h1, ?_⟩
    have heq : 100 / (-(Work.Spaces.eta) + 1) = 10000 := by rw [Work.Spaces.eta]; norm_num
    rwa [heq] at h2
  -- the `γ`-term
  have hBmeas : AEStronglyMeasurable
      (fun θ : ℝ => α ^ 2 * (Work.Spaces.Gam α θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) (volume.restrict Work.Spaces.Iθ) := by
    apply Measurable.aestronglyMeasurable
    simp only [Work.Spaces.Gam]
    fun_prop
  obtain ⟨hSint, hSbd⟩ := Work.Spaces.sin_two_rpow (17 * α / 30 - 1)
    (by linarith) (by linarith)
  have hSbd' : (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (17 * α / 30 - 1))
      ≤ 3000 / (17 * α) := by
    have heq : 100 / ((17 * α / 30 - 1) + 1) = 3000 / (17 * α) := by field_simp; ring
    rwa [heq] at hSbd
  have hB : MeasureTheory.IntegrableOn
      (fun θ : ℝ => α ^ 2 * (Work.Spaces.Gam α θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) Work.Spaces.Iθ ∧
      (∫ θ in Work.Spaces.Iθ, α ^ 2 * (Work.Spaces.Gam α θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) ≤ 200 := by
    have hMint : MeasureTheory.IntegrableOn
        (fun θ : ℝ => α ^ 2 * ((2 : ℝ) ^ (-(2 * α / 3))
          * (Real.sin (2 * θ)) ^ (17 * α / 30 - 1))) Work.Spaces.Iθ :=
      (hSint.const_mul ((2 : ℝ) ^ (-(2 * α / 3)))).const_mul (α ^ 2)
    have hpt : ∀ θ ∈ Work.Spaces.Iθ, α ^ 2 * (Work.Spaces.Gam α θ) ^ 2
        * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
        ≤ α ^ 2 * ((2 : ℝ) ^ (-(2 * α / 3)) * (Real.sin (2 * θ)) ^ (17 * α / 30 - 1)) := by
      intro θ hθ
      have h := Work.FTS.LocData.GamSq_sin_neg_gam_le α hα hα1 hθ
      have h4 : 0 ≤ α ^ 2 := sq_nonneg α
      calc α ^ 2 * (Work.Spaces.Gam α θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))
          = α ^ 2 * ((Work.Spaces.Gam α θ) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) := by ring
        _ ≤ α ^ 2 * ((2 : ℝ) ^ (-(2 * α / 3))
              * (Real.sin (2 * θ)) ^ (17 * α / 30 - 1)) :=
            mul_le_mul_of_nonneg_left h h4
    have hInt : MeasureTheory.IntegrableOn
        (fun θ : ℝ => α ^ 2 * (Work.Spaces.Gam α θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) Work.Spaces.Iθ :=
      hMint.mono' hBmeas (by
        filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
        rw [Real.norm_of_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))
          (Real.rpow_nonneg (hsin2 θ hθ) _))]
        exact hpt θ hθ)
    refine ⟨hInt, ?_⟩
    have hmono := MeasureTheory.integral_mono_ae hInt hMint
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc hpt)
    refine hmono.trans ?_
    rw [MeasureTheory.integral_const_mul]
    have hpoweq : (∫ θ in Work.Spaces.Iθ, (2 : ℝ) ^ (-(2 * α / 3))
        * (Real.sin (2 * θ)) ^ (17 * α / 30 - 1))
        = (2 : ℝ) ^ (-(2 * α / 3)) * (∫ θ in Work.Spaces.Iθ,
            (Real.sin (2 * θ)) ^ (17 * α / 30 - 1)) :=
      MeasureTheory.integral_const_mul _ _
    rw [hpoweq]
    have hbind : α ^ 2 * ((2 : ℝ) ^ (-(2 * α / 3)) * (3000 / (17 * α))) ≤ 200 := by
      have h3 : (2 : ℝ) ^ (-(2 * α / 3)) ≤ 1 := by
        have h := Real.rpow_le_rpow_of_exponent_le (x := (2 : ℝ))
          (by norm_num : (1 : ℝ) ≤ 2) (by linarith : -(2 * α / 3) ≤ 0)
        simpa using h
      have h5 : (2 : ℝ) ^ (-(2 * α / 3)) * (3000 / (17 * α)) ≤ 3000 / (17 * α) := by
        have h6 : 0 ≤ 3000 / (17 * α) := by positivity
        nlinarith [h3, h6]
      have h7 : α ^ 2 * (3000 / (17 * α)) ≤ 3000 / 17 := by
        have he : α ^ 2 * (3000 / (17 * α)) = 3000 * α / 17 := by field_simp
        rw [he]
        nlinarith [hα1, hα]
      have h8 : 0 ≤ α ^ 2 := sq_nonneg α
      calc α ^ 2 * ((2 : ℝ) ^ (-(2 * α / 3)) * (3000 / (17 * α)))
          ≤ α ^ 2 * (3000 / (17 * α)) := mul_le_mul_of_nonneg_left h5 h8
        _ ≤ 3000 / 17 := h7
        _ ≤ 200 := by norm_num
    have h4 : (2 : ℝ) ^ (-(2 * α / 3))
          * (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (17 * α / 30 - 1))
        ≤ (2 : ℝ) ^ (-(2 * α / 3)) * (3000 / (17 * α)) :=
      mul_le_mul_of_nonneg_left hSbd' (Real.rpow_nonneg (by norm_num) _)
    exact (mul_le_mul_of_nonneg_left h4 (sq_nonneg α)).trans hbind
  constructor
  · exact hA.1.add hB.1
  · have heq : (∫ θ in Work.Spaces.Iθ, radAngInt α θ)
        = (∫ θ in Work.Spaces.Iθ, (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
          + (∫ θ in Work.Spaces.Iθ, α ^ 2 * (Work.Spaces.Gam α θ) ^ 2
              * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) :=
      MeasureTheory.integral_add hA.1 hB.1
    rw [heq]
    linarith [hA.2, hB.2]

/-- Measurability of the `Zop`-iterates of the radial profile. -/
lemma measurable_Zop_iter (j : ℕ) : Measurable (Work.Spaces.Zop^[j] bcoefRad) := by
  induction j with
  | zero =>
      rw [show Work.Spaces.Zop^[0] bcoefRad = bcoefRad from rfl]
      rw [show bcoefRad = fun z : ℝ => 2 * z ^ 2 / (1 + z) ^ 3 from rfl]
      fun_prop
  | succ j ih =>
      have h : Work.Spaces.Zop^[j + 1] bcoefRad
          = fun z : ℝ => z * deriv (Work.Spaces.Zop^[j] bcoefRad) z := by
        funext z
        rw [Function.iterate_succ_apply']
        rfl
      rw [h]
      exact measurable_id.mul (measurable_deriv _)

lemma measurable_w : Measurable Work.Spaces.w := by
  unfold Work.Spaces.w
  fun_prop

lemma measurable_radSnorm : Measurable radSnorm := by
  unfold radSnorm
  refine Finset.measurable_sum _ fun j _ => ?_
  have h3 : Measurable (fun a : ℝ =>
      (Work.Spaces.Zop^[j] bcoefRad) a * Work.Spaces.w a) :=
    (measurable_Zop_iter j).mul measurable_w
  have hgoal : (fun a : ℝ => ((Work.Spaces.Zop^[j] bcoefRad) a * Work.Spaces.w a) ^ 2)
      = fun a : ℝ => ((Work.Spaces.Zop^[j] bcoefRad) a * Work.Spaces.w a)
          * ((Work.Spaces.Zop^[j] bcoefRad) a * Work.Spaces.w a) := by
    funext a; rw [pow_two]
  rw [hgoal]
  exact h3.mul h3

/-- The integral of `radSnorm` is bounded, given the pointwise radial bound. -/
theorem radSnorm_int_le {K : ℝ} (hK : 0 ≤ K)
    (hrb : ∀ j ≤ 3, ∀ z ∈ Set.Ici (0 : ℝ),
      |(Work.Spaces.Zop^[j] bcoefRad) z * Work.Spaces.w z| ≤ K / (1 + z)) :
    MeasureTheory.IntegrableOn radSnorm Work.Spaces.Iz ∧
    (∫ z in Work.Spaces.Iz, radSnorm z) ≤ 8 * K ^ 2 := by
  have hpt : ∀ z ∈ Work.Spaces.Iz, radSnorm z ≤ 4 * K ^ 2 * (1 / (1 + z) ^ 2) := by
    intro z hz
    have h1z : (0 : ℝ) < 1 + z := by
      have hz0 : 0 ≤ z := hz
      linarith
    have h1 : ∀ j ∈ Finset.range 4,
        ((Work.Spaces.Zop^[j] bcoefRad) z * Work.Spaces.w z) ^ 2 ≤ K ^ 2 * (1 / (1 + z) ^ 2) := by
      intro j hj
      have hj3 : j ≤ 3 := by have := Finset.mem_range.mp hj; omega
      have h := hrb j hj3 z hz
      have h2 : ((Work.Spaces.Zop^[j] bcoefRad) z * Work.Spaces.w z) ^ 2 ≤ (K / (1 + z)) ^ 2 := by
        rw [sq_le_sq, abs_of_nonneg (by positivity : (0 : ℝ) ≤ K / (1 + z))]
        exact h
      refine h2.trans (le_of_eq ?_)
      rw [div_pow, one_div]
      ring
    have hsum := Finset.sum_le_sum h1
    rw [radSnorm_apply]
    refine hsum.trans ?_
    have hsum' : (∑ _j ∈ Finset.range 4, K ^ 2 * (1 / (1 + z) ^ 2))
        = 4 * K ^ 2 * (1 / (1 + z) ^ 2) := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      ring
    rw [hsum']
  have hdom : MeasureTheory.IntegrableOn (fun z : ℝ => 4 * K ^ 2 * (1 / (1 + z) ^ 2))
      Work.Spaces.Iz := Work.Elliptic.WtoH_IntZ.1.const_mul (4 * K ^ 2)
  have hSint : MeasureTheory.IntegrableOn radSnorm Work.Spaces.Iz := by
    refine hdom.mono' measurable_radSnorm.aestronglyMeasurable ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ici] with z hz
    rw [Real.norm_of_nonneg (radSnorm_nonneg z)]
    exact hpt z hz
  refine ⟨hSint, ?_⟩
  have hmono := MeasureTheory.integral_mono_of_nonneg
    (Eventually.of_forall fun z => radSnorm_nonneg z) hdom
    (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici hpt)
  refine hmono.trans ?_
  rw [MeasureTheory.integral_const_mul]
  have h2 : (∫ z in Work.Spaces.Iz, 1 / (1 + z) ^ 2) ≤ 2 := Work.Elliptic.WtoH_IntZ.2
  have h3 : (0 : ℝ) ≤ 4 * K ^ 2 := by positivity
  calc 4 * K ^ 2 * (∫ z in Work.Spaces.Iz, 1 / (1 + z) ^ 2) ≤ 4 * K ^ 2 * 2 :=
        mul_le_mul_of_nonneg_left h2 h3
    _ = 8 * K ^ 2 := by ring

/-- The radial fact (proved in `bcoefRadBound`). -/
theorem rad_aux : ∃ K : ℝ, 0 < K ∧ ∀ (j : ℕ), j ≤ 3 → ∀ z ∈ Set.Ici (0 : ℝ),
      |(Work.Spaces.Zop^[j] bcoefRad) z * Work.Spaces.w z| ≤ K / (1 + z) :=
  bcoefRad_zop_bound

/-- The angular fact (proved as `radAngInt_bound` below). -/
theorem ang_aux : ∃ M : ℝ, 0 < M ∧ ∀ (α : ℝ), 0 < α → α ≤ 1 →
      MeasureTheory.IntegrableOn (radAngInt α) Work.Spaces.Iθ ∧
      (∫ θ in Work.Spaces.Iθ, radAngInt α θ) ≤ M := radAngInt_bound

theorem bcoef_gamCoef_le_aux :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ), 0 < α → α ≤ 1 →
    Work.FTS.EllipticEst.SmoothOpen (fun z θ => gamCoefAng α θ * bcoefRad z) ∧
    Work.Spaces.HkMem α 3 (fun z θ => gamCoefAng α θ * bcoefRad z) ∧
    Work.Spaces.HkSq α 3 (fun z θ => gamCoefAng α θ * bcoefRad z) ≤ C := by
  obtain ⟨K, hKpos, hrb⟩ := rad_aux
  obtain ⟨M, hMpos, hang⟩ := ang_aux
  have hK : 0 ≤ K := le_of_lt hKpos
  have hC0nn : (0 : ℝ) ≤ radC0 := radC0_nonneg
  refine ⟨128 * K ^ 2 * radC0 * M + 1,
    by have h : (0 : ℝ) ≤ 128 * K ^ 2 * radC0 * M :=
         mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) (sq_nonneg K)) hC0nn)
           (le_of_lt hMpos)
       linarith, fun α hα hα1 => ?_⟩
  obtain ⟨hangint, hangbd⟩ := hang α hα hα1
  have hsm : Work.FTS.EllipticEst.SmoothOpen (fun z θ => gamCoefAng α θ * bcoefRad z) := smoothOpen_prod α
  have hA0 : 0 ≤ ∫ θ in Work.Spaces.Iθ, radAngInt α θ :=
    integral_nonneg_of_ae (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
      (fun θ hθ => radAngInt_nonneg (sin_two_nonneg_of_mem_Iθ hθ)))
  have hmajint : ∀ z : ℝ, MeasureTheory.Integrable
      (fun θ : ℝ => radSnorm z * (16 * radC0 * radAngInt α θ))
      (volume.restrict Work.Spaces.Iθ) := by
    intro z
    exact (hangint.const_mul (16 * radC0)).const_mul (radSnorm z)
  have hinner : ∀ z ∈ Work.Spaces.Iz,
      (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 3 (fun z θ => gamCoefAng α θ * bcoefRad z) z θ)
        ≤ radSnorm z * (16 * radC0 * (∫ θ in Work.Spaces.Iθ, radAngInt α θ)) := by
    intro z hz
    have hae : ∀ᵐ θ ∂(volume.restrict Work.Spaces.Iθ),
        Work.Spaces.HkIntegrand α 3 (fun z θ => gamCoefAng α θ * bcoefRad z) z θ
          ≤ radSnorm z * (16 * radC0 * radAngInt α θ) :=
      MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc
        (fun θ hθ => hkIntegrand_le hα hα1 z hz θ hθ)
    have hmono := MeasureTheory.integral_mono_of_nonneg
      (Eventually.of_forall fun θ => Work.Spaces.HkIntegrand_nonneg α 3 _ z θ)
      (hmajint z) hae
    refine hmono.trans (le_of_eq ?_)
    rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
  refine ⟨hsm, ?_, ?_⟩
  · refine Work.FTS.LocData.HkMem_of_majorant α 3
      (M := fun z θ => radSnorm z * (16 * radC0 * radAngInt α θ)) ?_ ?_ ?_ ?_
    · simpa only [Work.FTS.EllipticEst.Q0] using hsm.continuousOn_HkIntegrand α 3
    · intro z hz
      exact hmajint z
    · have hS := (radSnorm_int_le hK hrb).1
      have he : (fun z : ℝ => ∫ θ in Work.Spaces.Iθ,
            radSnorm z * (16 * radC0 * radAngInt α θ))
          = fun z : ℝ => radSnorm z * (16 * radC0 * (∫ θ in Work.Spaces.Iθ, radAngInt α θ)) := by
        funext z
        rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
      rw [he]
      exact hS.mul_const _
    · intro z hz θ hθ
      exact hkIntegrand_le hα hα1 z hz θ hθ
  · rw [Work.Spaces.HkSq]
    have hSbd := (radSnorm_int_le hK hrb).2
    have houter := MeasureTheory.integral_mono_of_nonneg
      (Eventually.of_forall fun z => integral_nonneg fun θ =>
        Work.Spaces.HkIntegrand_nonneg α 3 _ z θ)
      ((radSnorm_int_le hK hrb).1.mul_const _)
      (MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ici hinner)
    rw [MeasureTheory.integral_mul_const] at houter
    refine houter.trans ?_
    have h1 : (∫ z in Work.Spaces.Iz, radSnorm z) * (16 * radC0 * (∫ θ in Work.Spaces.Iθ, radAngInt α θ))
        ≤ 8 * K ^ 2 * (16 * radC0 * (∫ θ in Work.Spaces.Iθ, radAngInt α θ)) :=
      mul_le_mul_of_nonneg_right hSbd (mul_nonneg (mul_nonneg (by norm_num) radC0_nonneg) hA0)
    refine h1.trans ?_
    have h2 : 8 * K ^ 2 * (16 * radC0 * (∫ θ in Work.Spaces.Iθ, radAngInt α θ))
        ≤ 8 * K ^ 2 * (16 * radC0 * M) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hangbd
        (mul_nonneg (by norm_num) radC0_nonneg)) (by positivity)
    refine h2.trans ?_
    have hEq : 8 * K ^ 2 * (16 * radC0 * M) = 128 * K ^ 2 * radC0 * M := by ring
    linarith [hEq]



/-- **The projector coefficient `Bcoef α = (Γ(θ)/c(α))·2z²/(1+z)³` is smooth on the open
quadrant and lies in `ℋ³`, with `ℋ³`-norm-square bounded uniformly for `α ∈ (0,1]`.** -/
theorem bcoef_gamCoef_le : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ), 0 < α → α ≤ 1 →
    Work.FTS.EllipticEst.SmoothOpen
      (fun z θ => (Work.Spaces.Gam α θ / Work.Spaces.c α) * (2 * z ^ 2 / (1 + z) ^ 3)) ∧
    Work.Spaces.HkMem α 3
      (fun z θ => (Work.Spaces.Gam α θ / Work.Spaces.c α) * (2 * z ^ 2 / (1 + z) ^ 3)) ∧
    Work.Spaces.HkSq α 3
      (fun z θ => (Work.Spaces.Gam α θ / Work.Spaces.c α) * (2 * z ^ 2 / (1 + z) ^ 3)) ≤ C := by
  simpa only [bcoefRad, gamCoefAng] using bcoef_gamCoef_le_aux

end Work.FTS.StrongPersist.L3Aux
