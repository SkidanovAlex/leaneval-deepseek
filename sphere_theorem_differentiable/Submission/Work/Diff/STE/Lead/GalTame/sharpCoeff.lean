import Mathlib
import Submission.Work.Diff.STE.B3.Comp
import Submission.Work.Diff.STE.B3.Data
import Submission.Work.Diff.STE.B3.BNorm_ENormB_equiv
import Submission.Work.Diff.STE.B3.TransportDefs
import Submission.Work.Diff.STE.B3.mat_ENormSq_le_clean
import Submission.Work.Diff.STE.B3.tmA_props
import Submission.Work.Diff.STE.B3.tmGamma_uniform
import Submission.Work.Diff.STE.B3.transport_tame_defs
import Submission.Work.Diff.STE.B3.bg_window_aux
import Submission.Work.Diff.STE.B3.tmw_bgwin
import Submission.Work.Diff.STE.D.Setup
import Submission.Work.Diff.STE.Man.Sect
import Submission.Work.Diff.STE.Man.isDeTurckNonlin_chartNonlin
import Submission.Work.Diff.STE.Torus
import Submission.Work.Diff.STE.Lead.Gal.transportExistsAUniformGal
import Submission.Work.Diff.STE.Lead.Gal.gardADefs
import Submission.Work.Diff.STE.Lead.GalTame.CoeffKit
import Submission.Work.Diff.STE.Lead.GalTame.ENormB_mono_level
import Submission.Work.Diff.STE.Lead.GalTame.energyPeriodization
import Submission.Work.Diff.STE.Lead.GalTame.gnSharpClean
import Submission.Work.Diff.STE.Lead.GalTame.ballMatJetGf
import Submission.Work.Diff.STE.Lead.GalTame.cutEnergyLeibnizOnSupport
import Submission.Work.Diff.STE.Lead.GalTame.invEnergyWhole
import Submission.Work.Diff.STE.B3.CSq_period_le_integral_deriv
import Submission.Work.Diff.STE.Lead.GalTame.tmA_l2_reduce

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.Lead.GalTame

set_option maxHeartbeats 8000000

/-! ## Private helpers for the `L²`-jet chain of clause 7 -/

/-- Iterated real partial derivatives of a compactly supported function are compactly
supported. -/
private lemma hasCompactSupport_pdRList {n : ℕ} {u : (Fin n → ℝ) → ℝ}
    (hu : HasCompactSupport u) :
    ∀ l : List (Fin n), HasCompactSupport (Work.Diff.STE.pdRList l u) := by
  intro l
  induction l with
  | nil => simpa only [Work.Diff.STE.pdRList, List.foldr_nil] using hu
  | cons i t ih =>
      have h1 : HasCompactSupport (Work.Diff.STE.pdR i (Work.Diff.STE.pdRList t u)) :=
        ih.fderiv_apply ℝ (Pi.single i (1 : ℝ))
      show HasCompactSupport (Work.Diff.STE.pdRList (i :: t) u)
      simpa only [Work.Diff.STE.pdRList, List.foldr_cons] using h1

/-- Complexification preserves compact support. -/
private lemma hasCompactSupport_ofReal_comp {n : ℕ} {u : (Fin n → ℝ) → ℝ}
    (h : HasCompactSupport u) :
    HasCompactSupport (fun y : Fin n → ℝ => ((u y : ℝ) : ℂ)) := by
  have hs : tsupport (fun y : Fin n → ℝ => ((u y : ℝ) : ℂ)) = tsupport u := by
    have h2 : Function.support (fun y : Fin n → ℝ => ((u y : ℝ) : ℂ)) = Function.support u := by
      ext y
      simp only [Function.mem_support, ne_eq, Complex.ofReal_eq_zero]
    exact congrArg closure h2
  rw [show HasCompactSupport (fun y : Fin n → ℝ => ((u y : ℝ) : ℂ))
      = IsCompact (tsupport (fun y : Fin n → ℝ => ((u y : ℝ) : ℂ))) from rfl, hs]
  exact h

/-- The complexified iterated partial derivatives of a compactly supported smooth real function
are compactly supported. -/
private lemma hasCompactSupport_pdVec_ofReal {n k : ℕ} {u : (Fin n → ℝ) → ℝ}
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) (hcs : HasCompactSupport u) (γ : Fin k → Fin n) :
    HasCompactSupport (Work.Diff.STE.pdVec k γ (fun y : Fin n → ℝ => ((u y : ℝ) : ℂ))) := by
  have h1 : HasCompactSupport (Work.Diff.STE.pdRVec k γ u) := by
    simpa only [Work.Diff.STE.pdRVec] using hasCompactSupport_pdRList hcs (List.ofFn γ)
  have h2 : Work.Diff.STE.pdVec k γ (fun y : Fin n → ℝ => ((u y : ℝ) : ℂ))
      = fun y : Fin n → ℝ => ((Work.Diff.STE.pdRVec k γ u y : ℝ) : ℂ) := by
    simpa only [Work.Diff.STE.pdVec, Work.Diff.STE.pdRVec] using
      Work.Diff.STE.cm_pdList_ofReal_smooth (List.ofFn γ) u hu
  rw [h2]
  exact hasCompactSupport_ofReal_comp h1

/-- The smoothness level of a `pdVec` is always at most `⊤`. -/
private lemma level_le_top (k : ℕ) :
    ((k : ℕ) : WithTop ℕ∞) ≤ ((⊤ : ℕ∞) : WithTop ℕ∞) :=
  WithTop.coe_le_coe.mpr le_top

/-- Continuity of the complexified `pdVec` of a smooth real function. -/
private lemma continuous_pdVec_ofReal {n k : ℕ} {u : (Fin n → ℝ) → ℝ}
    (hu : ContDiff ℝ (⊤ : ℕ∞) u) (γ : Fin k → Fin n) :
    Continuous (Work.Diff.STE.pdVec k γ (fun y : Fin n → ℝ => ((u y : ℝ) : ℂ))) :=
  Work.Diff.STE.continuous_pdVec k γ _
    ((Complex.ofRealCLM.contDiff.comp hu).of_le (level_le_top k))

/-- A function vanishing on an open set has vanishing iterated partial derivatives there. -/
private lemma pdList_eq_zero_of_mem_nhds {n : ℕ} {F : (Fin n → ℝ) → ℂ} {U : Set (Fin n → ℝ)}
    (hU : IsOpen U) (h0 : ∀ y ∈ U, F y = 0) :
    ∀ l : List (Fin n), ∀ y ∈ U, Work.Diff.STE.pdList l F y = 0 := by
  intro l
  induction l with
  | nil => intro y hy; simpa only [Work.Diff.STE.pdList, List.foldr_nil] using h0 y hy
  | cons i t ih =>
      intro y hy
      have hloc : Work.Diff.STE.pdList t F =ᶠ[nhds y] (fun _ => (0 : ℂ)) := by
        filter_upwards [hU.mem_nhds hy] with w hw
        exact ih w hw
      show Work.Diff.STE.pd i (Work.Diff.STE.pdList t F) y = 0
      simp only [Work.Diff.STE.pd]
      rw [Filter.EventuallyEq.fderiv_eq hloc]
      simp

private lemma tsupport_pdVec_subset {n k : ℕ} {F : (Fin n → ℝ) → ℂ} (γ : Fin k → Fin n) :
    tsupport (Work.Diff.STE.pdVec k γ F) ⊆ tsupport F := by
  have hkey : ∀ z ∉ tsupport F, Work.Diff.STE.pdVec k γ F z = 0 := by
    intro z hz
    have hU : IsOpen (tsupport F)ᶜ := (isClosed_tsupport F).isOpen_compl
    have h0 : ∀ y ∈ (tsupport F)ᶜ, F y = 0 := by
      intro y hy
      by_contra hy'
      exact hy (subset_tsupport F (Function.mem_support.mpr hy'))
    exact pdList_eq_zero_of_mem_nhds hU h0 (List.ofFn γ) z hz
  exact closure_minimal (fun z hz => by
    by_contra hz'
    exact hz (by simpa only [Function.mem_support, ne_eq] using hkey z hz'))
    (isClosed_tsupport F)

/-- The iterated partial derivatives of the zero function vanish. -/
private lemma pdList_zero {n : ℕ} (l : List (Fin n)) :
    Work.Diff.STE.pdList l (fun _ : Fin n → ℝ => (0 : ℂ)) = 0 := by
  induction l with
  | nil => rfl
  | cons i t ih =>
      rw [show Work.Diff.STE.pdList (i :: t) (fun _ : Fin n → ℝ => (0 : ℂ))
          = Work.Diff.STE.pd i (Work.Diff.STE.pdList t (fun _ : Fin n → ℝ => (0 : ℂ))) from rfl, ih]
      funext z
      simp [Work.Diff.STE.pd]

/-- A function supported in an open ball is compactly supported. -/
private lemma hasCompactSupport_of_support_subset_ball {n : ℕ} {f : (Fin n → ℝ) → ℝ}
    {R : ℝ} (h : Function.support f ⊆ Metric.ball 0 R) : HasCompactSupport f :=
  IsCompact.of_isClosed_subset (isCompact_closedBall 0 R) (isClosed_tsupport f)
    (closure_minimal (fun z hz => Metric.ball_subset_closedBall (h hz)) Metric.isClosed_closedBall)

/-- A complex-valued function supported in an open ball is compactly supported. -/
private lemma hasCompactSupportC_of_support_subset_ball {n : ℕ} {f : (Fin n → ℝ) → ℂ}
    {R : ℝ} (h : Function.support f ⊆ Metric.ball 0 R) : HasCompactSupport f :=
  IsCompact.of_isClosed_subset (isCompact_closedBall 0 R) (isClosed_tsupport f)
    (closure_minimal (fun z hz => Metric.ball_subset_closedBall (h hz)) Metric.isClosed_closedBall)

/-- The squared norm of a compactly supported function is compactly supported. -/
private lemma hasCompactSupport_normSq {n : ℕ} {F : (Fin n → ℝ) → ℂ}
    (h : HasCompactSupport F) :
    HasCompactSupport (fun z : Fin n → ℝ => ‖F z‖ ^ 2) := by
  refine h.mono' (fun z hz => ?_)
  refine subset_tsupport _ (Function.mem_support.mpr ?_)
  intro h0
  exact hz (by show ‖F z‖ ^ 2 = 0; rw [h0]; norm_num)

private lemma integrable_normSq_pdVec {n k : ℕ} {F : (Fin n → ℝ) → ℂ}
    (hsm : ContDiff ℝ (⊤ : ℕ∞) F) (hcs : HasCompactSupport F) (γ : Fin k → Fin n) :
    MeasureTheory.Integrable (fun z : Fin n → ℝ => ‖Work.Diff.STE.pdVec k γ F z‖ ^ 2) := by
  have hcs' : HasCompactSupport (Work.Diff.STE.pdVec k γ F) :=
    hcs.mono' (subset_trans (subset_tsupport _) (tsupport_pdVec_subset γ))
  have hcs2 := hasCompactSupport_normSq hcs' 
  have hcont : Continuous (fun z : Fin n → ℝ => ‖Work.Diff.STE.pdVec k γ F z‖ ^ 2) := by
    have hc := Work.Diff.STE.continuous_pdVec k γ F (hsm.of_le (level_le_top k))
    show Continuous ((fun z : Fin n → ℝ => ‖Work.Diff.STE.pdVec k γ F z‖) ^ 2)
    exact hc.norm.pow 2
  exact hcont.integrable_of_hasCompactSupport hcs2

/-- Restricting a nonnegative continuous integrand to a smaller ball. -/
private lemma setIntegral_ball_mono {n : ℕ} {f : (Fin n → ℝ) → ℝ} (hf : Continuous f)
    (hn : ∀ x, 0 ≤ f x) {r R : ℝ} (hr : r ≤ R) :
    ∫ x in Metric.ball (0 : Fin n → ℝ) r, f x ≤ ∫ x in Metric.ball (0 : Fin n → ℝ) R, f x := by
  refine MeasureTheory.setIntegral_mono_set ?_ ?_ ?_
  · exact (hf.continuousOn.integrableOn_compact (isCompact_closedBall 0 R)).mono_set
      (Metric.ball_subset_closedBall)
  · filter_upwards with x using hn x
  · filter_upwards with x hx using Metric.ball_subset_ball hr hx

/-- A function vanishing outside an open ball has its integral over the ball equal to its
integral over the whole space. -/
private lemma setIntegral_ball_eq_integral {n : ℕ} {R : ℝ} {f : (Fin n → ℝ) → ℝ}
    (hzero : ∀ x : Fin n → ℝ, x ∉ Metric.ball (0 : Fin n → ℝ) R → f x = 0) :
    ∫ x in Metric.ball (0 : Fin n → ℝ) R, f x = ∫ x : Fin n → ℝ, f x :=
  MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero hzero

/-- A smooth function times a function that is smooth on an open neighbourhood of its support
is smooth. -/
private lemma contDiff_mul_of_contDiffOn_of_tsupport {n : ℕ} {φ : (Fin n → ℝ) → ℝ}
    {f : (Fin n → ℝ) → ℝ} {s : Set (Fin n → ℝ)} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    (hs : IsOpen s) (hfs : ContDiffOn ℝ (⊤ : ℕ∞) f s) (hts : tsupport φ ⊆ s) :
    ContDiff ℝ (⊤ : ℕ∞) (fun z => φ z * f z) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z ∈ s
  · exact hφ.contDiffAt.mul (hfs.contDiffAt (hs.mem_nhds hz))
  · have hmem : (tsupport φ)ᶜ ∈ nhds z :=
      (isClosed_tsupport φ).isOpen_compl.mem_nhds (fun h => hz (hts h))
    have h0 : ContDiffAt ℝ (⊤ : ℕ∞) (fun _ : Fin n → ℝ => (0 : ℝ)) z := contDiffAt_const
    refine h0.congr_of_eventuallyEq ?_
    filter_upwards [hmem] with w hw
    have hw0 : φ w = 0 := by
      by_contra hw'
      exact hw (subset_tsupport φ (Function.mem_support.mpr hw'))
    simp [hw0]

/-- A partial derivative of a smooth complex function is smooth. -/
private lemma contDiff_pd' {n : ℕ} {F : (Fin n → ℝ) → ℂ} (hF : ContDiff ℝ (⊤ : ℕ∞) F)
    (r : Fin n) : ContDiff ℝ (⊤ : ℕ∞) (Work.Diff.STE.pd r F) := by
  have h1 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fderiv ℝ F) :=
    hF.fderiv_right (m := (⊤ : ℕ∞)) (by simp)
  have h2 : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun z : Fin n → ℝ => (fderiv ℝ F z) (Pi.single r (1 : ℝ))) := by
    fun_prop
  exact h2

/-- Iterated partial derivatives of a smooth complex function are smooth. -/
private lemma contDiff_pdList' {n : ℕ} (l : List (Fin n)) {F : (Fin n → ℝ) → ℂ}
    (hF : ContDiff ℝ (⊤ : ℕ∞) F) : ContDiff ℝ (⊤ : ℕ∞) (Work.Diff.STE.pdList l F) := by
  induction l with
  | nil => simpa only [Work.Diff.STE.pdList, List.foldr_nil] using hF
  | cons i t ih =>
      have h1 : Work.Diff.STE.pdList (i :: t) F = Work.Diff.STE.pd i (Work.Diff.STE.pdList t F) :=
        rfl
      rw [h1]
      exact contDiff_pd' ih i

/-- `pd` is additive over differences of smooth functions. -/
private lemma pd_sub_fun' {n : ℕ} {A B : (Fin n → ℝ) → ℂ}
    (hA : ContDiff ℝ (⊤ : ℕ∞) A) (hB : ContDiff ℝ (⊤ : ℕ∞) B) (r : Fin n) :
    Work.Diff.STE.pd r (A - B) = Work.Diff.STE.pd r A - Work.Diff.STE.pd r B := by
  funext z
  simp only [Work.Diff.STE.pd, Pi.sub_apply, ContinuousLinearMap.sub_apply]
  rw [fderiv_sub (hA.contDiffAt.differentiableAt (by simp))
    (hB.contDiffAt.differentiableAt (by simp))]
  rfl

/-- `pdList` is additive over differences of smooth functions. -/
private lemma pdList_sub_of_contDiff {n : ℕ} (l : List (Fin n)) {f g : (Fin n → ℝ) → ℂ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    Work.Diff.STE.pdList l (f - g) = Work.Diff.STE.pdList l f - Work.Diff.STE.pdList l g := by
  induction l with
  | nil => rfl
  | cons i t ih =>
      have h1 : Work.Diff.STE.pdList (i :: t) (f - g)
          = Work.Diff.STE.pd i (Work.Diff.STE.pdList t (f - g)) := rfl
      rw [h1, ih]
      exact pd_sub_fun' (contDiff_pdList' t hf) (contDiff_pdList' t hg) i

/-- `pdVec` is additive over differences of smooth functions. -/
private lemma pdVec_sub_of_contDiff {n k : ℕ} (γ : Fin k → Fin n) {f g : (Fin n → ℝ) → ℂ}
    (hf : ContDiff ℝ (⊤ : ℕ∞) f) (hg : ContDiff ℝ (⊤ : ℕ∞) g) :
    Work.Diff.STE.pdVec k γ (f - g)
      = Work.Diff.STE.pdVec k γ f - Work.Diff.STE.pdVec k γ g := by
  simpa only [Work.Diff.STE.pdVec] using pdList_sub_of_contDiff (List.ofFn γ) hf hg

/-- The quadratic form of an affine combination `a·1 + b·A` of matrices. -/
private lemma quadForm_affine {n : ℕ} (a b : ℝ) (A : Fin n → Fin n → ℝ) (ξ : Fin n → ℝ) :
    (∑ p, ∑ q, (a * (if p = q then (1 : ℝ) else 0) + b * A p q) * ξ p * ξ q)
      = a * (∑ p, (ξ p) ^ 2) + b * (∑ p, ∑ q, A p q * ξ p * ξ q) := by
  have hA : (∑ p, ∑ q, (if p = q then (1 : ℝ) else 0) * ξ p * ξ q) = ∑ p, (ξ p) ^ 2 := by
    refine Finset.sum_congr rfl (fun p _ => ?_)
    rw [Finset.sum_eq_single p]
    · rw [if_pos rfl, one_mul, pow_two]
    · intro q _ hq; rw [if_neg (fun hpq => hq hpq.symm)]; ring
    · intro hp; exact absurd (Finset.mem_univ p) hp
  calc (∑ p, ∑ q, (a * (if p = q then (1 : ℝ) else 0) + b * A p q) * ξ p * ξ q)
      = ∑ p, ∑ q, (a * ((if p = q then (1 : ℝ) else 0) * ξ p * ξ q)
            + b * (A p q * ξ p * ξ q)) := by
        refine Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun q _ => ?_))
        ring
    _ = ∑ p, ((∑ q, a * ((if p = q then (1 : ℝ) else 0) * ξ p * ξ q))
            + (∑ q, b * (A p q * ξ p * ξ q))) := by
        refine Finset.sum_congr rfl (fun p _ => Finset.sum_add_distrib)
    _ = ∑ p, (a * (∑ q, (if p = q then (1 : ℝ) else 0) * ξ p * ξ q)
            + b * (∑ q, A p q * ξ p * ξ q)) := by
        refine Finset.sum_congr rfl (fun p _ => ?_)
        rw [Finset.mul_sum, Finset.mul_sum]
    _ = (∑ p, a * (∑ q, (if p = q then (1 : ℝ) else 0) * ξ p * ξ q))
            + (∑ p, b * (∑ q, A p q * ξ p * ξ q)) := Finset.sum_add_distrib
    _ = a * (∑ p, ∑ q, (if p = q then (1 : ℝ) else 0) * ξ p * ξ q)
            + b * (∑ p, ∑ q, A p q * ξ p * ξ q) := by
        rw [Finset.mul_sum, Finset.mul_sum]
    _ = a * (∑ p, (ξ p) ^ 2) + b * (∑ p, ∑ q, A p q * ξ p * ξ q) := by rw [hA]

/-- The sum of a constant over a finite type. -/
private lemma sum_const_card {ι : Type*} [Fintype ι] (c : ℝ) :
    ∑ _ : ι, c = (Fintype.card ι : ℝ) * c := by
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]

/-- A function bounded by a constant has integral over a small ball at most the constant (times the
volume of the unit ball of radius `1/2`). -/
private lemma integral_ball_le_const {n : ℕ} {f : (Fin n → ℝ) → ℝ} (hf : Continuous f)
    {r c : ℝ} (hr : 0 < r) (hr2 : 2 * r ≤ 1) (hc : 0 ≤ c) (hb : ∀ z, f z ≤ c) :
    ∫ z in Metric.ball (0 : Fin n → ℝ) r, f z
      ≤ c * (MeasureTheory.volume (Metric.ball (0 : Fin n → ℝ) (1 / 2))).toReal := by
  have hV : (MeasureTheory.volume (Metric.ball (0 : Fin n → ℝ) (1 / 2))).toReal = 1 := by
    rw [Real.volume_pi_ball (0 : Fin n → ℝ) (by norm_num : (0 : ℝ) < 1 / 2)]
    norm_num
  have hvolr : (MeasureTheory.volume (Metric.ball (0 : Fin n → ℝ) r)).toReal ≤ 1 := by
    rw [Real.volume_pi_ball (0 : Fin n → ℝ) hr, ENNReal.toReal_ofReal (by positivity),
      Fintype.card_fin]
    calc (2 * r) ^ n ≤ 1 ^ n := pow_le_pow_left₀ (by linarith) hr2 n
      _ = 1 := one_pow n
  have hintf : MeasureTheory.IntegrableOn f (Metric.ball (0 : Fin n → ℝ) r) MeasureTheory.volume :=
    (hf.continuousOn.integrableOn_compact (isCompact_closedBall 0 r)).mono_set
      Metric.ball_subset_closedBall
  have hintc : MeasureTheory.IntegrableOn (fun _ : Fin n → ℝ => c) (Metric.ball 0 r)
      MeasureTheory.volume := MeasureTheory.integrableOn_const
  calc ∫ z in Metric.ball (0 : Fin n → ℝ) r, f z
      ≤ ∫ z in Metric.ball (0 : Fin n → ℝ) r, c :=
        MeasureTheory.setIntegral_mono_on hintf hintc Metric.isOpen_ball.measurableSet
          (fun z _ => hb z)
    _ = (MeasureTheory.volume (Metric.ball (0 : Fin n → ℝ) r)).toReal * c := by
        rw [MeasureTheory.setIntegral_const, smul_eq_mul]; rfl
    _ ≤ 1 * c := mul_le_mul_of_nonneg_right hvolr hc
    _ = c * (MeasureTheory.volume (Metric.ball (0 : Fin n → ℝ) (1 / 2))).toReal := by
        rw [hV]; ring

/-- The geometric sum over the low levels is dominated by the truncated geometric sum with the
shifted ratio which defines the counting constant. -/
private lemma sum_pow_le_geom {x : ℝ} (hx : 0 ≤ x) {m k : ℕ} (hmk : m ≤ k) :
    ∑ i ∈ Finset.range (m + 1), x ^ i
      ≤ ∑ ℓ ∈ Finset.range (k + 3), (x + 1) ^ ℓ := by
  have h1 : ∑ i ∈ Finset.range (m + 1), x ^ i
      ≤ ∑ i ∈ Finset.range (m + 1), (x + 1) ^ i :=
    Finset.sum_le_sum (fun i _ => pow_le_pow_left₀ hx (by linarith) i)
  have h2 : ∑ i ∈ Finset.range (m + 1), (x + 1) ^ i
      ≤ ∑ ℓ ∈ Finset.range (k + 3), (x + 1) ^ ℓ :=
    Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.range_subset.mpr (fun ℓ hℓ => Finset.mem_range.mpr (by omega)))
      (fun ℓ _ _ => pow_nonneg (by linarith) ℓ)
  linarith [h1, h2]

/-- Re-indexing an iterated partial derivative along an equality of the orders. -/
private lemma pdVec_cast_eq {n k m : ℕ} (h : k + 1 = m) (β : Fin m → Fin n)
    (F : (Fin n → ℝ) → ℂ) :
    Work.Diff.STE.pdVec m β F
      = Work.Diff.STE.pdVec (k + 1) (fun i : Fin (k + 1) => β (Fin.cast h i)) F := by
  show Work.Diff.STE.pdList (List.ofFn β) F
    = Work.Diff.STE.pdList (List.ofFn (fun i : Fin (k + 1) => β (Fin.cast h i))) F
  rw [List.ofFn_congr h.symm β]

/-- **The elliptic coefficient matrix `A` of the DeTurck transport, with the `pdR` jet hypothesis.**

`A` is globally smooth, `1`-periodic, symmetric, `lam'`-elliptic, agrees with the inverse `(Gf)⁻¹` of
the coordinate-frame chart matrix of `h` on the closed `2σ_j`-ball (`Gf = Work.Diff.STE.B3.Gf`, the
coordinate-frame chart matrix), and its value, its first partial derivative and all its `pdVec`-jets
of order `m ≤ k` are bounded by `CA` (the jets in `L²`, i.e. through `ENormSq 0`).  `lam'` and `CA`
are uniform in the section `h` and in the chart `j`.

This is the coefficient half of `Work.Diff.STE.Lead.GalTame.sharpTrans`; note that the only
hypothesis on `h`'s chart matrix is the first-order bound `hjet` (no higher jets are assumed).

Route: on the closed `2σ_j`-ball the coordinate chart matrix `Gf` is positive definite with
uniformly bounded inverse (`hell`, `hub`, `D.htarget`, compactness of the closed ball, and the
`g₀`-orthonormal frame `e j ·`), and the `pdVec`-jets of `Gf` are controlled by those of `h`'s
chart matrix `D.mat j h` (the frame change `Gf = Finvf · Mf · Finvfᵀ` and the Leibniz/product rule
for the `L²` energy); `D.mat j h`'s jet energies over a ball inside the chart are controlled by
`Σ_{i,c,d} ENormSq m (D.Rper i h c d)` — see `Work.Diff.STE.B3.mat_ENormSq_le_clean` (axiom-clean),
applied with a cut-off `φ` supported in the centre cube and equal to `1` on the closed `2σ_j`-ball.
Finally `A := λ' • 1 + per (φ · (γ - λ' • 1))` is the periodisation of the local inverse (the
periodisation does not change the `L²` energy of the jets, by the support condition). -/
theorem sharpCoeff
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (k : ℕ) (hk : 1 ≤ k) :
    ∀ (lam K : ℝ), 0 < lam → 0 < K →
      ∃ (lam' CA : ℝ), 0 < lam' ∧ 0 ≤ CA ∧
        ∀ (h : Work.Diff.STE.Bil (I := I) (M := M))
          (hsym : ∀ (x : M) (u v : TangentSpace I x), h x u v = h x v u)
          (hsmooth : Work.Diff.STE.D.ChartData (I := I) (M := M) h)
          (hell : ∀ (x : M) (v : TangentSpace I x), lam * g₀.inner x v v ≤ h x v v)
          (hub : ∀ (x : M) (v : TangentSpace I x), h x v v ≤ K * g₀.inner x v v)
          (hjet : ∀ (i : ι₀) (c d r : Fin (Module.finrank ℝ E))
            (z : Fin (Module.finrank ℝ E) → ℝ), ‖z‖ ≤ 2 * D.σ i →
            |Work.Diff.STE.pdR r (D.mat i h c d) z| ≤ K),
          ∀ j : ι₀,
          ∃ (A : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) →
                (Fin (Module.finrank ℝ E) → ℝ) → ℝ),
            (∀ (z : Fin (Module.finrank ℝ E) → ℝ) (c d : Fin (Module.finrank ℝ E)),
              A c d z = A d c z) ∧
            (∀ (z : Fin (Module.finrank ℝ E) → ℝ)
              (ξ : Fin (Module.finrank ℝ E) → ℝ),
              lam' * ∑ i, (ξ i) ^ 2 ≤ ∑ c, ∑ d, A c d z * ξ c * ξ d) ∧
            (∀ c d, ContDiff ℝ ((⊤ : ENat) : WithTop ENat) (A c d)) ∧
            (∀ c d, Work.Diff.STE.Periodic1 (A c d)) ∧
            (∀ (z : Fin (Module.finrank ℝ E) → ℝ) (c d : Fin (Module.finrank ℝ E)),
              |A c d z| ≤ CA) ∧
            (∀ (z : Fin (Module.finrank ℝ E) → ℝ) (r c d : Fin (Module.finrank ℝ E)),
              |Work.Diff.STE.pdR r (fun y : Fin (Module.finrank ℝ E) → ℝ => A c d y) z| ≤ CA) ∧
            (∀ (m : ℕ), m ≤ k → ∀ (β : Fin m → Fin (Module.finrank ℝ E))
              (c d : Fin (Module.finrank ℝ E)),
              Work.Diff.STE.ENormSq 0 (Work.Diff.STE.pdVec m β
                (fun y : Fin (Module.finrank ℝ E) → ℝ => ((A c d y : ℝ) : ℂ)))
                ≤ CA * (1 + D.ENormB m h)) ∧
            (∀ (z : Fin (Module.finrank ℝ E) → ℝ), ‖z‖ ≤ 2 * D.σ j →
              ∀ c d : Fin (Module.finrank ℝ E),
              A c d z = ((Matrix.of (Work.Diff.STE.B3.Gf (I := I) (M := M) D h j z))⁻¹) c d) := by
  intro lam K hlam hK
  -- ===== Step 0: the uniform data of the transport =====
  obtain ⟨δ₀, mlo, Mhi, c₀, Kr, Kr₁, cl, ch, hδ₀p, hmlo, hMhi, hc₀, hKr, hKr₁, hcl, hclch, hunif⟩ :=
    Work.Diff.STE.B3.tmGamma_uniform (I := I) (M := M) D lam K hlam hK
  obtain ⟨δb, m0, M0, hδbp, hm0, hM0, hbwin⟩ :=
    Work.Diff.STE.B3.bg_window_aux (I := I) (M := M) D
  obtain ⟨δt, hδtp, htgt0⟩ := Work.Diff.STE.Lead.Gal.gardTargetDelta (I := I) (M := M) D
  -- the uniform constant of the chart-matrix jet-energy estimate (clause 7)
  obtain ⟨δB, hδBpos, hBM⟩ :=
    Work.Diff.STE.Lead.GalTame.ballMatJetGf (I := I) (M := M) D k hk lam K hlam hK
  -- ===== Step 1: the uniform margin =====
  set mrg : ℝ := min δ₀ (min δb (min δt (1 / 8))) with hmrgdef
  have hmrgpos : 0 < mrg := by
    rw [hmrgdef]
    exact lt_min hδ₀p (lt_min hδbp (lt_min hδtp (by norm_num)))
  have hmrg₁ : mrg ≤ δ₀ := le_trans (min_le_left _ _) le_rfl
  have hmrg₂ : mrg ≤ δb := le_trans (min_le_right _ _) (min_le_left _ _)
  have hmrg₃ : mrg ≤ δt :=
    le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))
  have hmrg₄ : mrg ≤ 1 / 8 :=
    le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _))
  set δ : ℝ := min mrg δB / 64 with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; exact div_pos (lt_min hmrgpos hδBpos) (by norm_num)
  have hδle_mrg : δ ≤ mrg / 64 :=
    div_le_div_of_nonneg_right (min_le_left mrg δB) (by norm_num)
  have hδle_δB : δ ≤ δB / 64 :=
    div_le_div_of_nonneg_right (min_le_right mrg δB) (by norm_num)
  have hδmrg : 8 * δ ≤ mrg := by linarith
  have hδδB : 3 * δ ≤ 2 * δB := by linarith
  have hδδ₀ : 8 * δ ≤ δ₀ := le_trans hδmrg hmrg₁
  have hδδb : 8 * δ ≤ δb := le_trans hδmrg hmrg₂
  have hδδt : 8 * δ ≤ δt := le_trans hδmrg hmrg₃
  have hδ8 : 8 * δ ≤ 1 / 8 := le_trans hδmrg hmrg₄
  have hδ16 : δ ≤ 1 / 64 := by linarith
  -- ===== Step 2: the three cutoffs (families over the chart index) =====
  have hcutin : ∀ j : ι₀, ∃ φ : (Fin (Module.finrank ℝ E) → ℝ) → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) φ ∧ (∀ z, 0 ≤ φ z) ∧ (∀ z, φ z ≤ 1) ∧
      (∀ z, ‖z‖ ≤ 2 * D.σ j → φ z = 1) ∧
      tsupport φ ⊆ Metric.ball 0 (2 * D.σ j + δ) :=
    fun j => Kit.exists_cut_kit (r := 2 * D.σ j) (R := 2 * D.σ j + δ)
      (by linarith [D.hσ j, hδpos])
  choose φin hφin_sm hφin_0 hφin_1 hφin_eq1 hφin_ts using hcutin
  have hcutout : ∀ j : ι₀, ∃ φ : (Fin (Module.finrank ℝ E) → ℝ) → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) φ ∧ (∀ z, 0 ≤ φ z) ∧ (∀ z, φ z ≤ 1) ∧
      (∀ z, ‖z‖ ≤ 2 * D.σ j + δ → φ z = 1) ∧
      tsupport φ ⊆ Metric.ball 0 (2 * D.σ j + 2 * δ) :=
    fun j => Kit.exists_cut_kit (r := 2 * D.σ j + δ) (R := 2 * D.σ j + 2 * δ) (by linarith)
  choose φout hφout_sm hφout_0 hφout_1 hφout_eq1 hφout_ts using hcutout
  have hcutmid : ∀ j : ι₀, ∃ φ : (Fin (Module.finrank ℝ E) → ℝ) → ℝ,
      ContDiff ℝ (⊤ : ℕ∞) φ ∧ (∀ z, 0 ≤ φ z) ∧ (∀ z, φ z ≤ 1) ∧
      (∀ z, ‖z‖ ≤ 2 * D.σ j + 2 * δ → φ z = 1) ∧
      tsupport φ ⊆ Metric.ball 0 (2 * D.σ j + 3 * δ) :=
    fun j => Kit.exists_cut_kit (r := 2 * D.σ j + 2 * δ) (R := 2 * D.σ j + 3 * δ) (by linarith)
  choose φmid hφmid_sm hφmid_0 hφmid_1 hφmid_eq1 hφmid_ts using hcutmid
  -- uniform jet bounds of the cutoffs
  obtain ⟨Kφin, hKφin0, hKφin⟩ := Kit.exists_uniform_jet_bound (ι := ι₀)
    (n := Module.finrank ℝ E) (N := k + 1) φin (fun j => 2 * D.σ j + δ) hφin_sm
    (fun j z hz => Metric.ball_subset_closedBall (hφin_ts j hz))
  obtain ⟨Kφout, hKφout0, hKφout⟩ := Kit.exists_uniform_jet_bound (ι := ι₀)
    (n := Module.finrank ℝ E) (N := k + 1) φout (fun j => 2 * D.σ j + 2 * δ) hφout_sm
    (fun j z hz => Metric.ball_subset_closedBall (hφout_ts j hz))
  obtain ⟨Kφmid, hKφmid0, hKφmid⟩ := Kit.exists_uniform_jet_bound (ι := ι₀)
    (n := Module.finrank ℝ E) (N := k + 1) φmid (fun j => 2 * D.σ j + 3 * δ) hφmid_sm
    (fun j z hz => Metric.ball_subset_closedBall (hφmid_ts j hz))
  -- ===== Step 3: the elliptic window and the `tmA_props` constants =====
  rcases Nat.eq_zero_or_pos (Module.finrank ℝ E) with hn0 | hnpos
  · -- the model space is zero-dimensional: everything is vacuous
    refine ⟨1, 0, one_pos, le_refl 0, ?_⟩
    intro h hsym hsmooth hell hub hjet j
    have hc : ∀ c : Fin (Module.finrank ℝ E), False := fun c => by
      have h := c.isLt
      omega
    refine ⟨fun _ _ _ => (0 : ℝ), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro z c d; exact (hc c).elim
    · intro z ξ
      have hS : (∑ i : Fin (Module.finrank ℝ E), (ξ i) ^ 2) = 0 :=
        Finset.sum_eq_zero (fun i _ => by
          have h := i.isLt
          omega)
      have hT : (∑ c : Fin (Module.finrank ℝ E),
          ∑ d : Fin (Module.finrank ℝ E), (0 : ℝ) * ξ c * ξ d) = 0 :=
        Finset.sum_eq_zero (fun c _ => by
          have h := c.isLt
          omega)
      rw [hS, hT]
      norm_num
    · intro c d; exact (hc c).elim
    · intro c d; exact (hc c).elim
    · intro z c d; exact (hc c).elim
    · intro z r c d; exact (hc c).elim
    · intro m hm β c d; exact (hc c).elim
    · intro z hz c d; exact (hc c).elim
  · -- ===== the main case =====
    have hRj : ∀ j : ι₀, 2 * D.σ j + δ ≤ 1 / 2 := by
      intro j
      have h1 := D.hσ2 j
      linarith [hδ16]
    have hCj : ∀ j : ι₀, ∃ C : ℝ, 0 ≤ C ∧
        (∀ (φ' : (Fin (Module.finrank ℝ E) → ℝ) → ℝ)
          (γ : (Fin (Module.finrank ℝ E) → ℝ) → Fin (Module.finrank ℝ E) →
            Fin (Module.finrank ℝ E) → ℝ) (lam'' : ℝ), 0 < lam'' → lam'' ≤ c₀ →
          ContDiff ℝ (⊤ : ℕ∞) φ' → (∀ z, 0 ≤ φ' z) → (∀ z, φ' z ≤ 1) →
          (∀ (z : Fin (Module.finrank ℝ E) → ℝ) (r : Fin (Module.finrank ℝ E)),
            |Work.Diff.STE.pdR r φ' z| ≤ Kφin) →
          tsupport φ' ⊆ Metric.ball 0 (2 * D.σ j + δ) →
          (∀ (p q : Fin (Module.finrank ℝ E)), ContDiffOn ℝ (⊤ : ℕ∞) (fun w => γ w p q)
            (Metric.ball 0 (2 * D.σ j + δ))) →
          (∀ z ∈ Metric.ball 0 (2 * D.σ j + δ), ∀ p q,
            γ z p q = γ z q p) →
          (∀ z ∈ Metric.ball 0 (2 * D.σ j + δ), ∀ ξ : Fin (Module.finrank ℝ E) → ℝ,
            c₀ * ∑ p, (ξ p) ^ 2 ≤ ∑ p, ∑ q, γ z p q * ξ p * ξ q) →
          (∀ z ∈ Metric.ball 0 (2 * D.σ j + δ), ∀ p q,
            |γ z p q| ≤ max Kr Kr₁) →
          (∀ z ∈ Metric.ball 0 (2 * D.σ j + δ), ∀ (r p q : Fin (Module.finrank ℝ E)),
            |Work.Diff.STE.pdR r (fun w => γ w p q) z| ≤ max Kr Kr₁) →
          (∀ z p q, |Work.Diff.STE.B3.tmA φ' lam'' γ z p q| ≤ C) ∧
          (∀ z r p q,
            |Work.Diff.STE.pdR r (fun w => Work.Diff.STE.B3.tmA φ' lam'' γ w p q) z| ≤ C) ∧
          (∀ z p q, Work.Diff.STE.B3.tmA φ' lam'' γ z p q
              = Work.Diff.STE.B3.tmA φ' lam'' γ z q p) ∧
          (∀ z ξ : Fin (Module.finrank ℝ E) → ℝ,
            lam'' * ∑ p, (ξ p) ^ 2
              ≤ ∑ p, ∑ q, Work.Diff.STE.B3.tmA φ' lam'' γ z p q * ξ p * ξ q) ∧
          ContDiff ℝ (⊤ : ℕ∞) (Work.Diff.STE.B3.tmA φ' lam'' γ) ∧
          Work.Diff.STE.Periodic1 (Work.Diff.STE.B3.tmA φ' lam'' γ)) :=
      fun j => Work.Diff.STE.B3.tmA_props (2 * D.σ j + δ) c₀ (max Kr Kr₁) Kφin
        (hRj j) hc₀ (le_trans hKr (le_max_left Kr Kr₁)) hKφin0
    choose Cj hCj0 hCjb using hCj
    -- ===== Step 3b: the constants of the `L²`-jet chain of clause 7 =====
    -- the pointwise inverse of the globalised matrix field
    obtain ⟨cinv, Cinv, hcinvpos, hCinvnn, hMInv⟩ :=
      Kit.matrix_inv_quadForm (n := Module.finrank ℝ E) (mlo := min 1 mlo)
        (Mhi := max 1 Mhi) (lt_min one_pos hmlo) hnpos
    set U : ℝ := 2 + 2 * K * (Mhi / lam) with hUdef
    clear_value U
    have hU0 : 0 ≤ U := by
      rw [hUdef]
      have h1 : (0 : ℝ) ≤ Mhi / lam := div_nonneg (le_of_lt hMhi) (le_of_lt hlam)
      have h2 : (0 : ℝ) ≤ 2 * K * (Mhi / lam) := mul_nonneg (by linarith [hK]) h1
      linarith
    set Wg : ℝ := Cinv with hWgdef
    clear_value Wg
    have hWg0 : 0 ≤ Wg := hCinvnn
    -- the Gagliardo–Nirenberg bounds and the Moser inverse estimates, level by level
    choose Kgn hKgn0 hKgnb using fun ℓ : Fin k =>
      gnSharp (ι := Fin (Module.finrank ℝ E)) (ℓ.1 + 1)
    choose CinvE hCinvE0 hCinvEb using fun ℓ : Fin k =>
      invEnergyWhole (n := Module.finrank ℝ E) (ℓ.1 + 1) (by omega)
        ⟨Kgn ℓ, hKgn0 ℓ, fun U' f hf hper hb => hKgnb ℓ U' f hf hper hb⟩ U Wg hU0 hWg0
    -- the chart-matrix jet constants (uniform in the section and in the chart)
    choose Cmat hCmat0 hCmatb using fun ℓ : Fin (k + 1) =>
      hBM ℓ.1 (Nat.lt_succ_iff.mp ℓ.2) Kφmid hKφmid0
    choose Clei hClei0 hCleib using fun ℓ : Fin (k + 1) =>
      cutEnergyLeibnizOnSupport (n := Module.finrank ℝ E) ℓ.1
    -- the energy-monotonicity constants
    choose Cmon hCmon0 hCmonb using fun mm : Fin (k + 1) =>
      ENormB_mono_level (I := I) (M := M) D mm.1
    obtain ⟨Cstep, hCstep0, hCstepb⟩ := ENormB_step (I := I) (M := M) D 0
    -- the volume of the ball of radius `1/2`
    set Vb : ℝ := (MeasureTheory.volume
      (Metric.ball (0 : Fin (Module.finrank ℝ E) → ℝ) (1 / 2))).toReal with hVbdef
    have hVb0 : 0 ≤ Vb := ENNReal.toReal_nonneg
    -- crude uniform combinations
    set Cmatsum : ℝ := ∑ ℓ : Fin (k + 1), (Cmat ℓ + 1) with hCmatsumdef
    have hCmatsum0 : 0 ≤ Cmatsum := Finset.sum_nonneg (fun ℓ _ => by linarith [hCmat0 ℓ])
    set Cmonmax : ℝ := ∑ mm : Fin (k + 1), (Cmon mm + 1) with hCmonmaxdef
    have hCmonmax0 : 0 ≤ Cmonmax := Finset.sum_nonneg (fun ℓ _ => by linarith [hCmon0 ℓ])
    set Cleimax : ℝ := ∑ ℓ : Fin (k + 1), (Clei ℓ + 1) with hCleimaxdef
    have hCleimax0 : 0 ≤ Cleimax := Finset.sum_nonneg (fun ℓ _ => by linarith [hClei0 ℓ])
    set CinvEmax : ℝ := ∑ ℓ : Fin k, (CinvE ℓ + 1) with hCinvEmaxdef
    have hCinvEmax0 : 0 ≤ CinvEmax := Finset.sum_nonneg (fun ℓ _ => by linarith [hCinvE0 ℓ])
    set Nsum : ℝ := ∑ ℓ ∈ Finset.range (k + 3),
      ((Module.finrank ℝ E : ℝ) + 1) ^ ℓ with hNsumdef
    have hNsum1 : 1 ≤ Nsum := by
      rw [hNsumdef]
      refine le_trans ?_ (Finset.single_le_sum
        (f := fun ℓ => ((Module.finrank ℝ E : ℝ) + 1) ^ ℓ) (fun ℓ _ => by positivity)
        (Finset.mem_range.mpr (by omega : 0 < k + 3)))
      simp
    have hNsum0 : 0 ≤ Nsum := le_trans zero_le_one hNsum1
    clear_value Nsum
    -- the `G`-side and `H`-side constants
    set Kzero : ℝ := 1 + Cstep * Cmonmax with hKzerodef
    clear_value Kzero
    have hKzero0 : 0 ≤ Kzero := by rw [hKzerodef]; nlinarith [hCstep0, hCmonmax0]
    -- the uniform level constant: `1 + ENormB i h ≤ KmonE * (1 + ENormB m h)` for `i ≤ m ≤ k`
    set KmonE : ℝ := Kzero + Cmonmax + 1 with hKmonEdef
    clear_value KmonE
    have hKmonE0 : 0 ≤ KmonE := by rw [hKmonEdef]; linarith [hKzero0, hCmonmax0]
    have hKzero_le : Kzero ≤ KmonE := by rw [hKmonEdef]; linarith [hCmonmax0]
    have hCmonmax_le : Cmonmax + 1 ≤ KmonE := by rw [hKmonEdef]; linarith [hKzero0]
    -- the per-level constant of the inner sum
    set Kt : ℝ := 2 * Cmatsum * KmonE + 2 * (Kφmid ^ 2 * Vb + 1) with hKtdef
    clear_value Kt
    have hKt0 : 0 ≤ Kt := by
      rw [hKtdef]
      have h1 : (0 : ℝ) ≤ 2 * Cmatsum * KmonE :=
        mul_nonneg (by linarith [hCmatsum0]) (by linarith [hKmonE0])
      have h2 : (0 : ℝ) ≤ 2 * (Kφmid ^ 2 * Vb + 1) := by nlinarith [sq_nonneg Kφmid, hVb0]
      linarith
    set Kinner : ℝ := (Nsum + 1) * (Kt + 1) + 1 with hKinnerdef
    clear_value Kinner
    have hKinner0 : 0 ≤ Kinner := by
      rw [hKinnerdef]
      have h1 : (0 : ℝ) ≤ Nsum + 1 := by linarith [hNsum0]
      have h2 : (0 : ℝ) ≤ Kt + 1 := by linarith [hKt0]
      nlinarith [h1, h2]
    set Cg : ℝ := (Nsum + 1) * (Cleimax + 1) * (Kφout ^ 2 + 1) * (Kinner + 1) + 1
      with hCgdef
    clear_value Cg
    have hCg0 : 0 ≤ Cg := by
      rw [hCgdef]
      have h2 : (0 : ℝ) ≤ Kφout ^ 2 + 1 := by positivity
      have h4 : (0 : ℝ) ≤ Nsum + 1 := by linarith
      have h5 : (0 : ℝ) ≤ Cleimax + 1 := by linarith
      have h6 : (0 : ℝ) ≤ Kinner + 1 := by linarith
      have h8 : 0 ≤ (Nsum + 1) * (Cleimax + 1) * (Kφout ^ 2 + 1) * (Kinner + 1) :=
        mul_nonneg (mul_nonneg (mul_nonneg h4 h5) h2) h6
      linarith
    set Chs : ℝ := CinvEmax * (1 + Nsum * Cg) + Wg ^ 2 * Vb + 1 with hChsdef
    have hChs0 : 0 ≤ Chs := by
      rw [hChsdef]
      have h1 : (0 : ℝ) ≤ Nsum * Cg := mul_nonneg hNsum0 hCg0
      have h2 : (0 : ℝ) ≤ Wg ^ 2 * Vb := mul_nonneg (sq_nonneg Wg) hVb0
      nlinarith [hCinvEmax0, h1, h2]
    clear_value Chs
    -- the reduction constants (`tmA_l2_reduce`, level by level)
    have hCredEx := fun ℓ : Fin k =>
      Work.Diff.STE.Lead.GalTame.tmA_l2_reduce (n := Module.finrank ℝ E) (m := ℓ.1 + 1)
        (Nat.succ_pos ℓ.1) (Mφ := Kφin) (lam' := min c₀ 1) (hMφ := hKφin0)
    let Cred : Fin k → ℝ := fun ℓ => Classical.choose (hCredEx ℓ)
    have hCred0 : ∀ ℓ : Fin k, 0 ≤ Cred ℓ := fun ℓ => (Classical.choose_spec (hCredEx ℓ)).1
    have hCredb := fun ℓ : Fin k => (Classical.choose_spec (hCredEx ℓ)).2
    set CA0 : ℝ := ∑ ℓ : Fin k, (Cred ℓ + 1) with hCA0def
    clear_value CA0
    have hCA00 : 0 ≤ CA0 := by
      rw [hCA0def]
      exact Finset.sum_nonneg (fun ℓ _ => by linarith [hCred0 ℓ])
    have hCredle : ∀ ℓ : Fin k, Cred ℓ ≤ CA0 := by
      intro ℓ
      have h1 : Cred ℓ + 1 ≤ CA0 := by
        rw [hCA0def]
        exact Finset.single_le_sum (f := fun i : Fin k => Cred i + 1)
          (fun i _ => by linarith [hCred0 i]) (Finset.mem_univ ℓ)
      linarith
    set CA2 : ℝ := CA0 * (1 + Nsum * Chs) + 1 with hCA2def
    clear_value CA2
    set CA : ℝ := (∑ j : ι₀, Cj j) ^ 2 + (∑ j : ι₀, Cj j) + Kφin + Kφout + Kφmid + CA2 + 1
      with hCAdef
    clear_value CA
    have hCA20 : 0 ≤ CA2 := by
      rw [hCA2def]
      have h1 : (0 : ℝ) ≤ 1 + Nsum * Chs := by nlinarith [mul_nonneg hNsum0 hChs0]
      have h2 : (0 : ℝ) ≤ CA0 * (1 + Nsum * Chs) := mul_nonneg hCA00 h1
      linarith
    have hCA0 : 0 ≤ CA := by
      rw [hCAdef]
      have h1 : 0 ≤ ∑ j : ι₀, Cj j := Finset.sum_nonneg (fun j _ => hCj0 j)
      have h3 : (0 : ℝ) ≤ (∑ j : ι₀, Cj j) ^ 2 + (∑ j : ι₀, Cj j) := by positivity
      linarith
    have hCA2le : CA2 ≤ CA := by
      rw [hCAdef]
      have h1 : 0 ≤ ∑ j : ι₀, Cj j := Finset.sum_nonneg (fun j _ => hCj0 j)
      have h3 : (0 : ℝ) ≤ (∑ j : ι₀, Cj j) ^ 2 + (∑ j : ι₀, Cj j) := by positivity
      linarith
    have hCjle : ∀ j : ι₀, Cj j ≤ CA := by
      intro j
      have h1 : Cj j ≤ ∑ i : ι₀, Cj i :=
        Finset.single_le_sum (fun i _ => hCj0 i) (Finset.mem_univ j)
      have h2 : (0 : ℝ) ≤ ∑ i : ι₀, Cj i := Finset.sum_nonneg (fun i _ => hCj0 i)
      rw [hCAdef]
      have h3 : (0 : ℝ) ≤ (∑ i : ι₀, Cj i) ^ 2 := sq_nonneg _
      linarith
    have hlam'pos : 0 < min c₀ 1 := lt_min hc₀ one_pos
    have hlam'c : min c₀ 1 ≤ c₀ := min_le_left _ _ 
    refine ⟨min c₀ 1, CA, hlam'pos, hCA0, ?_⟩
    intro h hsym hsmooth hell hub hjet j
    -- the positive definiteness of `h` from the lower pinching bound
    have hpos : ∀ (x : M) (v : TangentSpace I x), v ≠ 0 → 0 < h x v v := by
      intro x v hv
      have h1 : 0 < g₀.inner x v v := g₀.pos x v hv
      have h2 := hell x v
      nlinarith [h1, h2, hlam]
    -- the window data of the transport, on the enlarged ball
    have hwin : ∀ (z : Fin (Module.finrank ℝ E) → ℝ), ‖z‖ ≤ 2 * D.σ j + 5 * δ →
        (∀ ξ : Fin (Module.finrank ℝ E) → ℝ,
          mlo * ∑ i, (ξ i) ^ 2 ≤ ∑ p, ∑ q,
            Work.Diff.STE.B3.Gf (I := I) (M := M) D h j z p q * ξ p * ξ q) ∧
        (∀ ξ : Fin (Module.finrank ℝ E) → ℝ,
          (∑ p, ∑ q, Work.Diff.STE.B3.Gf (I := I) (M := M) D h j z p q * ξ p * ξ q)
            ≤ Mhi * ∑ i, (ξ i) ^ 2) ∧
        (cl ≤ (Matrix.of (fun i k => Work.Diff.STE.B3.Gf (I := I) (M := M) D h j z i k)).det ∧
          (Matrix.of (fun i k => Work.Diff.STE.B3.Gf (I := I) (M := M) D h j z i k)).det ≤ ch) ∧
        (∀ ξ : Fin (Module.finrank ℝ E) → ℝ,
          c₀ * ∑ i, (ξ i) ^ 2 ≤ ∑ p, ∑ q,
            ((Matrix.of (fun i k => Work.Diff.STE.B3.Gf (I := I) (M := M) D h j z i k))⁻¹) p q
              * ξ p * ξ q) ∧
        (∀ p q : Fin (Module.finrank ℝ E),
          |((Matrix.of (fun i k => Work.Diff.STE.B3.Gf (I := I) (M := M) D h j z i k))⁻¹) p q|
            ≤ Kr) ∧
        (∀ (r p q : Fin (Module.finrank ℝ E)),
          |Work.Diff.STE.pdR r (fun w => ((Matrix.of (fun i k =>
              Work.Diff.STE.B3.Gf (I := I) (M := M) D h j w i k))⁻¹) p q) z| ≤ Kr₁) :=
      fun z hz => hunif h hsym hpos hsmooth hell hub hjet j z (by linarith [hδδ₀])
    -- the coefficient family `γ`: the inverse of the coordinate-frame chart matrix
    set γ : (Fin (Module.finrank ℝ E) → ℝ) → Fin (Module.finrank ℝ E) →
        Fin (Module.finrank ℝ E) → ℝ :=
      fun z p q => (Matrix.of (Work.Diff.STE.B3.Gf (I := I) (M := M) D h j z))⁻¹ p q with hγdef
    have hball : ∀ z : Fin (Module.finrank ℝ E) → ℝ, z ∈ Metric.ball 0 (2 * D.σ j + δ) →
        ‖z‖ ≤ 2 * D.σ j + 5 * δ := by
      intro z hz
      have hz' : ‖z‖ < 2 * D.σ j + δ := by
        rw [Metric.mem_ball, dist_zero_right] at hz
        exact hz
      linarith [hδpos]
    have hGfsm : ContDiffOn ℝ (⊤ : ℕ∞)
        (fun z : Fin (Module.finrank ℝ E) → ℝ => fun p q : Fin (Module.finrank ℝ E) =>
          Work.Diff.STE.B3.Gf (I := I) (M := M) D h j z p q) (Metric.ball 0 (2 * D.σ j + δ)) := by
      rw [contDiffOn_pi]
      intro p
      rw [contDiffOn_pi]
      intro q
      refine (Work.Diff.STE.Lead.Gal.Gf_contDiffOn_target (I := I) (M := M) D h hsmooth j p q).mono ?_
      intro z hz
      exact htgt0 j z (by linarith [hball z hz, hδδt, hδpos])
    have hγsm : ∀ p q : Fin (Module.finrank ℝ E), ContDiffOn ℝ (⊤ : ℕ∞)
        (fun w => γ w p q) (Metric.ball 0 (2 * D.σ j + δ)) := by
      intro p q
      refine (Work.Diff.STE.Man.contDiffOn_matrixInv_entry (n := Module.finrank ℝ E) p q).comp
        hGfsm ?_
      intro z hz
      have h1 := (hwin z (hball z hz)).2.2.1
      exact ne_of_gt (lt_of_lt_of_le hcl h1.1)
    have hγsym : ∀ z ∈ Metric.ball 0 (2 * D.σ j + δ), ∀ p q, γ z p q = γ z q p := by
      intro z hz p q
      have h1 : (Matrix.of (Work.Diff.STE.B3.Gf (I := I) (M := M) D h j z)).transpose
          = Matrix.of (Work.Diff.STE.B3.Gf (I := I) (M := M) D h j z) :=
        Work.Diff.STE.B3.tmw_Gf_transpose (I := I) (M := M) D h hsym j z
      have h2 : (Matrix.of (γ z)).transpose = Matrix.of (γ z) := by
        rw [show Matrix.of (γ z)
              = (Matrix.of (Work.Diff.STE.B3.Gf (I := I) (M := M) D h j z))⁻¹ from rfl,
          Matrix.transpose_nonsing_inv, h1]
      have h3 := congrFun (congrFun h2 q) p
      simpa [Matrix.transpose_apply] using h3
    have hγpos : ∀ z ∈ Metric.ball 0 (2 * D.σ j + δ), ∀ ξ : Fin (Module.finrank ℝ E) → ℝ,
        c₀ * ∑ p, (ξ p) ^ 2 ≤ ∑ p, ∑ q, γ z p q * ξ p * ξ q := by
      intro z hz ξ
      have h1 := (hwin z (hball z hz)).2.2.2.1 ξ
      simpa only [hγdef, Matrix.of_apply] using h1
    have hγb : ∀ z ∈ Metric.ball 0 (2 * D.σ j + δ), ∀ p q, |γ z p q| ≤ max Kr Kr₁ := by
      intro z hz p q
      have h1 := (hwin z (hball z hz)).2.2.2.2.1 p q
      simpa only [hγdef, Matrix.of_apply] using le_trans h1 (le_max_left Kr Kr₁)
    have hγd : ∀ z ∈ Metric.ball 0 (2 * D.σ j + δ), ∀ (r p q : Fin (Module.finrank ℝ E)),
        |Work.Diff.STE.pdR r (fun w => γ w p q) z| ≤ max Kr Kr₁ := by
      intro z hz r p q
      have h1 := (hwin z (hball z hz)).2.2.2.2.2 r p q
      simpa only [hγdef, Matrix.of_apply] using le_trans h1 (le_max_right Kr Kr₁)
    have hφin_pdR : ∀ (z : Fin (Module.finrank ℝ E) → ℝ) (r : Fin (Module.finrank ℝ E)),
        |Work.Diff.STE.pdR r (φin j) z| ≤ Kφin := by
      intro z r
      have h1 := (hKφin j).2 1 (by omega) (fun _ => r) z
      simpa [Work.Diff.STE.pdRVec, Work.Diff.STE.pdRList] using h1
    have hprops := hCjb j (φin j) γ (min c₀ 1) hlam'pos hlam'c (hφin_sm j) (hφin_0 j) (hφin_1 j)
      hφin_pdR (hφin_ts j) hγsm hγsym hγpos hγb hγd
    refine ⟨fun c d z => Work.Diff.STE.B3.tmA (φin j) (min c₀ 1) γ z c d, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- symmetry
      intro z c d
      exact hprops.2.2.1 z c d
    · -- ellipticity
      intro z ξ
      exact hprops.2.2.2.1 z ξ
    · -- smoothness of each component
      intro c d
      exact contDiff_pi.mp (contDiff_pi.mp hprops.2.2.2.2.1 c) d
    · -- periodicity
      intro c d i x
      exact congrFun (congrFun (hprops.2.2.2.2.2 i x) c) d
    · -- the value bound
      intro z c d
      exact le_trans (hprops.1 z c d) (hCjle j)
    · -- the first-derivative bound
      intro z r c d
      exact le_trans (hprops.2.1 z r c d) (hCjle j)
    · -- ===== clause 7: the `L²` jet bound =====
      -- ## Plan (complete; no gaps remain in this file)
      --  * `Gt := 1 + φout · (Gf - 1)` (smooth, symmetric `1`-periodic perturbation of `1`
      --    supported in `ball 0 (2σ j + 2δ) ⊆ ball 0 (1/2)`, with quadratic form squeezed between
      --    `min 1 mlo` and `max 1 Mhi`, hence invertible with `det` a unit and bounded inverse
      --    `Ht := (Gt)⁻¹` — `Kit.matrix_inv_quadForm`);
      --  * on `ball 0 (2σ j + δ)` one has `φout = 1`, hence `Gt = Gf` and `Ht = γ`;
      --  * `hmonE`: the uniform comparison `1 + ENormB i h ≤ KmonE (1 + ENormB m h)` for `i ≤ m`
      --    (level `0` via `ENormB_step`, levels `≥ 1` via `ENormB_mono_level`);
      --  * `hGside`: for every `1 ≤ j' ≤ m` the whole-space jet energy of `Gt` is `≤ Cg (1+E_m)`.
      --    The globalised field is split as `Gt = 1 + φout·(φmid·Gf - φmid·1)` (elements `FA`, `FB`
      --    of `hT`), bounded by the Leibniz estimate `cutEnergyLeibnizOnSupport`, the chart-matrix
      --    jet bound `ballMatJetGf` (for `FA`) and the uniform jet bound of the cut-off (for `FB`);
      --    the counting over the `(i,γ)`-indices is `sum_const_card` + `sum_pow_le_geom`;
      --  * `hHside`: the `H`-side follows from `invEnergyWhole` (Moser for the inverse of a
      --    compactly supported perturbation of the identity, with the sharp Grönwall–Nirenberg
      --    input `gnSharp`) applied at level `j'` to `Gt`, `Ht`;
      --  * the final step is the reduction `tmA_l2_reduce` (`hCredb`) converting the periodic
      --    coefficient to local ball jets, followed by the counting bound `hS` (with
      --    `sum_pow_le_geom`) and the constant assembly `hfinal`.
      intro m hm β c d
      rcases Nat.eq_zero_or_pos m with hm0 | hmpos
      · -- `m = 0`: only the pointwise bound is used
        subst hm0
        rw [Work.Diff.STE.ENormSq_zero]
        have hvol : (MeasureTheory.volume.restrict (Work.Diff.STE.unitCube
            (ι := Fin (Module.finrank ℝ E)))).real Set.univ = 1 := by
          show (((MeasureTheory.volume.restrict (Work.Diff.STE.unitCube
            (ι := Fin (Module.finrank ℝ E)))) :
              MeasureTheory.Measure (Fin (Module.finrank ℝ E) → ℝ)) Set.univ).toReal = 1
          rw [MeasureTheory.Measure.restrict_apply MeasurableSet.univ, Set.univ_inter,
            Work.Diff.STE.unitCube, Real.volume_pi_Ioc]
          simp
        have hbnd : (0 : ℝ) ≤ ∑ i : ι₀, Cj i := Finset.sum_nonneg (fun i _ => hCj0 i)
        have hpt : ∀ y : Fin (Module.finrank ℝ E) → ℝ,
            ‖Work.Diff.STE.pdVec 0 β (fun y => ((Work.Diff.STE.B3.tmA (φin j) (min c₀ 1) γ y c d
              : ℝ) : ℂ)) y‖ ^ 2 ≤ (∑ i : ι₀, Cj i) ^ 2 := by
          intro y
          have h2 : Work.Diff.STE.pdVec 0 β (fun y => ((Work.Diff.STE.B3.tmA (φin j) (min c₀ 1)
              γ y c d : ℝ) : ℂ)) y
              = ((Work.Diff.STE.B3.tmA (φin j) (min c₀ 1) γ y c d : ℝ) : ℂ) := by
            simp [Work.Diff.STE.pdVec, Work.Diff.STE.pdList]
          rw [h2, Complex.norm_real, Real.norm_eq_abs]
          simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg _)
            (le_trans (hprops.1 y c d)
              (Finset.single_le_sum (fun i _ => hCj0 i) (Finset.mem_univ j))) 2
        calc ∫ y in Work.Diff.STE.unitCube,
              ‖Work.Diff.STE.pdVec 0 β (fun y => ((Work.Diff.STE.B3.tmA (φin j) (min c₀ 1) γ y c d
                : ℝ) : ℂ)) y‖ ^ 2
            ≤ ∫ y in Work.Diff.STE.unitCube, (∑ i : ι₀, Cj i) ^ 2 :=
              MeasureTheory.integral_mono_of_nonneg (Filter.Eventually.of_forall fun y => by positivity)
                (MeasureTheory.integrable_const _) (Filter.Eventually.of_forall hpt)
          _ = (∑ i : ι₀, Cj i) ^ 2 := by
              rw [MeasureTheory.integral_const, hvol, one_smul]
          _ ≤ CA * (1 + D.ENormB 0 h) := by
              have h1 : (∑ i : ι₀, Cj i) ^ 2 ≤ CA := by
                have h2 : (0 : ℝ) ≤ ∑ i : ι₀, Cj i := Finset.sum_nonneg (fun i _ => hCj0 i)
                rw [hCAdef]
                nlinarith [h2, hKφin0, hKφout0, hKφmid0]
              have h2 : 0 ≤ D.ENormB 0 h := Work.Diff.STE.Lead.GalTame.ENormB_nonneg_gal D 0 h
              nlinarith [h1, h2, hCA0]
      · -- `m ≥ 1`
        have hE0 : 0 ≤ D.ENormB m h := Work.Diff.STE.Lead.GalTame.ENormB_nonneg_gal D m h
        -- ===== (0) the level index of `m` =====
        obtain ⟨ℓm, hℓm⟩ : ∃ ℓ : Fin k, ℓ.1 + 1 = m :=
          ⟨⟨m - 1, by omega⟩, by simp only [Fin.val_mk]; omega⟩
        -- ===== (1) the globalised matrix field `Gt = 1 + φout·(Gf - 1)` and its inverse `Ht` =====
        set Gt : (Fin (Module.finrank ℝ E) → ℝ) → Fin (Module.finrank ℝ E) →
            Fin (Module.finrank ℝ E) → ℝ := fun z p q => (if p = q then (1 : ℝ) else 0)
              + φout j z * (Work.Diff.STE.B3.Gf (I := I) (M := M) D h j z p q
                - (if p = q then (1 : ℝ) else 0)) with hGtdef
        set Ht : (Fin (Module.finrank ℝ E) → ℝ) → Fin (Module.finrank ℝ E) →
            Fin (Module.finrank ℝ E) → ℝ := fun z p q => (Matrix.of (Gt z))⁻¹ p q with hHtdef
        -- symmetry of the chart matrix
        have hGf_symm : ∀ z p q,
            Work.Diff.STE.B3.Gf (I := I) (M := M) D h j z p q
              = Work.Diff.STE.B3.Gf (I := I) (M := M) D h j z q p := by
          intro z p q
          have h1 := Work.Diff.STE.B3.tmw_Gf_transpose (I := I) (M := M) D h hsym j z
          have h2 := congrFun (congrFun h1 p) q
          simpa [Matrix.transpose_apply] using h2.symm
        -- the affine form of `Gt`
        have hGt_entry : ∀ z p q, Gt z p q
            = (1 - φout j z) * (if p = q then (1 : ℝ) else 0)
              + φout j z * Work.Diff.STE.B3.Gf (I := I) (M := M) D h j z p q := by
          intro z p q
          rw [hGtdef]
          ring
        have hGt_sym : ∀ z p q, Gt z p q = Gt z q p := by
          intro z p q
          rw [hGt_entry z p q, hGt_entry z q p, hGf_symm z p q]
          by_cases hpq : p = q
          · rw [if_pos hpq, if_pos hpq.symm]
          · rw [if_neg hpq, if_neg (fun h => hpq h.symm)]
        -- `φout` vanishes outside the window
        have hφout_zero : ∀ z : Fin (Module.finrank ℝ E) → ℝ,
            ¬ (‖z‖ ≤ 2 * D.σ j + 5 * δ) → φout j z = 0 := by
          intro z hz
          by_contra hz'
          have h1 : z ∈ tsupport (φout j) := subset_tsupport _ (Function.mem_support.mpr hz')
          have h2 : z ∈ Metric.ball (0 : Fin (Module.finrank ℝ E) → ℝ) (2 * D.σ j + 5 * δ) :=
            subset_trans (hφout_ts j) (Metric.ball_subset_ball (by linarith [hδpos])) h1
          rw [Metric.mem_ball, dist_zero_right] at h2
          exact hz (le_of_lt h2)
        -- the quadratic form of `Gt`
        have hGt_qf : ∀ (z : Fin (Module.finrank ℝ E) → ℝ)
            (ξ : Fin (Module.finrank ℝ E) → ℝ),
            (min 1 mlo) * ∑ i, (ξ i) ^ 2 ≤ ∑ p, ∑ q, Gt z p q * ξ p * ξ q ∧
            (∑ p, ∑ q, Gt z p q * ξ p * ξ q) ≤ (max 1 Mhi) * ∑ i, (ξ i) ^ 2 := by
          intro z ξ
          have hS : 0 ≤ ∑ i : Fin (Module.finrank ℝ E), (ξ i) ^ 2 :=
            Finset.sum_nonneg (fun i _ => sq_nonneg _)
          have hGsum : (∑ p, ∑ q, Gt z p q * ξ p * ξ q)
              = (1 - φout j z) * (∑ p, (ξ p) ^ 2)
                + φout j z * (∑ p, ∑ q,
                    Work.Diff.STE.B3.Gf (I := I) (M := M) D h j z p q * ξ p * ξ q) := by
            have hentry : ∀ p q, Gt z p q
                = (1 - φout j z) * (if p = q then (1 : ℝ) else 0)
                  + φout j z * Work.Diff.STE.B3.Gf (I := I) (M := M) D h j z p q :=
              hGt_entry z
            calc (∑ p, ∑ q, Gt z p q * ξ p * ξ q)
                = (∑ p, ∑ q, ((1 - φout j z) * (if p = q then (1 : ℝ) else 0)
                    + φout j z * Work.Diff.STE.B3.Gf (I := I) (M := M) D h j z p q)
                    * ξ p * ξ q) := by
                  refine Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun q _ => ?_))
                  rw [hentry p q]
              _ = _ := quadForm_affine (1 - φout j z) (φout j z)
                  (fun a b => Work.Diff.STE.B3.Gf (I := I) (M := M) D h j z a b) ξ
          by_cases hz : ‖z‖ ≤ 2 * D.σ j + 5 * δ
          · have h1 : mlo * (∑ i, (ξ i) ^ 2) ≤ (∑ p, ∑ q,
                Work.Diff.STE.B3.Gf (I := I) (M := M) D h j z p q * ξ p * ξ q) :=
              (hwin z hz).1 ξ
            have h2 : (∑ p, ∑ q,
                Work.Diff.STE.B3.Gf (I := I) (M := M) D h j z p q * ξ p * ξ q)
                ≤ Mhi * (∑ i, (ξ i) ^ 2) := (hwin z hz).2.1 ξ
            have h3 : 0 ≤ φout j z := hφout_0 j z
            have h4 : φout j z ≤ 1 := hφout_1 j z
            constructor
            · rw [hGsum]
              have h7 : ((1 - φout j z) + φout j z * mlo) * (∑ i, (ξ i) ^ 2)
                  ≤ (1 - φout j z) * (∑ p, (ξ p) ^ 2)
                    + φout j z * (∑ p, ∑ q,
                        Work.Diff.STE.B3.Gf (I := I) (M := M) D h j z p q * ξ p * ξ q) := by
                have h9 : φout j z * (mlo * (∑ i, (ξ i) ^ 2)) ≤ φout j z * (∑ p, ∑ q,
                    Work.Diff.STE.B3.Gf (I := I) (M := M) D h j z p q * ξ p * ξ q) :=
                  mul_le_mul_of_nonneg_left h1 h3
                linarith [h9]
              calc (min 1 mlo) * ∑ i, (ξ i) ^ 2
                  ≤ ((1 - φout j z) + φout j z * mlo) * ∑ i, (ξ i) ^ 2 :=
                    mul_le_mul_of_nonneg_right
                      (by nlinarith [min_le_left (1 : ℝ) mlo, min_le_right (1 : ℝ) mlo, h3, h4]) hS
                _ ≤ _ := h7
            · rw [hGsum]
              have h7 : (1 - φout j z) * (∑ p, (ξ p) ^ 2)
                    + φout j z * (∑ p, ∑ q,
                        Work.Diff.STE.B3.Gf (I := I) (M := M) D h j z p q * ξ p * ξ q)
                  ≤ ((1 - φout j z) + φout j z * Mhi) * (∑ i, (ξ i) ^ 2) := by
                have h9 : φout j z * (∑ p, ∑ q,
                    Work.Diff.STE.B3.Gf (I := I) (M := M) D h j z p q * ξ p * ξ q)
                    ≤ φout j z * (Mhi * (∑ i, (ξ i) ^ 2)) :=
                  mul_le_mul_of_nonneg_left h2 h3
                linarith [h9]
              calc _ ≤ ((1 - φout j z) + φout j z * Mhi) * ∑ i, (ξ i) ^ 2 := h7
                _ ≤ (max 1 Mhi) * ∑ i, (ξ i) ^ 2 :=
                    mul_le_mul_of_nonneg_right
                      (by nlinarith [le_max_left (1 : ℝ) Mhi, le_max_right (1 : ℝ) Mhi, h3, h4]) hS
          · have hz0 : φout j z = 0 := hφout_zero z hz
            have hq : (∑ p, ∑ q, Gt z p q * ξ p * ξ q) = ∑ p, (ξ p) ^ 2 := by
              rw [hGsum, hz0]
              simp only [zero_mul, add_zero, sub_zero, one_mul, Finset.sum_ite_eq',
                Finset.mem_univ, if_true]
            constructor
            · rw [hq]
              exact le_trans (mul_le_mul_of_nonneg_right (min_le_left (1 : ℝ) mlo) hS)
                (le_of_eq (one_mul _))
            · rw [hq]
              exact le_mul_of_one_le_left hS (le_max_left (1 : ℝ) Mhi)
        have hGt_lo : ∀ (z : Fin (Module.finrank ℝ E) → ℝ)
            (ξ : Fin (Module.finrank ℝ E) → ℝ),
            (min 1 mlo) * ∑ i, (ξ i) ^ 2 ≤ ∑ p, ∑ q, Gt z p q * ξ p * ξ q :=
          fun z ξ => (hGt_qf z ξ).1
        have hGt_hi : ∀ (z : Fin (Module.finrank ℝ E) → ℝ)
            (ξ : Fin (Module.finrank ℝ E) → ℝ),
            (∑ p, ∑ q, Gt z p q * ξ p * ξ q) ≤ (max 1 Mhi) * ∑ i, (ξ i) ^ 2 :=
          fun z ξ => (hGt_qf z ξ).2
        obtain ⟨hGt_unit, hHt_entry_b, hGtHt, hHt_qf⟩ := hMInv Gt hGt_sym hGt_lo hGt_hi
        -- ===== (2) smoothness =====
        have hGf_smon : ∀ p q, ContDiffOn ℝ (⊤ : ℕ∞)
            (fun z => Work.Diff.STE.B3.Gf (I := I) (M := M) D h j z p q)
            (Metric.ball (0 : Fin (Module.finrank ℝ E) → ℝ) (2 * D.σ j + 5 * δ)) := by
          intro p q
          refine (Work.Diff.STE.Lead.Gal.Gf_contDiffOn_target (I := I) (M := M) D h hsmooth j p q).mono ?_
          intro z hz
          refine htgt0 j z ?_
          rw [Metric.mem_ball, dist_zero_right] at hz
          linarith [hz, hδδt, hδpos]
        have hGt_sm : ∀ p q, ContDiff ℝ (⊤ : ℕ∞) (fun z => Gt z p q) := by
          intro p q
          have h1 : ContDiff ℝ (⊤ : ℕ∞) (fun z => (if p = q then (1 : ℝ) else 0)
              + φout j z * (Work.Diff.STE.B3.Gf (I := I) (M := M) D h j z p q
                - (if p = q then (1 : ℝ) else 0))) := by
            refine contDiff_const.add ?_
            have h2 : ContDiffOn ℝ (⊤ : ℕ∞) (fun z =>
                Work.Diff.STE.B3.Gf (I := I) (M := M) D h j z p q
                  - (if p = q then (1 : ℝ) else 0))
                (Metric.ball (0 : Fin (Module.finrank ℝ E) → ℝ) (2 * D.σ j + 5 * δ)) :=
              (hGf_smon p q).sub contDiff_const.contDiffOn
            exact contDiff_mul_of_contDiffOn_of_tsupport (hφout_sm j) Metric.isOpen_ball
              h2 (subset_trans (hφout_ts j) (Metric.ball_subset_ball (by linarith [hδpos])))
          simpa only [hGtdef] using h1
        have hHt_sm : ∀ p q, ContDiff ℝ (⊤ : ℕ∞) (fun z => Ht z p q) := by
          intro p q
          have h1 : ContDiff ℝ (⊤ : ℕ∞)
              (fun z : Fin (Module.finrank ℝ E) → ℝ =>
                fun a b : Fin (Module.finrank ℝ E) => Gt z a b) := by
            rw [contDiff_pi]
            intro a
            rw [contDiff_pi]
            exact hGt_sm a
          have h2 : ContDiffOn ℝ (⊤ : ℕ∞)
              (fun B : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ =>
                ((Matrix.of B)⁻¹) p q) {B | (Matrix.of B).det ≠ 0} :=
            Work.Diff.STE.Man.contDiffOn_matrixInv_entry p q
          have h3 : ContDiffOn ℝ (⊤ : ℕ∞)
              ((fun B : Fin (Module.finrank ℝ E) → Fin (Module.finrank ℝ E) → ℝ =>
                  ((Matrix.of B)⁻¹) p q) ∘
                (fun z : Fin (Module.finrank ℝ E) → ℝ =>
                  fun a b : Fin (Module.finrank ℝ E) => Gt z a b)) Set.univ :=
            h2.comp (h1.contDiffOn (s := Set.univ)) (by
              intro z _
              exact isUnit_iff_ne_zero.mp (hGt_unit z))
          exact contDiffOn_univ.mp h3
        -- ===== (3) supports and sup bounds =====
        have hφout_supp : ∀ {z : Fin (Module.finrank ℝ E) → ℝ}, z ∈ tsupport (φout j) →
            ‖z‖ < 2 * D.σ j + 2 * δ := by
          intro z hz
          have h1 := hφout_ts j hz
          rwa [Metric.mem_ball, dist_zero_right] at h1
        have hφin_supp : ∀ {z : Fin (Module.finrank ℝ E) → ℝ}, z ∈ tsupport (φin j) →
            ‖z‖ < 2 * D.σ j + δ := by
          intro z hz
          have h1 := hφin_ts j hz
          rwa [Metric.mem_ball, dist_zero_right] at h1
        have hφmid_supp : ∀ {z : Fin (Module.finrank ℝ E) → ℝ}, z ∈ tsupport (φmid j) →
            ‖z‖ < 2 * D.σ j + 3 * δ := by
          intro z hz
          have h1 := hφmid_ts j hz
          rwa [Metric.mem_ball, dist_zero_right] at h1
        have hGt_supp : ∀ p q, Function.support
            (fun z => Gt z p q - (if p = q then (1 : ℝ) else 0)) ⊆ Metric.ball 0 (1 / 2) := by
          intro p q
          refine subset_trans ?_ (Metric.ball_subset_ball (by linarith [hδ16, D.hσ2 j]))
          intro z hz
          have hz' : φout j z * (Work.Diff.STE.B3.Gf (I := I) (M := M) D h j z p q
              - (if p = q then (1 : ℝ) else 0)) ≠ 0 := by
            intro h0
            exact hz (by simp only [hGtdef, h0, add_zero, sub_self])
          have h1 : φout j z ≠ 0 := fun h => hz' (by rw [h]; ring)
          rw [Metric.mem_ball, dist_zero_right]
          exact lt_of_lt_of_le
            (hφout_supp (subset_tsupport (φout j) (Function.mem_support.mpr h1)))
            (by linarith [hδ16, D.hσ2 j])
        have hHt_supp : ∀ p q, Function.support
            (fun z => Ht z p q - (if p = q then (1 : ℝ) else 0)) ⊆ Metric.ball 0 (1 / 2) := by
          intro p q
          refine subset_trans ?_ (Metric.ball_subset_ball (by linarith [hδ16, D.hσ2 j]))
          intro z hz
          have hz0 : φout j z ≠ 0 := by
            intro h0
            refine hz ?_
            have h1 : ∀ a b, Gt z a b = (if a = b then (1 : ℝ) else 0) := by
              intro a b
              rw [hGt_entry z a b, h0]
              simp
            have h2 : Matrix.of (Gt z) = 1 := by
              ext a b
              simpa only [Matrix.of_apply, Matrix.one_apply] using h1 a b
            have h3 := hGtHt z
            rw [h2, Matrix.one_mul] at h3
            have h4 := congrFun (congrFun h3 p) q
            simp only [hHtdef]
            rw [h2, h4, Matrix.one_apply]
            split <;> ring
          rw [Metric.mem_ball, dist_zero_right]
          exact lt_of_lt_of_le
            (hφout_supp (subset_tsupport (φout j) (Function.mem_support.mpr hz0)))
            (by linarith [hδ16, D.hσ2 j])
        have hGt_b : ∀ z p q, ‖Gt z p q‖ ≤ U := by
          intro z p q
          rw [Real.norm_eq_abs]
          by_cases hz : ‖z‖ ≤ 2 * D.σ j + 5 * δ
          · have h3 : 0 ≤ φout j z := hφout_0 j z
            have h4 : φout j z ≤ 1 := hφout_1 j z
            have hd : |(if p = q then (1 : ℝ) else 0)| ≤ 1 := by split <;> norm_num
            have hg : |Work.Diff.STE.B3.Gf (I := I) (M := M) D h j z p q|
                ≤ 2 * K * (Mhi / lam) := by
              refine Work.Diff.STE.Lead.Gal.Gf_entry_bound (I := I) (M := M) D h hsym hlam
                (le_of_lt hK) hell hub j z ?_ p q
              intro ξ
              rw [Work.Diff.STE.Lead.Gal.G0f_quadForm]
              have h1 : lam * g₀.inner (D.pt j z)
                  (∑ a, ξ a • Work.Diff.STE.B3.cFrameAt (I := I) (M := M) D j z a)
                  (∑ b, ξ b • Work.Diff.STE.B3.cFrameAt (I := I) (M := M) D j z b)
                  ≤ h (D.pt j z) (∑ a, ξ a • Work.Diff.STE.B3.cFrameAt (I := I) (M := M) D j z a)
                      (∑ b, ξ b • Work.Diff.STE.B3.cFrameAt (I := I) (M := M) D j z b) :=
                hell (D.pt j z) _
              rw [← Work.Diff.STE.Lead.Gal.Gf_quadForm (I := I) (M := M) D h j z ξ] at h1
              have h2 := (hwin z hz).2.1 ξ
              have hS2 : 0 ≤ ∑ i : Fin (Module.finrank ℝ E), (ξ i) ^ 2 :=
                Finset.sum_nonneg (fun i _ => sq_nonneg _)
              rw [div_mul_eq_mul_div, le_div_iff₀ hlam]
              calc g₀.inner (D.pt j z)
                    (∑ a, ξ a • Work.Diff.STE.B3.cFrameAt (I := I) (M := M) D j z a)
                    (∑ b, ξ b • Work.Diff.STE.B3.cFrameAt (I := I) (M := M) D j z b) * lam
                  = lam * g₀.inner (D.pt j z)
                    (∑ a, ξ a • Work.Diff.STE.B3.cFrameAt (I := I) (M := M) D j z a)
                    (∑ b, ξ b • Work.Diff.STE.B3.cFrameAt (I := I) (M := M) D j z b) := by ring
                _ ≤ Mhi * (∑ i, (ξ i) ^ 2) := le_trans h1 h2
            calc |Gt z p q| = |(1 - φout j z) * (if p = q then (1 : ℝ) else 0)
                    + φout j z * Work.Diff.STE.B3.Gf (I := I) (M := M) D h j z p q| := by
                  rw [hGt_entry]
              _ ≤ |(1 - φout j z) * (if p = q then (1 : ℝ) else 0)|
                    + |φout j z * Work.Diff.STE.B3.Gf (I := I) (M := M) D h j z p q| :=
                  abs_add_le _ _
              _ = |1 - φout j z| * |(if p = q then (1 : ℝ) else 0)|
                    + |φout j z| * |Work.Diff.STE.B3.Gf (I := I) (M := M) D h j z p q| := by
                  rw [abs_mul, abs_mul]
              _ ≤ (1 - φout j z) * 1 + φout j z * (2 * K * (Mhi / lam)) := by
                  have h5 : |1 - φout j z| = 1 - φout j z := abs_of_nonneg (by linarith)
                  have h6 : |φout j z| = φout j z := abs_of_nonneg h3
                  rw [h5, h6]
                  exact add_le_add (mul_le_mul_of_nonneg_left hd (by linarith))
                    (mul_le_mul_of_nonneg_left hg h3)
              _ ≤ U := by
                  rw [hUdef]
                  have hX0 : (0 : ℝ) ≤ 2 * K * (Mhi / lam) :=
                    mul_nonneg (by linarith [hK]) (div_nonneg (le_of_lt hMhi) (le_of_lt hlam))
                  have h5 : φout j z * (2 * K * (Mhi / lam)) ≤ 2 * K * (Mhi / lam) :=
                    mul_le_of_le_one_left hX0 h4
                  linarith
          · have hz0 : φout j z = 0 := hφout_zero z hz
            have hd : |(if p = q then (1 : ℝ) else 0)| ≤ 1 := by split <;> norm_num
            calc |Gt z p q| = |(if p = q then (1 : ℝ) else 0)| := by
                  rw [hGt_entry, hz0]; simp
              _ ≤ 1 := hd
              _ ≤ U := by
                  rw [hUdef]
                  have hX0 : (0 : ℝ) ≤ 2 * K * (Mhi / lam) :=
                    mul_nonneg (by linarith [hK]) (div_nonneg (le_of_lt hMhi) (le_of_lt hlam))
                  linarith
        have hHt_b : ∀ z p q, ‖Ht z p q‖ ≤ Wg := by
          intro z p q
          rw [Real.norm_eq_abs, hHtdef]
          exact hHt_entry_b z p q
        have hGH : ∀ z, Matrix.of (Gt z) * Matrix.of (Ht z) = 1 := by
          intro z
          rw [hHtdef]
          exact hGtHt z
        -- ===== (4) agreement with `γ` on the `2σ+δ`-ball =====
        have hGt_eq : ∀ z, ‖z‖ ≤ 2 * D.σ j + δ → ∀ p q, Gt z p q
            = Work.Diff.STE.B3.Gf (I := I) (M := M) D h j z p q := by
          intro z hz p q
          rw [hGt_entry z p q, hφout_eq1 j z hz]
          ring
        have hHt_eq : ∀ z, ‖z‖ ≤ 2 * D.σ j + δ → ∀ p q, Ht z p q = γ z p q := by
          intro z hz p q
          have h1 : Matrix.of (Gt z)
              = Matrix.of (Work.Diff.STE.B3.Gf (I := I) (M := M) D h j z) := by
            ext a b
            rw [Matrix.of_apply, Matrix.of_apply]
            exact hGt_eq z hz a b
          have h2 : (Matrix.of (Gt z))⁻¹
              = (Matrix.of (Work.Diff.STE.B3.Gf (I := I) (M := M) D h j z))⁻¹ :=
            congrArg (fun M => M⁻¹) h1
          have h3 := congrFun (congrFun h2 p) q
          rw [hHtdef, hγdef]
          simpa only [Matrix.of_apply] using h3
        -- ===== (5) the reduction =====
        have htmA_eq : (fun y => ((Work.Diff.STE.B3.tmA (φin j) (min c₀ 1) γ y c d : ℝ) : ℂ))
            = (fun y => ((Work.Diff.STE.B3.tmA (φin j) (min c₀ 1) Ht y c d : ℝ) : ℂ)) := by
          funext y
          rw [Work.Diff.STE.B3.tmA, Work.Diff.STE.B3.tmA]
          simp only [Complex.ofReal_add]
          congr 1
          congr 1
          refine congrArg (fun u => Work.Diff.STE.B3.tmPer u y) ?_
          funext w
          by_cases hw : φin j w = 0
          · rw [hw]; ring
          · rw [hHt_eq w (le_of_lt (hφin_supp (subset_tsupport (φin j) (Function.mem_support.mpr hw))))]
        -- the uniform `pdRVec` bounds of `φin`
        have hφin_pdRvec : ∀ (r : ℕ), r ≤ m → ∀ (γ' : Fin r → Fin (Module.finrank ℝ E))
            (z : Fin (Module.finrank ℝ E) → ℝ),
            |Work.Diff.STE.pdRVec r γ' (φin j) z| ≤ Kφin := fun r hr γ' z =>
          (hKφin j).2 r (by omega) γ' z
        -- the uniform comparison of the energy levels: `1 + ENormB i h ≤ KmonE (1 + ENormB m h)`
        have hmonE : ∀ (i : ℕ), i ≤ m →
            1 + D.ENormB i h ≤ KmonE * (1 + D.ENormB m h) := by
          intro i hi
          have hEm0 : 0 ≤ D.ENormB m h := hE0
          have hE1 : (0 : ℝ) ≤ 1 + D.ENormB m h := by linarith
          have hkey : ∀ (C x : ℝ), 0 ≤ C → x ≤ C * D.ENormB m h →
              1 + x ≤ (1 + C) * (1 + D.ENormB m h) := by
            intro C x hC hx
            have h2 : 1 + C * D.ENormB m h ≤ (1 + C) * (1 + D.ENormB m h) := by
              nlinarith only [hC, hEm0]
            linarith only [h2, hx]
          rcases Nat.eq_zero_or_pos i with h0 | hpos
          · subst h0
            have h1 : D.ENormB 0 h ≤ Cstep * D.ENormB 1 h := hCstepb h hsmooth
            have h2 : D.ENormB 1 h ≤ Cmon ⟨m, by omega⟩ * D.ENormB m h :=
              hCmonb ⟨m, by omega⟩ h hsmooth 1 le_rfl hmpos
            have h5 : Cmon ⟨m, by omega⟩ ≤ Cmonmax := by
              have h6 : Cmon ⟨m, by omega⟩ + 1 ≤ Cmonmax := by
                rw [hCmonmaxdef]
                exact Finset.single_le_sum (f := fun mm : Fin (k + 1) => Cmon mm + 1)
                  (fun mm _ => by linarith [hCmon0 mm]) (Finset.mem_univ _)
              linarith
            have h3 : D.ENormB 0 h ≤ Cstep * Cmonmax * D.ENormB m h := by
              have h4 : Cstep * (Cmon ⟨m, by omega⟩ * D.ENormB m h)
                  ≤ Cstep * Cmonmax * D.ENormB m h := by
                have h7 : Cstep * Cmon ⟨m, by omega⟩ ≤ Cstep * Cmonmax :=
                  mul_le_mul_of_nonneg_left h5 hCstep0
                calc Cstep * (Cmon ⟨m, by omega⟩ * D.ENormB m h)
                    = (Cstep * Cmon ⟨m, by omega⟩) * D.ENormB m h := by ring
                  _ ≤ (Cstep * Cmonmax) * D.ENormB m h :=
                      mul_le_mul_of_nonneg_right h7 hEm0
                  _ = Cstep * Cmonmax * D.ENormB m h := by ring
              exact le_trans h1 (le_trans (mul_le_mul_of_nonneg_left h2 hCstep0) h4)
            have h8 : 1 + D.ENormB 0 h ≤ (1 + Cstep * Cmonmax) * (1 + D.ENormB m h) :=
              hkey _ _ (mul_nonneg hCstep0 hCmonmax0) h3
            refine le_trans h8 (mul_le_mul_of_nonneg_right ?_ hE1)
            rw [← hKzerodef]; exact hKzero_le
          · have h2 : D.ENormB i h ≤ Cmon ⟨m, by omega⟩ * D.ENormB m h :=
              hCmonb ⟨m, by omega⟩ h hsmooth i hpos hi
            have h5 : Cmon ⟨m, by omega⟩ ≤ Cmonmax := by
              have h6 : Cmon ⟨m, by omega⟩ + 1 ≤ Cmonmax := by
                rw [hCmonmaxdef]
                exact Finset.single_le_sum (f := fun mm : Fin (k + 1) => Cmon mm + 1)
                  (fun mm _ => by linarith [hCmon0 mm]) (Finset.mem_univ _)
              linarith
            have h3 : D.ENormB i h ≤ Cmonmax * D.ENormB m h :=
              le_trans h2 (mul_le_mul_of_nonneg_right h5 hEm0)
            have h8 : 1 + D.ENormB i h ≤ (1 + Cmonmax) * (1 + D.ENormB m h) :=
              hkey _ _ hCmonmax0 h3
            refine le_trans h8 (mul_le_mul_of_nonneg_right ?_ hE1)
            rw [hKmonEdef]; linarith [hKzero0]
        -- the `G`-side bound, level by level
        have hGside : ∀ (j' : ℕ) (hj' : 1 ≤ j') (hjk : j' ≤ m)
            (p q : Fin (Module.finrank ℝ E)) (γ' : Fin j' → Fin (Module.finrank ℝ E)),
            ∫ z : Fin (Module.finrank ℝ E) → ℝ,
              ‖Work.Diff.STE.pdVec j' γ'
                (fun y : Fin (Module.finrank ℝ E) → ℝ => ((Gt y p q : ℝ) : ℂ)) z‖ ^ 2
            ≤ Cg * (1 + D.ENormB m h) := by
          intro j' hj' hjk p q γ'
          -- (i) the identity part is killed by the derivative
          have hGt_fun : (fun y : Fin (Module.finrank ℝ E) → ℝ => ((Gt y p q : ℝ) : ℂ))
              = (fun y : Fin (Module.finrank ℝ E) → ℝ =>
                  (((if p = q then (1 : ℝ) else 0) : ℂ))
                    + ((φout j y * (Work.Diff.STE.B3.Gf (I := I) (M := M) D h j y p q
                        - (if p = q then (1 : ℝ) else 0)) : ℝ) : ℂ)) := by
            funext y
            rw [hGt_entry y p q]
            by_cases hpq : p = q <;>
              simp only [hpq, if_true, if_false, Complex.ofReal_one, Complex.ofReal_zero,
                Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_sub] <;> ring
          rw [hGt_fun, Kit.pdVec_const_add hj' γ']
          -- (ii) replace the localised product by a globally smooth one
          have hEqFun : (fun y : Fin (Module.finrank ℝ E) → ℝ =>
                ((φout j y * (Work.Diff.STE.B3.Gf (I := I) (M := M) D h j y p q
                  - (if p = q then (1 : ℝ) else 0)) : ℝ) : ℂ))
              = (fun y : Fin (Module.finrank ℝ E) → ℝ => ((φout j y : ℝ) : ℂ)
                  * ((φmid j y * Work.Diff.STE.B3.Gf (I := I) (M := M) D h j y p q
                      - φmid j y * (if p = q then (1 : ℝ) else 0) : ℝ) : ℂ)) := by
            funext y
            by_cases hy : φout j y = 0
            · rw [hy]; simp
            · have hy' : φmid j y = 1 :=
                hφmid_eq1 j y (le_of_lt (hφout_supp (subset_tsupport _ (Function.mem_support.mpr hy))))
              rw [hy']
              push_cast
              ring
          rw [hEqFun]
          -- (iii) the globally smooth localised matrix entry
          have hF1sm : ContDiff ℝ (⊤ : ℕ∞) (fun y : Fin (Module.finrank ℝ E) → ℝ =>
              ((φmid j y * Work.Diff.STE.B3.Gf (I := I) (M := M) D h j y p q
                - φmid j y * (if p = q then (1 : ℝ) else 0) : ℝ) : ℂ)) := by
            have h2 : ContDiffOn ℝ (⊤ : ℕ∞) (fun z => Work.Diff.STE.B3.Gf (I := I) (M := M)
                D h j z p q - (if p = q then (1 : ℝ) else 0))
                (Metric.ball (0 : Fin (Module.finrank ℝ E) → ℝ) (2 * D.σ j + 5 * δ)) :=
              (hGf_smon p q).sub contDiff_const.contDiffOn
            have h2ts : tsupport (φmid j) ⊆
                Metric.ball (0 : Fin (Module.finrank ℝ E) → ℝ) (2 * D.σ j + 5 * δ) :=
              subset_trans (hφmid_ts j) (Metric.ball_subset_ball (by linarith [hδpos]))
            have h3 : ContDiff ℝ (⊤ : ℕ∞) (fun z => φmid j z *
                Work.Diff.STE.B3.Gf (I := I) (M := M) D h j z p q
                  - φmid j z * (if p = q then (1 : ℝ) else 0)) :=
              (contDiff_mul_of_contDiffOn_of_tsupport (hφmid_sm j) Metric.isOpen_ball
                (hGf_smon p q) h2ts).sub ((hφmid_sm j).mul contDiff_const)
            exact Complex.ofRealCLM.contDiff.comp h3
          -- (iv) the support of the product
          have hF1supp : Function.support (fun y : Fin (Module.finrank ℝ E) → ℝ =>
              ((φout j y : ℝ) : ℂ) * ((φmid j y * Work.Diff.STE.B3.Gf (I := I) (M := M) D h j y p q
                  - φmid j y * (if p = q then (1 : ℝ) else 0) : ℝ) : ℂ))
              ⊆ Metric.ball (0 : Fin (Module.finrank ℝ E) → ℝ) (2 * D.σ j + 2 * δ) := by
            intro y hy
            have hy' : φout j y ≠ 0 := fun h0 => hy (by simp only [h0, Complex.ofReal_zero, zero_mul])
            rw [Metric.mem_ball, dist_zero_right]
            exact hφout_supp (subset_tsupport (φout j) (Function.mem_support.mpr hy'))
          have hF1suppR : Function.support (fun y : Fin (Module.finrank ℝ E) → ℝ =>
              φmid j y * Work.Diff.STE.B3.Gf (I := I) (M := M) D h j y p q
                - φmid j y * (if p = q then (1 : ℝ) else 0))
              ⊆ Metric.ball (0 : Fin (Module.finrank ℝ E) → ℝ) (2 * D.σ j + 3 * δ) := by
            intro y hy
            have h1 : φmid j y ≠ 0 := fun h0 => hy (by simp [h0])
            rw [Metric.mem_ball, dist_zero_right]
            exact lt_of_lt_of_le
              (hφmid_supp (subset_tsupport (φmid j) (Function.mem_support.mpr h1)))
              (le_of_eq rfl)
          -- (v) the Leibniz estimate, at the radius `2σ_j + 3δ`
          have hlei := hCleib ⟨j', by omega⟩ (φout j)
            (fun y : Fin (Module.finrank ℝ E) → ℝ =>
              ((φmid j y * Work.Diff.STE.B3.Gf (I := I) (M := M) D h j y p q
                - φmid j y * (if p = q then (1 : ℝ) else 0) : ℝ) : ℂ))
            Kφout (2 * D.σ j + 3 * δ) (hφout_sm j) hF1sm
            (fun r hr γ'' z => (hKφout j).2 r (by omega) γ'' z)
            (subset_trans hF1supp (Metric.ball_subset_ball (by linarith [hδpos])))
            (by linarith [hδ16, D.hσ2 j]) γ'
          -- (vi) the whole-space integral is the integral over the closed ball
          have hclosed_eq : ∫ z : Fin (Module.finrank ℝ E) → ℝ,
                ‖Work.Diff.STE.pdVec j' γ' (fun y : Fin (Module.finrank ℝ E) → ℝ =>
                  ((φout j y : ℝ) : ℂ) * ((φmid j y * Work.Diff.STE.B3.Gf (I := I) (M := M) D h j y p q
                      - φmid j y * (if p = q then (1 : ℝ) else 0) : ℝ) : ℂ)) z‖ ^ 2
              = ∫ z in Metric.closedBall (0 : Fin (Module.finrank ℝ E) → ℝ) (2 * D.σ j + 2 * δ),
                ‖Work.Diff.STE.pdVec j' γ' (fun y : Fin (Module.finrank ℝ E) → ℝ =>
                  ((φout j y : ℝ) : ℂ) * ((φmid j y * Work.Diff.STE.B3.Gf (I := I) (M := M) D h j y p q
                      - φmid j y * (if p = q then (1 : ℝ) else 0) : ℝ) : ℂ)) z‖ ^ 2 := by
            refine (MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hz => ?_)).symm
            have h1 : tsupport (Work.Diff.STE.pdVec j' γ' (fun y : Fin (Module.finrank ℝ E) → ℝ =>
                ((φout j y : ℝ) : ℂ) * ((φmid j y * Work.Diff.STE.B3.Gf (I := I) (M := M) D h j y p q
                    - φmid j y * (if p = q then (1 : ℝ) else 0) : ℝ) : ℂ)))
                ⊆ Metric.closedBall (0 : Fin (Module.finrank ℝ E) → ℝ) (2 * D.σ j + 2 * δ) :=
              subset_trans (tsupport_pdVec_subset γ')
                (closure_minimal (fun y hy => Metric.ball_subset_closedBall (hF1supp hy))
                  Metric.isClosed_closedBall)
            have h2 : Work.Diff.STE.pdVec j' γ' (fun y : Fin (Module.finrank ℝ E) → ℝ =>
                ((φout j y : ℝ) : ℂ) * ((φmid j y * Work.Diff.STE.B3.Gf (I := I) (M := M) D h j y p q
                    - φmid j y * (if p = q then (1 : ℝ) else 0) : ℝ) : ℂ)) z = 0 := by
              by_contra h3
              exact hz (h1 (subset_tsupport _ (Function.mem_support.mpr h3)))
            rw [h2]; norm_num
          -- (vii) monotonicity in the radius
          have hmono : ∫ z in Metric.closedBall (0 : Fin (Module.finrank ℝ E) → ℝ) (2 * D.σ j + 2 * δ),
                ‖Work.Diff.STE.pdVec j' γ' (fun y : Fin (Module.finrank ℝ E) → ℝ =>
                  ((φout j y : ℝ) : ℂ) * ((φmid j y * Work.Diff.STE.B3.Gf (I := I) (M := M) D h j y p q
                      - φmid j y * (if p = q then (1 : ℝ) else 0) : ℝ) : ℂ)) z‖ ^ 2
              ≤ ∫ z in Metric.ball (0 : Fin (Module.finrank ℝ E) → ℝ) (2 * D.σ j + 3 * δ),
                ‖Work.Diff.STE.pdVec j' γ' (fun y : Fin (Module.finrank ℝ E) → ℝ =>
                  ((φout j y : ℝ) : ℂ) * ((φmid j y * Work.Diff.STE.B3.Gf (I := I) (M := M) D h j y p q
                      - φmid j y * (if p = q then (1 : ℝ) else 0) : ℝ) : ℂ)) z‖ ^ 2 := by
            refine MeasureTheory.setIntegral_mono_set ?_ ?_ ?_
            · have hsmProd : ContDiff ℝ (⊤ : ℕ∞) (fun y : Fin (Module.finrank ℝ E) → ℝ =>
                  ((φout j y : ℝ) : ℂ) * ((φmid j y * Work.Diff.STE.B3.Gf (I := I) (M := M) D h j y p q
                      - φmid j y * (if p = q then (1 : ℝ) else 0) : ℝ) : ℂ)) :=
                (Complex.ofRealCLM.contDiff.comp (hφout_sm j)).mul hF1sm
              have hcsProd : HasCompactSupport (fun y : Fin (Module.finrank ℝ E) → ℝ =>
                  ((φout j y : ℝ) : ℂ) * ((φmid j y * Work.Diff.STE.B3.Gf (I := I) (M := M) D h j y p q
                      - φmid j y * (if p = q then (1 : ℝ) else 0) : ℝ) : ℂ)) :=
                hasCompactSupportC_of_support_subset_ball (R := 2 * D.σ j + 2 * δ) hF1supp
              exact (integrable_normSq_pdVec hsmProd hcsProd γ').integrableOn.mono_set
                (Metric.ball_subset_closedBall)
            · filter_upwards with z using by positivity
            · filter_upwards with z hz using Metric.closedBall_subset_ball (by linarith [hδpos]) hz
          -- ===== (viii) the two pieces of the localised factor =====
          set FA : (Fin (Module.finrank ℝ E) → ℝ) → ℂ := fun y =>
            ((φmid j y * Work.Diff.STE.B3.Gf (I := I) (M := M) D h j y p q : ℝ) : ℂ)
            with hFAdef
          set FB : (Fin (Module.finrank ℝ E) → ℝ) → ℂ := fun y =>
            ((φmid j y * (if p = q then (1 : ℝ) else 0) : ℝ) : ℂ) with hFBdef
          have hA_sm : ContDiff ℝ (⊤ : ℕ∞) FA :=
            Complex.ofRealCLM.contDiff.comp
              (contDiff_mul_of_contDiffOn_of_tsupport (hφmid_sm j) Metric.isOpen_ball
                (hGf_smon p q) (subset_trans (hφmid_ts j)
                  (Metric.ball_subset_ball (by linarith [hδpos]))))
          have hA_cs : HasCompactSupport FA := by
            refine hasCompactSupportC_of_support_subset_ball (R := 2 * D.σ j + 3 * δ) ?_
            intro y hy
            have hy' : φmid j y ≠ 0 := fun h0 => hy (by
              show ((φmid j y * Work.Diff.STE.B3.Gf (I := I) (M := M) D h j y p q : ℝ) : ℂ) = 0
              rw [h0]; simp)
            rw [Metric.mem_ball, dist_zero_right]
            exact hφmid_supp (subset_tsupport (φmid j) (Function.mem_support.mpr hy'))
          have hB_sm : ContDiff ℝ (⊤ : ℕ∞) FB := by
            rw [hFBdef]
            exact Complex.ofRealCLM.contDiff.comp ((hφmid_sm j).mul contDiff_const)
          have hB_cs : HasCompactSupport FB := by
            refine hasCompactSupportC_of_support_subset_ball (R := 2 * D.σ j + 3 * δ) ?_
            intro y hy
            have hy' : φmid j y ≠ 0 := fun h0 => hy (by
              show ((φmid j y * (if p = q then (1 : ℝ) else 0) : ℝ) : ℂ) = 0
              rw [h0]; simp)
            rw [Metric.mem_ball, dist_zero_right]
            exact hφmid_supp (subset_tsupport (φmid j) (Function.mem_support.mpr hy'))
          -- ===== (ix) the per-`(i,γ)` bound for the inner sum =====
          have hT : ∀ (i : ℕ), i ≤ m → ∀ (γ'' : Fin i → Fin (Module.finrank ℝ E)),
              ∫ z in Metric.ball (0 : Fin (Module.finrank ℝ E) → ℝ) (2 * D.σ j + 3 * δ),
                ‖Work.Diff.STE.pdVec i γ'' (fun y : Fin (Module.finrank ℝ E) → ℝ =>
                  ((φmid j y * Work.Diff.STE.B3.Gf (I := I) (M := M) D h j y p q
                    - φmid j y * (if p = q then (1 : ℝ) else 0) : ℝ) : ℂ)) z‖ ^ 2
              ≤ Kt * (1 + D.ENormB m h) := by
            intro i hi γ''
            have hGpart : ∫ z in Metric.ball (0 : Fin (Module.finrank ℝ E) → ℝ)
                  (2 * D.σ j + 3 * δ), ‖Work.Diff.STE.pdVec i γ'' FA z‖ ^ 2
                ≤ Cmatsum * KmonE * (1 + D.ENormB m h) := by
              have hint : MeasureTheory.Integrable (fun z : Fin (Module.finrank ℝ E) → ℝ =>
                  ‖Work.Diff.STE.pdVec i γ'' FA z‖ ^ 2) :=
                integrable_normSq_pdVec hA_sm hA_cs γ''
              have h1 : ∫ z in Metric.ball (0 : Fin (Module.finrank ℝ E) → ℝ)
                    (2 * D.σ j + 3 * δ), ‖Work.Diff.STE.pdVec i γ'' FA z‖ ^ 2
                  ≤ ∫ z : Fin (Module.finrank ℝ E) → ℝ,
                    ‖Work.Diff.STE.pdVec i γ'' FA z‖ ^ 2 :=
                MeasureTheory.setIntegral_le_integral hint
                  (Filter.Eventually.of_forall fun z => by positivity)
              have h2 : ∫ z : Fin (Module.finrank ℝ E) → ℝ,
                    ‖Work.Diff.STE.pdVec i γ'' FA z‖ ^ 2
                  ≤ Cmat ⟨i, by omega⟩ * (1 + D.ENormB i h) := by
                have h3 := hCmatb ⟨i, by omega⟩ h hsym hsmooth hell hub hjet j (φmid j)
                  (hφmid_sm j) (subset_trans (hφmid_ts j)
                    (Metric.ball_subset_ball (by linarith [hδδB])))
                  (fun r hr γ3 z => (hKφmid j).2 r (by omega) γ3 z) p q
                exact le_trans (Finset.single_le_sum
                  (f := fun β : Fin i → Fin (Module.finrank ℝ E) =>
                    ∫ z : Fin (Module.finrank ℝ E) → ℝ,
                      ‖Work.Diff.STE.pdVec i β FA z‖ ^ 2)
                  (s := Finset.univ)
                  (fun β _ => MeasureTheory.integral_nonneg (fun z => by positivity))
                  (Finset.mem_univ γ'')) h3
              have h4 : Cmat ⟨i, by omega⟩ ≤ Cmatsum := by
                have h5 : Cmat ⟨i, by omega⟩ + 1 ≤ Cmatsum := by
                  rw [hCmatsumdef]
                  exact Finset.single_le_sum (f := fun ℓ : Fin (k + 1) => Cmat ℓ + 1)
                    (fun ℓ _ => by linarith [hCmat0 ℓ]) (Finset.mem_univ _)
                linarith
              have h5 : 1 + D.ENormB i h ≤ KmonE * (1 + D.ENormB m h) := hmonE i hi
              calc ∫ z in Metric.ball (0 : Fin (Module.finrank ℝ E) → ℝ)
                    (2 * D.σ j + 3 * δ), ‖Work.Diff.STE.pdVec i γ'' FA z‖ ^ 2
                  ≤ ∫ z : Fin (Module.finrank ℝ E) → ℝ,
                    ‖Work.Diff.STE.pdVec i γ'' FA z‖ ^ 2 := h1
                _ ≤ Cmat ⟨i, by omega⟩ * (1 + D.ENormB i h) := h2
                _ ≤ Cmatsum * (1 + D.ENormB i h) :=
                    mul_le_mul_of_nonneg_right h4
                      (by have := ENormB_nonneg_gal D i h; linarith)
                _ ≤ Cmatsum * (KmonE * (1 + D.ENormB m h)) :=
                    mul_le_mul_of_nonneg_left h5 (by linarith [hCmatsum0])
                _ = Cmatsum * KmonE * (1 + D.ENormB m h) := by ring
            have hBpart : ∫ z in Metric.ball (0 : Fin (Module.finrank ℝ E) → ℝ)
                  (2 * D.σ j + 3 * δ), ‖Work.Diff.STE.pdVec i γ'' FB z‖ ^ 2
                ≤ Kφmid ^ 2 * Vb := by
              by_cases hpq : p = q
              · have hfun : FB = (fun y : Fin (Module.finrank ℝ E) → ℝ => ((φmid j y : ℝ) : ℂ)) := by
                  rw [hFBdef]
                  funext y; rw [if_pos hpq, mul_one]
                rw [hfun]
                have hpt : ∀ z : Fin (Module.finrank ℝ E) → ℝ,
                    ‖Work.Diff.STE.pdVec i γ'' (fun y : Fin (Module.finrank ℝ E) → ℝ =>
                      ((φmid j y : ℝ) : ℂ)) z‖ ^ 2 ≤ Kφmid ^ 2 := by
                  intro z
                  have h2 : Work.Diff.STE.pdVec i γ'' (fun y : Fin (Module.finrank ℝ E) → ℝ =>
                      ((φmid j y : ℝ) : ℂ)) z = ((Work.Diff.STE.pdRVec i γ'' (φmid j) z : ℝ) : ℂ) := by
                    rw [Work.Diff.STE.pdVec,
                      Work.Diff.STE.cm_pdList_ofReal_smooth (List.ofFn γ'') (φmid j) (hφmid_sm j)]
                    rfl
                  rw [h2, Complex.norm_real, Real.norm_eq_abs]
                  exact pow_le_pow_left₀ (abs_nonneg _) ((hKφmid j).2 i (by omega) γ'' z) 2
                have hcont : Continuous (fun z : Fin (Module.finrank ℝ E) → ℝ =>
                    ‖Work.Diff.STE.pdVec i γ'' (fun y : Fin (Module.finrank ℝ E) → ℝ =>
                      ((φmid j y : ℝ) : ℂ)) z‖ ^ 2) := by
                  have h3 := Work.Diff.STE.continuous_pdVec i γ''
                    (fun y : Fin (Module.finrank ℝ E) → ℝ => ((φmid j y : ℝ) : ℂ))
                    ((Complex.ofRealCLM.contDiff.comp (hφmid_sm j)).of_le (level_le_top i))
                  exact h3.norm.pow 2
                have h1 : ∫ z in Metric.ball (0 : Fin (Module.finrank ℝ E) → ℝ)
                      (2 * D.σ j + 3 * δ),
                      ‖Work.Diff.STE.pdVec i γ'' (fun y : Fin (Module.finrank ℝ E) → ℝ =>
                        ((φmid j y : ℝ) : ℂ)) z‖ ^ 2
                    ≤ Kφmid ^ 2 * (MeasureTheory.volume
                      (Metric.ball (0 : Fin (Module.finrank ℝ E) → ℝ) (1 / 2))).toReal :=
                  integral_ball_le_const hcont (by linarith [D.hσ j, hδpos])
                    (by linarith [D.hσ2 j, hδ16]) (sq_nonneg Kφmid) hpt
                rw [← hVbdef] at h1
                exact h1
              · have hfun : FB = (fun _ : Fin (Module.finrank ℝ E) → ℝ => (0 : ℂ)) := by
                  funext y; rw [hFBdef, if_neg hpq]; simp
                rw [hfun]
                have hz : Work.Diff.STE.pdVec i γ''
                    (fun _ : Fin (Module.finrank ℝ E) → ℝ => (0 : ℂ)) = 0 := by
                  simp only [Work.Diff.STE.pdVec, pdList_zero]
                rw [hz]
                have hI : (∫ z in Metric.ball (0 : Fin (Module.finrank ℝ E) → ℝ)
                      (2 * D.σ j + 3 * δ),
                      ‖(0 : (Fin (Module.finrank ℝ E) → ℝ) → ℂ) z‖ ^ 2) = 0 := by
                  simp
                rw [hI]
                exact mul_nonneg (sq_nonneg _) hVb0
            have hdiff : (fun y : Fin (Module.finrank ℝ E) → ℝ =>
                  ((φmid j y * Work.Diff.STE.B3.Gf (I := I) (M := M) D h j y p q
                    - φmid j y * (if p = q then (1 : ℝ) else 0) : ℝ) : ℂ)) = FA - FB := by
              funext y
              simp only [Pi.sub_apply, hFAdef, hFBdef]
              push_cast
              ring
            have hIA : MeasureTheory.IntegrableOn (fun z : Fin (Module.finrank ℝ E) → ℝ =>
                ‖Work.Diff.STE.pdVec i γ'' FA z‖ ^ 2)
                (Metric.ball (0 : Fin (Module.finrank ℝ E) → ℝ) (2 * D.σ j + 3 * δ))
                MeasureTheory.volume :=
              (integrable_normSq_pdVec hA_sm hA_cs γ'').integrableOn
            have hIB : MeasureTheory.IntegrableOn (fun z : Fin (Module.finrank ℝ E) → ℝ =>
                ‖Work.Diff.STE.pdVec i γ'' FB z‖ ^ 2)
                (Metric.ball (0 : Fin (Module.finrank ℝ E) → ℝ) (2 * D.σ j + 3 * δ))
                MeasureTheory.volume :=
              (integrable_normSq_pdVec hB_sm hB_cs γ'').integrableOn
            rw [hdiff, pdVec_sub_of_contDiff γ'' hA_sm hB_sm]
            refine le_trans (Kit.setIntegral_normSq_sub_le MeasureTheory.volume
              (Metric.ball (0 : Fin (Module.finrank ℝ E) → ℝ) (2 * D.σ j + 3 * δ))
              (fun z : Fin (Module.finrank ℝ E) → ℝ => Work.Diff.STE.pdVec i γ'' FA z)
              (fun z : Fin (Module.finrank ℝ E) → ℝ => Work.Diff.STE.pdVec i γ'' FB z)
              hIA hIB) ?_
            rw [hKtdef]
            have hE1 : (1 : ℝ) ≤ 1 + D.ENormB m h := by linarith [hE0]
            have h1 : 2 * (Kφmid ^ 2 * Vb) ≤ 2 * (Kφmid ^ 2 * Vb + 1) * (1 + D.ENormB m h) := by
              have h3 : (0 : ℝ) ≤ Kφmid ^ 2 * Vb + 1 := by nlinarith [sq_nonneg Kφmid, hVb0]
              nlinarith only [h3, hE1]
            calc 2 * (∫ z in Metric.ball (0 : Fin (Module.finrank ℝ E) → ℝ)
                    (2 * D.σ j + 3 * δ), ‖Work.Diff.STE.pdVec i γ'' FA z‖ ^ 2)
                  + 2 * (∫ z in Metric.ball (0 : Fin (Module.finrank ℝ E) → ℝ)
                    (2 * D.σ j + 3 * δ), ‖Work.Diff.STE.pdVec i γ'' FB z‖ ^ 2)
                ≤ 2 * (Cmatsum * KmonE * (1 + D.ENormB m h)) + 2 * (Kφmid ^ 2 * Vb) :=
                  add_le_add (mul_le_mul_of_nonneg_left hGpart (by norm_num))
                    (mul_le_mul_of_nonneg_left hBpart (by norm_num))
              _ ≤ (2 * Cmatsum * KmonE) * (1 + D.ENormB m h)
                    + 2 * (Kφmid ^ 2 * Vb + 1) * (1 + D.ENormB m h) := by
                  have h4 : 2 * (Cmatsum * KmonE * (1 + D.ENormB m h))
                      = (2 * Cmatsum * KmonE) * (1 + D.ENormB m h) := by ring
                  linarith only [h4, h1]
              _ = (2 * Cmatsum * KmonE + 2 * (Kφmid ^ 2 * Vb + 1)) * (1 + D.ENormB m h) := by ring
          -- ===== (x) the counting bound for the inner sum =====
          have hInner : ∑ i ∈ Finset.range (j' + 1),
                ∑ γ'' : Fin i → Fin (Module.finrank ℝ E),
                  ∫ z in Metric.ball (0 : Fin (Module.finrank ℝ E) → ℝ) (2 * D.σ j + 3 * δ),
                    ‖Work.Diff.STE.pdVec i γ'' (fun y : Fin (Module.finrank ℝ E) → ℝ =>
                      ((φmid j y * Work.Diff.STE.B3.Gf (I := I) (M := M) D h j y p q
                        - φmid j y * (if p = q then (1 : ℝ) else 0) : ℝ) : ℂ)) z‖ ^ 2
                ≤ Kinner * (1 + D.ENormB m h) := by
            have hE1 : (0 : ℝ) ≤ 1 + D.ENormB m h := by linarith [hE0]
            have hterm : ∀ i ∈ Finset.range (j' + 1),
                ∑ γ'' : Fin i → Fin (Module.finrank ℝ E),
                  ∫ z in Metric.ball (0 : Fin (Module.finrank ℝ E) → ℝ) (2 * D.σ j + 3 * δ),
                    ‖Work.Diff.STE.pdVec i γ'' (fun y : Fin (Module.finrank ℝ E) → ℝ =>
                      ((φmid j y * Work.Diff.STE.B3.Gf (I := I) (M := M) D h j y p q
                        - φmid j y * (if p = q then (1 : ℝ) else 0) : ℝ) : ℂ)) z‖ ^ 2
                ≤ ((Module.finrank ℝ E : ℝ) ^ i) * (Kt * (1 + D.ENormB m h)) := by
              intro i hi
              have him : i ≤ m := by
                have h := Finset.mem_range.mp hi
                omega
              calc ∑ γ'' : Fin i → Fin (Module.finrank ℝ E),
                    ∫ z in Metric.ball (0 : Fin (Module.finrank ℝ E) → ℝ) (2 * D.σ j + 3 * δ),
                      ‖Work.Diff.STE.pdVec i γ'' (fun y : Fin (Module.finrank ℝ E) → ℝ =>
                        ((φmid j y * Work.Diff.STE.B3.Gf (I := I) (M := M) D h j y p q
                          - φmid j y * (if p = q then (1 : ℝ) else 0) : ℝ) : ℂ)) z‖ ^ 2
                  ≤ ∑ _γ'' : Fin i → Fin (Module.finrank ℝ E),
                      (Kt * (1 + D.ENormB m h)) :=
                    Finset.sum_le_sum (fun γ'' _ => hT i him γ'')
                _ = ((Module.finrank ℝ E : ℝ) ^ i) * (Kt * (1 + D.ENormB m h)) := by
                    simp only [sum_const_card, Fintype.card_fun, Fintype.card_fin]
                    push_cast
                    ring
            calc ∑ i ∈ Finset.range (j' + 1),
                  ∑ γ'' : Fin i → Fin (Module.finrank ℝ E),
                    ∫ z in Metric.ball (0 : Fin (Module.finrank ℝ E) → ℝ) (2 * D.σ j + 3 * δ),
                      ‖Work.Diff.STE.pdVec i γ'' (fun y : Fin (Module.finrank ℝ E) → ℝ =>
                        ((φmid j y * Work.Diff.STE.B3.Gf (I := I) (M := M) D h j y p q
                          - φmid j y * (if p = q then (1 : ℝ) else 0) : ℝ) : ℂ)) z‖ ^ 2
                ≤ ∑ i ∈ Finset.range (j' + 1),
                    ((Module.finrank ℝ E : ℝ) ^ i) * (Kt * (1 + D.ENormB m h)) :=
                  Finset.sum_le_sum hterm
              _ = (∑ i ∈ Finset.range (j' + 1), ((Module.finrank ℝ E : ℝ) ^ i))
                    * (Kt * (1 + D.ENormB m h)) := by rw [Finset.sum_mul]
              _ ≤ Nsum * (Kt * (1 + D.ENormB m h)) := by
                  refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg hKt0 (by linarith [hE0]))
                  rw [hNsumdef]
                  exact sum_pow_le_geom (by positivity) (le_trans hjk hm)
              _ ≤ Kinner * (1 + D.ENormB m h) := by
                  rw [hKinnerdef]
                  have h1 : Nsum * Kt ≤ (Nsum + 1) * (Kt + 1) := by
                    nlinarith only [hNsum0, hKt0]
                  calc Nsum * (Kt * (1 + D.ENormB m h))
                      = (Nsum * Kt) * (1 + D.ENormB m h) := by ring
                    _ ≤ ((Nsum + 1) * (Kt + 1)) * (1 + D.ENormB m h) :=
                        mul_le_mul_of_nonneg_right h1 hE1
                    _ ≤ ((Nsum + 1) * (Kt + 1) + 1) * (1 + D.ENormB m h) := by
                        nlinarith only [hE1]
          -- ===== (xi) the constant assembly =====
          have hfin : Clei ⟨j', by omega⟩ * Kφout ^ 2 * (Kinner * (1 + D.ENormB m h))
              ≤ Cg * (1 + D.ENormB m h) := by
            rw [hCgdef]
            have hE1 : (0 : ℝ) ≤ 1 + D.ENormB m h := by linarith [hE0]
            have h1 : Clei ⟨j', by omega⟩ ≤ Cleimax := by
              have h5 : Clei ⟨j', by omega⟩ + 1 ≤ Cleimax := by
                rw [hCleimaxdef]
                exact Finset.single_le_sum (f := fun ℓ : Fin (k + 1) => Clei ℓ + 1)
                  (fun ℓ _ => by linarith [hClei0 ℓ]) (Finset.mem_univ _)
              linarith
            have h6 : (0 : ℝ) ≤ Clei ⟨j', by omega⟩ := hClei0 _
            have hA : Clei ⟨j', by omega⟩ ≤ (Nsum + 1) * (Cleimax + 1) := by
              have h9 : (1 : ℝ) ≤ Nsum + 1 := by linarith [hNsum0]
              have h7 : (0 : ℝ) ≤ Cleimax + 1 := by linarith [hCleimax0]
              nlinarith only [h1, h6, h7, h9]
            have hstep1 : Clei ⟨j', by omega⟩ * Kφout ^ 2
                ≤ (Nsum + 1) * (Cleimax + 1) * (Kφout ^ 2 + 1) := by
              have h7 : (0 : ℝ) ≤ (Nsum + 1) * (Cleimax + 1) :=
                mul_nonneg (by linarith [hNsum0]) (by linarith [hCleimax0])
              calc Clei ⟨j', by omega⟩ * Kφout ^ 2
                  ≤ ((Nsum + 1) * (Cleimax + 1)) * (Kφout ^ 2 + 1) :=
                    mul_le_mul hA (by linarith [sq_nonneg Kφout]) (sq_nonneg _) h7
                _ = (Nsum + 1) * (Cleimax + 1) * (Kφout ^ 2 + 1) := by ring
            have h4 : Clei ⟨j', by omega⟩ * Kφout ^ 2 * Kinner
                ≤ (Nsum + 1) * (Cleimax + 1) * (Kφout ^ 2 + 1) * (Kinner + 1) := by
              have h8 : (0 : ℝ) ≤ (Nsum + 1) * (Cleimax + 1) * (Kφout ^ 2 + 1) :=
                mul_nonneg (mul_nonneg (by linarith [hNsum0]) (by linarith [hCleimax0]))
                  (by linarith [sq_nonneg Kφout])
              calc Clei ⟨j', by omega⟩ * Kφout ^ 2 * Kinner
                  ≤ ((Nsum + 1) * (Cleimax + 1) * (Kφout ^ 2 + 1)) * (Kinner + 1) :=
                    mul_le_mul hstep1 (by linarith [hKinner0]) hKinner0 h8
                _ = (Nsum + 1) * (Cleimax + 1) * (Kφout ^ 2 + 1) * (Kinner + 1) := by ring
            calc Clei ⟨j', by omega⟩ * Kφout ^ 2 * (Kinner * (1 + D.ENormB m h))
                = (Clei ⟨j', by omega⟩ * Kφout ^ 2 * Kinner) * (1 + D.ENormB m h) := by ring
              _ ≤ ((Nsum + 1) * (Cleimax + 1) * (Kφout ^ 2 + 1) * (Kinner + 1))
                    * (1 + D.ENormB m h) := mul_le_mul_of_nonneg_right h4 hE1
              _ ≤ ((Nsum + 1) * (Cleimax + 1) * (Kφout ^ 2 + 1) * (Kinner + 1) + 1)
                    * (1 + D.ENormB m h) := by nlinarith only [hE1]
          exact le_trans (le_of_eq hclosed_eq) (le_trans hmono (le_trans hlei
            (le_trans (mul_le_mul_of_nonneg_left hInner
              (mul_nonneg (hClei0 ⟨j', by omega⟩) (sq_nonneg _))) hfin)))
        -- ===== the `H`-side bound, level by level =====
        have hHside : ∀ (j' : ℕ) (hj' : j' ≤ m) (γ' : Fin j' → Fin (Module.finrank ℝ E)),
            ∫ z in Metric.ball (0 : Fin (Module.finrank ℝ E) → ℝ) (2 * D.σ j + δ),
              ‖Work.Diff.STE.pdVec j' γ'
                (fun y : Fin (Module.finrank ℝ E) → ℝ => ((Ht y c d : ℝ) : ℂ)) z‖ ^ 2
            ≤ Chs * (1 + D.ENormB m h) := by
          intro j' hj' γ'
          have hE1 : (1 : ℝ) ≤ 1 + D.ENormB m h := by linarith [hE0]
          rcases Nat.eq_zero_or_pos j' with h0 | hpos
          · subst h0
            have hpt : ∀ z : Fin (Module.finrank ℝ E) → ℝ,
                ‖Work.Diff.STE.pdVec 0 γ' (fun y : Fin (Module.finrank ℝ E) → ℝ =>
                  ((Ht y c d : ℝ) : ℂ)) z‖ ^ 2 ≤ Wg ^ 2 := by
              intro z
              have h2 : Work.Diff.STE.pdVec 0 γ' (fun y : Fin (Module.finrank ℝ E) → ℝ =>
                  ((Ht y c d : ℝ) : ℂ)) z = ((Ht z c d : ℝ) : ℂ) := by
                simp [Work.Diff.STE.pdVec, Work.Diff.STE.pdList]
              rw [h2, Complex.norm_real, Real.norm_eq_abs]
              exact pow_le_pow_left₀ (abs_nonneg _) (hHt_b z c d) 2
            have hcont : Continuous (fun z : Fin (Module.finrank ℝ E) → ℝ =>
                ‖Work.Diff.STE.pdVec 0 γ' (fun y : Fin (Module.finrank ℝ E) → ℝ =>
                  ((Ht y c d : ℝ) : ℂ)) z‖ ^ 2) := by
              have h3 := Work.Diff.STE.continuous_pdVec 0 γ'
                (fun y : Fin (Module.finrank ℝ E) → ℝ => ((Ht y c d : ℝ) : ℂ))
                ((Complex.ofRealCLM.contDiff.comp (hHt_sm c d)).of_le (level_le_top 0))
              exact h3.norm.pow 2
            have h1 : ∫ z in Metric.ball (0 : Fin (Module.finrank ℝ E) → ℝ) (2 * D.σ j + δ),
                  ‖Work.Diff.STE.pdVec 0 γ' (fun y : Fin (Module.finrank ℝ E) → ℝ =>
                    ((Ht y c d : ℝ) : ℂ)) z‖ ^ 2
                ≤ Wg ^ 2 * (MeasureTheory.volume
                    (Metric.ball (0 : Fin (Module.finrank ℝ E) → ℝ) (1 / 2))).toReal :=
              integral_ball_le_const hcont (by linarith [D.hσ j, hδpos])
                (by linarith [hδ16, D.hσ2 j]) (sq_nonneg Wg) hpt
            rw [← hVbdef] at h1
            have h1b : Wg ^ 2 * Vb ≤ Chs := by
              rw [hChsdef]
              have h2 : (0 : ℝ) ≤ CinvEmax * (1 + Nsum * Cg) :=
                mul_nonneg hCinvEmax0 (by linarith [mul_nonneg hNsum0 hCg0])
              linarith
            exact le_trans h1 (le_trans h1b (by nlinarith only [hChs0, hE1]))
          · obtain ⟨ℓj, hℓj⟩ : ∃ ℓ : Fin k, ℓ.1 + 1 = j' :=
              ⟨⟨j' - 1, by omega⟩, by simp only [Fin.val_mk]; omega⟩
            set HB : (Fin (Module.finrank ℝ E) → ℝ) → ℂ := fun y =>
              ((Ht y c d - (if c = d then (1 : ℝ) else 0) : ℝ) : ℂ) with hHBdef
            have hHfun : (fun y : Fin (Module.finrank ℝ E) → ℝ => ((Ht y c d : ℝ) : ℂ))
                = (fun y : Fin (Module.finrank ℝ E) → ℝ =>
                    (((if c = d then (1 : ℝ) else 0) : ℂ)) + HB y) := by
              funext y
              simp only [hHBdef]
              by_cases hcd : c = d <;>
                simp only [hcd, if_true, if_false, Complex.ofReal_one, Complex.ofReal_zero,
                  Complex.ofReal_sub] <;> ring
            rw [hHfun, Kit.pdVec_const_add hpos γ']
            have hHB_sm : ContDiff ℝ (⊤ : ℕ∞) HB :=
              Complex.ofRealCLM.contDiff.comp ((hHt_sm c d).sub contDiff_const)
            have hHB_cs : HasCompactSupport HB := by
              refine hasCompactSupportC_of_support_subset_ball (R := 1 / 2) ?_
              intro y hy
              refine hHt_supp c d ?_
              intro h0
              refine hy ?_
              show ((Ht y c d - (if c = d then (1 : ℝ) else 0) : ℝ) : ℂ) = 0
              rw [show Ht y c d - (if c = d then (1 : ℝ) else 0)
                    = (fun z : Fin (Module.finrank ℝ E) → ℝ =>
                        Ht z c d - (if c = d then (1 : ℝ) else 0)) y from rfl, h0]
              simp
            have hHB_eq : Work.Diff.STE.pdVec j' γ' HB
                = Work.Diff.STE.pdVec j' γ' (fun y : Fin (Module.finrank ℝ E) → ℝ =>
                    ((Ht y c d : ℝ) : ℂ)) := by
              rw [hHfun]
              exact (Kit.pdVec_const_add hpos γ'
                (((if c = d then (1 : ℝ) else 0) : ℂ)) HB).symm
            -- the Moser estimate for the residual field at level `j'`
            have hmos := hCinvEb ℓj Gt Ht hGt_sm hHt_sm hGt_supp hHt_supp hGt_b hHt_b hGH
              (fun i : Fin (ℓj.1 + 1) => γ' (Fin.cast hℓj i)) c d
            have hGsum : ∑ p : Fin (Module.finrank ℝ E), ∑ q : Fin (Module.finrank ℝ E),
                  ∑ γ'' : Fin (ℓj.1 + 1) → Fin (Module.finrank ℝ E),
                    ∫ z : Fin (Module.finrank ℝ E) → ℝ,
                      ‖Work.Diff.STE.pdVec (ℓj.1 + 1) γ''
                        (fun y : Fin (Module.finrank ℝ E) → ℝ => ((Gt y p q : ℝ) : ℂ)) z‖ ^ 2
                ≤ Nsum * (Cg * (1 + D.ENormB m h)) := by
              have hper : ∀ (p q : Fin (Module.finrank ℝ E))
                  (γ'' : Fin (ℓj.1 + 1) → Fin (Module.finrank ℝ E)),
                  ∫ z : Fin (Module.finrank ℝ E) → ℝ,
                    ‖Work.Diff.STE.pdVec (ℓj.1 + 1) γ''
                      (fun y : Fin (Module.finrank ℝ E) → ℝ => ((Gt y p q : ℝ) : ℂ)) z‖ ^ 2
                    ≤ Cg * (1 + D.ENormB m h) :=
                fun p q γ'' => hGside (ℓj.1 + 1) (by omega) (by rw [hℓj]; exact hj') p q γ''
              calc ∑ p : Fin (Module.finrank ℝ E), ∑ q : Fin (Module.finrank ℝ E),
                    ∑ γ'' : Fin (ℓj.1 + 1) → Fin (Module.finrank ℝ E),
                      ∫ z : Fin (Module.finrank ℝ E) → ℝ,
                        ‖Work.Diff.STE.pdVec (ℓj.1 + 1) γ''
                          (fun y : Fin (Module.finrank ℝ E) → ℝ => ((Gt y p q : ℝ) : ℂ)) z‖ ^ 2
                  ≤ ∑ _p : Fin (Module.finrank ℝ E), ∑ _q : Fin (Module.finrank ℝ E),
                      ∑ _γ'' : Fin (ℓj.1 + 1) → Fin (Module.finrank ℝ E),
                        (Cg * (1 + D.ENormB m h)) :=
                    Finset.sum_le_sum (fun p _ => Finset.sum_le_sum (fun q _ =>
                      Finset.sum_le_sum (fun γ'' _ => hper p q γ'')))
                _ = ((Module.finrank ℝ E : ℝ) ^ (ℓj.1 + 1))
                      * ((Module.finrank ℝ E : ℝ) * (Module.finrank ℝ E : ℝ))
                      * (Cg * (1 + D.ENormB m h)) := by
                    simp only [sum_const_card, Fintype.card_fin, Fintype.card_fun]
                    push_cast
                    ring
                _ ≤ Nsum * (Cg * (1 + D.ENormB m h)) := by
                    refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg hCg0 (by linarith [hE0]))
                    rw [hℓj, ← pow_two, ← pow_add]
                    rw [hNsumdef]
                    have hp : (Module.finrank ℝ E : ℝ) ^ (j' + 2)
                        ≤ ((Module.finrank ℝ E : ℝ) + 1) ^ (j' + 2) :=
                      pow_le_pow_left₀ (by positivity) (by linarith) (j' + 2)
                    exact le_trans hp (Finset.single_le_sum
                      (f := fun ℓ => ((Module.finrank ℝ E : ℝ) + 1) ^ ℓ)
                      (fun ℓ _ => pow_nonneg (by positivity) ℓ)
                      (Finset.mem_range.mpr (by omega)))
            have hglob : ∫ z in Metric.ball (0 : Fin (Module.finrank ℝ E) → ℝ) (2 * D.σ j + δ),
                  ‖Work.Diff.STE.pdVec j' γ' HB z‖ ^ 2
                ≤ CinvE ℓj * (1 + Nsum * (Cg * (1 + D.ENormB m h))) := by
              have hint : MeasureTheory.Integrable (fun z : Fin (Module.finrank ℝ E) → ℝ =>
                  ‖Work.Diff.STE.pdVec j' γ' HB z‖ ^ 2) := integrable_normSq_pdVec hHB_sm hHB_cs γ'
              have h1 : ∫ z in Metric.ball (0 : Fin (Module.finrank ℝ E) → ℝ) (2 * D.σ j + δ),
                    ‖Work.Diff.STE.pdVec j' γ' HB z‖ ^ 2
                  ≤ ∫ z : Fin (Module.finrank ℝ E) → ℝ,
                    ‖Work.Diff.STE.pdVec j' γ' HB z‖ ^ 2 :=
                MeasureTheory.setIntegral_le_integral hint
                  (Filter.Eventually.of_forall fun z => by positivity)
              have h2 : ∫ z : Fin (Module.finrank ℝ E) → ℝ, ‖Work.Diff.STE.pdVec j' γ' HB z‖ ^ 2
                  = ∫ z : Fin (Module.finrank ℝ E) → ℝ,
                    ‖Work.Diff.STE.pdVec (ℓj.1 + 1)
                      (fun i : Fin (ℓj.1 + 1) => γ' (Fin.cast hℓj i))
                      (fun y : Fin (Module.finrank ℝ E) → ℝ => ((Ht y c d : ℝ) : ℂ)) z‖ ^ 2 := by
                rw [hHB_eq]
                rw [pdVec_cast_eq hℓj γ' (fun y : Fin (Module.finrank ℝ E) → ℝ =>
                  ((Ht y c d : ℝ) : ℂ))]
              have h3 : ∫ z : Fin (Module.finrank ℝ E) → ℝ,
                    ‖Work.Diff.STE.pdVec (ℓj.1 + 1)
                      (fun i : Fin (ℓj.1 + 1) => γ' (Fin.cast hℓj i))
                      (fun y : Fin (Module.finrank ℝ E) → ℝ => ((Ht y c d : ℝ) : ℂ)) z‖ ^ 2
                  ≤ CinvE ℓj * (1 + Nsum * (Cg * (1 + D.ENormB m h))) :=
                le_trans hmos (mul_le_mul_of_nonneg_left (by linarith only [hGsum]) (hCinvE0 ℓj))
              linarith only [h1, h2, h3]
            have hfin2 : CinvE ℓj * (1 + Nsum * (Cg * (1 + D.ENormB m h)))
                ≤ Chs * (1 + D.ENormB m h) := by
              rw [hChsdef]
              have h1 : CinvE ℓj ≤ CinvEmax := by
                have h5 : CinvE ℓj + 1 ≤ CinvEmax := by
                  rw [hCinvEmaxdef]
                  exact Finset.single_le_sum (f := fun ℓ : Fin k => CinvE ℓ + 1)
                    (fun ℓ _ => by linarith [hCinvE0 ℓ]) (Finset.mem_univ _)
                linarith
              have h2 : 1 + Nsum * (Cg * (1 + D.ENormB m h))
                  ≤ (1 + Nsum * Cg) * (1 + D.ENormB m h) := by
                have h3 : (0 : ℝ) ≤ Nsum * Cg := mul_nonneg hNsum0 hCg0
                nlinarith only [hE1, h3]
              have hA0 : (0 : ℝ) ≤ 1 + Nsum * (Cg * (1 + D.ENormB m h)) := by
                have h8 : (0 : ℝ) ≤ Cg * (1 + D.ENormB m h) :=
                  mul_nonneg hCg0 (by linarith [hE0])
                have h9 : (0 : ℝ) ≤ Nsum * (Cg * (1 + D.ENormB m h)) :=
                  mul_nonneg hNsum0 h8
                linarith
              have h4 : CinvE ℓj * (1 + Nsum * (Cg * (1 + D.ENormB m h)))
                  ≤ CinvEmax * ((1 + Nsum * Cg) * (1 + D.ENormB m h)) :=
                mul_le_mul h1 h2 hA0 (by linarith [hCinvEmax0])
              calc CinvE ℓj * (1 + Nsum * (Cg * (1 + D.ENormB m h)))
                  ≤ CinvEmax * ((1 + Nsum * Cg) * (1 + D.ENormB m h)) := h4
                _ = CinvEmax * (1 + Nsum * Cg) * (1 + D.ENormB m h) := by ring
                _ ≤ (CinvEmax * (1 + Nsum * Cg) + Wg ^ 2 * Vb + 1)
                      * (1 + D.ENormB m h) := by
                    have h3 : (0 : ℝ) ≤ CinvEmax * (1 + Nsum * Cg) :=
                      mul_nonneg hCinvEmax0 (by linarith [mul_nonneg hNsum0 hCg0])
                    have h5 : (0 : ℝ) ≤ Wg ^ 2 * Vb + 1 := by
                      nlinarith [sq_nonneg Wg, hVb0]
                    have h6 : (0 : ℝ) ≤ 1 + D.ENormB m h := by linarith
                    have h7 : CinvEmax * (1 + Nsum * Cg)
                        ≤ CinvEmax * (1 + Nsum * Cg) + Wg ^ 2 * Vb + 1 := by linarith
                    exact mul_le_mul_of_nonneg_right h7 h6
            exact le_trans hglob hfin2
        -- ===== (6) the reduction (`tmA_l2_reduce`) and the constant assembly =====
        have hcast : Work.Diff.STE.pdVec m β (fun y : Fin (Module.finrank ℝ E) → ℝ =>
              ((Work.Diff.STE.B3.tmA (φin j) (min c₀ 1) Ht y c d : ℝ) : ℂ))
            = Work.Diff.STE.pdVec (ℓm.1 + 1) (fun i : Fin (ℓm.1 + 1) => β (Fin.cast hℓm i))
              (fun y : Fin (Module.finrank ℝ E) → ℝ =>
                ((Work.Diff.STE.B3.tmA (φin j) (min c₀ 1) Ht y c d : ℝ) : ℂ)) :=
          pdVec_cast_eq hℓm β _
        rw [htmA_eq, Work.Diff.STE.ENormSq_zero, hcast, ← Work.Diff.STE.ENormSq_zero]
        have hCred := hCredb ℓm (2 * D.σ j + δ) (by linarith [D.hσ j, hδpos]) (hRj j)
          (φin j) (hφin_sm j) (hφin_0 j) (hφin_1 j)
          (fun r hr γ'' z => hφin_pdRvec r (hℓm ▸ hr) γ'' z) (hφin_ts j) Ht hHt_sm c d
          (fun i : Fin (ℓm.1 + 1) => β (Fin.cast hℓm i))
        have hS : ∑ j1 ∈ Finset.range (ℓm.1 + 1 + 1),
              ∑ γ'' : Fin j1 → Fin (Module.finrank ℝ E),
                ∫ z in Metric.ball (0 : Fin (Module.finrank ℝ E) → ℝ) (2 * D.σ j + δ),
                  ‖Work.Diff.STE.pdVec j1 γ''
                    (fun y : Fin (Module.finrank ℝ E) → ℝ => ((Ht y c d : ℝ) : ℂ)) z‖ ^ 2
            ≤ Nsum * (Chs * (1 + D.ENormB m h)) := by
          have hterm : ∀ j1 ∈ Finset.range (ℓm.1 + 1 + 1),
              ∑ γ'' : Fin j1 → Fin (Module.finrank ℝ E),
                ∫ z in Metric.ball (0 : Fin (Module.finrank ℝ E) → ℝ) (2 * D.σ j + δ),
                  ‖Work.Diff.STE.pdVec j1 γ''
                    (fun y : Fin (Module.finrank ℝ E) → ℝ => ((Ht y c d : ℝ) : ℂ)) z‖ ^ 2
              ≤ ((Module.finrank ℝ E : ℝ) ^ j1) * (Chs * (1 + D.ENormB m h)) := by
            intro j1 hj1
            have hjm : j1 ≤ m := by
              have h := Finset.mem_range.mp hj1
              omega
            calc ∑ γ'' : Fin j1 → Fin (Module.finrank ℝ E),
                  ∫ z in Metric.ball (0 : Fin (Module.finrank ℝ E) → ℝ) (2 * D.σ j + δ),
                    ‖Work.Diff.STE.pdVec j1 γ''
                      (fun y : Fin (Module.finrank ℝ E) → ℝ => ((Ht y c d : ℝ) : ℂ)) z‖ ^ 2
                ≤ ∑ _γ'' : Fin j1 → Fin (Module.finrank ℝ E), (Chs * (1 + D.ENormB m h)) :=
                  Finset.sum_le_sum (fun γ'' _ => hHside j1 hjm γ'')
              _ = ((Module.finrank ℝ E : ℝ) ^ j1) * (Chs * (1 + D.ENormB m h)) := by
                  simp only [sum_const_card, Fintype.card_fun, Fintype.card_fin]
                  push_cast
                  ring
          calc ∑ j1 ∈ Finset.range (ℓm.1 + 1 + 1),
                ∑ γ'' : Fin j1 → Fin (Module.finrank ℝ E),
                  ∫ z in Metric.ball (0 : Fin (Module.finrank ℝ E) → ℝ) (2 * D.σ j + δ),
                    ‖Work.Diff.STE.pdVec j1 γ''
                      (fun y : Fin (Module.finrank ℝ E) → ℝ => ((Ht y c d : ℝ) : ℂ)) z‖ ^ 2
              ≤ ∑ j1 ∈ Finset.range (ℓm.1 + 1 + 1),
                  ((Module.finrank ℝ E : ℝ) ^ j1) * (Chs * (1 + D.ENormB m h)) :=
                Finset.sum_le_sum hterm
            _ = (∑ j1 ∈ Finset.range (ℓm.1 + 1 + 1), ((Module.finrank ℝ E : ℝ) ^ j1))
                  * (Chs * (1 + D.ENormB m h)) := by rw [Finset.sum_mul]
            _ ≤ Nsum * (Chs * (1 + D.ENormB m h)) := by
                refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg hChs0 (by linarith [hE0]))
                rw [show ℓm.1 + 1 + 1 = m + 1 from by omega]
                rw [hNsumdef]
                exact sum_pow_le_geom (by positivity) hm
        have hfinal : Cred ℓm * (1 + ∑ j1 ∈ Finset.range (ℓm.1 + 1 + 1),
              ∑ γ'' : Fin j1 → Fin (Module.finrank ℝ E),
                ∫ z in Metric.ball (0 : Fin (Module.finrank ℝ E) → ℝ) (2 * D.σ j + δ),
                  ‖Work.Diff.STE.pdVec j1 γ''
                    (fun y : Fin (Module.finrank ℝ E) → ℝ => ((Ht y c d : ℝ) : ℂ)) z‖ ^ 2)
            ≤ CA * (1 + D.ENormB m h) := by
          have hC0 : (0 : ℝ) ≤ Cred ℓm := hCred0 ℓm
          have hEa : (0 : ℝ) ≤ 1 + D.ENormB m h := by linarith [hE0]
          have hEb : (1 : ℝ) ≤ 1 + D.ENormB m h := by linarith [hE0]
          have hChsN : (0 : ℝ) ≤ Nsum * Chs := mul_nonneg hNsum0 hChs0
          have h1 : 1 + (∑ j1 ∈ Finset.range (ℓm.1 + 1 + 1),
                ∑ γ'' : Fin j1 → Fin (Module.finrank ℝ E),
                  ∫ z in Metric.ball (0 : Fin (Module.finrank ℝ E) → ℝ) (2 * D.σ j + δ),
                    ‖Work.Diff.STE.pdVec j1 γ''
                      (fun y : Fin (Module.finrank ℝ E) → ℝ => ((Ht y c d : ℝ) : ℂ)) z‖ ^ 2)
              ≤ (1 + Nsum * Chs) * (1 + D.ENormB m h) := by
            have h3 : Nsum * Chs * (1 + D.ENormB m h)
                = Nsum * (Chs * (1 + D.ENormB m h)) := by ring
            have h2 : 1 + Nsum * (Chs * (1 + D.ENormB m h))
                ≤ (1 + Nsum * Chs) * (1 + D.ENormB m h) := by
              nlinarith only [hEb, hChsN, h3]
            linarith only [hS, h2]
          have h4 : Cred ℓm * (1 + ∑ j1 ∈ Finset.range (ℓm.1 + 1 + 1),
                ∑ γ'' : Fin j1 → Fin (Module.finrank ℝ E),
                  ∫ z in Metric.ball (0 : Fin (Module.finrank ℝ E) → ℝ) (2 * D.σ j + δ),
                    ‖Work.Diff.STE.pdVec j1 γ''
                      (fun y : Fin (Module.finrank ℝ E) → ℝ => ((Ht y c d : ℝ) : ℂ)) z‖ ^ 2)
              ≤ Cred ℓm * ((1 + Nsum * Chs) * (1 + D.ENormB m h)) :=
            mul_le_mul_of_nonneg_left h1 hC0
          have h5 : Cred ℓm * (1 + Nsum * Chs) ≤ CA0 * (1 + Nsum * Chs) :=
            mul_le_mul_of_nonneg_right (hCredle ℓm) (by linarith [hChsN])
          have h6 : CA0 * (1 + Nsum * Chs) ≤ CA2 := by rw [hCA2def]; linarith
          calc Cred ℓm * (1 + ∑ j1 ∈ Finset.range (ℓm.1 + 1 + 1),
                ∑ γ'' : Fin j1 → Fin (Module.finrank ℝ E),
                  ∫ z in Metric.ball (0 : Fin (Module.finrank ℝ E) → ℝ) (2 * D.σ j + δ),
                    ‖Work.Diff.STE.pdVec j1 γ''
                      (fun y : Fin (Module.finrank ℝ E) → ℝ => ((Ht y c d : ℝ) : ℂ)) z‖ ^ 2)
              ≤ Cred ℓm * ((1 + Nsum * Chs) * (1 + D.ENormB m h)) := h4
            _ = (Cred ℓm * (1 + Nsum * Chs)) * (1 + D.ENormB m h) := by ring
            _ ≤ (CA0 * (1 + Nsum * Chs)) * (1 + D.ENormB m h) :=
                mul_le_mul_of_nonneg_right h5 hEa
            _ ≤ CA2 * (1 + D.ENormB m h) := mul_le_mul_of_nonneg_right h6 hEa
            _ ≤ CA * (1 + D.ENormB m h) := mul_le_mul_of_nonneg_right hCA2le hEa
        exact le_trans hCred hfinal
    · -- the agreement with the inverse on the closed `2σ j`-ball
      intro z hz c d
      have hper : Work.Diff.STE.B3.tmPer
          (fun w => φin j w * (γ w c d - (if c = d then min c₀ 1 else 0))) z
          = φin j z * (γ z c d - (if c = d then min c₀ 1 else 0)) := by
        refine Work.Diff.STE.Lead.Gal.gardTmPer_core (R := 2 * D.σ j + δ) (R₀ := 2 * D.σ j)
          ?_ ?_ hz
        · have h1 := D.hσ2 j
          linarith [hδ16]
        · intro w hw
          refine hφin_ts j (subset_tsupport (φin j) ?_)
          intro h0
          exact hw (by simp [h0])
      have hφ1 : φin j z = 1 := hφin_eq1 j z hz
      simp only [Work.Diff.STE.B3.tmA]
      rw [hper, hφ1]
      ring

end Work.Diff.STE.Lead.GalTame
