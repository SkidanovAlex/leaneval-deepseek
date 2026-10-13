import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Submission.Work.FTS.EllipticEst.H2W.Ae.Defs
import Submission.Work.FTS.EllipticEst.AngSecond.Defs
import Submission.Work.FTS.EllipticEst.AeI1Fts.hardy_N
import Submission.Work.FTS.EllipticEst.Honest.SliceIbpThetaHonest
import Submission.Work.FTS.EllipticEst.TT.AeI1.aeDzTraceHk
import Submission.Work.FTS.EllipticEst.AngClean.HkMem_zero_IPMem
import Submission.Work.FTS.EllipticEst.Endpt.sliceBdd_of_hmB
import Submission.Work.FTS.EllipticEst.H2W.AeLeftClean
import Submission.Work.FTS.EllipticEst.Dispatch.AeI1Defs
import Submission.Work.EllipticEst.RegQ.DzWeak.SliceCalc
import Submission.Work.Spaces.mixed_comm
import Submission.Work.Spaces.aesm_of_continuousOn_Qd
import Submission.Work.FTS.EllipticEst.remov.wsAux
import Submission.Work.FTS.EllipticEst.Mine.SliceAgmonWeighted
import Submission.Work.FTS.EllipticEst.Honest.slice_bdd_of_sq_mul_sEta
import Submission.Work.FTS.EllipticEst.H2W.Radial.hkMem_of_ae_slice_bound
import Submission.Work.FTS.EllipticEst.TT.ipMemUHtermFts
import Submission.Work.FTS.EllipticEst.TT.sliceSharpFts
import Submission.Work.FTS.EllipticEst.TT.sliceBoundsOfTraceFts

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.TT

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false

/-! ## Elementary facts about the angular weight -/

/-- The angular weight `sEta` is the weight `sig` of the pairing (definitionally). -/
private lemma sEta_eq_sig (θ : ℝ) :
    Work.FTS.EllipticEst.sEta θ = Work.FTS.EllipticEst.AngSecond.sig θ := rfl

/-- At the two endpoints of `Iθ` the angular weight vanishes. -/
private lemma sEta_eq_zero_of_sin_eq_zero {θ : ℝ} (h : Real.sin (2 * θ) = 0) :
    Work.FTS.EllipticEst.sEta θ = 0 := by
  rw [Work.FTS.EllipticEst.sEta, h]
  exact Real.zero_rpow (by rw [Work.Spaces.eta]; norm_num)

/-! ## The derivatives of the slice of `U = z ∂_z u` -/

/-- The `θ`-derivative of `U = z∂_zu` is `z ∂_θ∂_zu`. -/
private lemma pth_grad_eq (u : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.pth (Work.FTS.EllipticEst.H2W.Ae.grad u) z θ
      = z * Work.Spaces.pth (Work.Spaces.pz u) z θ := by
  show deriv (fun θ' => Work.FTS.EllipticEst.H2W.Ae.grad u z θ') θ
      = z * deriv (fun θ' => Work.Spaces.pz u z θ') θ
  have h : (fun θ' => Work.FTS.EllipticEst.H2W.Ae.grad u z θ')
      = fun θ' => z * Work.Spaces.pz u z θ' := by
    funext θ'; rfl
  rw [h, deriv_const_mul_field]

/-- The second `θ`-derivative of `U = z∂_zu` is `z ∂_θ²∂_zu`. -/
private lemma pthIter_two_grad_eq (u : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.pthIter 2 (Work.FTS.EllipticEst.H2W.Ae.grad u) z θ
      = z * Work.Spaces.pthIter 2 (Work.Spaces.pz u) z θ := by
  show deriv (fun θ' => Work.Spaces.pth (Work.FTS.EllipticEst.H2W.Ae.grad u) z θ') θ
      = z * deriv (fun θ' => Work.Spaces.pth (Work.Spaces.pz u) z θ') θ
  have h : (fun θ' => Work.Spaces.pth (Work.FTS.EllipticEst.H2W.Ae.grad u) z θ')
      = fun θ' => z * Work.Spaces.pth (Work.Spaces.pz u) z θ' := by
    funext θ'; exact pth_grad_eq u z θ'
  rw [h, deriv_const_mul_field]

/-- **Clairaut for the slice of `U = z∂_zu`**: on the open quadrant the second `θ`-derivative of
the slice equals `z ∂_z∂_θ²u`. -/
private lemma slice_second_deriv_eq (u : ℝ → ℝ → ℝ)
    (hS : Work.FTS.EllipticEst.SmoothOpen u) {z θ : ℝ}
    (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    deriv (deriv (fun θ' => Work.FTS.EllipticEst.H2W.Ae.grad u z θ')) θ
      = z * Work.Spaces.pz (Work.Spaces.pthIter 2 u) z θ := by
  have h1 : deriv (deriv (fun θ' => Work.FTS.EllipticEst.H2W.Ae.grad u z θ')) θ
      = Work.Spaces.pthIter 2 (Work.FTS.EllipticEst.H2W.Ae.grad u) z θ := by
    show deriv (fun θ' => deriv (fun θ'' => Work.FTS.EllipticEst.H2W.Ae.grad u z θ'') θ') θ = _
    rw [show Work.Spaces.pthIter 2 (Work.FTS.EllipticEst.H2W.Ae.grad u)
        = Work.Spaces.pth (Work.Spaces.pth (Work.FTS.EllipticEst.H2W.Ae.grad u)) from by
      rw [Work.Spaces.pthIter_succ, Work.Spaces.pthIter_succ, Work.Spaces.pthIter_zero]]
    rfl
  rw [h1, pthIter_two_grad_eq u z θ]
  have h3 : Work.Spaces.pthIter 2 (Work.Spaces.pz u) z θ
      = Work.Spaces.pz (Work.Spaces.pthIter 2 u) z θ :=
    Work.EllipticEst.RegQ.DzWeak.pthIter_two_pz_eqOn hS
      (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ.1, hθ.2⟩)
  rw [h3]

/-! ## The `θ`-integral of the `H^0`-integrand -/

/-- The `θ`-integral of the level-`0` `HkIntegrand` is the `w²`-weighted `σ`-mass. -/
private lemma integral_HkIntegrand_zero_eq (α : ℝ) (g : ℝ → ℝ → ℝ) (z : ℝ) :
    (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 g z θ)
      = Work.FTS.EllipticEst.AngSecond.w2 z
        * ∫ θ in Work.Spaces.Iθ, (g z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ := by
  rw [show (∫ θ in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 0 g z θ)
      = ∫ θ in Work.Spaces.Iθ,
          (g z θ) ^ 2 * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.sEta θ from
    MeasureTheory.setIntegral_congr_fun measurableSet_Icc
      (fun θ hθ => Work.FTS.EllipticEst.Endpt.HkIntegrand_zero_eq_sEta α g z hθ)]
  rw [show (fun θ : ℝ => (g z θ) ^ 2 * (Work.Spaces.w z) ^ 2 * Work.FTS.EllipticEst.sEta θ)
      = fun θ : ℝ => Work.FTS.EllipticEst.AngSecond.w2 z
          * ((g z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) from by
    funext θ
    rw [Work.FTS.EllipticEst.AngSecond.w2]
    ring]
  rw [MeasureTheory.integral_const_mul]

/-- **The pairing integrand against the second `θ`-derivative of the slice.**  On `Iθ` the
product `U · ∂_θ²U` agrees with `f · f''` for the slice `f` of `U = z∂_zu` (at the endpoints both
integrands carry the vanishing weight `σ`), so the two `θ`-integrals agree. -/
private lemma pairing_integrand_eq (u : ℝ → ℝ → ℝ) (hS : Work.FTS.EllipticEst.SmoothOpen u)
    {z : ℝ} (hz : 0 < z) {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    Work.FTS.EllipticEst.H2W.Ae.grad u z θ
        * (fun z θ => z * Work.Spaces.pz (Work.Spaces.pthIter 2 u) z θ) z θ
        * Work.FTS.EllipticEst.AngSecond.sig θ
      = Work.FTS.EllipticEst.H2W.Ae.grad u z θ
        * deriv (deriv (fun θ' => Work.FTS.EllipticEst.H2W.Ae.grad u z θ')) θ
        * Work.FTS.EllipticEst.sEta θ := by
  by_cases hsin : Real.sin (2 * θ) = 0
  · have hz0 : Work.FTS.EllipticEst.sEta θ = 0 := sEta_eq_zero_of_sin_eq_zero hsin
    have hz1 : Work.FTS.EllipticEst.AngSecond.sig θ = 0 := hz0
    simp only [hz0, hz1, mul_zero]
  · have hθ' : θ ∈ Set.Ioo 0 (Real.pi / 2) := by
      refine ⟨?_, ?_⟩
      · rcases lt_or_ge 0 θ with h | h
        · exact h
        · exfalso
          have hθ0 : θ = 0 := le_antisymm h hθ.1
          rw [hθ0] at hsin
          rw [show (2 : ℝ) * 0 = 0 by norm_num, Real.sin_zero] at hsin
          exact hsin rfl
      · rcases lt_or_ge θ (Real.pi / 2) with h | h
        · exact h
        · exfalso
          have hθπ : θ = Real.pi / 2 := le_antisymm hθ.2 h
          rw [hθπ] at hsin
          rw [show (2 : ℝ) * (Real.pi / 2) = Real.pi by ring, Real.sin_pi] at hsin
          exact hsin rfl
    have hmain : (fun z θ => z * Work.Spaces.pz (Work.Spaces.pthIter 2 u) z θ) z θ
        = deriv (deriv (fun θ' => Work.FTS.EllipticEst.H2W.Ae.grad u z θ')) θ :=
      (slice_second_deriv_eq u hS hz hθ').symm
    rw [hmain]
    rfl

private lemma integral_pairing_eq (u : ℝ → ℝ → ℝ) (hS : Work.FTS.EllipticEst.SmoothOpen u)
    {z : ℝ} (hz : 0 < z) :
    (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.H2W.Ae.grad u z θ
        * (fun z θ => z * Work.Spaces.pz (Work.Spaces.pthIter 2 u) z θ) z θ
        * Work.FTS.EllipticEst.AngSecond.w2 z * Work.FTS.EllipticEst.AngSecond.sig θ)
      = Work.FTS.EllipticEst.AngSecond.w2 z
        * ∫ θ in Work.Spaces.Iθ,
            Work.FTS.EllipticEst.H2W.Ae.grad u z θ
              * deriv (deriv (fun θ' => Work.FTS.EllipticEst.H2W.Ae.grad u z θ')) θ
              * Work.FTS.EllipticEst.sEta θ := by
  rw [show (∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.H2W.Ae.grad u z θ
        * (fun z θ => z * Work.Spaces.pz (Work.Spaces.pthIter 2 u) z θ) z θ
        * Work.FTS.EllipticEst.AngSecond.w2 z * Work.FTS.EllipticEst.AngSecond.sig θ)
      = ∫ θ in Work.Spaces.Iθ, Work.FTS.EllipticEst.AngSecond.w2 z
          * (Work.FTS.EllipticEst.H2W.Ae.grad u z θ
            * (fun z θ => z * Work.Spaces.pz (Work.Spaces.pthIter 2 u) z θ) z θ
            * Work.FTS.EllipticEst.AngSecond.sig θ) from
    MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ _ => by ring)]
  rw [MeasureTheory.integral_const_mul]
  congr 1
  exact MeasureTheory.setIntegral_congr_fun measurableSet_Icc
    (fun θ hθ => pairing_integrand_eq u hS hz hθ)

/-! ## The mixed-derivative honesty -/

/-- `sEta` is nonnegative on `Iθ`. -/
private lemma sEta_nonneg_Iθ {θ : ℝ} (hθ : θ ∈ Work.Spaces.Iθ) :
    0 ≤ Work.FTS.EllipticEst.sEta θ :=
  Work.FTS.EllipticEst.thEta_nonneg hθ

/-- The two forms of the mixed slot agree as functions: `z ∂_θ∂_zu = ∂_θ(z∂_zu)`. -/
private lemma grad_pth_eq_Dz_pth (u : ℝ → ℝ → ℝ) (z θ : ℝ) :
    z * Work.Spaces.pth (Work.Spaces.pz u) z θ = Work.Spaces.pth (Work.Spaces.Dz u) z θ := by
  have hfun : (fun θ' => Work.Spaces.Dz u z θ') = fun θ' => z * Work.Spaces.pz u z θ' := by
    funext θ'; rfl
  show z * deriv (fun θ' => Work.Spaces.pz u z θ') θ = deriv (fun θ' => Work.Spaces.Dz u z θ') θ
  rw [hfun, deriv_const_mul_field]

/-- The second `θ`-derivative of the slice of `D_z u` is the mixed slot `z∂_z∂_θ²u`. -/
private lemma slice_second_deriv_eq_Dz (u : ℝ → ℝ → ℝ)
    (hS : Work.FTS.EllipticEst.SmoothOpen u) {z θ : ℝ}
    (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    deriv (deriv (fun θ' => Work.Spaces.Dz u z θ')) θ
      = z * Work.Spaces.pz (Work.Spaces.pthIter 2 u) z θ := by
  have h1 : (fun θ' => Work.Spaces.Dz u z θ')
      = fun θ' => Work.FTS.EllipticEst.H2W.Ae.grad u z θ' := by
    funext θ'; rfl
  rw [h1]
  exact slice_second_deriv_eq u hS hz hθ

/-- The level-`0` `HkIntegrand` is the square of the weighted profile. -/
private lemma HkIntegrand_zero_pt (α : ℝ) (f : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.Spaces.HkIntegrand α 0 f z θ
      = (f z θ * (Work.Spaces.w z / (Real.sin (2 * θ)) ^ (Work.Spaces.eta / 2))) ^ 2 := by
  simp only [Work.Spaces.HkIntegrand]
  rw [Finset.sum_range_succ, Finset.sum_range_zero, zero_add, Work.Spaces.DzIter_zero]
  rw [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  rw [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  norm_num

/-- **The mixed-derivative honesty.**  The `θ`-derivative of the slice of `U = z∂_zu` is the
mixed slot `z∂_z∂_θu = ∂_θ(z∂_zu)`; the slicewise Agmon inequality (`Mine.SliceAgmonWeighted`)
bounds its `σ`-energy by the two energies supplied by `HkMem α 0 U` and
`HkMem α 0 (z∂_z∂_θ²u)`, and that domination makes the global `z`-integral finite. -/
private lemma mixedHkMem_aux {α : ℝ} {u G : ℝ → ℝ → ℝ}
    (h : Work.FTS.EllipticEst.H2W.Ae.AeData α u G)
    (hU : Work.Spaces.HkMem α 0 (Work.FTS.EllipticEst.H2W.Ae.grad u))
    (hH : Work.Spaces.HkMem α 0
      (fun z θ => z * Work.Spaces.pz (Work.Spaces.pthIter 2 u) z θ)) :
    Work.Spaces.HkMem α 0 (fun z θ => z * Work.Spaces.pth (Work.Spaces.pz u) z θ) := by
  classical
  have hS : Work.FTS.EllipticEst.SmoothOpen u :=
    Work.FTS.EllipticEst.smoothOpen_of_forall h.smooth
  obtain ⟨C, hCpos, hCagm⟩ := Work.FTS.EllipticEst.Mine.SliceAgmonWeighted
  -- (0) the second-derivative integrability of the slice of `D_z u`
  have hsecint : ∀ z, 0 < z → MeasureTheory.IntegrableOn
      (fun θ => (deriv (deriv (fun θ' => Work.Spaces.Dz u z θ')) θ) ^ 2
        * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ := by
    intro z hz
    have hbase : MeasureTheory.IntegrableOn
        (fun θ => (z * Work.Spaces.pz (Work.Spaces.pthIter 2 u) z θ) ^ 2
          * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ :=
      Work.FTS.EllipticEst.H2W.AeLeftClean.hkMemSliceSqSigma hH hz
    refine hbase.congr_fun (fun θ hθ => ?_) measurableSet_Icc
    by_cases hθ' : θ ∈ Set.Ioo 0 (Real.pi / 2)
    · rw [slice_second_deriv_eq_Dz u hS hz hθ']
    · have hsin0 : Real.sin (2 * θ) = 0 := by
        have h1 : θ = 0 ∨ θ = Real.pi / 2 := by
          by_contra hcon
          push_neg at hcon
          exact hθ' ⟨lt_of_le_of_ne hθ.1 (Ne.symm hcon.1), lt_of_le_of_ne hθ.2 hcon.2⟩
        rcases h1 with h1 | h1
        · rw [h1, mul_zero, Real.sin_zero]
        · rw [h1, show 2 * (Real.pi / 2) = Real.pi by ring, Real.sin_pi]
      simp only [sEta_eq_zero_of_sin_eq_zero hsin0, mul_zero]
  -- (1) the slicewise integrability of the `σ`-energy of `∂_θ(z∂_zu) = z∂_z∂_θu`
  have hsliceDz : ∀ z, 0 < z → MeasureTheory.IntegrableOn
      (fun θ => (Work.Spaces.pth (Work.Spaces.Dz u) z θ) ^ 2
        * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ := by
    intro z hz
    obtain ⟨M, hM0, hM⟩ := Work.FTS.EllipticEst.Honest.slice_bdd_of_sq_mul_sEta
      (u := fun θ => Work.Spaces.Dz u z θ)
      (Work.FTS.EllipticEst.remov.ws_contDiffOn_slice hS.Dz hz) (hsecint z hz)
    refine MeasureTheory.Integrable.mono'
      ((Work.FTS.EllipticEst.remov.ws_sEta_integrableOn.const_mul (M ^ 2))) ?_ ?_
    · exact ((Work.FTS.EllipticEst.remov.ws_aesm_slice (hS.Dz.pth) hz).pow 2).mul
        (Work.FTS.EllipticEst.remov.ws_sEta_integrableOn.aestronglyMeasurable)
    · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Icc (fun θ hθ => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (sq_nonneg _) (sEta_nonneg_Iθ hθ))]
      by_cases hθ' : θ ∈ Set.Ioo 0 (Real.pi / 2)
      · have hb : |deriv (fun θ' => Work.Spaces.Dz u z θ') θ| ≤ M := (hM θ hθ').2
        have h2 : (deriv (fun θ' => Work.Spaces.Dz u z θ') θ) ^ 2 ≤ M ^ 2 := by
          rw [← sq_abs (deriv (fun θ' => Work.Spaces.Dz u z θ') θ)]
          exact pow_le_pow_left₀ (abs_nonneg _) hb 2
        have heq : Work.Spaces.pth (Work.Spaces.Dz u) z θ
            = deriv (fun θ' => Work.Spaces.Dz u z θ') θ := rfl
        rw [heq]
        exact mul_le_mul_of_nonneg_right h2 (sEta_nonneg_Iθ hθ)
      · have hsin0 : Real.sin (2 * θ) = 0 := by
          have h1 : θ = 0 ∨ θ = Real.pi / 2 := by
            by_contra hcon
            push_neg at hcon
            exact hθ' ⟨lt_of_le_of_ne hθ.1 (Ne.symm hcon.1), lt_of_le_of_ne hθ.2 hcon.2⟩
          rcases h1 with h1 | h1
          · rw [h1, mul_zero, Real.sin_zero]
          · rw [h1, show 2 * (Real.pi / 2) = Real.pi by ring, Real.sin_pi]
        rw [sEta_eq_zero_of_sin_eq_zero hsin0]
        simp
  -- (2) the slicewise Agmon bound
  have hagm : ∀ z, 0 < z →
      (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pth (Work.Spaces.Dz u) z θ) ^ 2
          * Work.FTS.EllipticEst.sEta θ)
        ≤ C * ((∫ θ in Work.Spaces.Iθ,
              (z * Work.Spaces.pz (Work.Spaces.pthIter 2 u) z θ) ^ 2
                * Work.FTS.EllipticEst.sEta θ)
            + (∫ θ in Work.Spaces.Iθ, (Work.Spaces.Dz u z θ) ^ 2
                * Work.FTS.EllipticEst.sEta θ)) := by
    intro z hz
    have hbase : MeasureTheory.IntegrableOn
        (fun θ => (Work.Spaces.Dz u z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        Work.Spaces.Iθ :=
      Work.FTS.EllipticEst.H2W.AeLeftClean.hkMemSliceSqSigma hU hz
    have hkey := hCagm (fun θ => Work.Spaces.Dz u z θ)
      (Work.FTS.EllipticEst.remov.ws_contDiffOn_slice hS.Dz hz) (hsecint z hz) hbase
    have h1 : (∫ θ in Work.Spaces.Iθ,
          (deriv (fun θ' => Work.Spaces.Dz u z θ') θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        = ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pth (Work.Spaces.Dz u) z θ) ^ 2
            * Work.FTS.EllipticEst.sEta θ := rfl
    have h2 : (∫ θ in Work.Spaces.Iθ,
          (deriv (deriv (fun θ' => Work.Spaces.Dz u z θ')) θ) ^ 2
            * Work.FTS.EllipticEst.sEta θ)
        = ∫ θ in Work.Spaces.Iθ,
            (z * Work.Spaces.pz (Work.Spaces.pthIter 2 u) z θ) ^ 2
              * Work.FTS.EllipticEst.sEta θ := by
      refine MeasureTheory.setIntegral_congr_fun measurableSet_Icc (fun θ hθ => ?_)
      by_cases hθ' : θ ∈ Set.Ioo 0 (Real.pi / 2)
      · rw [slice_second_deriv_eq_Dz u hS hz hθ']
      · have hsin0 : Real.sin (2 * θ) = 0 := by
          have h1' : θ = 0 ∨ θ = Real.pi / 2 := by
            by_contra hcon
            push_neg at hcon
            exact hθ' ⟨lt_of_le_of_ne hθ.1 (Ne.symm hcon.1), lt_of_le_of_ne hθ.2 hcon.2⟩
          rcases h1' with h1' | h1'
          · rw [h1', mul_zero, Real.sin_zero]
          · rw [h1', show 2 * (Real.pi / 2) = Real.pi by ring, Real.sin_pi]
        rw [sEta_eq_zero_of_sin_eq_zero hsin0]
        ring
    have hkey' : (∫ θ in Work.Spaces.Iθ,
          (deriv (fun θ' => Work.Spaces.Dz u z θ') θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
        ≤ C * ((∫ θ in Work.Spaces.Iθ,
              (deriv (deriv (fun θ' => Work.Spaces.Dz u z θ')) θ) ^ 2
                * Work.FTS.EllipticEst.sEta θ)
            + (∫ θ in Work.Spaces.Iθ, (Work.Spaces.Dz u z θ) ^ 2
                * Work.FTS.EllipticEst.sEta θ)) := by
      simpa only [Work.FTS.EllipticEst.sEta] using hkey
    rw [h1, h2] at hkey'
    exact hkey'
  -- (3) continuity of the `HkIntegrand` of the mixed slot on the open quadrant
  have hcont : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.HkIntegrand α 0
      (fun z θ => z * Work.Spaces.pth (Work.Spaces.pz u) z θ) p.1 p.2)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
    have hVcont : ContinuousOn (fun p : ℝ × ℝ =>
        p.1 * Work.Spaces.pth (Work.Spaces.pz u) p.1 p.2)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
      (continuous_fst.continuousOn).mul ((hS.pz.pth).continuousOn)
    have hquot : ContinuousOn (fun p : ℝ × ℝ =>
        Work.Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2))
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := by
      have hsinpos : ∀ p : ℝ × ℝ, p ∈ Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2) →
          (0 : ℝ) < Real.sin (2 * p.2) := by
        intro p hp
        obtain ⟨-, hp2⟩ := Set.mem_prod.mp hp
        exact Real.sin_pos_of_pos_of_lt_pi (by linarith [hp2.1])
          (by linarith [hp2.2, Real.pi_pos])
      refine ContinuousOn.div ?_ ?_ ?_
      · show ContinuousOn (fun p : ℝ × ℝ => (1 + p.1) ^ 2 / p.1 ^ 2)
            (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2))
        exact ((continuous_fst.continuousOn.const_add 1).pow 2).div
          ((continuous_fst.continuousOn).pow 2)
          (fun p hp => pow_ne_zero 2 (ne_of_gt (Set.mem_Ioi.mp (Set.mem_prod.mp hp).1)))
      · have hsin2 : ContinuousOn (fun p : ℝ × ℝ => Real.sin (2 * p.2))
            (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) :=
          (Real.continuous_sin.comp (continuous_const.mul
            (continuous_snd : Continuous (fun p : ℝ × ℝ => p.2)))).continuousOn
        exact hsin2.rpow_const (fun p hp => Or.inl (ne_of_gt (hsinpos p hp)))
      · intro p hp
        exact ne_of_gt (Real.rpow_pos_of_pos (hsinpos p hp) _)
    have hmain : ContinuousOn (fun p : ℝ × ℝ =>
        ((fun z θ => z * Work.Spaces.pth (Work.Spaces.pz u) z θ) p.1 p.2
          * (Work.Spaces.w p.1 / (Real.sin (2 * p.2)) ^ (Work.Spaces.eta / 2))) ^ 2)
        (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)) := (hVcont.mul hquot).pow 2
    refine hmain.congr ?_
    intro p _
    exact HkIntegrand_zero_pt α (fun z θ => z * Work.Spaces.pth (Work.Spaces.pz u) z θ) p.1 p.2
  -- (4) assemble
  refine Work.FTS.EllipticEst.H2W.Radial.hkMem_of_ae_slice_bound
    (g := fun z θ => z * Work.Spaces.pth (Work.Spaces.pz u) z θ)
    (Ψ := fun z θ => z * Work.Spaces.pz (Work.Spaces.pthIter 2 u) z θ)
    (L := Work.Spaces.Dz u) (K := C) hCpos hcont ?_ ?_ hH ?_
  · intro z hz
    exact (hsliceDz z hz).congr_fun
      (fun θ _ => by
        show (Work.Spaces.pth (Work.Spaces.Dz u) z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ
            = (z * Work.Spaces.pth (Work.Spaces.pz u) z θ) ^ 2
              * Work.FTS.EllipticEst.sEta θ
        rw [← grad_pth_eq_Dz_pth u z θ]) measurableSet_Icc
  · intro z hz
    have h := hagm z hz
    have h' : (∫ θ in Work.Spaces.Iθ, (Work.Spaces.pth (Work.Spaces.Dz u) z θ) ^ 2
          * Work.FTS.EllipticEst.sEta θ)
        = ∫ θ in Work.Spaces.Iθ, (z * Work.Spaces.pth (Work.Spaces.pz u) z θ) ^ 2
            * Work.FTS.EllipticEst.sEta θ :=
      MeasureTheory.setIntegral_congr_fun measurableSet_Icc
        (fun θ _ => by
          show (Work.Spaces.pth (Work.Spaces.Dz u) z θ) ^ 2 * Work.FTS.EllipticEst.sEta θ
              = (z * Work.Spaces.pth (Work.Spaces.pz u) z θ) ^ 2
                * Work.FTS.EllipticEst.sEta θ
          rw [← grad_pth_eq_Dz_pth u z θ])
    rw [h'] at h
    exact h
  · exact hU

/-! ## The main theorem -/

theorem aeHtermOpen : ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (u G : ℝ → ℝ → ℝ),
    Work.FTS.EllipticEst.H2W.Ae.AeData α u G →
    Work.Spaces.HkMem α 0 (Work.FTS.EllipticEst.H2W.Ae.grad u) →
    Work.Spaces.HkMem α 0 (fun z θ => z * Work.Spaces.pz (Work.Spaces.pthIter 2 u) z θ) →
    Work.FTS.EllipticEst.AngSecond.IP (Work.FTS.EllipticEst.H2W.Ae.grad u)
        (fun z θ => z * Work.Spaces.pz (Work.Spaces.pthIter 2 u) z θ)
      ≤ - ((1 - Work.Spaces.eta) / (1 + Work.Spaces.eta)) * Work.Spaces.HkSq α 0
            (Work.Spaces.pth (Work.FTS.EllipticEst.H2W.Ae.grad u))
        + C * Work.FTS.EllipticEst.AngSecond.IP (Work.FTS.EllipticEst.H2W.Ae.grad u)
            (Work.FTS.EllipticEst.H2W.Ae.grad u) := by
  classical
  refine ⟨2 * Work.Spaces.eta, by linarith [Work.Spaces.eta_pos], ?_⟩
  intro α u G hAe hU hH
  have hS : Work.FTS.EllipticEst.SmoothOpen u :=
    Work.FTS.EllipticEst.smoothOpen_of_forall hAe.smooth
  -- (1) the mixed-derivative honesty and the honesty of the pairing
  have hV : Work.Spaces.HkMem α 0 (fun z θ => z * Work.Spaces.pth (Work.Spaces.pz u) z θ) :=
    mixedHkMem_aux hAe hU hH
  have hW : Work.Spaces.HkMem α 0 (Work.Spaces.pth (Work.FTS.EllipticEst.H2W.Ae.grad u)) := by
    have hfe : (fun z θ => z * Work.Spaces.pth (Work.Spaces.pz u) z θ)
        = Work.Spaces.pth (Work.FTS.EllipticEst.H2W.Ae.grad u) := by
      funext z θ; exact (pth_grad_eq u z θ).symm
    rw [← hfe]
    exact hV
  have hIP : Work.FTS.EllipticEst.AngSecond.IPMem (Work.FTS.EllipticEst.H2W.Ae.grad u)
      (fun z θ => z * Work.Spaces.pz (Work.Spaces.pthIter 2 u) z θ) :=
    ipMemUHtermFts α u G hAe hU hH
  -- (2) the traces of the slices of `U = z∂_zu` vanish a.e.
  have htr := AeI1.aeDzTraceHk α u G hAe hU hV
  -- (3) the three slice integrals
  set A : ℝ → ℝ := fun z => ∫ θ in Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 0 (Work.Spaces.pth (Work.FTS.EllipticEst.H2W.Ae.grad u)) z θ
    with hA
  set B : ℝ → ℝ := fun z => ∫ θ in Work.Spaces.Iθ,
      Work.Spaces.HkIntegrand α 0 (Work.FTS.EllipticEst.H2W.Ae.grad u) z θ with hB
  set D : ℝ → ℝ := fun z => ∫ θ in Work.Spaces.Iθ,
      Work.FTS.EllipticEst.H2W.Ae.grad u z θ
        * (fun z θ => z * Work.Spaces.pz (Work.Spaces.pthIter 2 u) z θ) z θ
        * Work.FTS.EllipticEst.AngSecond.w2 z * Work.FTS.EllipticEst.AngSecond.sig θ with hD
  -- (4) integrability of the three
  have hIntA : MeasureTheory.IntegrableOn A Work.Spaces.Iz := by
    have h := hW.2
    simpa only [hA] using h
  have hIntB : MeasureTheory.IntegrableOn B Work.Spaces.Iz := by
    have h := hU.2
    simpa only [hB] using h
  have hIntD : MeasureTheory.IntegrableOn D Work.Spaces.Iz := by
    have h := hIP.2
    simpa only [hD] using h
  -- (5) the slicewise inequality, almost everywhere in `z`
  have haeslice : ∀ᵐ z ∂(MeasureTheory.volume.restrict Work.Spaces.Iz),
      D z ≤ -((1 - Work.Spaces.eta) / (1 + Work.Spaces.eta)) * A z
        + (2 * Work.Spaces.eta) * B z := by
    refine (MeasureTheory.ae_restrict_congr_set (s := Set.Ioi (0 : ℝ)) (t := Set.Ici (0 : ℝ))
      (MeasureTheory.Ioi_ae_eq_Ici (μ := MeasureTheory.volume) (a := (0 : ℝ)))).mp ?_
    filter_upwards [htr, MeasureTheory.self_mem_ae_restrict measurableSet_Ioi] with z htz hzpos
    set f : ℝ → ℝ := fun θ => Work.FTS.EllipticEst.H2W.Ae.grad u z θ with hf
    have hfun : (fun θ => Work.Spaces.Dz u z θ) = f := by
      funext θ; rw [hf]; rfl
    have hfcd : ContDiffOn ℝ 2 f (Set.Ioo 0 (Real.pi / 2)) := by
      have h := Work.FTS.EllipticEst.remov.ws_contDiffOn_slice hS.Dz hzpos
      rwa [hfun] at h
    have hfun2 : (fun θ => z * Work.Spaces.pz u z θ) = f := by
      funext θ; rw [hf]; rfl
    have ht0 : Filter.Tendsto f (nhdsWithin (0 : ℝ) (Set.Ioi 0)) (nhds 0) := by
      have h := htz.1
      rwa [hfun2] at h
    have htπ : Filter.Tendsto f (nhdsWithin (Real.pi / 2) (Set.Iio (Real.pi / 2))) (nhds 0) := by
      have h := htz.2
      rwa [hfun2] at h
    have hderiv : ∀ θ ∈ Set.Ioo 0 (Real.pi / 2),
        deriv (deriv f) θ = z * Work.Spaces.pz (Work.Spaces.pthIter 2 u) z θ := by
      intro θ hθ
      have h := slice_second_deriv_eq u hS hzpos hθ
      rw [hf]
      exact h
    have h2 : MeasureTheory.IntegrableOn
        (fun θ => (deriv (deriv f) θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
        Work.Spaces.Iθ := by
      have hbase : MeasureTheory.IntegrableOn
          (fun θ => (z * Work.Spaces.pz (Work.Spaces.pthIter 2 u) z θ) ^ 2
            * Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ :=
        Work.FTS.EllipticEst.H2W.AeLeftClean.hkMemSliceSqSigma hH hzpos
      refine hbase.congr_fun (fun θ hθ => ?_) measurableSet_Icc
      by_cases hsin : Real.sin (2 * θ) = 0
      · have hz0 : Work.FTS.EllipticEst.sEta θ = 0 := sEta_eq_zero_of_sin_eq_zero hsin
        have hz1 : (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)) = 0 := by
          rw [hsin]
          exact Real.zero_rpow (by rw [Work.Spaces.eta]; norm_num)
        change (z * Work.Spaces.pz (Work.Spaces.pthIter 2 u) z θ) ^ 2
            * Work.FTS.EllipticEst.sEta θ
          = deriv (deriv f) θ ^ 2 * Real.sin (2 * θ) ^ (-(Work.Spaces.eta))
        rw [hz0, hz1, mul_zero, mul_zero]
      · have hθ' : θ ∈ Set.Ioo 0 (Real.pi / 2) := by
          refine ⟨?_, ?_⟩
          · rcases lt_or_ge 0 θ with h | h
            · exact h
            · exfalso
              have hθ0 : θ = 0 := le_antisymm h hθ.1
              rw [hθ0] at hsin
              rw [show (2 : ℝ) * 0 = 0 by norm_num, Real.sin_zero] at hsin
              exact hsin rfl
          · rcases lt_or_ge θ (Real.pi / 2) with h | h
            · exact h
            · exfalso
              have hθπ : θ = Real.pi / 2 := le_antisymm hθ.2 h
              rw [hθπ] at hsin
              rw [show (2 : ℝ) * (Real.pi / 2) = Real.pi by ring, Real.sin_pi] at hsin
              exact hsin rfl
        rw [hderiv θ hθ']
        rfl
    -- the bounds and the sharp one-dimensional inequality
    obtain ⟨M, hM0, hMb, hMd⟩ := sliceBoundsOfTraceFts hfcd ht0 htπ h2
    have hsharp := sliceSharpFts hfcd ⟨M, hM0, hMb, hMd⟩ h2
    have hsharp' : (∫ θ in Work.Spaces.Iθ,
          f θ * deriv (deriv f) θ * Work.FTS.EllipticEst.sEta θ)
        ≤ -((1 - Work.Spaces.eta) / (1 + Work.Spaces.eta))
            * (∫ θ in Work.Spaces.Iθ, (deriv f θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
          + (2 * Work.Spaces.eta)
            * (∫ θ in Work.Spaces.Iθ, (f θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) := by
      simpa only [Work.FTS.EllipticEst.sEta] using hsharp
    -- the three slice integrals in the `σ`-form
    have eD : D z = Work.FTS.EllipticEst.AngSecond.w2 z
        * (∫ θ in Work.Spaces.Iθ,
            f θ * deriv (deriv f) θ * Work.FTS.EllipticEst.sEta θ) := by
      simp only [hD]
      rw [integral_pairing_eq u hS hzpos]
    have eA : A z = Work.FTS.EllipticEst.AngSecond.w2 z
        * (∫ θ in Work.Spaces.Iθ, (deriv f θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) := by
      simp only [hA]
      rw [integral_HkIntegrand_zero_eq, hf]
      refine congrArg (fun t => Work.FTS.EllipticEst.AngSecond.w2 z * t) ?_
      exact MeasureTheory.setIntegral_congr_fun measurableSet_Icc
        (fun θ _ => by simp only [Work.Spaces.pth])
    have eB : B z = Work.FTS.EllipticEst.AngSecond.w2 z
        * (∫ θ in Work.Spaces.Iθ, (f θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) := by
      simp only [hB]
      rw [integral_HkIntegrand_zero_eq, hf]
    rw [eD, eA, eB]
    calc Work.FTS.EllipticEst.AngSecond.w2 z
          * (∫ θ in Work.Spaces.Iθ, f θ * deriv (deriv f) θ * Work.FTS.EllipticEst.sEta θ)
        ≤ Work.FTS.EllipticEst.AngSecond.w2 z
            * (-((1 - Work.Spaces.eta) / (1 + Work.Spaces.eta))
                * (∫ θ in Work.Spaces.Iθ, (deriv f θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
              + (2 * Work.Spaces.eta)
                * (∫ θ in Work.Spaces.Iθ, (f θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)) :=
          mul_le_mul_of_nonneg_left hsharp' (Work.FTS.EllipticEst.AngSecond.w2_nonneg z)
      _ = -((1 - Work.Spaces.eta) / (1 + Work.Spaces.eta))
            * (Work.FTS.EllipticEst.AngSecond.w2 z
              * ∫ θ in Work.Spaces.Iθ, (deriv f θ) ^ 2 * Work.FTS.EllipticEst.sEta θ)
          + (2 * Work.Spaces.eta) * (Work.FTS.EllipticEst.AngSecond.w2 z
              * ∫ θ in Work.Spaces.Iθ, (f θ) ^ 2 * Work.FTS.EllipticEst.sEta θ) := by
          ring
  -- (6) integrate in `z`
  have hIntR : MeasureTheory.IntegrableOn
      (fun z => -((1 - Work.Spaces.eta) / (1 + Work.Spaces.eta)) * A z
        + (2 * Work.Spaces.eta) * B z) Work.Spaces.Iz :=
    (hIntA.const_mul (-((1 - Work.Spaces.eta) / (1 + Work.Spaces.eta)))).add
      (hIntB.const_mul (2 * Work.Spaces.eta))
  have hmono : (∫ z in Work.Spaces.Iz, D z)
      ≤ ∫ z in Work.Spaces.Iz, (-((1 - Work.Spaces.eta) / (1 + Work.Spaces.eta)) * A z
          + (2 * Work.Spaces.eta) * B z) :=
    MeasureTheory.integral_mono_ae hIntD hIntR haeslice
  have hsplit : (∫ z in Work.Spaces.Iz, (-((1 - Work.Spaces.eta) / (1 + Work.Spaces.eta)) * A z
        + (2 * Work.Spaces.eta) * B z))
      = -((1 - Work.Spaces.eta) / (1 + Work.Spaces.eta)) * (∫ z in Work.Spaces.Iz, A z)
        + (2 * Work.Spaces.eta) * (∫ z in Work.Spaces.Iz, B z) := by
    rw [MeasureTheory.integral_add
        (hIntA.const_mul (-((1 - Work.Spaces.eta) / (1 + Work.Spaces.eta))))
        (hIntB.const_mul (2 * Work.Spaces.eta)),
      MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
  have hAeq : (∫ z in Work.Spaces.Iz, A z)
      = Work.Spaces.HkSq α 0 (Work.Spaces.pth (Work.FTS.EllipticEst.H2W.Ae.grad u)) := by
    rw [Work.Spaces.HkSq, hA]
  have hBeq : (∫ z in Work.Spaces.Iz, B z)
      = Work.Spaces.HkSq α 0 (Work.FTS.EllipticEst.H2W.Ae.grad u) := by
    rw [Work.Spaces.HkSq, hB]
  have hIPeq : Work.FTS.EllipticEst.AngSecond.IP (Work.FTS.EllipticEst.H2W.Ae.grad u)
      (fun z θ => z * Work.Spaces.pz (Work.Spaces.pthIter 2 u) z θ)
      = ∫ z in Work.Spaces.Iz, D z := by
    rw [Work.FTS.EllipticEst.AngSecond.IP, hD]
  calc Work.FTS.EllipticEst.AngSecond.IP (Work.FTS.EllipticEst.H2W.Ae.grad u)
        (fun z θ => z * Work.Spaces.pz (Work.Spaces.pthIter 2 u) z θ)
      = ∫ z in Work.Spaces.Iz, D z := hIPeq
    _ ≤ ∫ z in Work.Spaces.Iz, (-((1 - Work.Spaces.eta) / (1 + Work.Spaces.eta)) * A z
          + (2 * Work.Spaces.eta) * B z) := hmono
    _ = -((1 - Work.Spaces.eta) / (1 + Work.Spaces.eta)) * (∫ z in Work.Spaces.Iz, A z)
          + (2 * Work.Spaces.eta) * (∫ z in Work.Spaces.Iz, B z) := hsplit
    _ = -((1 - Work.Spaces.eta) / (1 + Work.Spaces.eta))
          * Work.Spaces.HkSq α 0 (Work.Spaces.pth (Work.FTS.EllipticEst.H2W.Ae.grad u))
        + (2 * Work.Spaces.eta)
          * Work.FTS.EllipticEst.AngSecond.IP (Work.FTS.EllipticEst.H2W.Ae.grad u)
              (Work.FTS.EllipticEst.H2W.Ae.grad u) := by
        rw [hAeq, hBeq,
          Work.FTS.EllipticEst.Dispatch.HkSq_zero_eq_IP α (Work.FTS.EllipticEst.H2W.Ae.grad u)]

end Work.FTS.EllipticEst.TT
