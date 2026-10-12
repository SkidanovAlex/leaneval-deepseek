import Mathlib.Tactic.Have
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BSKinetic.dSpace_eq_dBox_of_supp
import Submission.Work.BSKinetic.integrable_kinFT_sq
import Submission.Work.BSKinetic.kinFT_energy_sum
import Submission.Work.BSKinetic.kinWord_eq_slotSum
import Submission.Work.BSKinetic.plancherel_pconv
import Submission.Work.BSKinetic.tBwordKinBigU_eq_slotSum
import Submission.Work.SmallBoxTBWord.integrable_kinFT_energy_cspt
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.BSKinetic

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

open Submission.BoseGases

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option linter.unusedVariables false

/-! ## 1. The slot fibre of a box-supported state -/

lemma fibre_contDiff {n : ℕ} {Φ : X (n + 1) → ℝ} (hΦ : ContDiff ℝ (⊤ : ENat) Φ)
    (i : Fin (n + 1)) (r : X n) :
    ContDiff ℝ (⊤ : ENat) (fun z : ℝ³ => Φ (kcInsN n i (z, r))) :=
  hΦ.comp (Work.SmallBoxBridge.Fourier.contDiff_kcInsN_right i r)

lemma fibre_supp {ℓ : ℝ} (n : ℕ) {Φ : X (n + 1) → ℝ} (hsupp : SuppInBox (n + 1) ℓ Φ)
    (i : Fin (n + 1)) (r : X n) :
    ∀ z : ℝ³, z ∉ acube ℓ → Φ (kcInsN n i (z, r)) = 0 :=
  fun z hz => hsupp _ ⟨i, by rwa [kc_insN_apply_same]⟩

lemma fibre_hasCompactSupport {ℓ : ℝ} (hℓ : 0 < ℓ) (n : ℕ) {Φ : X (n + 1) → ℝ}
    (hsupp : SuppInBox (n + 1) ℓ Φ) (i : Fin (n + 1)) (r : X n) :
    HasCompactSupport (fun z : ℝ³ => Φ (kcInsN n i (z, r))) := by
  refine IsCompact.of_isClosed_subset (acube_compact hℓ) (isClosed_tsupport _) ?_
  refine closure_minimal ?_ (acube_isClosed ℓ)
  intro z hz
  by_contra hcon
  exact hz (fibre_supp n hsupp i r z hcon)

lemma fibre_eq_zero_of_not_mem_abox {ℓ : ℝ} (n : ℕ) {Φ : X (n + 1) → ℝ}
    (hsupp : SuppInBox (n + 1) ℓ Φ) (i : Fin (n + 1)) {r : X n} (hr : r ∉ abox n ℓ) :
    ∀ z : ℝ³, Φ (kcInsN n i (z, r)) = 0 := by
  intro z
  have hr' : ¬ (∀ j : Fin n, r j ∈ acube ℓ) := hr
  rcases not_forall.mp hr' with ⟨j, hj⟩
  exact hsupp _ ⟨i.succAbove j, by rw [kc_insN_apply_succ]; exact hj⟩

lemma mem_abox_kcInsN {n : ℕ} {ℓ : ℝ} (i : Fin (n + 1)) {r : X n}
    (hr : r ∈ abox n ℓ) {z : ℝ³} (hz : z ∈ acube ℓ) :
    kcInsN n i (z, r) ∈ abox (n + 1) ℓ := by
  intro j
  by_cases hj : j = i
  · subst hj; rwa [kc_insN_apply_same]
  · rcases Fin.exists_succAbove_eq hj with ⟨j', rfl⟩
    rw [kc_insN_apply_succ]; exact hr j'

lemma bsOneBody_nonneg' {ℓ : ℝ} {F : ℝ → ℝ} (hF : ∀ t, 0 ≤ F t) (u : ℝ³) (ψ : ℝ³ → ℝ) :
    0 ≤ bsOneBody ℓ F u ψ := by
  unfold bsOneBody
  refine mul_nonneg (inv_nonneg.mpr (by positivity)) ?_
  exact integral_nonneg fun p => mul_nonneg (hF ‖p‖) (sq_nonneg _)

lemma bsWin_hasCompactSupport {ℓ : ℝ} (hℓ : 0 < ℓ) (u : ℝ³) :
    HasCompactSupport (bsWin ℓ u) := by
  have h : bsWin ℓ u = chiScale ℓ ∘ ⇑(Homeomorph.subRight (ℓ • u)) := rfl
  rw [h]
  exact (chiScale_hasCompactSupport (ne_of_gt hℓ)).comp_homeomorph _

/-! ## 2. The symbol bound and the weighted `p`-form estimate -/

lemma fsKinCoeff_le_quadratic (c t : ℝ) (ht : 0 ≤ t) :
    fsKinCoeff c t ≤ 2 * (1 + c ^ 2) * (1 + t ^ 2) := by
  rw [fsKinCoeff]
  have h1 : max (t - c) 0 ≤ t + |c| := by
    refine max_le ?_ ?_
    · have := neg_le_abs c; linarith
    · positivity
  have h2 : (t + |c|) ^ 2 ≤ 2 * (1 + c ^ 2) * (1 + t ^ 2) := by
    have hc := sq_abs c
    nlinarith [sq_nonneg (t - |c|), sq_nonneg t, abs_nonneg c, ht]
  exact le_trans (pow_le_pow_left₀ (le_max_right _ _) h1 2) h2

lemma bsOneBody_le_weighted {ℓ c : ℝ} (hℓ : 0 < ℓ) (u : ℝ³) {ψ : ℝ³ → ℝ}
    (hψ : ContDiff ℝ (⊤ : ENat) ψ) (hcs : HasCompactSupport ψ) :
    bsOneBody ℓ (fsKinCoeff c) u ψ ≤ 2 * (1 + c ^ 2) *
      ((∫ z : ℝ³, (bsWin ℓ u z * bsQ ℓ u ψ z) ^ 2)
        + ∑ k : Fin 3, ∫ z : ℝ³, (fderiv ℝ (fun y : ℝ³ => bsWin ℓ u y * bsQ ℓ u ψ y) z
            (kcStdBasis k)) ^ 2) := by
  set h : ℝ³ → ℝ := fun z => bsWin ℓ u z * bsQ ℓ u ψ z with hh
  have hQcd : ContDiff ℝ (⊤ : ENat) (bsQ ℓ u ψ) := by
    have h' : bsQ ℓ u ψ = fun z : ℝ³ => ψ z - bsMean ℓ u ψ := rfl
    rw [h']; exact hψ.sub contDiff_const
  have hWcd : ContDiff ℝ (⊤ : ENat) (bsWin ℓ u) := by
    have h' : bsWin ℓ u = fun z : ℝ³ => chiScale ℓ (z - ℓ • u) := rfl
    rw [h']
    exact (chiScale_contDiff (ne_of_gt hℓ)).comp (contDiff_id.sub contDiff_const)
  have hcd : ContDiff ℝ (⊤ : ENat) h := by rw [hh]; exact hWcd.mul hQcd
  have hcs' : HasCompactSupport h := by
    rw [hh]; exact HasCompactSupport.mul_right (bsWin_hasCompactSupport hℓ u)
  have hcomplex : (fun z : ℝ³ => (bsWin ℓ u z : ℂ) * (bsQ ℓ u ψ z : ℂ)) = fun z => (h z : ℂ) := by
    funext z; rw [hh, Complex.ofReal_mul]
  have hPl := plancherel_pconv h hcd hcs'
  have hEn := kinFT_energy_sum h hcd hcs'
  have hI1 : Integrable (fun p : ℝ³ => ‖kinFT (fun z : ℝ³ => (h z : ℂ)) p‖ ^ 2) :=
    integrable_kinFT_sq h hcd hcs'
  have hI2 : Integrable (fun p : ℝ³ => ‖p‖ ^ 2 * ‖kinFT (fun z : ℝ³ => (h z : ℂ)) p‖ ^ 2) :=
    Work.SmallBoxTBWord.integrable_kinFT_energy_cspt h hcd hcs'
  have hIg : Integrable (fun p : ℝ³ => 2 * (1 + c ^ 2) *
      (‖kinFT (fun z : ℝ³ => (h z : ℂ)) p‖ ^ 2
        + ‖p‖ ^ 2 * ‖kinFT (fun z : ℝ³ => (h z : ℂ)) p‖ ^ 2)) :=
    (hI1.add hI2).const_mul _
  have hpt : ∀ p : ℝ³, fsKinCoeff c ‖p‖ * ‖kinFT (fun z : ℝ³ => (h z : ℂ)) p‖ ^ 2
      ≤ 2 * (1 + c ^ 2) * (‖kinFT (fun z : ℝ³ => (h z : ℂ)) p‖ ^ 2
          + ‖p‖ ^ 2 * ‖kinFT (fun z : ℝ³ => (h z : ℂ)) p‖ ^ 2) := by
    intro p
    have hb := fsKinCoeff_le_quadratic c ‖p‖ (norm_nonneg p)
    have hA : (0:ℝ) ≤ ‖kinFT (fun z : ℝ³ => (h z : ℂ)) p‖ ^ 2 := sq_nonneg _
    have hB : (0:ℝ) ≤ ‖p‖ ^ 2 := sq_nonneg _
    nlinarith [hb, hA, hB, fsKinCoeff_nonneg c ‖p‖]
  have hmono := integral_mono_of_nonneg
    (Eventually.of_forall fun p => mul_nonneg (fsKinCoeff_nonneg c ‖p‖) (sq_nonneg _))
    hIg (Eventually.of_forall hpt)
  have hsplit : (fun p : ℝ³ => (1 + ‖p‖ ^ 2) * ‖kinFT (fun z : ℝ³ => (h z : ℂ)) p‖ ^ 2)
      = fun p : ℝ³ => ‖kinFT (fun z : ℝ³ => (h z : ℂ)) p‖ ^ 2
          + ‖p‖ ^ 2 * ‖kinFT (fun z : ℝ³ => (h z : ℂ)) p‖ ^ 2 := by
    funext p; ring
  have hmain : ((2 * Real.pi) ^ 3)⁻¹ * (∫ p : ℝ³,
      (1 + ‖p‖ ^ 2) * ‖kinFT (fun z : ℝ³ => (h z : ℂ)) p‖ ^ 2)
      = (∫ z : ℝ³, (h z) ^ 2)
        + ∑ k : Fin 3, ∫ z : ℝ³, (fderiv ℝ h z (kcStdBasis k)) ^ 2 := by
    rw [hsplit, integral_add hI1 hI2, mul_add, hPl, hEn]
  have hstep : (∫ p : ℝ³, 2 * (1 + c ^ 2) * (‖kinFT (fun z : ℝ³ => (h z : ℂ)) p‖ ^ 2
          + ‖p‖ ^ 2 * ‖kinFT (fun z : ℝ³ => (h z : ℂ)) p‖ ^ 2))
      = 2 * (1 + c ^ 2) * ∫ p : ℝ³,
          (1 + ‖p‖ ^ 2) * ‖kinFT (fun z : ℝ³ => (h z : ℂ)) p‖ ^ 2 := by
    rw [hsplit, integral_const_mul]
  calc bsOneBody ℓ (fsKinCoeff c) u ψ
      = ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : ℝ³, fsKinCoeff c ‖p‖ *
          ‖kinFT (fun z : ℝ³ => (bsWin ℓ u z : ℂ) * (bsQ ℓ u ψ z : ℂ)) p‖ ^ 2 := rfl
    _ = ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : ℝ³, fsKinCoeff c ‖p‖ *
          ‖kinFT (fun z : ℝ³ => (h z : ℂ)) p‖ ^ 2 := by rw [hcomplex]
    _ ≤ ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : ℝ³, 2 * (1 + c ^ 2) *
          (‖kinFT (fun z : ℝ³ => (h z : ℂ)) p‖ ^ 2
            + ‖p‖ ^ 2 * ‖kinFT (fun z : ℝ³ => (h z : ℂ)) p‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hmono (by positivity)
    _ = 2 * (1 + c ^ 2) * (((2 * Real.pi) ^ 3)⁻¹ *
          ∫ p : ℝ³, (1 + ‖p‖ ^ 2) * ‖kinFT (fun z : ℝ³ => (h z : ℂ)) p‖ ^ 2) := by
        rw [hstep]; ring
    _ = 2 * (1 + c ^ 2) * ((∫ z : ℝ³, (h z) ^ 2)
          + ∑ k : Fin 3, ∫ z : ℝ³, (fderiv ℝ h z (kcStdBasis k)) ^ 2) := by rw [hmain]
    _ = 2 * (1 + c ^ 2) * ((∫ z : ℝ³, (bsWin ℓ u z * bsQ ℓ u ψ z) ^ 2)
          + ∑ k : Fin 3, ∫ z : ℝ³, (fderiv ℝ (fun y : ℝ³ => bsWin ℓ u y * bsQ ℓ u ψ y) z
              (kcStdBasis k)) ^ 2) := rfl

/-! ## 3. The uniform bound on the slot form -/

/-- The (moving) window-times-fibre product, seen as a one-body state on `ℝ³`. -/
private lemma fderiv_bsWin_mul_apply {ℓ : ℝ} (u x e : ℝ³) {ψ : ℝ³ → ℝ}
    (hψ : ContDiff ℝ (⊤ : ENat) ψ) :
    fderiv ℝ (fun y : ℝ³ => bsWin ℓ u y * ψ y) x e
      = bsWin ℓ u x * fderiv ℝ ψ x e
        + ψ x * fderiv ℝ (chiScale ℓ) (x - ℓ • u) e := by
  have hwin : DifferentiableAt ℝ (fun y : ℝ³ => bsWin ℓ u y) x := by
    have h' : (fun y : ℝ³ => bsWin ℓ u y) = fun y : ℝ³ => chiScale ℓ (y - ℓ • u) := rfl
    rw [h']
    exact ((Work.UBBInputs9.B.ChiDeriv.chiScale_contDiff_any ℓ).differentiable (by norm_num) _).comp
      x (by fun_prop)
  have hψd : DifferentiableAt ℝ ψ x := hψ.differentiable (by norm_num) x
  have hfd : fderiv ℝ (fun y : ℝ³ => bsWin ℓ u y * ψ y) x
      = bsWin ℓ u x • fderiv ℝ ψ x + ψ x • fderiv ℝ (fun y : ℝ³ => bsWin ℓ u y) x := by
    show fderiv ℝ ((fun y : ℝ³ => bsWin ℓ u y) * ψ) x = _
    exact fderiv_mul hwin hψd
  have hderiv : (fderiv ℝ (fun y : ℝ³ => bsWin ℓ u y) x) e
      = (fderiv ℝ (chiScale ℓ) (x - ℓ • u)) e :=
    Work.UBBInputs9.B.ChiDeriv.fderiv_chiScale_comp_sub_const ℓ (ℓ • u) x e
  rw [hfd, add_apply, smul_apply, smul_apply, smul_eq_mul, smul_eq_mul, hderiv]


/-! ## 4. Far vanishing of the slot form (the moving box leaves the support) -/

lemma norm_lt_of_mem_acube {ℓ : ℝ} (hℓ : 0 < ℓ) {z : ℝ³} (hz : z ∈ acube ℓ) :
    ‖z‖ < ℓ := by
  have hcomp : ∀ m : Fin 3, ‖z m‖ ≤ ℓ / 2 := by
    intro m
    have h := (mem_acube_iff ℓ z).mp hz m
    rw [Set.mem_Icc] at h
    rw [Real.norm_eq_abs, abs_le]
    exact ⟨by linarith [h.1], h.2⟩
  have hsq : ‖z‖ ^ 2 < ℓ ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    calc ∑ i : Fin 3, ‖z i‖ ^ 2 ≤ ∑ _i : Fin 3, (ℓ / 2) ^ 2 :=
          Finset.sum_le_sum (fun i _ => pow_le_pow_left₀ (norm_nonneg _) (hcomp i) 2)
      _ = 3 * (ℓ / 2) ^ 2 := by simp
      _ < ℓ ^ 2 := by nlinarith [sq_nonneg ℓ]
  have h2 := sq_lt_sq.mp hsq
  rw [abs_of_nonneg (norm_nonneg z), abs_of_nonneg hℓ.le] at h2
  exact h2

private lemma bsMean_eq_zero_of_far {ℓ R : ℝ} (hℓ : 0 < ℓ) {ψ : ℝ³ → ℝ}
    (hψ : ∀ x : ℝ³, R ≤ ‖x‖ → ψ x = 0) {u : ℝ³} (hu : R + ℓ ≤ ℓ * ‖u‖) :
    bsMean ℓ u ψ = 0 := by
  unfold bsMean
  have hzero : ∫ z in acube ℓ, ψ (ℓ • u + z) = 0 := by
    rw [show (∫ z in acube ℓ, ψ (ℓ • u + z)) = ∫ z in acube ℓ, (0 : ℝ) from
      setIntegral_congr_fun (acube_measurable ℓ) (fun z hz => ?_)]
    simp
    apply hψ
    have hzℓ : ‖z‖ ≤ ℓ := le_of_lt (norm_lt_of_mem_acube hℓ hz)
    have h1 : ‖ℓ • u‖ = ℓ * ‖u‖ := by rw [norm_smul, Real.norm_of_nonneg hℓ.le]
    have h2 : ‖ℓ • u‖ - ‖z‖ ≤ ‖ℓ • u + z‖ := by
      have h := norm_sub_le (ℓ • u + z) z
      simp only [add_sub_cancel_right] at h
      linarith
    calc R ≤ ℓ * ‖u‖ - ℓ := by linarith
      _ = ‖ℓ • u‖ - ℓ := by rw [h1]
      _ ≤ ‖ℓ • u‖ - ‖z‖ := by linarith
      _ ≤ ‖ℓ • u + z‖ := h2
  rw [hzero, mul_zero]

private lemma norm_ge_of_bsWin_ne_zero {ℓ R : ℝ} (hℓ : 0 < ℓ) {u z : ℝ³}
    (hu : R + ℓ ≤ ℓ * ‖u‖) (hz : bsWin ℓ u z ≠ 0) : R ≤ ‖z‖ := by
  have hsupp : ‖z - ℓ • u‖ ≤ ℓ / 2 := chiScale_support_le hℓ hz
  have hnormu : ‖ℓ • u‖ = ℓ * ‖u‖ := by rw [norm_smul, Real.norm_of_nonneg hℓ.le]
  have htri : ‖ℓ • u‖ ≤ ‖z‖ + ‖z - ℓ • u‖ := by
    have h := norm_add_le z (ℓ • u - z)
    rw [add_sub_cancel] at h
    rwa [norm_sub_rev (ℓ • u) z] at h
  have hzlb : ℓ * ‖u‖ - ℓ / 2 ≤ ‖z‖ := by
    have h := htri; rw [hnormu] at h; linarith
  linarith

private lemma bsOneBody_eq_zero_of_far {ℓ c : ℝ} (hℓ : 0 < ℓ) (n : ℕ)
    (Φ : X (n + 1) → ℝ) (hsupp : SuppInBox (n + 1) ℓ Φ) (i : Fin (n + 1)) (r : X n)
    {u : ℝ³} (hu : 2 ≤ ‖u‖) :
    bsOneBody ℓ (fsKinCoeff c) u (fun z : ℝ³ => Φ (kcInsN n i (z, r))) = 0 := by
  have hψfar : ∀ z : ℝ³, ℓ ≤ ‖z‖ → Φ (kcInsN n i (z, r)) = 0 := fun z hz =>
    fibre_supp n hsupp i r z
      (fun hcon => absurd hz (not_le.mpr (norm_lt_of_mem_acube hℓ hcon)))
  have hℓu : ℓ + ℓ ≤ ℓ * ‖u‖ := by
    have h : ℓ * 2 ≤ ℓ * ‖u‖ := mul_le_mul_of_nonneg_left hu hℓ.le
    linarith
  have hprod : (fun z : ℝ³ => (bsWin ℓ u z : ℂ) *
      (bsQ ℓ u (fun z : ℝ³ => Φ (kcInsN n i (z, r))) z : ℂ)) = fun _ => 0 := by
    funext z
    by_cases hz : bsWin ℓ u z = 0
    · rw [hz]; simp
    · have hznorm : ℓ ≤ ‖z‖ := norm_ge_of_bsWin_ne_zero hℓ hℓu hz
      have hψz : Φ (kcInsN n i (z, r)) = 0 := hψfar z hznorm
      have hm : bsMean ℓ u (fun z : ℝ³ => Φ (kcInsN n i (z, r))) = 0 :=
        bsMean_eq_zero_of_far hℓ hψfar hℓu
      simp only [bsQ, hψz, hm, sub_zero, mul_zero, Complex.ofReal_zero]
  rw [bsOneBody, hprod]
  simp [kinFT]

/-! ## 5. The uniform bound on the slot form -/

lemma exists_bound_bsOneBody_fibre {ℓ c : ℝ} (hℓ : 0 < ℓ) (n : ℕ)
    (Φ : X (n + 1) → ℝ) (hΦ : ContDiff ℝ (⊤ : ENat) Φ) (hsupp : SuppInBox (n + 1) ℓ Φ)
    (i : Fin (n + 1)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : ℝ³, ∀ r ∈ abox n ℓ,
      bsOneBody ℓ (fsKinCoeff c) u (fun z : ℝ³ => Φ (kcInsN n i (z, r))) ≤ C := by
  obtain ⟨S0, hS00, hS0⟩ : ∃ S0 : ℝ, 0 ≤ S0 ∧ ∀ x ∈ abox (n + 1) ℓ, |Φ x| ≤ S0 := by
    obtain ⟨C, hC⟩ := (abox_compact (n + 1) hℓ).exists_bound_of_continuousOn
      hΦ.continuous.continuousOn
    refine ⟨max C 0, le_max_right _ _, fun x hx => ?_⟩
    have h := hC x hx
    rw [Real.norm_eq_abs] at h
    exact le_trans h (le_max_left _ _)
  obtain ⟨S1, hS10, hS1⟩ : ∃ S1 : ℝ, 0 ≤ S1 ∧ ∀ x ∈ abox (n + 1) ℓ, ‖fderiv ℝ Φ x‖ ≤ S1 := by
    obtain ⟨C, hC⟩ := (abox_compact (n + 1) hℓ).exists_bound_of_continuousOn
      (hΦ.continuous_fderiv (by norm_num)).norm.continuousOn
    refine ⟨max C 0, le_max_right _ _, fun x hx => ?_⟩
    have h := hC x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] at h
    exact le_trans h (le_max_left _ _)
  set E0 : ℝ := ∫ z : ℝ³, (chiScale ℓ z) ^ 2 with hE0
  set Dk : Fin 3 → ℝ :=
    fun k => ∫ z : ℝ³, (fderiv ℝ (chiScale ℓ) z (kcStdBasis k)) ^ 2 with hDk
  set C0 : ℝ := 2 * (1 + c ^ 2) * (4 * S0 ^ 2 * E0
      + ∑ k : Fin 3, (8 * S0 ^ 2 * Dk k + 2 * S1 ^ 2 * E0)) with hC0
  refine ⟨max C0 0, le_max_right _ _, ?_⟩
  intro u r hr
  set ψ : ℝ³ → ℝ := fun z => Φ (kcInsN n i (z, r)) with hψ
  have hψsupp : ∀ z : ℝ³, z ∉ acube ℓ → ψ z = 0 := fun z hz => by
    show Φ (kcInsN n i (z, r)) = 0
    exact fibre_supp n hsupp i r z hz
  have hψcd : ContDiff ℝ (⊤ : ENat) ψ := fibre_contDiff hΦ i r
  have hψcs : HasCompactSupport ψ := fibre_hasCompactSupport hℓ n hsupp i r
  have hψabs : ∀ w : ℝ³, |ψ w| ≤ S0 := by
    intro w
    by_cases hw : w ∈ acube ℓ
    · show |Φ (kcInsN n i (w, r))| ≤ S0
      exact hS0 _ (mem_abox_kcInsN i hr hw)
    · rw [hψsupp w hw, abs_zero]; exact hS00
  have hvol : (volume : Measure ℝ³).real (acube ℓ) = ℓ ^ 3 := by
    rw [MeasureTheory.Measure.real_def, acube_volume ℓ hℓ.le, ENNReal.toReal_ofReal (by positivity)]
  have hm_bound : (bsMean ℓ u ψ) ^ 2 ≤ S0 ^ 2 := by
    rw [← sq_abs]
    refine pow_le_pow_left₀ (abs_nonneg _) ?_ 2
    rw [bsMean]
    have hIntAbs : ∫ z in acube ℓ, |ψ (ℓ • u + z)| ≤ ∫ z in acube ℓ, S0 := by
      have h1int : IntegrableOn (fun z : ℝ³ => |ψ (ℓ • u + z)|) (acube ℓ) volume :=
        ContinuousOn.integrableOn_compact (acube_compact hℓ)
          ((continuous_abs.comp (hψcd.continuous.comp
            (continuous_const.add continuous_id))).continuousOn)
      have h2int : IntegrableOn (fun _ : ℝ³ => S0) (acube ℓ) volume :=
        integrableOn_const (by rw [acube_volume ℓ hℓ.le]; exact ENNReal.ofReal_lt_top.ne) (by simp)
      exact setIntegral_mono_on h1int h2int (acube_measurable ℓ) (fun z _ => hψabs (ℓ • u + z))
    calc |(ℓ ^ 3)⁻¹ * ∫ z in acube ℓ, ψ (ℓ • u + z)|
        = (ℓ ^ 3)⁻¹ * |∫ z in acube ℓ, ψ (ℓ • u + z)| := by
          rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (ℓ ^ 3)⁻¹)]
      _ ≤ (ℓ ^ 3)⁻¹ * ∫ z in acube ℓ, |ψ (ℓ • u + z)| :=
          mul_le_mul_of_nonneg_left (MeasureTheory.abs_integral_le_integral_abs) (by positivity)
      _ ≤ (ℓ ^ 3)⁻¹ * ∫ z in acube ℓ, S0 :=
          mul_le_mul_of_nonneg_left hIntAbs (by positivity)
      _ = (ℓ ^ 3)⁻¹ * (ℓ ^ 3 * S0) := by
          rw [MeasureTheory.setIntegral_const, hvol, smul_eq_mul]
      _ = S0 := by field_simp
  have hm_abs : |bsMean ℓ u ψ| ≤ S0 := by
    have h : |bsMean ℓ u ψ| ^ 2 ≤ S0 ^ 2 := by
      rw [sq_abs]; exact hm_bound
    simpa [abs_of_nonneg hS00] using sq_le_sq.mp h
  have hbsQ_bound : ∀ z : ℝ³, (bsQ ℓ u ψ z) ^ 2 ≤ 4 * S0 ^ 2 := by
    intro z
    have hbsQ : bsQ ℓ u ψ z = ψ z - bsMean ℓ u ψ := rfl
    rw [hbsQ, ← sq_abs]
    calc (|ψ z - bsMean ℓ u ψ|) ^ 2 ≤ (2 * S0) ^ 2 := by
          refine pow_le_pow_left₀ (abs_nonneg _) ?_ 2
          calc |ψ z - bsMean ℓ u ψ| ≤ |ψ z| + |bsMean ℓ u ψ| := abs_sub _ _
            _ ≤ S0 + S0 := add_le_add (hψabs z) hm_abs
            _ = 2 * S0 := by ring
      _ = 4 * S0 ^ 2 := by ring
  have hL2 : ∫ z : ℝ³, (ψ z) ^ 2 ≤ S0 ^ 2 * ℓ ^ 3 := by
    have hset : ∫ z : ℝ³, (ψ z) ^ 2 = ∫ z in acube ℓ, (ψ z) ^ 2 :=
      (MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
        (s := acube ℓ) (f := fun z : ℝ³ => (ψ z) ^ 2)
        (fun z hz => by rw [hψsupp z hz]; simp)).symm
    rw [hset]
    calc ∫ z in acube ℓ, (ψ z) ^ 2 ≤ ∫ z in acube ℓ, S0 ^ 2 := by
          refine setIntegral_mono_on
            (ContinuousOn.integrableOn_compact (acube_compact hℓ) (hψcd.continuous.pow 2).continuousOn)
            (integrableOn_const (by rw [acube_volume ℓ hℓ.le]; exact ENNReal.ofReal_lt_top.ne)
              (by simp))
            (acube_measurable ℓ) (fun z _ => ?_)
          simpa only [sq_abs] using pow_le_pow_left₀ (abs_nonneg (ψ z)) (hψabs z) 2
      _ = S0 ^ 2 * ℓ ^ 3 := by
          rw [MeasureTheory.setIntegral_const, hvol, smul_eq_mul, mul_comm]
  have hψS1 : ∀ k : Fin 3, ∀ z : ℝ³, (fderiv ℝ ψ z (kcStdBasis k)) ^ 2 ≤ S1 ^ 2 := by
    intro k z
    rw [← sq_abs]
    by_cases hz : z ∈ acube ℓ
    · have hmem := mem_abox_kcInsN i hr hz
      have hd : fderiv ℝ ψ z (kcStdBasis k)
          = fderiv ℝ Φ (kcInsN n i (z, r)) (kcDir (n + 1) i k) := by
        show (fderiv ℝ (fun z : ℝ³ => Φ (kcInsN n i (z, r))) z) (kcStdBasis k) = _
        exact fiber_fderiv_kcDir i hΦ r z k
      rw [hd]
      refine pow_le_pow_left₀ (abs_nonneg _) ?_ 2
      calc |fderiv ℝ Φ (kcInsN n i (z, r)) (kcDir (n + 1) i k)|
          = ‖(fderiv ℝ Φ (kcInsN n i (z, r))) (kcDir (n + 1) i k)‖ := Real.norm_eq_abs _
        _ ≤ ‖fderiv ℝ Φ (kcInsN n i (z, r))‖ * ‖kcDir (n + 1) i k‖ :=
              (fderiv ℝ Φ (kcInsN n i (z, r))).le_opNorm _
        _ = ‖fderiv ℝ Φ (kcInsN n i (z, r))‖ := by rw [kc_norm_dir, mul_one]
        _ ≤ S1 := hS1 _ hmem
    · have hz' : fderiv ℝ ψ z = 0 :=
        fderiv_eq_zero_of_notMem_acube hψsupp z hz
      have hval : fderiv ℝ ψ z (kcStdBasis k) = 0 := by rw [hz']; rfl
      rw [hval]
      simpa using pow_le_pow_left₀ (le_refl (0:ℝ)) hS10 2
  have hDir : ∀ k : Fin 3, ∫ z : ℝ³, (fderiv ℝ ψ z (kcStdBasis k)) ^ 2 ≤ S1 ^ 2 * ℓ ^ 3 := by
    intro k
    have hset : ∫ z : ℝ³, (fderiv ℝ ψ z (kcStdBasis k)) ^ 2
        = ∫ z in acube ℓ, (fderiv ℝ ψ z (kcStdBasis k)) ^ 2 :=
      (MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
        (s := acube ℓ) (f := fun z : ℝ³ => (fderiv ℝ ψ z (kcStdBasis k)) ^ 2)
        (fun z hz => by
          have hz' : fderiv ℝ ψ z = 0 := fderiv_eq_zero_of_notMem_acube hψsupp z hz
          rw [hz', ContinuousLinearMap.zero_apply]; simp)).symm
    rw [hset]
    calc ∫ z in acube ℓ, (fderiv ℝ ψ z (kcStdBasis k)) ^ 2 ≤ ∫ z in acube ℓ, S1 ^ 2 := by
          refine setIntegral_mono_on
            (ContinuousOn.integrableOn_compact (acube_compact hℓ)
              (((hψcd.continuous_fderiv (by norm_num)).clm_apply continuous_const).pow 2).continuousOn)
            (integrableOn_const (by rw [acube_volume ℓ hℓ.le]; exact ENNReal.ofReal_lt_top.ne)
              (by simp))
            (acube_measurable ℓ) (fun z _ => hψS1 k z)
      _ = S1 ^ 2 * ℓ ^ 3 := by
          rw [MeasureTheory.setIntegral_const, hvol, smul_eq_mul, mul_comm]
  have htrans2 : ∫ z : ℝ³, (bsWin ℓ u z) ^ 2 = E0 := by
    have hfun : (fun z : ℝ³ => (bsWin ℓ u z) ^ 2)
        = fun z : ℝ³ => (chiScale ℓ (z + -(ℓ • u))) ^ 2 := rfl
    rw [hfun, hE0, MeasureTheory.integral_add_right_eq_self
      (fun y : ℝ³ => (chiScale ℓ y) ^ 2) (-(ℓ • u))]
  have htransD : ∀ k : Fin 3,
      ∫ z : ℝ³, (fderiv ℝ (chiScale ℓ) (z - ℓ • u) (kcStdBasis k)) ^ 2 = Dk k := by
    intro k
    have hfun : (fun z : ℝ³ => (fderiv ℝ (chiScale ℓ) (z - ℓ • u) (kcStdBasis k)) ^ 2)
        = fun z : ℝ³ => (fderiv ℝ (chiScale ℓ) (z + -(ℓ • u)) (kcStdBasis k)) ^ 2 := rfl
    rw [hfun, hDk]
    rw [MeasureTheory.integral_add_right_eq_self
      (fun y : ℝ³ => (fderiv ℝ (chiScale ℓ) y (kcStdBasis k)) ^ 2) (-(ℓ • u))]
  have hbsWincs : HasCompactSupport (bsWin ℓ u) := bsWin_hasCompactSupport hℓ u
  have hbsWincont : Continuous (bsWin ℓ u) := by
    rw [show bsWin ℓ u = fun z : ℝ³ => chiScale ℓ (z - ℓ • u) from rfl]
    exact (chiScale_contDiff (ne_of_gt hℓ)).continuous.comp (continuous_id.sub continuous_const)
  have hW2 : HasCompactSupport (fun z : ℝ³ => (bsWin ℓ u z) ^ 2) :=
    hbsWincs.comp_left (g := fun x : ℝ => x ^ 2) (by norm_num : ((0 : ℝ)) ^ 2 = 0)
  have hL2h : ∫ z : ℝ³, (bsWin ℓ u z * bsQ ℓ u ψ z) ^ 2 ≤ 4 * S0 ^ 2 * E0 := by
    have hpt : ∀ z : ℝ³, (bsWin ℓ u z * bsQ ℓ u ψ z) ^ 2 ≤ (bsWin ℓ u z) ^ 2 * (4 * S0 ^ 2) := by
      intro z
      have h1 : (bsQ ℓ u ψ z) ^ 2 ≤ 4 * S0 ^ 2 := hbsQ_bound z
      nlinarith [h1, sq_nonneg (bsWin ℓ u z)]
    have hcsg : HasCompactSupport (fun z : ℝ³ => (bsWin ℓ u z) ^ 2 * (4 * S0 ^ 2)) := by
      have h1 : (fun z : ℝ³ => (bsWin ℓ u z) ^ 2 * (4 * S0 ^ 2))
          = (fun z : ℝ³ => (bsWin ℓ u z) ^ 2) * (fun _ => (4 * S0 ^ 2)) := rfl
      rw [h1]
      exact hW2.mul_right
    have hint : Integrable (fun z : ℝ³ => (bsWin ℓ u z) ^ 2 * (4 * S0 ^ 2)) :=
      ((hbsWincont.pow 2).mul continuous_const).integrable_of_hasCompactSupport hcsg
    calc ∫ z : ℝ³, (bsWin ℓ u z * bsQ ℓ u ψ z) ^ 2
        ≤ ∫ z : ℝ³, (bsWin ℓ u z) ^ 2 * (4 * S0 ^ 2) :=
          integral_mono_of_nonneg (Eventually.of_forall (fun z => sq_nonneg _)) hint
            (Eventually.of_forall hpt)
      _ = 4 * S0 ^ 2 * E0 := by rw [MeasureTheory.integral_mul_const, htrans2]; ring
  have hDirh : ∀ k : Fin 3, ∫ z : ℝ³,
      (fderiv ℝ (fun y : ℝ³ => bsWin ℓ u y * bsQ ℓ u ψ y) z (kcStdBasis k)) ^ 2
        ≤ 8 * S0 ^ 2 * Dk k + 2 * S1 ^ 2 * E0 := by
    intro k
    have hpt : ∀ z : ℝ³,
        (fderiv ℝ (fun y : ℝ³ => bsWin ℓ u y * bsQ ℓ u ψ y) z (kcStdBasis k)) ^ 2
        ≤ 8 * S0 ^ 2 * (fderiv ℝ (chiScale ℓ) (z - ℓ • u) (kcStdBasis k)) ^ 2
          + 2 * S1 ^ 2 * (bsWin ℓ u z) ^ 2 := by
      intro z
      have hbsQcd : ContDiff ℝ (⊤ : ENat) (bsQ ℓ u ψ) := by
        rw [show bsQ ℓ u ψ = fun y : ℝ³ => ψ y - bsMean ℓ u ψ from rfl]
        exact hψcd.sub contDiff_const
      have hd := fderiv_bsWin_mul_apply (ℓ := ℓ) u z (kcStdBasis k) hbsQcd
      have hbsQd : fderiv ℝ (bsQ ℓ u ψ) z (kcStdBasis k) = fderiv ℝ ψ z (kcStdBasis k) := by
        have h : fderiv ℝ (bsQ ℓ u ψ) z = fderiv ℝ ψ z := by
          rw [show bsQ ℓ u ψ = fun y : ℝ³ => ψ y - bsMean ℓ u ψ from rfl]
          exact ((hψcd.differentiable (by norm_num) z).hasFDerivAt.sub_const _).fderiv
        rw [h]
      rw [hd, hbsQd]
      have h1 := hbsQ_bound z
      have h2 := hψS1 k z
      nlinarith [h1, h2, sq_nonneg ((fderiv ℝ (chiScale ℓ) (z - ℓ • u) (kcStdBasis k)) * bsQ ℓ u ψ z
          - bsWin ℓ u z * fderiv ℝ ψ z (kcStdBasis k)),
        sq_nonneg (fderiv ℝ (chiScale ℓ) (z - ℓ • u) (kcStdBasis k))]
    have hAcs : HasCompactSupport (fun z : ℝ³ =>
        (fderiv ℝ (chiScale ℓ) (z - ℓ • u) (kcStdBasis k)) ^ 2) := by
      have h2 : HasCompactSupport (fun z : ℝ³ =>
          fderiv ℝ (chiScale ℓ) (z - ℓ • u) (kcStdBasis k)) :=
        (HasCompactSupport.fderiv_apply ℝ (chiScale_hasCompactSupport (ne_of_gt hℓ))
          (kcStdBasis k)).comp_homeomorph (Homeomorph.subRight (ℓ • u))
      exact h2.comp_left (g := fun x : ℝ => x ^ 2) (by norm_num : ((0 : ℝ)) ^ 2 = 0)
    have hAcont : Continuous (fun z : ℝ³ =>
        (fderiv ℝ (chiScale ℓ) (z - ℓ • u) (kcStdBasis k)) ^ 2) :=
      (((chiScale_contDiff (ne_of_gt hℓ)).continuous_fderiv (by norm_num)).clm_apply
        continuous_const |>.comp (continuous_id.sub continuous_const)).pow 2
    have hIntA : Integrable (fun z : ℝ³ =>
        8 * S0 ^ 2 * (fderiv ℝ (chiScale ℓ) (z - ℓ • u) (kcStdBasis k)) ^ 2) :=
      (hAcont.integrable_of_hasCompactSupport hAcs).const_mul _
    have hIntB : Integrable (fun z : ℝ³ => 2 * S1 ^ 2 * (bsWin ℓ u z) ^ 2) :=
      ((hbsWincont.pow 2).integrable_of_hasCompactSupport hW2).const_mul _
    calc ∫ z : ℝ³, (fderiv ℝ (fun y : ℝ³ => bsWin ℓ u y * bsQ ℓ u ψ y) z
          (kcStdBasis k)) ^ 2
        ≤ ∫ z : ℝ³, (8 * S0 ^ 2 * (fderiv ℝ (chiScale ℓ) (z - ℓ • u)
              (kcStdBasis k)) ^ 2 + 2 * S1 ^ 2 * (bsWin ℓ u z) ^ 2) :=
          integral_mono_of_nonneg (Eventually.of_forall (fun z => sq_nonneg _)) (hIntA.add hIntB)
            (Eventually.of_forall hpt)
      _ = 8 * S0 ^ 2 * Dk k + 2 * S1 ^ 2 * E0 := by
          rw [integral_add hIntA hIntB, MeasureTheory.integral_const_mul,
            MeasureTheory.integral_const_mul, htransD k, htrans2]
  have hw := bsOneBody_le_weighted (c := c) hℓ u hψcd hψcs
  have hfin : 2 * (1 + c ^ 2) * ((∫ z : ℝ³, (bsWin ℓ u z * bsQ ℓ u ψ z) ^ 2)
      + ∑ k : Fin 3, (∫ z : ℝ³, (fderiv ℝ (fun y : ℝ³ => bsWin ℓ u y * bsQ ℓ u ψ y) z
          (kcStdBasis k)) ^ 2)) ≤ C0 := by
    rw [hC0]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact add_le_add hL2h (Finset.sum_le_sum (fun k _ => hDirh k))
  exact le_trans (le_trans hw hfin) (le_max_left C0 0)


/-! ## 6. Measurability of the uncurried slot form -/

lemma bsMean_pair_continuous {ℓ : ℝ} (hℓ : 0 < ℓ) (n : ℕ)
    (Φ : X (n + 1) → ℝ) (hΦ : ContDiff ℝ (⊤ : ENat) Φ) (i : Fin (n + 1)) :
    Continuous (fun q : ℝ³ × X n =>
      bsMean ℓ q.1 (fun z : ℝ³ => Φ (kcInsN n i (z, q.2)))) := by
  have hcont : Continuous (Function.uncurry (fun (q : ℝ³ × X n) (z : ℝ³) =>
      Φ (kcInsN n i (ℓ • q.1 + z, q.2)))) := by
    refine hΦ.continuous.comp ?_
    refine (kcInsN_cont i).comp ?_
    exact (((continuous_fst.fst).const_smul ℓ).add continuous_snd).prodMk continuous_fst.snd
  have h := Commons.Analysis.Calculus.continuous_setIntegral_isCompact
    (E := ℝ) (acube_compact hℓ) hcont
  have hfun : (fun q : ℝ³ × X n =>
      bsMean ℓ q.1 (fun z : ℝ³ => Φ (kcInsN n i (z, q.2))))
      = fun q : ℝ³ × X n => (ℓ ^ 3)⁻¹ *
          ∫ z in acube ℓ, Φ (kcInsN n i (ℓ • q.1 + z, q.2)) := rfl
  rw [hfun]
  exact h.const_mul _

lemma continuous_fsKinCoeff (c : ℝ) : Continuous (fun r : ℝ => fsKinCoeff c r) := by
  rw [show (fun r : ℝ => fsKinCoeff c r) = fun r : ℝ => (max (r - c) 0) ^ 2 from rfl]
  exact ((continuous_id.sub continuous_const).max continuous_const).pow 2

/-- The windowed mean-free inserted state, as a function of the moving-box parameter
`q = (u,r)` and the position: `z ↦ χ_u(z)·(Q_{Λ(u)}ψ_r)(z)`. -/
noncomputable def famState (ℓ : ℝ) (n : ℕ) (Φ : X (n + 1) → ℝ) (i : Fin (n + 1)) :
    ℝ³ × X n → ℝ³ → ℂ :=
  fun q z => (bsWin ℓ q.1 z : ℂ) *
    (bsQ ℓ q.1 (fun z' : ℝ³ => Φ (kcInsN n i (z', q.2))) z : ℂ)

/-- The `(p,z)`-integrand of the `p`-convention Fourier transform of `famState`. -/
noncomputable def famAmp (ℓ : ℝ) (n : ℕ) (Φ : X (n + 1) → ℝ) (i : Fin (n + 1)) :
    (ℝ³ × X n) × ℝ³ → ℝ³ → ℂ :=
  fun w z => Complex.exp (-(Complex.I * (inner ℝ w.2 z : ℂ))) * famState ℓ n Φ i w.1 z

/-- The `p`-integrand of the one-body slot form. -/
noncomputable def famSpec (ℓ c : ℝ) (n : ℕ) (Φ : X (n + 1) → ℝ) (i : Fin (n + 1)) :
    (ℝ³ × X n) × ℝ³ → ℝ :=
  fun w => fsKinCoeff c ‖w.2‖ * ‖kinFT (famState ℓ n Φ i w.1) w.2‖ ^ 2

/-- The one-body slot form, as a function of the moving-box parameter `(u,r)`. -/
noncomputable def famOneBody (ℓ c : ℝ) (n : ℕ) (Φ : X (n + 1) → ℝ) (i : Fin (n + 1)) :
    ℝ³ × X n → ℝ :=
  fun q => ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : ℝ³, famSpec ℓ c n Φ i (q, p)

lemma continuous_bsWin_pair {ℓ : ℝ} {n : ℕ} (hℓ : 0 < ℓ) :
    Continuous (fun w : (ℝ³ × X n) × ℝ³ => bsWin ℓ w.1.1 w.2) := by
  have hfun : (fun w : (ℝ³ × X n) × ℝ³ => bsWin ℓ w.1.1 w.2)
      = fun w : (ℝ³ × X n) × ℝ³ => chiScale ℓ (w.2 - ℓ • w.1.1) := rfl
  rw [hfun]
  exact (chiScale_contDiff (ne_of_gt hℓ)).continuous.comp
    (continuous_snd.sub (continuous_fst.fst.const_smul ℓ))

lemma continuous_bsQ_pair {ℓ : ℝ} (hℓ : 0 < ℓ) (n : ℕ) (Φ : X (n + 1) → ℝ)
    (hΦ : ContDiff ℝ (⊤ : ENat) Φ) (i : Fin (n + 1)) :
    Continuous (fun w : (ℝ³ × X n) × ℝ³ =>
      bsQ ℓ w.1.1 (fun z : ℝ³ => Φ (kcInsN n i (z, w.1.2))) w.2) := by
  have hfun : (fun w : (ℝ³ × X n) × ℝ³ =>
      bsQ ℓ w.1.1 (fun z : ℝ³ => Φ (kcInsN n i (z, w.1.2))) w.2)
      = fun w : (ℝ³ × X n) × ℝ³ => Φ (kcInsN n i (w.2, w.1.2))
          - bsMean ℓ w.1.1 (fun z : ℝ³ => Φ (kcInsN n i (z, w.1.2))) := rfl
  rw [hfun]
  refine (hΦ.continuous.comp ((kcInsN_cont i).comp ?_)).sub ?_
  · exact continuous_snd.prodMk continuous_fst.snd
  · exact (bsMean_pair_continuous hℓ n Φ hΦ i).comp continuous_fst

lemma continuous_famState {ℓ : ℝ} (hℓ : 0 < ℓ) (n : ℕ) {Φ : X (n + 1) → ℝ}
    (hΦ : ContDiff ℝ (⊤ : ENat) Φ) (i : Fin (n + 1)) :
    Continuous (fun w : ((ℝ³ × X n) × ℝ³) × ℝ³ => famState ℓ n Φ i w.1.1 w.2) := by
  have hwin : Continuous (fun w : ((ℝ³ × X n) × ℝ³) × ℝ³ => bsWin ℓ w.1.1.1 w.2) := by
    have hfun : (fun w : ((ℝ³ × X n) × ℝ³) × ℝ³ => bsWin ℓ w.1.1.1 w.2)
        = fun w : ((ℝ³ × X n) × ℝ³) × ℝ³ => chiScale ℓ (w.2 - ℓ • w.1.1.1) := rfl
    rw [hfun]
    exact (chiScale_contDiff (ne_of_gt hℓ)).continuous.comp
      (continuous_snd.sub ((continuous_fst.fst.fst).const_smul ℓ))
  have hQ : Continuous (fun w : ((ℝ³ × X n) × ℝ³) × ℝ³ =>
      bsQ ℓ w.1.1.1 (fun z : ℝ³ => Φ (kcInsN n i (z, w.1.1.2))) w.2) := by
    have hfun : (fun w : ((ℝ³ × X n) × ℝ³) × ℝ³ =>
        bsQ ℓ w.1.1.1 (fun z : ℝ³ => Φ (kcInsN n i (z, w.1.1.2))) w.2)
        = fun w : ((ℝ³ × X n) × ℝ³) × ℝ³ => Φ (kcInsN n i (w.2, w.1.1.2))
            - bsMean ℓ w.1.1.1 (fun z : ℝ³ => Φ (kcInsN n i (z, w.1.1.2))) := rfl
    rw [hfun]
    refine (hΦ.continuous.comp ((kcInsN_cont i).comp ?_)).sub ?_
    · exact Continuous.prodMk continuous_snd continuous_fst.fst.snd
    · exact (bsMean_pair_continuous hℓ n Φ hΦ i).comp continuous_fst.fst
  have h := (Complex.continuous_ofReal.comp hwin).mul (Complex.continuous_ofReal.comp hQ)
  have h' : (fun w : ((ℝ³ × X n) × ℝ³) × ℝ³ => famState ℓ n Φ i w.1.1 w.2)
      = (Complex.ofReal ∘ fun w : ((ℝ³ × X n) × ℝ³) × ℝ³ => bsWin ℓ w.1.1.1 w.2) *
        (Complex.ofReal ∘ fun w : ((ℝ³ × X n) × ℝ³) × ℝ³ =>
          bsQ ℓ w.1.1.1 (fun z : ℝ³ => Φ (kcInsN n i (z, w.1.1.2))) w.2) := by
    funext w; rfl
  rw [h']
  exact h

lemma continuous_famAmp {ℓ : ℝ} (hℓ : 0 < ℓ) (n : ℕ) {Φ : X (n + 1) → ℝ}
    (hΦ : ContDiff ℝ (⊤ : ENat) Φ) (i : Fin (n + 1)) :
    Continuous (Function.uncurry (famAmp ℓ n Φ i)) := by
  have hexp : Continuous (fun w : ((ℝ³ × X n) × ℝ³) × ℝ³ =>
      Complex.exp (-(Complex.I * (inner ℝ w.1.2 w.2 : ℂ)))) := by
    have hinner : Continuous (fun w : ((ℝ³ × X n) × ℝ³) × ℝ³ => (inner ℝ w.1.2 w.2 : ℂ)) :=
      Complex.continuous_ofReal.comp (continuous_inner.comp
        (Continuous.prodMk continuous_fst.snd continuous_snd))
    have hI : Continuous (fun _ : ((ℝ³ × X n) × ℝ³) × ℝ³ => (Complex.I : ℂ)) := continuous_const
    exact Complex.continuous_exp.comp ((hI.mul hinner).neg)
  have hstate : Continuous (fun w : ((ℝ³ × X n) × ℝ³) × ℝ³ => famState ℓ n Φ i w.1.1 w.2) :=
    continuous_famState (Φ := Φ) hℓ n hΦ i
  have h := hexp.mul hstate
  have h' : (fun w : ((ℝ³ × X n) × ℝ³) × ℝ³ => famAmp ℓ n Φ i w.1 w.2)
      = (fun w : ((ℝ³ × X n) × ℝ³) × ℝ³ =>
          Complex.exp (-(Complex.I * (inner ℝ w.1.2 w.2 : ℂ)))) *
        (fun w : ((ℝ³ × X n) × ℝ³) × ℝ³ => famState ℓ n Φ i w.1.1 w.2) := by
    funext w; rfl
  rw [show Function.uncurry (famAmp ℓ n Φ i)
      = fun w : ((ℝ³ × X n) × ℝ³) × ℝ³ => famAmp ℓ n Φ i w.1 w.2 from rfl, h']
  exact h

lemma aemeas_famKinFT {ℓ : ℝ} (hℓ : 0 < ℓ) (n : ℕ) {Φ : X (n + 1) → ℝ}
    (hΦ : ContDiff ℝ (⊤ : ENat) Φ) (i : Fin (n + 1)) (ν : Measure (X n)) :
    AEStronglyMeasurable (fun w : (ℝ³ × X n) × ℝ³ => kinFT (famState ℓ n Φ i w.1) w.2)
      (((volume : Measure ℝ³).prod ν).prod (volume : Measure ℝ³)) := by
  have h : AEStronglyMeasurable (Function.uncurry (famAmp ℓ n Φ i))
      (((((volume : Measure ℝ³).prod ν).prod (volume : Measure ℝ³)).prod (volume : Measure ℝ³))) :=
    (continuous_famAmp (Φ := Φ) hℓ n hΦ i).stronglyMeasurable.aestronglyMeasurable
  have h2 := h.integral_prod_right' (ν := (volume : Measure ℝ³))
  have h2' : AEStronglyMeasurable (fun w : (ℝ³ × X n) × ℝ³ =>
      ∫ z : ℝ³, famAmp ℓ n Φ i w z ∂volume) (((volume : Measure ℝ³).prod ν).prod (volume : Measure ℝ³)) := by
    simpa only [Function.uncurry] using h2
  refine h2'.congr (Eventually.of_forall (fun w => ?_))
  show (∫ z : ℝ³, famAmp ℓ n Φ i w z ∂volume) = ∫ z : ℝ³,
    Complex.exp (-(Complex.I * (inner ℝ w.2 z : ℂ))) * famState ℓ n Φ i w.1 z
  rfl

lemma aemeas_famSpec {ℓ c : ℝ} (hℓ : 0 < ℓ) (n : ℕ) {Φ : X (n + 1) → ℝ}
    (hΦ : ContDiff ℝ (⊤ : ENat) Φ) (i : Fin (n + 1)) (ν : Measure (X n)) :
    AEStronglyMeasurable (famSpec ℓ c n Φ i)
      (((volume : Measure ℝ³).prod ν).prod (volume : Measure ℝ³)) := by
  have hK := aemeas_famKinFT (Φ := Φ) hℓ n hΦ i ν
  have hf : AEStronglyMeasurable (fun w : (ℝ³ × X n) × ℝ³ => fsKinCoeff c ‖w.2‖)
      (((volume : Measure ℝ³).prod ν).prod (volume : Measure ℝ³)) :=
    ((continuous_fsKinCoeff c).comp continuous_snd.norm).stronglyMeasurable.aestronglyMeasurable
  have h := hf.mul ((hK.norm).pow 2)
  have h' : famSpec ℓ c n Φ i
      = (fun w : (ℝ³ × X n) × ℝ³ => fsKinCoeff c ‖w.2‖) *
        (fun x : (ℝ³ × X n) × ℝ³ => ‖kinFT (famState ℓ n Φ i x.1) x.2‖) ^ 2 := by
    funext w; rfl
  rw [h']
  exact h

lemma aemeas_famOneBody {ℓ c : ℝ} (hℓ : 0 < ℓ) (n : ℕ) {Φ : X (n + 1) → ℝ}
    (hΦ : ContDiff ℝ (⊤ : ENat) Φ) (i : Fin (n + 1)) (ν : Measure (X n)) :
    AEStronglyMeasurable (famOneBody ℓ c n Φ i) ((volume : Measure ℝ³).prod ν) := by
  have h := (aemeas_famSpec (c := c) (Φ := Φ) hℓ n hΦ i ν).integral_prod_right'
    (ν := (volume : Measure ℝ³))
  have h2 : AEStronglyMeasurable
      (fun q : ℝ³ × X n => ∫ p : ℝ³, famSpec ℓ c n Φ i (q, p) ∂volume)
      ((volume : Measure ℝ³).prod ν) := h
  have h3 : famOneBody ℓ c n Φ i = fun q : ℝ³ × X n =>
      ((2 * Real.pi) ^ 3)⁻¹ * ∫ p : ℝ³, famSpec ℓ c n Φ i (q, p) ∂volume := rfl
  rw [h3]
  exact h2.const_mul _

lemma aemeas_uncurry_fibre {ℓ c : ℝ} (hℓ : 0 < ℓ) (n : ℕ)
    (Φ : X (n + 1) → ℝ) (hΦ : ContDiff ℝ (⊤ : ENat) Φ) (i : Fin (n + 1)) :
    AEStronglyMeasurable
      (Function.uncurry (fun (u : ℝ³) (r : X n) =>
        bsOneBody ℓ (fsKinCoeff c) u (fun z : ℝ³ => Φ (kcInsN n i (z, r)))))
      ((volume : Measure ℝ³).prod ((volume : Measure (X n)).restrict (abox n ℓ))) := by
  have h := aemeas_famOneBody (c := c) (Φ := Φ) hℓ n hΦ i
    ((volume : Measure (X n)).restrict (abox n ℓ))
  refine h.congr (Eventually.of_forall (fun q => ?_))
  show famOneBody ℓ c n Φ i q
    = bsOneBody ℓ (fsKinCoeff c) q.1 (fun z : ℝ³ => Φ (kcInsN n i (z, q.2)))
  unfold famOneBody famSpec famState bsOneBody
  rfl

/-! ## 7. Joint integrability of the uncurried slot form -/

lemma integrable_uncurry_fibre {ℓ c : ℝ} (hℓ : 0 < ℓ) (n : ℕ)
    (Φ : X (n + 1) → ℝ) (hΦ : ContDiff ℝ (⊤ : ENat) Φ) (hsupp : SuppInBox (n + 1) ℓ Φ)
    (i : Fin (n + 1)) :
    Integrable (Function.uncurry (fun (u : ℝ³) (r : X n) =>
      bsOneBody ℓ (fsKinCoeff c) u (fun z : ℝ³ => Φ (kcInsN n i (z, r)))))
      ((volume : Measure ℝ³).prod ((volume : Measure (X n)).restrict (abox n ℓ))) := by
  obtain ⟨C, hC0, hC⟩ := exists_bound_bsOneBody_fibre (c := c) hℓ n Φ hΦ hsupp i
  have hνfin : (volume : Measure (X n)).restrict (abox n ℓ) (abox n ℓ) ≠ ⊤ := by
    rw [Measure.restrict_apply_self]
    exact (abox_lt_top n ℓ hℓ.le).ne
  have hint : Integrable (fun q : ℝ³ × X n =>
      (Metric.closedBall (0 : ℝ³) 2).indicator (fun _ => C) q.1 *
        (abox n ℓ).indicator (fun _ => (1 : ℝ)) q.2)
      ((volume : Measure ℝ³).prod ((volume : Measure (X n)).restrict (abox n ℓ))) := by
    refine Integrable.mul_prod ?_ ?_
    · rw [integrable_indicator_iff Metric.isClosed_closedBall.measurableSet]
      exact integrableOn_const (ne_of_lt (isCompact_closedBall 0 2).measure_lt_top) (by simp)
    · rw [integrable_indicator_iff (abox_measurable n ℓ)]
      exact integrableOn_const (by
        rw [Measure.restrict_apply_self]
        exact (abox_lt_top n ℓ hℓ.le).ne) (by simp)
  refine Integrable.mono' hint (aemeas_uncurry_fibre hℓ n Φ hΦ i) (Eventually.of_forall ?_)
  rintro ⟨q, r⟩
  show ‖bsOneBody ℓ (fsKinCoeff c) q (fun z : ℝ³ => Φ (kcInsN n i (z, r)))‖ ≤
    (Metric.closedBall (0 : ℝ³) 2).indicator (fun _ => C) q *
      (abox n ℓ).indicator (fun _ => (1 : ℝ)) r
  have hfnn : 0 ≤ bsOneBody ℓ (fsKinCoeff c) q
      (fun z : ℝ³ => Φ (kcInsN n i (z, r))) :=
    bsOneBody_nonneg' (fun t => fsKinCoeff_nonneg c t) q _
  rw [Real.norm_of_nonneg hfnn]
  by_cases hr : r ∈ abox n ℓ
  · by_cases hu : ‖q‖ ≤ 2
    · have h1 : (Metric.closedBall (0 : ℝ³) 2).indicator (fun _ => C) q = C :=
        Set.indicator_of_mem (by rwa [Metric.mem_closedBall, dist_zero_right]) _
      rw [h1, Set.indicator_of_mem hr]
      simpa using hC q r hr
    · have hfar := bsOneBody_eq_zero_of_far (c := c) hℓ n Φ hsupp i r
        (le_of_lt (lt_of_not_ge hu))
      have h1 : (Metric.closedBall (0 : ℝ³) 2).indicator (fun _ => C) q = 0 :=
        Set.indicator_of_notMem (by rwa [Metric.mem_closedBall, dist_zero_right]) _
      rw [hfar, h1, zero_mul]
  · have hfib : (fun z : ℝ³ => Φ (kcInsN n i (z, r))) = fun _ => (0 : ℝ) := by
      funext z
      exact fibre_eq_zero_of_not_mem_abox n hsupp i hr z
    have hzero : bsOneBody ℓ (fsKinCoeff c) q (fun _ => (0 : ℝ)) = 0 := by
      simp [bsOneBody, bsQ, bsMean, kinFT]
    rw [hfib, Set.indicator_of_notMem hr, mul_zero, hzero]

/-! ## 8. Integrability of the fibre Dirichlet word -/

lemma dBox_fibre_eq {ℓ : ℝ} (hℓ : 0 < ℓ) (n : ℕ) (Φ : X (n + 1) → ℝ)
    (hΦ : ContDiff ℝ (⊤ : ENat) Φ) (i : Fin (n + 1)) (r : X n) :
    dBox ℓ (fun z : ℝ³ => Φ (kcInsN n i (z, r)))
      = ∫ z in acube ℓ, ∑ k : Fin 3,
          (fderiv ℝ Φ (kcInsN n i (z, r)) (kcDir (n + 1) i k)) ^ 2 := by
  have hint : ∀ k : Fin 3, IntegrableOn
      (fun z : ℝ³ => (fderiv ℝ Φ (kcInsN n i (z, r)) (kcDir (n + 1) i k)) ^ 2)
      (acube ℓ) volume := fun k =>
    ContinuousOn.integrableOn_compact (acube_compact hℓ)
      ((((hΦ.continuous_fderiv (by norm_num)).comp
        ((kcInsN_cont i).comp (continuous_id.prodMk continuous_const))).clm_apply
          continuous_const).pow 2).continuousOn
  calc dBox ℓ (fun z : ℝ³ => Φ (kcInsN n i (z, r)))
      = ∑ k : Fin 3, ∫ x in acube ℓ,
          (fderiv ℝ Φ (kcInsN n i (x, r)) (kcDir (n + 1) i k)) ^ 2 := by
        rw [dBox]
        exact Finset.sum_congr rfl (fun k _ => by
          apply integral_congr_ae
          filter_upwards with x
          rw [fiber_fderiv_kcDir i hΦ r x k])
    _ = ∫ z in acube ℓ, ∑ k : Fin 3,
          (fderiv ℝ Φ (kcInsN n i (z, r)) (kcDir (n + 1) i k)) ^ 2 :=
        (integral_finsetSum Finset.univ (fun k _ => hint k)).symm

lemma integrable_dBox_fibre {ℓ : ℝ} (hℓ : 0 < ℓ) (n : ℕ)
    (Φ : X (n + 1) → ℝ) (hΦ : ContDiff ℝ (⊤ : ENat) Φ) (i : Fin (n + 1)) :
    Integrable (fun r : X n => dBox ℓ (fun z : ℝ³ => Φ (kcInsN n i (z, r))))
      ((volume : Measure (X n)).restrict (abox n ℓ)) := by
  obtain ⟨C, hC⟩ := (abox_compact (n + 1) hℓ).exists_bound_of_continuousOn
    (hΦ.continuous_fderiv (by norm_num)).norm.continuousOn
  have hC' : ∀ x ∈ abox (n + 1) ℓ, ‖fderiv ℝ Φ x‖ ≤ C := by
    intro x hx
    have h := hC x hx
    rwa [Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] at h
  have hvol : (volume : Measure ℝ³).real (acube ℓ) = ℓ ^ 3 := by
    rw [MeasureTheory.Measure.real_def, acube_volume ℓ hℓ.le, ENNReal.toReal_ofReal (by positivity)]
  have hbound : ∀ r ∈ abox n ℓ,
      ‖dBox ℓ (fun z : ℝ³ => Φ (kcInsN n i (z, r)))‖ ≤ 3 * ℓ ^ 3 * C ^ 2 := by
    intro r hr
    have hnn : 0 ≤ dBox ℓ (fun z : ℝ³ => Φ (kcInsN n i (z, r))) := by
      rw [dBox_fibre_eq hℓ n Φ hΦ i r]
      exact integral_nonneg (fun z => Finset.sum_nonneg (fun k _ => sq_nonneg _))
    rw [Real.norm_of_nonneg hnn, dBox_fibre_eq hℓ n Φ hΦ i r]
    calc ∫ z in acube ℓ, ∑ k : Fin 3,
            (fderiv ℝ Φ (kcInsN n i (z, r)) (kcDir (n + 1) i k)) ^ 2
          ≤ ∫ z in acube ℓ, ∑ _k : Fin 3, C ^ 2 := by
            refine setIntegral_mono_on ?_ ?_ (acube_measurable ℓ) (fun z hz => ?_)
            · have hcontk : Continuous (fun z : ℝ³ => ∑ k : Fin 3,
                  (fderiv ℝ Φ (kcInsN n i (z, r)) (kcDir (n + 1) i k)) ^ 2) := by
                apply continuous_finsetSum
                intro k _
                exact ((((hΦ.continuous_fderiv (by norm_num)).comp
                  ((kcInsN_cont i).comp (continuous_id.prodMk continuous_const))).clm_apply
                    continuous_const).pow 2)
              exact ContinuousOn.integrableOn_compact (acube_compact hℓ) hcontk.continuousOn
            · exact ContinuousOn.integrableOn_compact (acube_compact hℓ) continuousOn_const
            · refine Finset.sum_le_sum (fun k _ => ?_)
              rw [← sq_abs]
              refine pow_le_pow_left₀ (abs_nonneg _) ?_ 2
              calc |fderiv ℝ Φ (kcInsN n i (z, r)) (kcDir (n + 1) i k)|
                  = ‖(fderiv ℝ Φ (kcInsN n i (z, r))) (kcDir (n + 1) i k)‖ := Real.norm_eq_abs _
                _ ≤ ‖fderiv ℝ Φ (kcInsN n i (z, r))‖ * ‖kcDir (n + 1) i k‖ :=
                    (fderiv ℝ Φ (kcInsN n i (z, r))).le_opNorm _
                _ = ‖fderiv ℝ Φ (kcInsN n i (z, r))‖ := by rw [kc_norm_dir, mul_one]
                _ ≤ C := hC' _ (mem_abox_kcInsN i hr hz)
        _ = ℓ ^ 3 * (3 * C ^ 2) := by
            rw [MeasureTheory.setIntegral_const, Finset.sum_const, Finset.card_fin, hvol]
            simp [smul_eq_mul]
        _ = 3 * ℓ ^ 3 * C ^ 2 := by ring
  have hmeas : AEStronglyMeasurable (fun r : X n => dBox ℓ (fun z : ℝ³ => Φ (kcInsN n i (z, r))))
      ((volume : Measure (X n)).restrict (abox n ℓ)) := by
    have hcont : Continuous (Function.uncurry (fun (r : X n) (z : ℝ³) =>
        ∑ k : Fin 3, (fderiv ℝ Φ (kcInsN n i (z, r)) (kcDir (n + 1) i k)) ^ 2)) := by
      apply continuous_finsetSum
      intro k _
      exact ((((hΦ.continuous_fderiv (by norm_num)).comp
        ((kcInsN_cont i).comp (continuous_snd.prodMk continuous_fst))).clm_apply
          continuous_const).pow 2)
    have hK : AEStronglyMeasurable (fun r : X n => ∫ z in acube ℓ,
        ∑ k : Fin 3, (fderiv ℝ Φ (kcInsN n i (z, r)) (kcDir (n + 1) i k)) ^ 2)
        ((volume : Measure (X n)).restrict (abox n ℓ)) :=
      hcont.aestronglyMeasurable.integral_prod_right'
    refine hK.congr ?_
    filter_upwards with r
    exact (dBox_fibre_eq hℓ n Φ hΦ i r).symm
  have hI : IsFiniteMeasure ((volume : Measure (X n)).restrict (abox n ℓ)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact abox_lt_top n ℓ hℓ.le⟩
  have _ := hI
  refine Integrable.of_bound hmeas (3 * ℓ ^ 3 * C ^ 2) ?_
  rw [MeasureTheory.ae_restrict_iff' (abox_measurable n ℓ)]
  exact Eventually.of_forall (fun r hr => hbound r hr)


/-! ## 9. The main theorem -/

theorem locKinEnWordBox_of_familyBound {ℓ c : ℝ} (hℓ : 0 < ℓ)
    (h : Work.BSKinetic.FamilyBound ℓ c) (n : ℕ)
    (Φ : Submission.BoseGases.X (n + 1) → ℝ) (hΦ : ContDiff ℝ (⊤ : ENat) Φ)
    (hsupp : Work.BSKinetic.SuppInBox (n + 1) ℓ Φ) :
    Work.BSKinetic.familyBigKin (n + 1) ℓ c Φ
      ≤ Submission.BoseGases.kinWord (n + 1) ℓ Φ := by
  classical
  have hJ : ∀ i : Fin (n + 1),
      Integrable (Function.uncurry (fun (u : ℝ³) (r : X n) =>
        bsOneBody ℓ (fsKinCoeff c) u (fun z : ℝ³ => Φ (kcInsN n i (z, r)))))
        ((volume : Measure ℝ³).prod ((volume : Measure (X n)).restrict (abox n ℓ))) :=
    fun i => integrable_uncurry_fibre hℓ n Φ hΦ hsupp i
  have hslot : ∀ u : ℝ³, Work.UBBInputs9.tBwordKinBigU (n + 1) ℓ c u Φ
      = ∑ i : Fin (n + 1), ∫ r, bsOneBody ℓ (fsKinCoeff c) u
          (fun z : ℝ³ => Φ (kcInsN n i (z, r))) ∂((volume : Measure (X n)).restrict (abox n ℓ)) := by
    intro u
    rw [tBwordKinBigU_eq_slotSum (c := c) hℓ n u Φ hΦ]
  have hstep1 : (∫ u : ℝ³, Work.UBBInputs9.tBwordKinBigU (n + 1) ℓ c u Φ)
      = ∑ i : Fin (n + 1), ∫ u : ℝ³, ∫ r, bsOneBody ℓ (fsKinCoeff c) u
          (fun z : ℝ³ => Φ (kcInsN n i (z, r)))
            ∂((volume : Measure (X n)).restrict (abox n ℓ)) ∂volume := by
    rw [show (∫ u : ℝ³, Work.UBBInputs9.tBwordKinBigU (n + 1) ℓ c u Φ)
        = ∫ u : ℝ³, ∑ i : Fin (n + 1), ∫ r, bsOneBody ℓ (fsKinCoeff c) u
            (fun z : ℝ³ => Φ (kcInsN n i (z, r)))
              ∂((volume : Measure (X n)).restrict (abox n ℓ)) from
      integral_congr_ae (Eventually.of_forall hslot)]
    rw [integral_finsetSum]
    intro i _
    exact (hJ i).integral_prod_left
  have hstep2 : (∑ i : Fin (n + 1), ∫ u : ℝ³, ∫ r, bsOneBody ℓ (fsKinCoeff c) u
          (fun z : ℝ³ => Φ (kcInsN n i (z, r)))
            ∂((volume : Measure (X n)).restrict (abox n ℓ)) ∂volume)
      = ∑ i : Fin (n + 1), ∫ r, ∫ u : ℝ³, bsOneBody ℓ (fsKinCoeff c) u
          (fun z : ℝ³ => Φ (kcInsN n i (z, r)))
            ∂volume ∂((volume : Measure (X n)).restrict (abox n ℓ)) :=
    Finset.sum_congr rfl (fun i _ => integral_integral_swap (hJ i))
  have hstep3 : (∑ i : Fin (n + 1), ∫ r, ∫ u : ℝ³, bsOneBody ℓ (fsKinCoeff c) u
          (fun z : ℝ³ => Φ (kcInsN n i (z, r)))
            ∂volume ∂((volume : Measure (X n)).restrict (abox n ℓ)))
      ≤ ∑ i : Fin (n + 1), ∫ r, dBox ℓ (fun z : ℝ³ => Φ (kcInsN n i (z, r)))
            ∂((volume : Measure (X n)).restrict (abox n ℓ)) := by
    refine Finset.sum_le_sum (fun i _ => ?_)
    refine integral_mono_of_nonneg ?_ (integrable_dBox_fibre hℓ n Φ hΦ i) ?_
    · filter_upwards with r
      exact integral_nonneg (fun u => bsOneBody_nonneg' (fun t => fsKinCoeff_nonneg c t) u _)
    · filter_upwards with r
      have hbd := h _ (fibre_contDiff hΦ i r) (fibre_hasCompactSupport hℓ n hsupp i r)
      rwa [dSpace_eq_dBox_of_supp hℓ (fibre_contDiff hΦ i r)
        (fibre_supp n hsupp i r)] at hbd
  have hstep4 : (∑ i : Fin (n + 1), ∫ r, dBox ℓ (fun z : ℝ³ => Φ (kcInsN n i (z, r)))
        ∂((volume : Measure (X n)).restrict (abox n ℓ)))
      = Submission.BoseGases.kinWord (n + 1) ℓ Φ := by
    rw [kinWord_eq_slotSum hℓ n Φ hΦ]
    exact Finset.sum_congr rfl (fun i _ =>
      integral_congr_ae (Eventually.of_forall (fun r => rfl)))
  rw [show familyBigKin (n + 1) ℓ c Φ
      = ∫ u : ℝ³, Work.UBBInputs9.tBwordKinBigU (n + 1) ℓ c u Φ from rfl, hstep1, hstep2]
  exact le_trans hstep3 (le_of_eq hstep4)

end Work.BSKinetic




