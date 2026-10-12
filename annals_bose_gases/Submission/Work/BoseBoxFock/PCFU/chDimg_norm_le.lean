import ChallengeDeps
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Submission.Work.BoseBoxFock.PCFU.chDimg_caseArith
import Submission.Work.BoseBoxFock.PCFU.chDimg_coefB
import Submission.Work.BoseBoxFock.PCFU.chDimg_fibre_le
import Submission.Work.BoseBoxFock.PCFU.chiScale_imageSum_lowKer_le_exp
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock.PCFU

open MeasureTheory
local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-! ## The assembly of `chDimg_norm_le`.

The chain (all steps fixed constants, no `μ`-dependence in the constant):

* the state-side reduction `chDimg_fibre_le` gives, for any pointwise kernel bound
  `W` with `chiScale ℓ w * ‖Σ'_{d≠0} lowKer fc κ (u + w + ℓ•latVec d)‖ ≤ W w` (`u ∈ acube ℓ`),
  `‖chDimg … (boxRestrictR ℓ Φ)‖ ≤ ℓ³·A·(∫ W)·(∫_{abox}Φ²)` where `A = sup_w ‖KχfrU w‖`;
* `chiScale_imageSum_lowKer_le_exp` (the `κ`-explicit version of the proved lattice-image bound)
  supplies `W := C·(1+κ^{2N})κ^{3-2N}ℓ^{-M-3}·1_{boxL ℓ}`, so `∫ W = C(1+κ^{2N})κ^{3-2N}ℓ^{-M}`;
* the case split `ℓ ≤ max (a v) 1` / `max (a v) 1 ≤ ℓ` (with the parametrisation
  `ℓ = (a v)t^{-163/323}`, `κℓ = t^{-12/323}`, `t = μ(a v)³`) finishes the arithmetic. -/

/-- `chiScale` agrees with the corpus bump `chiLam`. -/
private lemma chiScale_eq_chiLam (ℓ : ℝ) (w : E3) :
    Submission.BoseGases.chiScale ℓ w = Work.BoseK15.corpusBox.chiLam ℓ w := by
  simp only [Submission.BoseGases.chiScale, Work.BoseB4.BoxData.chiLam,
    Work.BoseK15.corpusBox_chi]

/-- `chiScale` is even in its second argument. -/
private lemma chiScale_even (ℓ : ℝ) (w : E3) :
    Submission.BoseGases.chiScale ℓ (-w) = Submission.BoseGases.chiScale ℓ w := by
  simp only [Submission.BoseGases.chiScale]
  rw [smul_neg, Submission.BoseGases.chi_even]

/-- `chiScale ℓ` vanishes off the box `ℓ • cell`. -/
private lemma chiScale_eq_zero_of_notMem_boxL {ℓ : ℝ} (hℓ : 0 < ℓ) {w : E3}
    (hw : w ∉ Work.BoseK15.corpusBox.boxL ℓ) :
    Submission.BoseGases.chiScale ℓ w = 0 := by
  by_contra h
  exact hw (Work.BoseB4.BoxData.chiLam_supp (B := Work.BoseK15.corpusBox) hℓ
    (by rw [chiScale_eq_chiLam] at h; exact h))

/-- The box `ℓ • cell` has volume `ℓ³` (as a real number). -/
private lemma real_volume_boxL {ℓ : ℝ} (hℓ : 0 < ℓ) :
    MeasureTheory.volume.real (Work.BoseK15.corpusBox.boxL ℓ) = ℓ ^ 3 := by
  rw [MeasureTheory.Measure.real_def,
    Work.BoseB4.BoxData.volume_boxL (B := Work.BoseK15.corpusBox) hℓ,
    ENNReal.toReal_ofReal (by positivity)]

/-- The integral of the indicator of the box `ℓ • cell`. -/
private lemma integral_indicator_boxL {ℓ : ℝ} (hℓ : 0 < ℓ) :
    (∫ w : E3,
        (Work.BoseK15.corpusBox.boxL ℓ).indicator (fun _ => (1 : ℝ)) w) = ℓ ^ 3 := by
  have hmeas : MeasurableSet (Work.BoseK15.corpusBox.boxL ℓ) :=
    Work.BoseB4.BoxData.boxL_measurableSet _ ℓ
  have hne : (MeasureTheory.volume : MeasureTheory.Measure E3)
      (Work.BoseK15.corpusBox.boxL ℓ) ≠ ⊤ :=
    (Work.BoseB4.BoxData.boxL_compact _ ℓ).measure_ne_top
  rw [MeasureTheory.integral_indicator_const (1 : ℝ) hmeas, smul_eq_mul, mul_one]
  exact real_volume_boxL hℓ


/-! ## Local copies of the parametrisation facts

(`ellH v μ = (a v)·t^{-163/323}` and `chKappa v μ · ellH v μ = d^{-2}`, `d = t^{6/323}`,
`t = μ(a v)³`.)  These are proved in the sibling file `PCFU/chDimg_le.lean`; they are
reproved here (privately, under different names) so that this file does not depend on it. -/

/-- The box side at FS's parameters: `ℓ = (a v)·t^{−163/323}`, `t = μ(a v)³`. -/
private theorem ellH_eq_rpow (v : E3 → ℝ) {μ : ℝ} (hμ : 0 < μ) (hav : 0 < BoseGases.a v) :
    Work.BoseBoxFock.ellH v μ
      = BoseGases.a v * (μ * (BoseGases.a v) ^ 3) ^ (-(163 / 323) : ℝ) := by
  have ht : 0 < μ * (BoseGases.a v) ^ 3 := by positivity
  have hμa : 0 < μ * BoseGases.a v := mul_pos hμ hav
  have ha0 : BoseGases.a v ≠ 0 := ne_of_gt hav
  have hpos : 0 < Work.BoseBox.sideAt μ (BoseGases.a v) := Work.BoseBox.sideAt_pos hμ hav
  have hell : Work.BoseBoxFock.ellH v μ = Work.BoseBox.sideAt μ (BoseGases.a v) := by
    rw [Work.BoseBoxFock.ellH, if_pos hpos]
  rw [hell]
  show Work.BoseBox.fsXp (μ * BoseGases.a v ^ 3) (-(3 / 2))
        * (μ * BoseGases.a v) ^ (-(1 / 2 : ℝ))
      = BoseGases.a v * (μ * BoseGases.a v ^ 3) ^ (-(163 / 323) : ℝ)
  rw [Work.BoseBox.fsXp]
  have h3 : (μ * (BoseGases.a v) ^ 3) ^ (-(1 / 2 : ℝ))
      = (μ * BoseGases.a v) ^ (-(1 / 2 : ℝ)) * (BoseGases.a v)⁻¹ := by
    calc (μ * (BoseGases.a v) ^ 3) ^ (-(1 / 2 : ℝ))
        = ((μ * BoseGases.a v) * (BoseGases.a v) ^ 2) ^ (-(1 / 2 : ℝ)) := by ring_nf
      _ = (μ * BoseGases.a v) ^ (-(1 / 2 : ℝ)) * ((BoseGases.a v) ^ 2) ^ (-(1 / 2 : ℝ)) :=
          Real.mul_rpow hμa.le (by positivity)
      _ = (μ * BoseGases.a v) ^ (-(1 / 2 : ℝ)) * (BoseGases.a v)⁻¹ := by
          rw [← Real.rpow_natCast (BoseGases.a v) 2, ← Real.rpow_mul hav.le,
            show ((2 : ℕ) : ℝ) * (-(1 / 2 : ℝ)) = -1 by norm_num, Real.rpow_neg_one]
  have h1 : (μ * BoseGases.a v) ^ (-(1 / 2 : ℝ))
      = (μ * (BoseGases.a v) ^ 3) ^ (-(1 / 2 : ℝ)) * BoseGases.a v := by
    have h := congrArg (fun t : ℝ => t * BoseGases.a v) h3
    simp only [mul_assoc] at h
    rw [inv_mul_cancel₀ ha0, mul_one] at h
    exact h.symm
  have h4 : (μ * (BoseGases.a v) ^ 3) ^ (-(3 / 2 : ℝ) / 323)
        * (μ * (BoseGases.a v) ^ 3) ^ (-(1 / 2 : ℝ))
      = (μ * (BoseGases.a v) ^ 3) ^ (-(163 / 323) : ℝ) := by
    rw [← Real.rpow_add ht,
      show (-(3 / 2 : ℝ) / 323) + (-(1 / 2 : ℝ)) = -(163 / 323) by norm_num]
  rw [h1]
  calc (μ * (BoseGases.a v) ^ 3) ^ (-(3 / 2 : ℝ) / 323)
        * ((μ * (BoseGases.a v) ^ 3) ^ (-(1 / 2 : ℝ)) * BoseGases.a v)
      = ((μ * (BoseGases.a v) ^ 3) ^ (-(3 / 2 : ℝ) / 323)
          * (μ * (BoseGases.a v) ^ 3) ^ (-(1 / 2 : ℝ))) * BoseGases.a v := by ring
    _ = (μ * (BoseGases.a v) ^ 3) ^ (-(163 / 323) : ℝ) * BoseGases.a v := by rw [h4]
    _ = BoseGases.a v * (μ * (BoseGases.a v) ^ 3) ^ (-(163 / 323) : ℝ) := by ring

/-- The cut-off/box-side relation `chKappa v μ · ellH v μ = d^{-2}`, `d = t^{6/323}`. -/
private theorem chKappa_mul_ellH_rpow (v : E3 → ℝ) {μ : ℝ} (hμ : 0 < μ)
    (hav : 0 < BoseGases.a v) :
    Work.BoseBoxFock.PCFU.chKappa v μ * Work.BoseBoxFock.ellH v μ
      = (((μ * (BoseGases.a v) ^ 3) ^ (6 / 323 : ℝ))⁻¹) ^ 2 := by
  have hpos : 0 < Work.BoseBox.sideAt μ (BoseGases.a v) := Work.BoseBox.sideAt_pos hμ hav
  have hside : Work.BoseBox.sideAt μ (BoseGases.a v) ≠ 0 := ne_of_gt hpos
  have hell : Work.BoseBoxFock.ellH v μ = Work.BoseBox.sideAt μ (BoseGases.a v) := by
    rw [Work.BoseBoxFock.ellH, if_pos hpos]
  rw [hell]
  show ((Work.BoseBox.fsXp (μ * BoseGases.a v ^ 3) 6) ^ 2
        * Work.BoseBox.sideAt μ (BoseGases.a v))⁻¹ * Work.BoseBox.sideAt μ (BoseGases.a v)
      = (((μ * BoseGases.a v ^ 3) ^ (6 / 323 : ℝ))⁻¹) ^ 2
  rw [Work.BoseBox.fsXp, mul_inv, inv_pow, mul_assoc, inv_mul_cancel₀ hside, mul_one]

/-- Positivity of the low-momentum cut-off. -/
private theorem chKappa_pos_rpow (v : E3 → ℝ) {μ : ℝ} (hμ : 0 < μ)
    (hav : 0 < BoseGases.a v) : 0 < Work.BoseBoxFock.PCFU.chKappa v μ := by
  have hpos : 0 < Work.BoseBox.sideAt μ (BoseGases.a v) := Work.BoseBox.sideAt_pos hμ hav
  have ht : 0 < μ * (BoseGases.a v) ^ 3 := by positivity
  have hd : 0 < Work.BoseBox.fsXp (μ * BoseGases.a v ^ 3) 6 := by
    rw [Work.BoseBox.fsXp]
    exact Real.rpow_pos_of_pos ht _
  have hck : Work.BoseBoxFock.PCFU.chKappa v μ
      = ((Work.BoseBox.fsXp (μ * BoseGases.a v ^ 3) 6) ^ 2
          * Work.BoseBox.sideAt μ (BoseGases.a v))⁻¹ := by
    simp only [Work.BoseBoxFock.PCFU.chKappa, Work.BoseBox.paramsAt, Work.BoseBox.fsParams]
  rw [hck]
  exact inv_pos.mpr (mul_pos (pow_pos hd 2) hpos)

/-- The constant multiple of the indicator of `ℓ • cell` is integrable. -/
private lemma integrable_const_indicator_boxL (ℓ c : ℝ) :
    MeasureTheory.Integrable (fun w : E3 =>
      c * (Work.BoseK15.corpusBox.boxL ℓ).indicator (fun _ => (1 : ℝ)) w) := by
  have h : MeasureTheory.Integrable
      ((Work.BoseK15.corpusBox.boxL ℓ).indicator (fun _ => (1 : ℝ))) :=
    (MeasureTheory.integrableOn_const (μ := MeasureTheory.volume)
      (s := Work.BoseK15.corpusBox.boxL ℓ) (C := (1 : ℝ))
      (Work.BoseB4.BoxData.boxL_compact _ ℓ).measure_ne_top (by simp)).integrable_indicator
      (Work.BoseB4.BoxData.boxL_measurableSet _ ℓ)
  exact h.const_mul c

/-- **The `(D)`-channel lattice-image norm bound.** -/


theorem chDimg_norm_le (v : EuclideanSpace ℝ (Fin 3) → ℝ) (h : Work.UBB.ScatSol v) (hv : 0 ≤ v)
    (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < BoseGases.a v) (fc fu : Work.BoseBoxFix.LowCut) (M₀ : ℕ) (hM₀ : 19 ≤ M₀) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {μ : ℝ}, 0 < μ →
      R ≤ Work.BoseBoxFock.ellH v μ * Submission.BoseGases.chiR0 →
      2 * R ≤ Work.BoseBoxFock.ellH v μ →
      ∀ (N n : ℕ),
        ∀ (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (BoseGases.a v)))
        (i j : Fin n), i ≠ j →
        ‖Work.BoseBoxFock.PCFU.chDimg v h fc fu μ N i j
            (Work.BoseBoxFock.boxRestrictR (Work.BoseBoxFock.ellH v μ)
              (Φ : Submission.BoseGases.X n → ℝ))‖
          ≤ C * (1 + (Work.BoseBoxFock.PCFU.chKappa v μ) ^ (2 * M₀))
              * ((Work.BoseBoxFock.PCFU.chKappa v μ * Work.BoseBoxFock.ellH v μ)⁻¹) ^ (2 * M₀ - 3)
              * (Work.BoseBoxFock.ellH v μ) ^ (3 / 2 : ℝ)
              * Work.BoseBoxFix.normB v μ n Φ := by
  classical
  obtain ⟨A, hA0, hAK⟩ := chBimg_Kchi_sup v h hv hav hv1 hvrad hR hv_supp fu
  obtain ⟨C₁, hC₁0, hC₁⟩ :=
    chiScale_imageSum_lowKer_le_exp fc (2 * M₀ - 3) M₀ (2 * M₀) (by omega) le_rfl
  obtain ⟨C₂, hC₂0, hC₂⟩ :=
    chiScale_imageSum_lowKer_le_exp fc (2 * M₀ + 19) (M₀ + 11) (2 * M₀ + 22) (by omega) le_rfl
  let Λ : ℝ := max (BoseGases.a v) 1
  let Cst : ℝ := max 1 (max (A * C₁ * Λ ^ (3 / 2 : ℝ))
      (A * C₂ * (Λ ^ ((3 : ℝ) / 2 - 22) + (BoseGases.a v) ^ (3 / 2 : ℝ))))
  have hCst0 : 0 ≤ Cst := by
    refine le_trans (by norm_num : (0 : ℝ) ≤ 1) ?_
    dsimp only [Cst]; exact le_max_left _ _
  have hCst₁ : A * C₁ * Λ ^ (3 / 2 : ℝ) ≤ Cst := by
    dsimp only [Cst]
    exact le_trans (le_max_left _ _) (le_max_right _ _)
  have hCst₂ : A * C₂ * (Λ ^ ((3 : ℝ) / 2 - 22) + (BoseGases.a v) ^ (3 / 2 : ℝ)) ≤ Cst := by
    dsimp only [Cst]
    exact le_trans (le_max_right _ _) (le_max_right _ _)
  refine ⟨Cst, hCst0, ?_⟩
  intro μ hμ hRℓ h2R N n Φ i j hij
  have hside : 0 < Work.BoseBox.sideAt μ (BoseGases.a v) := Work.BoseBox.sideAt_pos hμ hav
  have hellH : Work.BoseBoxFock.ellH v μ = Work.BoseBox.sideAt μ (BoseGases.a v) := by
    rw [Work.BoseBoxFock.ellH, if_pos hside]
  have hℓpos : 0 < Work.BoseBoxFock.ellH v μ := by rw [hellH]; exact hside
  have hκpos : 0 < Work.BoseBoxFock.PCFU.chKappa v μ := chKappa_pos_rpow v hμ hav
  -- the box-restricted state
  set Θ : Submission.BoseGases.X n → ℝ :=
    Work.BoseBoxFock.boxRestrictR (Work.BoseBoxFock.ellH v μ)
      (Φ : Submission.BoseGases.X n → ℝ) with hΘdef
  have hΘm : Measurable Θ := by
    rw [hΘdef]
    exact (Φ.contDiff.continuous.measurable).mul
      (measurable_const.indicator (Submission.BoseGases.abox_measurable n _))
  have hΘb : ∃ B : ℝ, ∀ x, |Θ x| ≤ B := by
    obtain ⟨B, hB⟩ := (Submission.BoseGases.abox_compact n hℓpos).exists_bound_of_continuousOn
      (s := Submission.BoseGases.abox n (Work.BoseBoxFock.ellH v μ))
      (f := (Φ : Submission.BoseGases.X n → ℝ)) Φ.contDiff.continuous.continuousOn
    refine ⟨max B 0, fun x => ?_⟩
    rw [hΘdef]
    simp only [Work.BoseBoxFock.boxRestrictR]
    by_cases hx : x ∈ Submission.BoseGases.abox n (Work.BoseBoxFock.ellH v μ)
    · rw [Set.indicator_of_mem hx, mul_one]
      exact le_trans (by simpa only [Real.norm_eq_abs] using hB x hx) (le_max_left _ _)
    · rw [Set.indicator_of_notMem hx, mul_zero, abs_zero]
      exact le_max_right _ _
  have hA : ∀ w : E3, ‖Work.BoseBoxFock.PCFU.KχfrU v h μ fu N w‖ ≤ A :=
    fun w => hAK μ hμ hRℓ h2R N w
  -- the kernel sum
  set Sf : E3 → E3 → ℂ := fun u w => ∑' d : Fin 3 → ℤ, if d = 0 then (0 : ℂ) else
      ((Work.BoseBoxFock.PCFU.lowKer fc (Work.BoseBoxFock.PCFU.chKappa v μ)
        (u + w + (Work.BoseBoxFock.ellH v μ) • Work.BoseBoxFock.latVec d) : ℝ) : ℂ) with hSf
  -- the state norms
  have hnormB : (∫ x in Submission.BoseGases.abox n (Work.BoseBoxFock.ellH v μ),
      ((Φ : Submission.BoseGases.X n → ℝ) x) ^ 2) = Work.BoseBoxFix.normB v μ n Φ := by
    rw [Work.BoseBoxFix.normB, Work.BoseKinLoc.sqNormB, hellH]
  have hΘsq : (∫ x in Submission.BoseGases.abox n (Work.BoseBoxFock.ellH v μ), (Θ x) ^ 2)
      = ∫ x in Submission.BoseGases.abox n (Work.BoseBoxFock.ellH v μ),
          ((Φ : Submission.BoseGases.X n → ℝ) x) ^ 2 := by
    refine MeasureTheory.integral_congr_ae ?_
    filter_upwards [MeasureTheory.ae_restrict_mem
      (Submission.BoseGases.abox_measurable n (Work.BoseBoxFock.ellH v μ))] with x hx
    have hx' : Θ x = (Φ : Submission.BoseGases.X n → ℝ) x := by
      simp only [hΘdef, Work.BoseBoxFock.boxRestrictR, Set.indicator_of_mem hx, mul_one]
    rw [hx']
  have hidem : Work.BoseBoxFock.boxRestrictR (Work.BoseBoxFock.ellH v μ) Θ = Θ := by
    funext x
    by_cases hx : x ∈ Submission.BoseGases.abox n (Work.BoseBoxFock.ellH v μ)
    · have hx' : Θ x = (Φ : Submission.BoseGases.X n → ℝ) x := by
        simp only [hΘdef, Work.BoseBoxFock.boxRestrictR, Set.indicator_of_mem hx, mul_one]
      simp only [Work.BoseBoxFock.boxRestrictR, Set.indicator_of_mem hx, mul_one, hx']
    · have hx' : Θ x = 0 := by
        simp only [hΘdef, Work.BoseBoxFock.boxRestrictR, Set.indicator_of_notMem hx, mul_zero]
      simp only [Work.BoseBoxFock.boxRestrictR, Set.indicator_of_notMem hx, mul_zero, hx']
  have hboxvol : (∫ w : E3,
      (Work.BoseK15.corpusBox.boxL (Work.BoseBoxFock.ellH v μ)).indicator
        (fun _ => (1 : ℝ)) w) = (Work.BoseBoxFock.ellH v μ) ^ 3 :=
    integral_indicator_boxL hℓpos
  rcases le_or_gt (Work.BoseBoxFock.ellH v μ) Λ with hcase | hcase
  · -- ============================ CASE 1: `ℓ ≤ Λ` ============================
    have hW₁0 : 0 ≤ C₁ * (1 + (Work.BoseBoxFock.PCFU.chKappa v μ) ^ (2 * M₀))
        * (Work.BoseBoxFock.PCFU.chKappa v μ) ^ ((3 : ℤ) - 2 * (M₀ : ℤ))
        / (Work.BoseBoxFock.ellH v μ) ^ (2 * M₀ - 3) / (Work.BoseBoxFock.ellH v μ) ^ 3 := by
      refine div_nonneg (div_nonneg ?_ (pow_nonneg hℓpos.le _)) (pow_nonneg hℓpos.le _)
      exact mul_nonneg (mul_nonneg hC₁0 (by positivity)) (zpow_nonneg hκpos.le _)
    set W₁ : E3 → ℝ := fun w => (C₁ * (1 + (Work.BoseBoxFock.PCFU.chKappa v μ) ^ (2 * M₀))
        * (Work.BoseBoxFock.PCFU.chKappa v μ) ^ ((3 : ℤ) - 2 * (M₀ : ℤ))
        / (Work.BoseBoxFock.ellH v μ) ^ (2 * M₀ - 3) / (Work.BoseBoxFock.ellH v μ) ^ 3)
        * (Work.BoseK15.corpusBox.boxL (Work.BoseBoxFock.ellH v μ)).indicator
            (fun _ => (1 : ℝ)) w with hW1def
    have hW1nn : ∀ w, 0 ≤ W₁ w := fun w => by
      rw [hW1def]
      exact mul_nonneg hW₁0 (Set.indicator_nonneg (fun _ _ => zero_le_one) w)
    have hW1int : MeasureTheory.Integrable W₁ := by
      rw [hW1def]
      exact integrable_const_indicator_boxL (Work.BoseBoxFock.ellH v μ) _
    have hpt₁ : ∀ w (u : E3), u ∈ Submission.BoseGases.acube (Work.BoseBoxFock.ellH v μ) →
        Submission.BoseGases.chiScale (Work.BoseBoxFock.ellH v μ) w * ‖Sf u w‖ ≤ W₁ w := by
      intro w u hu
      by_cases hw : w ∈ Work.BoseK15.corpusBox.boxL (Work.BoseBoxFock.ellH v μ)
      · rw [hW1def]
        beta_reduce
        rw [Set.indicator_of_mem hw, mul_one]
        have hSl : Sf u w = (∑' d : Fin 3 → ℤ, if d = 0 then (0 : ℂ) else
            ((Work.BoseBoxFock.PCFU.lowKer fc (Work.BoseBoxFock.PCFU.chKappa v μ)
              (u + w + (Work.BoseBoxFock.ellH v μ) • Work.BoseBoxFock.latVec d) : ℝ) : ℂ)) := rfl
        rw [hSl]
        have hP := hC₁ hκpos hℓpos (-w) u hu
        rw [chiScale_even] at hP
        have hsum : (∑' d : Fin 3 → ℤ, if d = 0 then (0 : ℂ) else
              ((Work.BoseBoxFock.PCFU.lowKer fc (Work.BoseBoxFock.PCFU.chKappa v μ)
                (u - (-w) + (Work.BoseBoxFock.ellH v μ) • Work.BoseBoxFock.latVec d) : ℝ) : ℂ))
            = (∑' d : Fin 3 → ℤ, if d = 0 then (0 : ℂ) else
              ((Work.BoseBoxFock.PCFU.lowKer fc (Work.BoseBoxFock.PCFU.chKappa v μ)
                (u + w + (Work.BoseBoxFock.ellH v μ) • Work.BoseBoxFock.latVec d) : ℝ) : ℂ)) := by
          refine tsum_congr (fun d => ?_)
          rw [sub_neg_eq_add]
        rw [hsum] at hP
        have h1 : ‖((Submission.BoseGases.chiScale (Work.BoseBoxFock.ellH v μ) w : ℝ) : ℂ)‖
            = Submission.BoseGases.chiScale (Work.BoseBoxFock.ellH v μ) w := by
          have hnn : 0 ≤ Submission.BoseGases.chiScale (Work.BoseBoxFock.ellH v μ) w := by
            rw [Submission.BoseGases.chiScale]
            exact Submission.BoseGases.chi_nonneg _
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnn]
        have h2 : ‖((((Work.BoseBoxFock.ellH v μ) ^ 3 : ℝ)) : ℂ)‖
            = (Work.BoseBoxFock.ellH v μ) ^ 3 := by
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        rw [norm_mul, norm_mul, h1, h2] at hP
        refine (le_div_iff₀ (pow_pos hℓpos 3)).mpr ?_
        calc Submission.BoseGases.chiScale (Work.BoseBoxFock.ellH v μ) w
              * ‖(∑' d : Fin 3 → ℤ, if d = 0 then (0 : ℂ) else
                ((Work.BoseBoxFock.PCFU.lowKer fc (Work.BoseBoxFock.PCFU.chKappa v μ)
                  (u + w + (Work.BoseBoxFock.ellH v μ) • Work.BoseBoxFock.latVec d) : ℝ) : ℂ))‖
              * (Work.BoseBoxFock.ellH v μ) ^ 3
            = (Submission.BoseGases.chiScale (Work.BoseBoxFock.ellH v μ) w
                * (Work.BoseBoxFock.ellH v μ) ^ 3)
              * ‖(∑' d : Fin 3 → ℤ, if d = 0 then (0 : ℂ) else
                ((Work.BoseBoxFock.PCFU.lowKer fc (Work.BoseBoxFock.PCFU.chKappa v μ)
                  (u + w + (Work.BoseBoxFock.ellH v μ) • Work.BoseBoxFock.latVec d) : ℝ) : ℂ))‖ := by
              ring
          _ ≤ C₁ * (1 + (Work.BoseBoxFock.PCFU.chKappa v μ) ^ (2 * M₀))
                * (Work.BoseBoxFock.PCFU.chKappa v μ) ^ ((3 : ℤ) - 2 * (M₀ : ℤ))
                / (Work.BoseBoxFock.ellH v μ) ^ (2 * M₀ - 3) := hP
      · rw [hW1def]
        beta_reduce
        rw [Set.indicator_of_notMem hw]
        have hzero : Submission.BoseGases.chiScale (Work.BoseBoxFock.ellH v μ) w = 0 :=
          chiScale_eq_zero_of_notMem_boxL hℓpos hw
        rw [hzero, zero_mul, mul_zero]
    have hfib₁ : ‖Work.BoseBoxFock.PCFU.chDimg v h fc fu μ N i j
          (Work.BoseBoxFock.boxRestrictR (Work.BoseBoxFock.ellH v μ)
            (Φ : Submission.BoseGases.X n → ℝ))‖
        ≤ (Work.BoseBoxFock.ellH v μ) ^ 3 * A * (∫ w, W₁ w)
          * (∫ x in Submission.BoseGases.abox n (Work.BoseBoxFock.ellH v μ),
              ((Φ : Submission.BoseGases.X n → ℝ) x) ^ 2) := by
      obtain ⟨B, hΘB⟩ := hΘb
      have h := chDimg_fibre_le (v := v) (h := h) (fc := fc) (fu := fu) (μ := μ) (N := N)
        i j hij hℓpos hΘm (B := B) hΘB hW1nn hW1int hA0 hA hpt₁
      rw [hidem, hΘsq] at h
      exact h
    have hWint : (∫ w, W₁ w) = C₁ * (1 + (Work.BoseBoxFock.PCFU.chKappa v μ) ^ (2 * M₀))
        * ((Work.BoseBoxFock.PCFU.chKappa v μ * Work.BoseBoxFock.ellH v μ)⁻¹) ^ (2 * M₀ - 3) := by
      rw [hW1def]
      beta_reduce
      rw [MeasureTheory.integral_const_mul, hboxvol]
      have hκpow : (Work.BoseBoxFock.PCFU.chKappa v μ) ^ ((3 : ℤ) - 2 * (M₀ : ℤ))
          = ((Work.BoseBoxFock.PCFU.chKappa v μ)⁻¹) ^ (2 * M₀ - 3) := by
        rw [show ((3 : ℤ) - 2 * (M₀ : ℤ)) = -(((2 * M₀ - 3 : ℕ)) : ℤ) by omega,
          zpow_neg, zpow_natCast, inv_pow]
      rw [hκpow, div_eq_mul_inv, div_eq_mul_inv, inv_pow, inv_pow]
      field_simp
      rw [mul_pow]
      ring
    have hfinal : ‖Work.BoseBoxFock.PCFU.chDimg v h fc fu μ N i j
          (Work.BoseBoxFock.boxRestrictR (Work.BoseBoxFock.ellH v μ)
            (Φ : Submission.BoseGases.X n → ℝ))‖
        ≤ Cst * (1 + (Work.BoseBoxFock.PCFU.chKappa v μ) ^ (2 * M₀))
            * ((Work.BoseBoxFock.PCFU.chKappa v μ * Work.BoseBoxFock.ellH v μ)⁻¹) ^ (2 * M₀ - 3)
            * (Work.BoseBoxFock.ellH v μ) ^ (3 / 2 : ℝ) * Work.BoseBoxFix.normB v μ n Φ := by
      have hnormB0 : 0 ≤ Work.BoseBoxFix.normB v μ n Φ := by
        rw [Work.BoseBoxFix.normB, Work.BoseKinLoc.sqNormB]
        exact MeasureTheory.integral_nonneg (fun x => sq_nonneg _)
      have hℓ3 : (Work.BoseBoxFock.ellH v μ) ^ (3 : ℕ)
          = (Work.BoseBoxFock.ellH v μ) ^ (3 / 2 : ℝ)
            * (Work.BoseBoxFock.ellH v μ) ^ (3 / 2 : ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_add hℓpos]
        norm_num
      refine le_trans hfib₁ ?_
      have hcore : A * C₁ * (Work.BoseBoxFock.ellH v μ) ^ (3 / 2 : ℝ) ≤ Cst :=
        le_trans (mul_le_mul_of_nonneg_left
          (Real.rpow_le_rpow hℓpos.le hcase (by norm_num)) (by positivity)) hCst₁
      have hc : (Work.BoseBoxFock.ellH v μ) ^ (3 : ℕ) * A * C₁
          ≤ Cst * (Work.BoseBoxFock.ellH v μ) ^ (3 / 2 : ℝ) := by
        rw [hℓ3]
        calc (Work.BoseBoxFock.ellH v μ) ^ (3 / 2 : ℝ) * (Work.BoseBoxFock.ellH v μ) ^ (3 / 2 : ℝ)
              * A * C₁
            = (A * C₁ * (Work.BoseBoxFock.ellH v μ) ^ (3 / 2 : ℝ))
              * (Work.BoseBoxFock.ellH v μ) ^ (3 / 2 : ℝ) := by ring
          _ ≤ Cst * (Work.BoseBoxFock.ellH v μ) ^ (3 / 2 : ℝ) :=
              mul_le_mul_of_nonneg_right hcore (by positivity)
      calc (Work.BoseBoxFock.ellH v μ) ^ (3 : ℕ) * A * (∫ w, W₁ w)
            * (∫ x in Submission.BoseGases.abox n (Work.BoseBoxFock.ellH v μ),
                ((Φ : Submission.BoseGases.X n → ℝ) x) ^ 2)
          = (Work.BoseBoxFock.ellH v μ) ^ (3 : ℕ) * A
            * (C₁ * (1 + (Work.BoseBoxFock.PCFU.chKappa v μ) ^ (2 * M₀))
              * ((Work.BoseBoxFock.PCFU.chKappa v μ * Work.BoseBoxFock.ellH v μ)⁻¹) ^ (2 * M₀ - 3))
            * Work.BoseBoxFix.normB v μ n Φ := by rw [hWint, hnormB]
        _ = ((Work.BoseBoxFock.ellH v μ) ^ (3 : ℕ) * A * C₁)
            * ((1 + (Work.BoseBoxFock.PCFU.chKappa v μ) ^ (2 * M₀))
              * ((Work.BoseBoxFock.PCFU.chKappa v μ * Work.BoseBoxFock.ellH v μ)⁻¹) ^ (2 * M₀ - 3))
            * Work.BoseBoxFix.normB v μ n Φ := by ring
        _ ≤ (Cst * (Work.BoseBoxFock.ellH v μ) ^ (3 / 2 : ℝ))
            * ((1 + (Work.BoseBoxFock.PCFU.chKappa v μ) ^ (2 * M₀))
              * ((Work.BoseBoxFock.PCFU.chKappa v μ * Work.BoseBoxFock.ellH v μ)⁻¹) ^ (2 * M₀ - 3))
            * Work.BoseBoxFix.normB v μ n Φ :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hc (by positivity)) hnormB0
        _ = Cst * (1 + (Work.BoseBoxFock.PCFU.chKappa v μ) ^ (2 * M₀))
            * ((Work.BoseBoxFock.PCFU.chKappa v μ * Work.BoseBoxFock.ellH v μ)⁻¹) ^ (2 * M₀ - 3)
            * (Work.BoseBoxFock.ellH v μ) ^ (3 / 2 : ℝ) * Work.BoseBoxFix.normB v μ n Φ := by ring
    exact hfinal
  · -- ============================ CASE 2: `Λ ≤ ℓ` ============================
    -- the parametrisation facts
    have ht : 0 < μ * (BoseGases.a v) ^ 3 := by positivity
    have hℓparam : Work.BoseBoxFock.ellH v μ
        = BoseGases.a v * (μ * (BoseGases.a v) ^ 3) ^ (-(163 / 323) : ℝ) :=
      ellH_eq_rpow v hμ hav
    have hκℓparam : Work.BoseBoxFock.PCFU.chKappa v μ * Work.BoseBoxFock.ellH v μ
        = (μ * (BoseGases.a v) ^ 3) ^ (-(12 / 323) : ℝ) := by
      rw [chKappa_mul_ellH_rpow v hμ hav, inv_pow, ← Real.rpow_natCast,
        ← Real.rpow_mul (le_of_lt ht), ← Real.rpow_neg (le_of_lt ht)]
      congr 1
      norm_num
    have harith := chDimg_caseArith (a := BoseGases.a v) (t := μ * (BoseGases.a v) ^ 3)
      (κ := Work.BoseBoxFock.PCFU.chKappa v μ) (ℓ := Work.BoseBoxFock.ellH v μ)
      (j := 11) (le_refl 11) hav ht hℓparam hκℓparam hcase.le
    -- the pointwise bound with `(M,N) = (2M₀+19, M₀+11)`
    have hW₂0 : 0 ≤ C₂ * (1 + (Work.BoseBoxFock.PCFU.chKappa v μ) ^ (2 * (M₀ + 11)))
        * (Work.BoseBoxFock.PCFU.chKappa v μ) ^ ((3 : ℤ) - 2 * (((M₀ + 11 : ℕ)) : ℤ))
        / (Work.BoseBoxFock.ellH v μ) ^ (2 * M₀ + 19) / (Work.BoseBoxFock.ellH v μ) ^ 3 := by
      refine div_nonneg (div_nonneg ?_ (pow_nonneg hℓpos.le _)) (pow_nonneg hℓpos.le _)
      exact mul_nonneg (mul_nonneg hC₂0 (by positivity)) (zpow_nonneg hκpos.le _)
    set W₂ : E3 → ℝ := fun w => (C₂ * (1 + (Work.BoseBoxFock.PCFU.chKappa v μ) ^ (2 * (M₀ + 11)))
        * (Work.BoseBoxFock.PCFU.chKappa v μ) ^ ((3 : ℤ) - 2 * (((M₀ + 11 : ℕ)) : ℤ))
        / (Work.BoseBoxFock.ellH v μ) ^ (2 * M₀ + 19) / (Work.BoseBoxFock.ellH v μ) ^ 3)
        * (Work.BoseK15.corpusBox.boxL (Work.BoseBoxFock.ellH v μ)).indicator
            (fun _ => (1 : ℝ)) w with hW2def
    have hW2nn : ∀ w, 0 ≤ W₂ w := fun w => by
      rw [hW2def]
      exact mul_nonneg hW₂0 (Set.indicator_nonneg (fun _ _ => zero_le_one) w)
    have hW2int : MeasureTheory.Integrable W₂ := by
      rw [hW2def]
      exact integrable_const_indicator_boxL (Work.BoseBoxFock.ellH v μ) _
    have hpt₂ : ∀ w (u : E3), u ∈ Submission.BoseGases.acube (Work.BoseBoxFock.ellH v μ) →
        Submission.BoseGases.chiScale (Work.BoseBoxFock.ellH v μ) w * ‖Sf u w‖ ≤ W₂ w := by
      intro w u hu
      by_cases hw : w ∈ Work.BoseK15.corpusBox.boxL (Work.BoseBoxFock.ellH v μ)
      · rw [hW2def]
        beta_reduce
        rw [Set.indicator_of_mem hw, mul_one]
        have hSl : Sf u w = (∑' d : Fin 3 → ℤ, if d = 0 then (0 : ℂ) else
            ((Work.BoseBoxFock.PCFU.lowKer fc (Work.BoseBoxFock.PCFU.chKappa v μ)
              (u + w + (Work.BoseBoxFock.ellH v μ) • Work.BoseBoxFock.latVec d) : ℝ) : ℂ)) := rfl
        rw [hSl]
        have hP := hC₂ hκpos hℓpos (-w) u hu
        rw [chiScale_even] at hP
        have hsum : (∑' d : Fin 3 → ℤ, if d = 0 then (0 : ℂ) else
              ((Work.BoseBoxFock.PCFU.lowKer fc (Work.BoseBoxFock.PCFU.chKappa v μ)
                (u - (-w) + (Work.BoseBoxFock.ellH v μ) • Work.BoseBoxFock.latVec d) : ℝ) : ℂ))
            = (∑' d : Fin 3 → ℤ, if d = 0 then (0 : ℂ) else
              ((Work.BoseBoxFock.PCFU.lowKer fc (Work.BoseBoxFock.PCFU.chKappa v μ)
                (u + w + (Work.BoseBoxFock.ellH v μ) • Work.BoseBoxFock.latVec d) : ℝ) : ℂ)) := by
          refine tsum_congr (fun d => ?_)
          rw [sub_neg_eq_add]
        rw [hsum] at hP
        have h1 : ‖((Submission.BoseGases.chiScale (Work.BoseBoxFock.ellH v μ) w : ℝ) : ℂ)‖
            = Submission.BoseGases.chiScale (Work.BoseBoxFock.ellH v μ) w := by
          have hnn : 0 ≤ Submission.BoseGases.chiScale (Work.BoseBoxFock.ellH v μ) w := by
            rw [Submission.BoseGases.chiScale]
            exact Submission.BoseGases.chi_nonneg _
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnn]
        have h2 : ‖((((Work.BoseBoxFock.ellH v μ) ^ 3 : ℝ)) : ℂ)‖
            = (Work.BoseBoxFock.ellH v μ) ^ 3 := by
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
        rw [norm_mul, norm_mul, h1, h2] at hP
        refine (le_div_iff₀ (pow_pos hℓpos 3)).mpr ?_
        calc Submission.BoseGases.chiScale (Work.BoseBoxFock.ellH v μ) w
              * ‖(∑' d : Fin 3 → ℤ, if d = 0 then (0 : ℂ) else
                ((Work.BoseBoxFock.PCFU.lowKer fc (Work.BoseBoxFock.PCFU.chKappa v μ)
                  (u + w + (Work.BoseBoxFock.ellH v μ) • Work.BoseBoxFock.latVec d) : ℝ) : ℂ))‖
              * (Work.BoseBoxFock.ellH v μ) ^ 3
            = (Submission.BoseGases.chiScale (Work.BoseBoxFock.ellH v μ) w
                * (Work.BoseBoxFock.ellH v μ) ^ 3)
              * ‖(∑' d : Fin 3 → ℤ, if d = 0 then (0 : ℂ) else
                ((Work.BoseBoxFock.PCFU.lowKer fc (Work.BoseBoxFock.PCFU.chKappa v μ)
                  (u + w + (Work.BoseBoxFock.ellH v μ) • Work.BoseBoxFock.latVec d) : ℝ) : ℂ))‖ := by
              ring
          _ ≤ C₂ * (1 + (Work.BoseBoxFock.PCFU.chKappa v μ) ^ (2 * (M₀ + 11)))
                * (Work.BoseBoxFock.PCFU.chKappa v μ) ^ ((3 : ℤ) - 2 * (((M₀ + 11 : ℕ)) : ℤ))
                / (Work.BoseBoxFock.ellH v μ) ^ (2 * M₀ + 19) := hP
      · rw [hW2def]
        beta_reduce
        rw [Set.indicator_of_notMem hw]
        have hzero : Submission.BoseGases.chiScale (Work.BoseBoxFock.ellH v μ) w = 0 :=
          chiScale_eq_zero_of_notMem_boxL hℓpos hw
        rw [hzero, zero_mul, mul_zero]
    have hfib₂ : ‖Work.BoseBoxFock.PCFU.chDimg v h fc fu μ N i j
          (Work.BoseBoxFock.boxRestrictR (Work.BoseBoxFock.ellH v μ)
            (Φ : Submission.BoseGases.X n → ℝ))‖
        ≤ (Work.BoseBoxFock.ellH v μ) ^ 3 * A * (∫ w, W₂ w)
          * (∫ x in Submission.BoseGases.abox n (Work.BoseBoxFock.ellH v μ),
              ((Φ : Submission.BoseGases.X n → ℝ) x) ^ 2) := by
      obtain ⟨B, hΘB⟩ := hΘb
      have h := chDimg_fibre_le (v := v) (h := h) (fc := fc) (fu := fu) (μ := μ) (N := N)
        i j hij hℓpos hΘm (B := B) hΘB hW2nn hW2int hA0 hA hpt₂
      rw [hidem, hΘsq] at h
      exact h
    have hW2int_eq : (∫ w, W₂ w) = C₂ * (1 + (Work.BoseBoxFock.PCFU.chKappa v μ) ^ (2 * (M₀ + 11)))
        * ((Work.BoseBoxFock.PCFU.chKappa v μ * Work.BoseBoxFock.ellH v μ)⁻¹) ^ (2 * M₀ + 19) := by
      rw [hW2def]
      beta_reduce
      rw [MeasureTheory.integral_const_mul, hboxvol]
      have hκpow : (Work.BoseBoxFock.PCFU.chKappa v μ) ^ ((3 : ℤ) - 2 * (((M₀ + 11 : ℕ)) : ℤ))
          = ((Work.BoseBoxFock.PCFU.chKappa v μ)⁻¹) ^ (2 * M₀ + 19) := by
        rw [show ((3 : ℤ) - 2 * (((M₀ + 11 : ℕ)) : ℤ))
              = -(((2 * M₀ + 19 : ℕ)) : ℤ) by omega, zpow_neg, zpow_natCast, inv_pow]
      rw [hκpow, div_eq_mul_inv, div_eq_mul_inv, inv_pow, inv_pow]
      field_simp
      rw [mul_pow]
      ring
    -- the coefficient comparison
    have harith' : (1 + (Work.BoseBoxFock.PCFU.chKappa v μ) ^ (-(2 * (11 : ℤ))))
          * (Work.BoseBoxFock.ellH v μ) ^ ((3 : ℝ) / 2 - 2 * (11 : ℝ))
        ≤ max (BoseGases.a v) 1 ^ ((3 : ℝ) / 2 - 22) + (BoseGases.a v) ^ (3 / 2 : ℝ) := by
      convert harith using 2 <;> norm_num
    have hcoef : (Work.BoseBoxFock.ellH v μ) ^ (3 : ℕ) * A
          * (C₂ * (1 + (Work.BoseBoxFock.PCFU.chKappa v μ) ^ (2 * (M₀ + 11)))
            * ((Work.BoseBoxFock.PCFU.chKappa v μ * Work.BoseBoxFock.ellH v μ)⁻¹) ^ (2 * M₀ + 19))
        ≤ Cst * (1 + (Work.BoseBoxFock.PCFU.chKappa v μ) ^ (2 * M₀))
          * ((Work.BoseBoxFock.PCFU.chKappa v μ * Work.BoseBoxFock.ellH v μ)⁻¹) ^ (2 * M₀ - 3)
          * (Work.BoseBoxFock.ellH v μ) ^ (3 / 2 : ℝ) :=
      chDimg_coefB (M₀ := M₀) (Λ := max (BoseGases.a v) 1) (a := BoseGases.a v) (by omega) hA0 hC₂0 hCst0 hℓpos hκpos harith' hCst₂
    have hfinal : ‖Work.BoseBoxFock.PCFU.chDimg v h fc fu μ N i j
          (Work.BoseBoxFock.boxRestrictR (Work.BoseBoxFock.ellH v μ)
            (Φ : Submission.BoseGases.X n → ℝ))‖
        ≤ Cst * (1 + (Work.BoseBoxFock.PCFU.chKappa v μ) ^ (2 * M₀))
            * ((Work.BoseBoxFock.PCFU.chKappa v μ * Work.BoseBoxFock.ellH v μ)⁻¹) ^ (2 * M₀ - 3)
            * (Work.BoseBoxFock.ellH v μ) ^ (3 / 2 : ℝ) * Work.BoseBoxFix.normB v μ n Φ := by
      have hnormB0 : 0 ≤ Work.BoseBoxFix.normB v μ n Φ := by
        rw [Work.BoseBoxFix.normB, Work.BoseKinLoc.sqNormB]
        exact MeasureTheory.integral_nonneg (fun x => sq_nonneg _)
      refine le_trans hfib₂ ?_
      calc (Work.BoseBoxFock.ellH v μ) ^ (3 : ℕ) * A * (∫ w, W₂ w)
            * (∫ x in Submission.BoseGases.abox n (Work.BoseBoxFock.ellH v μ),
                ((Φ : Submission.BoseGases.X n → ℝ) x) ^ 2)
          = (Work.BoseBoxFock.ellH v μ) ^ (3 : ℕ) * A
            * (C₂ * (1 + (Work.BoseBoxFock.PCFU.chKappa v μ) ^ (2 * (M₀ + 11)))
              * ((Work.BoseBoxFock.PCFU.chKappa v μ * Work.BoseBoxFock.ellH v μ)⁻¹) ^ (2 * M₀ + 19))
            * Work.BoseBoxFix.normB v μ n Φ := by rw [hW2int_eq, hnormB]
        _ ≤ (Cst * (1 + (Work.BoseBoxFock.PCFU.chKappa v μ) ^ (2 * M₀))
              * ((Work.BoseBoxFock.PCFU.chKappa v μ * Work.BoseBoxFock.ellH v μ)⁻¹) ^ (2 * M₀ - 3)
              * (Work.BoseBoxFock.ellH v μ) ^ (3 / 2 : ℝ)) * Work.BoseBoxFix.normB v μ n Φ :=
            mul_le_mul_of_nonneg_right hcoef hnormB0
        _ = Cst * (1 + (Work.BoseBoxFock.PCFU.chKappa v μ) ^ (2 * M₀))
            * ((Work.BoseBoxFock.PCFU.chKappa v μ * Work.BoseBoxFock.ellH v μ)⁻¹) ^ (2 * M₀ - 3)
            * (Work.BoseBoxFock.ellH v μ) ^ (3 / 2 : ℝ) * Work.BoseBoxFix.normB v μ n Φ := by ring
    exact hfinal

end Work.BoseBoxFock.PCFU
