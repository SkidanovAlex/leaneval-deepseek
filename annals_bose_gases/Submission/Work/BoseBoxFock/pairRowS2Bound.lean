import ChallengeDeps
import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Submission.Work.BoseBoxFock.K1exp_meas_bdd
import Submission.Work.BoseBoxFock.W1omega_weight_facts
import Submission.Work.BoseBoxFock.exists_threshold_sideAt_ge_mul
import Submission.Work.BoseBoxFock.kinFormBLeLowBudgetB
import Submission.Work.BoseBoxFock.pairRowHonestRed
import Submission.Work.BoseBoxFock.pairRowS2Arith
import Submission.Work.BoseBoxFock.pinCond_norm_sq
import Submission.Work.BoseBoxFock.pinDirChi_le_kinFormB
import Submission.Work.BoseBoxFock.rowPairSubC_stateDir_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.pairRowS2Bound` — the (S2) substitution of the `Q₂` row, at the honest data

This file is the *instantiation* of the (S2) interface of
`FINDING_PotPairRows_exists.md` §12.1 at the honest data
(`Θ = boxRestrictC (ellH v μ) Φ`, `A = pinCond v μ c`, `KI = K1exp` with the coefficients
`k1cfun fu W₁ W₂`, `KII = K1exp` with `k1cfun fu W₁ 0`), together with the choice of the truncation
`ε(μ)` and of the mode threshold `Nmin μ`.

The ingredients (all PROVED, all in the import cone above):

* `rowPairSubC_stateDir_le` — the row-level (S2) bound with the `n`-free row sum
  `Cf ℓ n² (cA²√pinL2√(pinDirChi+pinL2) + (∫‖A‖²)(∫‖Θ‖²))`;
* `K1exp_sub_K1lim_pairing_dirB` — the pairing accuracy `ε` at any `N ≥ N₀(ε,μ)`;
* `W1fun_integrable_of_regime`, `W1omega_weight_facts`, `L1Tails.W1fun_coulomb_le` — the `L¹`
  weight facts at the honest weights `W₁ = W1fun`, `W₁ω = W1omegaFun` (they need the régime
  `R/ℓ ≤ r₁` and the quadratic deviation of `χ ⋆ χ`, obtained from
  `Submission.BoseGases.conv3chi_second_order_bound`);
* `kinFormBLeLowBudgetB`, `pinDirChi_le_kinFormB` (in the `n`-uniform form
  `pinDirChi_le_kinFormB_unif`, proved here since the (S2) arithmetic needs one constant which is
  valid for all particle numbers), `pairRowS2Arith` — the arithmetic;
* `pinCond_norm_sq` — `∫‖pinCond‖² = 1` at the pinning `c̄c = (ℓ³)⁻¹`.

`sorry`-free.
-/

noncomputable section
open scoped BigOperators

namespace Work.BoseBoxFock

local notation "E3" => EuclideanSpace ℝ (Fin 3)
local notation "Xn" => Work.BoseDict.Xn
local notation "boxL" => Work.BoseK15.corpusBox.boxL

section Aux

open MeasureTheory

/-- **The `∃Nmin`-trick**: for any `P : Ω → ℕ → Prop` there is a threshold function `Nmin` such
that, whenever `P ω ·` holds eventually, it holds at every `N ≥ Nmin ω`. -/
private lemma exists_Nmin {Ω : Type*} (P : Ω → ℕ → Prop) :
    ∃ Nmin : Ω → ℕ, ∀ ω (N : ℕ), (∃ N₀, ∀ N', N₀ ≤ N' → P ω N') → Nmin ω ≤ N → P ω N := by
  classical
  refine ⟨fun ω => if h : ∃ N₀, ∀ N', N₀ ≤ N' → P ω N' then h.choose else 0, fun ω N h hle => ?_⟩
  dsimp only at hle
  rw [dif_pos h] at hle
  exact h.choose_spec N hle

/-- `ellH v μ = sideAt μ (a v)` at a positive box side. -/
private lemma ellH_eq_sideAt_of_pos {v : E3 → ℝ} {μ : ℝ}
    (h : 0 < Work.BoseBox.sideAt μ (BoseGases.a v)) :
    ellH v μ = Work.BoseBox.sideAt μ (BoseGases.a v) := by
  rw [ellH, if_pos h]

/-- `W₁ = wScaled ℓ (g₀ v h)` is even (the potential and the scattering solution are radial). -/
private lemma W1fun_even {v : E3 → ℝ} {h : Work.UBB.ScatSol v} {ℓ : ℝ}
    (hvrad : _root_.BoseGases.IsRadial v) (x : E3) :
    Work.BoseFixR.W1fun v h ℓ (-x) = Work.BoseFixR.W1fun v h ℓ x := by
  simp only [Work.BoseFixR.W1fun, Submission.BoseGases.wScaled]
  rw [Submission.BoseGases.g0_even hvrad h x, Submission.BoseGases.convScale_symm ℓ x]

/-- **`IsLowB` is monotone in the threshold `J`** (`Θ(a,J,μ)` is increasing in `J`). -/
private lemma isLowB_mono_J {v : E3 → ℝ} {h : Work.UBB.ScatSol v} {J J' μ : ℝ} {n : ℕ}
    {Φ : Submission.BoseGases.X n → ℝ} (hμ : 0 < μ) (hav : 0 < BoseGases.a v) (hJJ : J ≤ J')
    (hlow : Work.BoseBoxFix.IsLowB v h J μ n Φ) : Work.BoseBoxFix.IsLowB v h J' μ n Φ := by
  unfold Work.BoseBoxFix.IsLowB at *
  refine le_trans hlow ?_
  have hΘ : Work.UBB.Theta (BoseGases.a v) J μ ≤ Work.UBB.Theta (BoseGases.a v) J' μ := by
    have hs : 0 ≤ Real.sqrt (μ * (BoseGases.a v) ^ 3) := Real.sqrt_nonneg _
    have hcoef : 0 ≤ 4 * Real.pi * μ ^ 2 * (BoseGases.a v) := by positivity
    have h1 : J * Real.sqrt (μ * (BoseGases.a v) ^ 3)
        ≤ J' * Real.sqrt (μ * (BoseGases.a v) ^ 3) :=
      mul_le_mul_of_nonneg_right hJJ hs
    have h3 : 1 - J' * Real.sqrt (μ * (BoseGases.a v) ^ 3)
        ≤ 1 - J * Real.sqrt (μ * (BoseGases.a v) ^ 3) := by linarith
    have h4 := mul_le_mul_of_nonneg_left h3 hcoef
    unfold Work.UBB.Theta
    linarith [h4]
  exact mul_le_mul_of_nonneg_right
    (mul_le_mul_of_nonneg_left hΘ (pow_nonneg (Work.BoseBox.sideAt_pos hμ hav).le 3))
    (Work.BoseFixB1.normB_nonneg Φ)

/-- **`errKafz` is positive** (at a positive chemical potential and positive scattering length). -/
private lemma errKafz_pos {v : E3 → ℝ} {R μ C : ℝ} (hμ : 0 < μ) (hav : 0 < BoseGases.a v)
    (hC : 0 < C) : 0 < Work.BoseFixR.errKafz v R μ C := by
  have hside : 0 < Work.BoseBox.sideAt μ (BoseGases.a v) := Work.BoseBox.sideAt_pos hμ hav
  have hell3 : 0 < Work.BoseFixR.ell3 v μ := by
    unfold Work.BoseFixR.ell3 Work.BoseFixR.ell
    exact pow_pos hside 3
  have hdil : 0 < Work.BoseFixR.dil v μ := by
    unfold Work.BoseFixR.dil
    positivity
  have hKl : 0 < (Work.BoseBox.paramsAt μ (BoseGases.a v)).Kl := by
    have ht : 0 < μ * (BoseGases.a v) ^ 3 := by positivity
    simp only [Work.BoseBox.paramsAt, Work.BoseBox.fsParams]
    exact Work.BoseBox.fsXp_pos ht
  have hbr : 0 < (Work.BoseBox.paramsAt μ (BoseGases.a v)).Kl ^ (-(3 : ℝ))
      + Work.BoseFixR.fsX v μ ^ 2
      + (R / BoseGases.a v) ^ 2 * Real.sqrt (Work.BoseFixR.dil v μ)
      + Work.BoseFixR.errExp v μ := by
    have h1 : 0 < (Work.BoseBox.paramsAt μ (BoseGases.a v)).Kl ^ (-(3 : ℝ)) :=
      Real.rpow_pos_of_pos hKl _
    have h2 : 0 ≤ Work.BoseFixR.fsX v μ ^ 2 := sq_nonneg _
    have h3 : 0 ≤ (R / BoseGases.a v) ^ 2 * Real.sqrt (Work.BoseFixR.dil v μ) :=
      mul_nonneg (sq_nonneg _) (Real.sqrt_nonneg _)
    have h4 : 0 ≤ Work.BoseFixR.errExp v μ := by
      unfold Work.BoseFixR.errExp
      exact Real.rpow_nonneg hdil.le _
    linarith
  unfold Work.BoseFixR.errKafz
  exact mul_pos (mul_pos (mul_pos (mul_pos (mul_pos hC (pow_pos hμ 2)) hav) hell3)
    (Real.sqrt_pos.mpr hdil)) hbr

/-- **`errKafz` is nonnegative.** -/
private lemma errKafz_nonneg {v : E3 → ℝ} {R μ C : ℝ} (hμ : 0 < μ) (hav : 0 < BoseGases.a v)
    (hC : 0 ≤ C) : 0 ≤ Work.BoseFixR.errKafz v R μ C := by
  have hside : 0 < Work.BoseBox.sideAt μ (BoseGases.a v) := Work.BoseBox.sideAt_pos hμ hav
  have hell3 : 0 ≤ Work.BoseFixR.ell3 v μ := by
    unfold Work.BoseFixR.ell3 Work.BoseFixR.ell
    exact pow_nonneg hside.le 3
  have hdil : 0 ≤ Work.BoseFixR.dil v μ := by
    unfold Work.BoseFixR.dil
    positivity
  have hbr : 0 ≤ (Work.BoseBox.paramsAt μ (BoseGases.a v)).Kl ^ (-(3 : ℝ))
      + Work.BoseFixR.fsX v μ ^ 2
      + (R / BoseGases.a v) ^ 2 * Real.sqrt (Work.BoseFixR.dil v μ)
      + Work.BoseFixR.errExp v μ := by
    have h1 : 0 ≤ (Work.BoseBox.paramsAt μ (BoseGases.a v)).Kl ^ (-(3 : ℝ)) := by
      have ht : 0 < μ * (BoseGases.a v) ^ 3 := by positivity
      simp only [Work.BoseBox.paramsAt, Work.BoseBox.fsParams]
      exact Real.rpow_nonneg (Work.BoseBox.fsXp_pos ht).le _
    have h2 : 0 ≤ Work.BoseFixR.fsX v μ ^ 2 := sq_nonneg _
    have h3 : 0 ≤ (R / BoseGases.a v) ^ 2 * Real.sqrt (Work.BoseFixR.dil v μ) :=
      mul_nonneg (sq_nonneg _) (Real.sqrt_nonneg _)
    have h4 : 0 ≤ Work.BoseFixR.errExp v μ := by
      unfold Work.BoseFixR.errExp
      exact Real.rpow_nonneg hdil _
    linarith
  unfold Work.BoseFixR.errKafz
  exact mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hC (sq_nonneg μ)) hav.le)
    hell3) (Real.sqrt_nonneg _)) hbr

/-- `‖pinCond v μ c x‖ ≤ ‖c‖`: the condensate pin is `c` times the sharp box indicator. -/
private lemma norm_pinCond_le (v : E3 → ℝ) (μ : ℝ) (c : ℂ) (x : E3) :
    ‖pinCond v μ c x‖ ≤ ‖c‖ := by
  rw [show pinCond v μ c x = c * Work.BoseK15.corpusBox.thetaFun (ellH v μ) x from rfl,
    norm_mul]
  refine mul_le_of_le_one_right (norm_nonneg c) ?_
  rw [Work.BoseB4.BoxData.thetaFun_apply]
  by_cases hx : x ∈ Work.BoseK15.corpusBox.boxL (ellH v μ)
  · rw [if_pos hx]; simp
  · rw [if_neg hx]; simp

/-- The complex box restriction of a continuous state is measurable. -/
private lemma boxRestrictC_measurable_aux {n : ℕ} (ℓ : ℝ)
    {Φ : Submission.BoseGases.X n → ℝ} (hΦc : Continuous Φ) :
    Measurable (boxRestrictC ℓ Φ) := by
  have h : boxRestrictC ℓ Φ = fun x : Submission.BoseGases.X n =>
      ((Φ x : ℝ) : ℂ) *
        ((((Submission.BoseGases.abox n ℓ).indicator (fun _ => (1 : ℝ)) x : ℝ)) : ℂ) := rfl
  rw [h]
  exact (Complex.continuous_ofReal.measurable.comp hΦc.measurable).mul
    (Complex.continuous_ofReal.measurable.comp
      (measurable_const.indicator (Submission.BoseGases.abox_measurable n ℓ)))

/-- The complex box restriction is supported in the box. -/
private lemma support_boxRestrictC_aux {n : ℕ} (ℓ : ℝ) (Φ : Submission.BoseGases.X n → ℝ) :
    Function.support (boxRestrictC ℓ Φ) ⊆ Submission.BoseGases.abox n ℓ := by
  intro x hx
  by_contra h
  exact hx (by
    rw [show boxRestrictC ℓ Φ x = ((Φ x : ℝ) : ℂ) *
        ((((Submission.BoseGases.abox n ℓ).indicator (fun _ => (1 : ℝ)) x : ℝ)) : ℂ) from rfl,
      Set.indicator_of_notMem h]
    simp)

/-- The complex box restriction is supported in `boxPow n ℓ`. -/
private lemma support_boxRestrictC_boxPow {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    (Φ : Submission.BoseGases.X n → ℝ) :
    Function.support (boxRestrictC ℓ Φ) ⊆ Work.MB.boxPow n ℓ := by
  have hab : Submission.BoseGases.abox n ℓ = Work.MB.boxPow n ℓ := by
    unfold Work.MB.boxPow
    rw [Submission.BoseGases.abox_eq_pi_acube, Work.BoseBoxFock.corpusBox_boxL_eq_acube hℓ]
  rw [← hab]
  exact support_boxRestrictC_aux ℓ Φ

/-- The complex box restriction is the indicator of the box times the (complexified) state. -/
private lemma indicator_boxRestrictC_aux {n : ℕ} (ℓ : ℝ) (Φ : Submission.BoseGases.X n → ℝ) :
    ∀ x, boxRestrictC ℓ Φ x = Set.indicator (Submission.BoseGases.abox n ℓ)
      (fun x => ((Φ x : ℝ) : ℂ)) x := by
  intro x
  by_cases hx : x ∈ Submission.BoseGases.abox n ℓ
  · rw [Set.indicator_of_mem hx]
    simp [boxRestrictC, Set.indicator_of_mem hx]
  · rw [Set.indicator_of_notMem hx]
    simp [boxRestrictC, Set.indicator_of_notMem hx]

/-- The box restriction of a continuous state is globally bounded. -/
private lemma exists_bound_boxRestrictC {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {Φ : Submission.BoseGases.X n → ℝ} (hΦ : Continuous Φ) :
    ∃ K : ℝ, ∀ x, ‖boxRestrictC ℓ Φ x‖ ≤ K := by
  obtain ⟨C, hC⟩ := (Submission.BoseGases.abox_compact n hℓ).exists_bound_of_continuousOn
    hΦ.continuousOn
  refine ⟨max C 0, fun x => ?_⟩
  by_cases hx : x ∈ Submission.BoseGases.abox n ℓ
  · rw [show boxRestrictC ℓ Φ x = ((Φ x : ℝ) : ℂ) *
        ((((Submission.BoseGases.abox n ℓ).indicator (fun _ => (1 : ℝ)) x : ℝ)) : ℂ) from rfl,
      Set.indicator_of_mem hx]
    simp only [Complex.ofReal_one, mul_one, Complex.norm_real, Real.norm_eq_abs]
    obtain ⟨hC1, hC2⟩ := abs_le.mp (hC x hx)
    refine abs_le.mpr ⟨?_, ?_⟩ <;> linarith [hC1, hC2, le_max_left C (0 : ℝ), le_max_right C (0 : ℝ)]
  · have hz : boxRestrictC ℓ Φ x = 0 := by
      rw [show boxRestrictC ℓ Φ x = ((Φ x : ℝ) : ℂ) *
          ((((Submission.BoseGases.abox n ℓ).indicator (fun _ => (1 : ℝ)) x : ℝ)) : ℂ) from rfl,
        Set.indicator_of_notMem hx]
      simp
    rw [hz, norm_zero]
    exact le_max_right C 0

/-- The `L²`-mass of the box restriction, as a set integral over the box. -/
private lemma integral_normSq_boxRestrictC {n : ℕ} {ℓ : ℝ}
    (Φ : Submission.BoseGases.X n → ℝ) :
    ∫ x : Submission.BoseGases.X n, ‖boxRestrictC ℓ Φ x‖ ^ 2
      = ∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2 := by
  have hpt : ∀ x : Submission.BoseGases.X n, ‖boxRestrictC ℓ Φ x‖ ^ 2
      = (Submission.BoseGases.abox n ℓ).indicator (fun x => (Φ x) ^ 2) x := by
    intro x
    rw [show boxRestrictC ℓ Φ x = ((Φ x : ℝ) : ℂ) *
        ((((Submission.BoseGases.abox n ℓ).indicator (fun _ => (1 : ℝ)) x : ℝ)) : ℂ) from rfl]
    by_cases hx : x ∈ Submission.BoseGases.abox n ℓ
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx,
        Complex.ofReal_one, mul_one, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]
      simp
  rw [funext hpt, MeasureTheory.integral_indicator
    (Submission.BoseGases.abox_measurable n ℓ)]

/-- The `L²`-mass of the complexified state, as a set integral over the box. -/
private lemma pinL2_ofReal_eq {n : ℕ} {ℓ : ℝ}
    (Φ : Submission.BoseGases.X n → ℝ) :
    pinL2 ℓ (fun x => ((Φ x : ℝ) : ℂ))
      = ∫ x in Submission.BoseGases.abox n ℓ, (Φ x) ^ 2 := by
  rw [pinL2]
  exact integral_congr_ae (Filter.Eventually.of_forall fun x => by
    show ‖((Φ x : ℝ) : ℂ)‖ ^ 2 = (Φ x : ℝ) ^ 2
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_ofReal]
    ring)

/-- The box restriction of a `C^∞` state is `L²`. -/
private lemma integrable_normSq_boxRestrictC {n : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ)
    {Φ : Submission.BoseGases.X n → ℝ} (hΦ : ContDiff ℝ (⊤ : ℕ∞) Φ) :
    MeasureTheory.Integrable (fun x : Submission.BoseGases.X n => ‖boxRestrictC ℓ Φ x‖ ^ 2) := by
  have hpt : ∀ x : Submission.BoseGases.X n, ‖boxRestrictC ℓ Φ x‖ ^ 2
      = (Submission.BoseGases.abox n ℓ).indicator (fun x => (Φ x) ^ 2) x := by
    intro x
    rw [show boxRestrictC ℓ Φ x = ((Φ x : ℝ) : ℂ) *
        ((((Submission.BoseGases.abox n ℓ).indicator (fun _ => (1 : ℝ)) x : ℝ)) : ℂ) from rfl]
    by_cases hx : x ∈ Submission.BoseGases.abox n ℓ
    · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx,
        Complex.ofReal_one, mul_one, Complex.norm_real, Real.norm_eq_abs, sq_abs]
    · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]
      simp
  rw [funext hpt]
  exact MeasureTheory.IntegrableOn.integrable_indicator
    (ContinuousOn.integrableOn_compact (Submission.BoseGases.abox_compact n hℓ)
      ((hΦ.continuous.pow 2).continuousOn))
    (Submission.BoseGases.abox_measurable n ℓ)

/-- The condensate pin is `L²` (it is `c` times the sharp box indicator). -/
private lemma integrable_normSq_pinCond (v : E3 → ℝ) (μ : ℝ) (c : ℂ) :
    MeasureTheory.Integrable (fun x : E3 => ‖pinCond v μ c x‖ ^ 2) := by
  have hpt : ∀ x : E3, ‖pinCond v μ c x‖ ^ 2
      = ‖c‖ ^ 2 * (Work.BoseK15.corpusBox.boxL (ellH v μ)).indicator
          (fun _ : E3 => (1 : ℝ)) x := by
    intro x
    rw [show pinCond v μ c x = c * Work.BoseK15.corpusBox.thetaFun (ellH v μ) x from rfl,
      norm_mul, mul_pow]
    congr 1
    rw [Work.BoseB4.BoxData.thetaFun_apply]
    by_cases hx : x ∈ Work.BoseK15.corpusBox.boxL (ellH v μ)
    · rw [if_pos hx, Set.indicator_of_mem hx]; norm_num
    · rw [if_neg hx, Set.indicator_of_notMem hx]; norm_num
  rw [funext hpt]
  refine MeasureTheory.Integrable.const_mul ?_ _
  have hfin : (volume : Measure E3) (Work.BoseK15.corpusBox.boxL (ellH v μ)) < ⊤ :=
    (Work.BoseBoxFock.isCompact_boxL (ellH_pos v μ)).measure_lt_top
  exact (MeasureTheory.integrable_indicator_iff
    (Work.BoseB4.BoxData.boxL_measurableSet Work.BoseK15.corpusBox (ellH v μ))).mpr
    (MeasureTheory.integrableOn_const (C := (1 : ℝ)) (hs := ne_of_lt hfin))

/-- The `L¹`-integrability of `coulInt` of the zero weight. -/
private lemma integrable_coulInt_zero :
    MeasureTheory.Integrable (coulInt (fun _ : E3 => (0 : ℝ))) := by
  have h : coulInt (fun _ : E3 => (0 : ℝ)) = fun _ : E3 × E3 => (0 : ℝ) := by
    funext p
    simp [coulInt]
  rw [h]
  exact MeasureTheory.integrable_zero (E3 × E3) ℝ (volume : Measure (E3 × E3))

/-! ## 2. The `n`-uniform form of `pinDirChi_le_kinFormB`

`pinDirChi_le_kinFormB` produces its constant *after* the state `Φ` (and hence possibly depending on
the particle number `n`), while the (S2) arithmetic below needs one constant valid for all `n`.
The proof is a verbatim transcription of the original with the `n`-quantifier moved inside the
`∃`. -/

private theorem pinDirChi_le_kinFormB_unif {v : EuclideanSpace ℝ (Fin 3) → ℝ}
    {h : Work.UBB.ScatSol v} {μ : ℝ} (hav : 0 < _root_.BoseGases.a v) (hμ : 0 < μ)
    (hd : 0 < (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d)
    (hs : 0 < (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s)
    (hb : 0 ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).b)
    (hεT0 : 0 ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT)
    (hεT1 : (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT ≤ 1) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))),
        Work.BoseBoxFock.pinDirChi (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (fun x => ((Φ x : ℝ) : ℂ))
          ≤ C * (Work.BoseKinLoc.kinFormB n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).b
                (Φ : Submission.BoseGases.X n → ℝ)
              + (n : ℝ) * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)) := by
  -- abbreviations for the parameters at FS's choice
  set ℓ : ℝ := Work.BoseBox.sideAt μ (_root_.BoseGases.a v) with hℓdef
  set d : ℝ := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d with hddef
  set s : ℝ := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s with hsdef
  set εT : ℝ := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT with hεTdef
  set b : ℝ := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).b with hbdef
  have hℓ : 0 < ℓ := by rw [hℓdef]; exact Work.BoseBox.sideAt_pos hμ hav
  have hd' : 0 < d := by rw [hddef]; exact hd
  have hs' : 0 < s := by rw [hsdef]; exact hs
  have hb' : 0 ≤ b := by rw [hbdef]; exact hb
  have hεT0' : 0 ≤ εT := by rw [hεTdef]; exact hεT0
  have hεT1' : εT ≤ 1 := by rw [hεTdef]; exact hεT1
  obtain ⟨C₁, hC₁pos, hC₁⟩ := chiSqDirichletFsT (ℓ := ℓ) (d := d) (s := s) (εT := εT) (b := b)
    hℓ hd' hs' hb' hεT0' hεT1'
  refine ⟨C₁, hC₁pos, ?_⟩
  intro n Φ
  have hΦc : ContDiff ℝ (⊤ : ℕ∞) (Φ : Submission.BoseGases.X n → ℝ) := Φ.contDiff
  -- the complexification of the fibre derivative
  have hcpx : ∀ (v : Submission.BoseGases.X n) (x : Submission.BoseGases.X n),
      fderiv ℝ (fun y : Submission.BoseGases.X n => ((Φ y : ℝ) : ℂ)) x v
        = ((fderiv ℝ (Φ : Submission.BoseGases.X n → ℝ) x v : ℝ) : ℂ) := by
    intro v x
    have h1 : HasFDerivAt (fun y : Submission.BoseGases.X n => ((Φ y : ℝ) : ℂ))
        ((Complex.ofRealCLM).comp (fderiv ℝ (Φ : Submission.BoseGases.X n → ℝ) x)) x :=
      Complex.ofRealCLM.hasFDerivAt.comp _
        ((hΦc.differentiable (by simp) x).hasFDerivAt)
    rw [h1.fderiv, ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply]
  -- continuity of the slot integrands
  have hcont (i : Fin n) (j : Fin 3) : Continuous (fun x : Submission.BoseGases.X n =>
      (Submission.BoseGases.chiScale ℓ (x i)) ^ 2 *
        ‖fderiv ℝ (fun y : Submission.BoseGases.X n => ((Φ y : ℝ) : ℂ)) x
          (Work.BoseBoxFock.slotDirVec i j)‖ ^ 2) := by
    have hfun : (fun x : Submission.BoseGases.X n =>
        (Submission.BoseGases.chiScale ℓ (x i)) ^ 2 *
          ‖fderiv ℝ (fun y : Submission.BoseGases.X n => ((Φ y : ℝ) : ℂ)) x
            (Work.BoseBoxFock.slotDirVec i j)‖ ^ 2)
        = fun x : Submission.BoseGases.X n =>
            (Submission.BoseGases.chiScale ℓ (x i)) ^ 2 *
              (fderiv ℝ (Φ : Submission.BoseGases.X n → ℝ) x
                (Work.BoseBoxFock.slotDirVec i j)) ^ 2 := by
      funext x
      rw [hcpx (Work.BoseBoxFock.slotDirVec i j) x, ← Complex.normSq_eq_norm_sq,
        Complex.normSq_ofReal]
      ring
    rw [hfun]
    exact (((Submission.BoseGases.chiScale_continuous ℓ).comp (continuous_apply i)).pow 2).mul
      (((hΦc.continuous_fderiv (by simp)).clm_apply continuous_const).pow 2)
  -- `pinDirChi` splits into its slot-`(i,j)` summands
  have hpin : Work.BoseBoxFock.pinDirChi ℓ (fun x => ((Φ x : ℝ) : ℂ))
      = ∑ i : Fin n, ∑ j : Fin 3, ∫ x in Submission.BoseGases.abox n ℓ,
          (Submission.BoseGases.chiScale ℓ (x i)) ^ 2 *
            ‖fderiv ℝ (fun y : Submission.BoseGases.X n => ((Φ y : ℝ) : ℂ)) x
              (Work.BoseBoxFock.slotDirVec i j)‖ ^ 2 := by
    rw [Work.BoseBoxFock.pinDirChi]
    rw [MeasureTheory.integral_finsetSum]
    · refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [MeasureTheory.integral_finsetSum]
      exact fun j _ => Work.BoseBoxFock.integrableOn_abox_of_continuous hℓ (hcont i j)
    · intro i _
      exact Work.BoseBoxFock.integrableOn_abox_of_continuous hℓ
        (continuous_finsetSum _ (fun j _ => hcont i j))
  -- the per-slot bound
  have hslot (i : Fin n) : (∑ j : Fin 3, ∫ x in Submission.BoseGases.abox n ℓ,
        (Submission.BoseGases.chiScale ℓ (x i)) ^ 2 *
          ‖fderiv ℝ (fun y : Submission.BoseGases.X n => ((Φ y : ℝ) : ℂ)) x
            (Work.BoseBoxFock.slotDirVec i j)‖ ^ 2)
      ≤ C₁ * (ℓ ^ (-3 : ℤ) * (∫ x in Submission.BoseGases.abox n ℓ,
            Work.BoseKinLoc.indU ℓ 0 (x i) *
              Work.BoseKinLoc.fsT ℓ d s εT b 0
                (Work.BoseKinLoc.fibre n i (Φ : Submission.BoseGases.X n → ℝ) x))
          + (∫ x in Submission.BoseGases.abox n ℓ,
              ((Φ : Submission.BoseGases.X n → ℝ) x) ^ 2)) :=
    pinDirChi_slot_le (ℓ := ℓ) (d := d) (s := s) (εT := εT) (b := b)
      (Φ := (Φ : Submission.BoseGases.X n → ℝ)) hℓ hΦc i hC₁
      (fun j => pinDirChi_slot_slice hℓ hΦc i j)
      (kinFormB_slot_fsT hℓ hΦc i).2 (kinFormB_slot_fsT hℓ hΦc i).1
      (mass_slice hℓ hΦc.continuous i)
  -- the two `Finset` identifications
  have hkinSum : (∑ i : Fin n, ℓ ^ (-3 : ℤ) * (∫ x in Submission.BoseGases.abox n ℓ,
        Work.BoseKinLoc.indU ℓ 0 (x i) *
          Work.BoseKinLoc.fsT ℓ d s εT b 0
            (Work.BoseKinLoc.fibre n i (Φ : Submission.BoseGases.X n → ℝ) x)))
      = Work.BoseKinLoc.kinFormB n ℓ d s εT b (Φ : Submission.BoseGases.X n → ℝ) := by
    rw [Work.BoseKinLoc.kinFormB, Finset.mul_sum]
  have hmassSum : (∑ i : Fin n, ∫ x in Submission.BoseGases.abox n ℓ,
        ((Φ : Submission.BoseGases.X n → ℝ) x) ^ 2)
      = (n : ℝ) * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ) := by
    rw [Work.BoseBoxFix.normB, Work.BoseKinLoc.sqNormB, ← hℓdef, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  calc Work.BoseBoxFock.pinDirChi ℓ (fun x => ((Φ x : ℝ) : ℂ))
      = ∑ i : Fin n, ∑ j : Fin 3, ∫ x in Submission.BoseGases.abox n ℓ,
          (Submission.BoseGases.chiScale ℓ (x i)) ^ 2 *
            ‖fderiv ℝ (fun y : Submission.BoseGases.X n => ((Φ y : ℝ) : ℂ)) x
              (Work.BoseBoxFock.slotDirVec i j)‖ ^ 2 := hpin
    _ ≤ ∑ i : Fin n, C₁ * (ℓ ^ (-3 : ℤ) * (∫ x in Submission.BoseGases.abox n ℓ,
            Work.BoseKinLoc.indU ℓ 0 (x i) *
              Work.BoseKinLoc.fsT ℓ d s εT b 0
                (Work.BoseKinLoc.fibre n i (Φ : Submission.BoseGases.X n → ℝ) x))
          + (∫ x in Submission.BoseGases.abox n ℓ,
              ((Φ : Submission.BoseGases.X n → ℝ) x) ^ 2)) :=
        Finset.sum_le_sum (fun i _ => hslot i)
    _ = C₁ * ((∑ i : Fin n, ℓ ^ (-3 : ℤ) * (∫ x in Submission.BoseGases.abox n ℓ,
            Work.BoseKinLoc.indU ℓ 0 (x i) *
              Work.BoseKinLoc.fsT ℓ d s εT b 0
                (Work.BoseKinLoc.fibre n i (Φ : Submission.BoseGases.X n → ℝ) x)))
          + (∑ i : Fin n, ∫ x in Submission.BoseGases.abox n ℓ,
              ((Φ : Submission.BoseGases.X n → ℝ) x) ^ 2)) := by
        simp only [mul_add, Finset.sum_add_distrib, Finset.mul_sum]
    _ = C₁ * (Work.BoseKinLoc.kinFormB n ℓ d s εT b (Φ : Submission.BoseGases.X n → ℝ)
          + (n : ℝ) * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)) := by
        rw [hkinSum, hmassSum]

end Aux

theorem pairRowS2Bound (v : ℝ³ → ℝ) (h : Work.UBB.ScatSol v) (hv : 0 ≤ v)
    (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : ℝ³) R) (hav : 0 < BoseGases.a v)
    (fc fu : Work.BoseBoxFix.LowCut) (J : ℝ) (hB3 : Work.BoseBoxFix.NodeB3B v h R fc) :
    ∃ (Nmin : ℝ → ℕ) (ε₀ C : ℝ), 0 < ε₀ ∧ 0 ≤ C ∧
      ∀ (HM : ∀ μ : ℝ, HonestModes v μ), (∀ μ, Nmin μ ≤ (HM μ).N) →
        ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
          J ≤ (Work.BoseBox.paramsAt μ (BoseGases.a v)).KB ^ 3 →
          ∀ (n : ℕ) (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (BoseGases.a v))),
            (n : ℝ) ≤ 2 * μ * Work.BoseBox.sideAt μ (BoseGases.a v) ^ 3 →
            0 < Work.BoseBoxFix.normB v μ n Φ →
            Work.BoseBoxFix.IsLowB v h J μ n Φ →
            Work.BoseBox.SpectralNPlusLe (Work.BoseBox.sideAt μ (BoseGases.a v))
              (Work.BoseBox.bigM (Work.BoseBox.paramsAt μ (BoseGases.a v)) (BoseGases.a v) μ)
              (Φ : Submission.BoseGases.X n → ℝ) →
            ∀ (c : ℂ), (starRingEnd ℂ) c * c = ((Work.BoseBoxFock.ellH v μ) ^ 3)⁻¹ →
              ‖Work.BoseBoxFock.rowPairSubC (((Work.BoseBoxFock.ellH v μ) ^ 3)⁻¹)
                  (Work.BoseBoxFock.boxRestrictC (Work.BoseBoxFock.ellH v μ) Φ)
                  (Work.BoseBoxFock.pinCond v μ c)
                  (Work.BoseBoxFock.K1exp v μ (HM μ).N (Work.BoseBoxFock.k1cfun fu
                    (Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ))
                    (Work.BoseFixR.W1omegaFun v h (Work.BoseBoxFock.ellH v μ))
                    (Work.BoseBoxFock.ellH v μ) (HM μ).N))
                  (Work.BoseBoxFock.K1exp v μ (HM μ).N (Work.BoseBoxFock.k1cfun fu
                    (Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ)) 0
                    (Work.BoseBoxFock.ellH v μ) (HM μ).N))
                - Work.BoseBoxFock.rowPairSubC (((Work.BoseBoxFock.ellH v μ) ^ 3)⁻¹)
                  (Work.BoseBoxFock.boxRestrictC (Work.BoseBoxFock.ellH v μ) Φ)
                  (Work.BoseBoxFock.pinCond v μ c)
                  (Work.BoseBoxFock.K1lim (Work.BoseBoxFock.ellH v μ)
                    (fun x => Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ) x
                      + Work.BoseFixR.W1omegaFun v h (Work.BoseBoxFock.ellH v μ) x))
                  (Work.BoseBoxFock.K1lim (Work.BoseBoxFock.ellH v μ)
                    (Work.BoseFixR.W1fun v h (Work.BoseBoxFock.ellH v μ)))‖
                ≤ (1 / 2) * Work.BoseFixR.errKafz v R μ C * Work.BoseBoxFix.normB v μ n Φ := by
  classical
  -- ## 0. the χ-shape data and the box-side threshold
  obtain ⟨chiC, hchiC0, rchi, hrchi, hchiT⟩ := Submission.BoseGases.conv3chi_second_order_bound
  set rm : ℝ := (Real.sqrt (2 * chiC + 1))⁻¹ with hrmdef
  have hrmpos : 0 < rm := by
    rw [hrmdef]
    exact inv_pos.mpr (Real.sqrt_pos.mpr (by linarith))
  have hrmsq : chiC * rm ^ 2 ≤ 1 / 2 := by
    have h1 : rm ^ 2 = (2 * chiC + 1)⁻¹ := by
      rw [hrmdef, inv_pow, Real.sq_sqrt (by linarith : (0 : ℝ) ≤ 2 * chiC + 1)]
    rw [h1, mul_inv_le_iff₀ (by linarith : (0 : ℝ) < 2 * chiC + 1)]
    linarith
  set rr : ℝ := min (1 / 4) (min rchi rm) with hrrdef
  have hrrpos : 0 < rr := lt_min (by norm_num) (lt_min hrchi hrmpos)
  have hrr4 : rr ≤ 1 / 4 := min_le_left _ _
  have hrrr : rr ≤ rchi := le_trans (min_le_right _ _) (min_le_left _ _)
  have hrrm : rr ≤ rm := le_trans (min_le_right _ _) (min_le_right _ _)
  obtain ⟨ε₃, hε₃pos, _hε₃le1, hε₃⟩ :=
    exists_threshold_sideAt_ge_mul (v := v) hav hR hrrpos
  obtain ⟨kap, εkap, hkappos, hεkappos, hkap⟩ :=
    kinFormBLeLowBudgetB (v := v) h hv hv1 hvrad hR hv_supp hav
  obtain ⟨CfRow, hCfRow0, hCfRow⟩ := rowPairSubC_stateDir_le
  -- ## 1. the local definitions (`ε(μ)`, `Nmin`)
  set C1f : ℝ → ℝ := fun μ' => if _hh : (0 < μ'
      ∧ 0 < (Work.BoseBox.paramsAt μ' (BoseGases.a v)).d
      ∧ 0 < (Work.BoseBox.paramsAt μ' (BoseGases.a v)).s
      ∧ 0 ≤ (Work.BoseBox.paramsAt μ' (BoseGases.a v)).b
      ∧ 0 ≤ (Work.BoseBox.paramsAt μ' (BoseGases.a v)).eT
      ∧ (Work.BoseBox.paramsAt μ' (BoseGases.a v)).eT ≤ 1) then
      (pinDirChi_le_kinFormB_unif (v := v) (h := h) (μ := μ') hav _hh.1 _hh.2.1 _hh.2.2.1
        _hh.2.2.2.1 _hh.2.2.2.2.1 _hh.2.2.2.2.2).choose
    else 1 with hC1fdef
  set eps : ℝ → ℝ := fun μ => Work.BoseFixR.errKafz v R μ 16 /
    (16 * max (CfRow (ellH v μ)) 1 * μ ^ 2 *
      (Real.sqrt (C1f μ * (kap * μ ^ 2 * (BoseGases.a v) * (ellH v μ) ^ 3
          + 2 * μ * (ellH v μ) ^ 3) + 1) + (ellH v μ) ^ 3)) with hepsdef
  set PairI : ℝ → ℕ → Prop := fun μ N => ∀ G : E3 → E3 → ℂ, BoxSmooth (ellH v μ) G →
      ‖∫ w in boxL (ellH v μ), ∫ y in boxL (ellH v μ),
        (K1exp v μ N (k1cfun fu (Work.BoseFixR.W1fun v h (ellH v μ))
            (Work.BoseFixR.W1omegaFun v h (ellH v μ)) (ellH v μ) N) w y
          - K1lim (ellH v μ)
              (fun x => Work.BoseFixR.W1fun v h (ellH v μ) x
                + Work.BoseFixR.W1omegaFun v h (ellH v μ) x) w y) * G w y‖
        ≤ eps μ * (Real.sqrt (Work.BoseBoxFock.L1Tails.pairEnergy (ellH v μ) G)
            + Real.sqrt (massBox (ellH v μ) G)) with hPairIdef
  set PairII : ℝ → ℕ → Prop := fun μ N => ∀ G : E3 → E3 → ℂ, BoxSmooth (ellH v μ) G →
      ‖∫ w in boxL (ellH v μ), ∫ y in boxL (ellH v μ),
        (K1exp v μ N (k1cfun fu (Work.BoseFixR.W1fun v h (ellH v μ)) 0 (ellH v μ) N) w y
          - K1lim (ellH v μ) (Work.BoseFixR.W1fun v h (ellH v μ)) w y) * G w y‖
        ≤ eps μ * (Real.sqrt (Work.BoseBoxFock.L1Tails.pairEnergy (ellH v μ) G)
            + Real.sqrt (massBox (ellH v μ) G)) with hPairIIdef
  obtain ⟨Nmin, hNmin⟩ := exists_Nmin (Ω := ℝ) (fun μ N => PairI μ N ∧ PairII μ N)
  refine ⟨Nmin, min ε₃ (min εkap 1), 16, lt_min hε₃pos (lt_min hεkappos one_pos),
    by norm_num, ?_⟩
  -- ## 2. the main estimate
  intro HM hNM μ hAdm hJ n Φ hn _hnorm hlow _hspec c hc
  have hμ : 0 < μ := hAdm.1
  have ht : μ * (BoseGases.a v) ^ 3 ≤ min ε₃ (min εkap 1) := hAdm.2.1
  have hP : Work.BoseBox.ParamsOK (Work.BoseBox.paramsAt μ (BoseGases.a v))
      (μ * (BoseGases.a v) ^ 3) := hAdm.2.2
  obtain ⟨_ha, hd, hs, heT0, heT1, hb, _hKl⟩ := Work.BoseBox.paramsAt_facts hμ hP
  have hℓ : 0 < ellH v μ := ellH_pos v μ
  have hside : 0 < Work.BoseBox.sideAt μ (BoseGases.a v) := Work.BoseBox.sideAt_pos hμ hav
  have hℓeq : ellH v μ = Work.BoseBox.sideAt μ (BoseGases.a v) := ellH_eq_sideAt_of_pos hside
  have ht3 : μ * (BoseGases.a v) ^ 3 ≤ ε₃ := le_trans ht (min_le_left _ _)
  have htk : μ * (BoseGases.a v) ^ 3 ≤ εkap :=
    le_trans ht (le_trans (min_le_right _ _) (min_le_left _ _))
  have hAdmκ : Work.BoseBoxFix.Adm v εkap μ :=
    Work.BoseFixB1.Adm.mono hAdm (le_trans (min_le_right _ _) (min_le_left _ _))
  have hRrr : R ≤ Work.BoseBox.sideAt μ (BoseGases.a v) * rr := hε₃ μ hμ ht3
  have hRdivrr : R / ellH v μ ≤ rr := by
    rw [div_le_iff₀ hℓ]
    calc R ≤ Work.BoseBox.sideAt μ (BoseGases.a v) * rr := hRrr
      _ = ellH v μ * rr := by rw [hℓeq]
      _ = rr * ellH v μ := by ring
  have hRq : R ≤ ellH v μ / 4 := by
    calc R ≤ Work.BoseBox.sideAt μ (BoseGases.a v) * rr := hRrr
      _ = ellH v μ * rr := by rw [hℓeq]
      _ ≤ ellH v μ * (1 / 4) := mul_le_mul_of_nonneg_left hrr4 hℓ.le
      _ = ellH v μ / 4 := by ring
  have hreg : R / ellH v μ ≤ rchi := le_trans hRdivrr hrrr
  have hcond : chiC * (R / ellH v μ) ^ 2 ≤ 1 / 2 := by
    have hRl0 : 0 ≤ R / ellH v μ := by positivity
    have h : R / ellH v μ ≤ rm := le_trans hRdivrr hrrm
    have hsq : (R / ellH v μ) ^ 2 ≤ rm ^ 2 := by
      have hmul := mul_le_mul h h hRl0 hrmpos.le
      simpa [pow_two] using hmul
    exact le_trans (mul_le_mul_of_nonneg_left hsq hchiC0) hrmsq
  -- ## 3. the weight facts at the honest weights
  obtain ⟨hW1i, hW10, hW1s⟩ :=
    W1fun_integrable_of_regime (v := v) (h := h) (R := R) (ℓ := ellH v μ) (r₁ := rchi)
      (C := chiC) hR hv hvrad hv_supp hchiC0 hrchi hchiT hℓ hreg hcond
  obtain ⟨hW2i, hW20, hW2s, hW2e, hW2J, hWJ⟩ :=
    W1omega_weight_facts (v := v) (h := h) (R := R) (ℓ := ellH v μ) (r₁ := rchi)
      (C := chiC) hR hv hvrad hv_supp hchiC0 hrchi hchiT hℓ hreg hcond
  obtain ⟨hW1J, _hW1Jb, _hW2Jb, _hW2Jb'⟩ :=
    L1Tails.W1fun_coulomb_le (v := v) (R := R) (ℓ := ellH v μ) (r₁ := rchi) (C := chiC)
      hR hv hvrad hv_supp h hchiC0 hrchi hchiT hℓ hreg hcond
  have hW1e : ∀ x : E3, Work.BoseFixR.W1fun v h (ellH v μ) (-x)
      = Work.BoseFixR.W1fun v h (ellH v μ) x := W1fun_even hvrad
  have hsum0 : Work.BoseFixR.W1fun v h (ellH v μ) + (fun _ : E3 => (0 : ℝ))
      = Work.BoseFixR.W1fun v h (ellH v μ) := by
    funext x; simp
  -- ## 4. `ε(μ) > 0`
  have heps_eq : ∀ μ' : ℝ, eps μ' = Work.BoseFixR.errKafz v R μ' 16 /
      (16 * max (CfRow (ellH v μ')) 1 * μ' ^ 2 *
        (Real.sqrt (C1f μ' * (kap * μ' ^ 2 * (BoseGases.a v) * (ellH v μ') ^ 3
            + 2 * μ' * (ellH v μ') ^ 3) + 1) + (ellH v μ') ^ 3)) := by
    intro μ'
    simp only [hepsdef]
  have hepspos : 0 < eps μ := by
    rw [heps_eq μ]
    refine div_pos (errKafz_pos hμ hav (by norm_num)) ?_
    have h3 : 0 < Real.sqrt (C1f μ * (kap * μ ^ 2 * (BoseGases.a v) * (ellH v μ) ^ 3
        + 2 * μ * (ellH v μ) ^ 3) + 1) + (ellH v μ) ^ 3 := by
      have h4 : 0 ≤ Real.sqrt (C1f μ * (kap * μ ^ 2 * (BoseGases.a v) * (ellH v μ) ^ 3
          + 2 * μ * (ellH v μ) ^ 3) + 1) := Real.sqrt_nonneg _
      have h5 : 0 < (ellH v μ) ^ 3 := by positivity
      linarith
    exact mul_pos (mul_pos (mul_pos (by norm_num)
      (lt_of_lt_of_le one_pos (le_max_right _ _))) (pow_pos hμ 2)) h3
  -- ## 5. the pairing bound and `Nmin`
  have hPairExists : ∃ N₀, ∀ N', N₀ ≤ N' → PairI μ N' ∧ PairII μ N' := by
    obtain ⟨N₁, hN₁⟩ := K1exp_sub_K1lim_pairing_dirB (v := v) (μ := μ) (R := R)
      hR hRq (Wa := Work.BoseFixR.W1fun v h (ellH v μ))
      (Wb := Work.BoseFixR.W1omegaFun v h (ellH v μ)) hW1i hW10 hW1s hW1e hW1J
      hW2i hW20 hW2s hW2e hW2J hWJ fu (eps μ) hepspos
    obtain ⟨N₂, hN₂⟩ := K1exp_sub_K1lim_pairing_dirB (v := v) (μ := μ) (R := R)
      hR hRq (Wa := Work.BoseFixR.W1fun v h (ellH v μ)) (Wb := fun _ : E3 => (0 : ℝ))
      hW1i hW10 hW1s hW1e hW1J
      (MeasureTheory.integrable_zero E3 ℝ MeasureTheory.volume)
      (Filter.Eventually.of_forall fun _ => le_refl (0 : ℝ))
      (fun _ _ => rfl) (fun _ => rfl) integrable_coulInt_zero
      (by rw [hsum0]; exact hW1J)
      fu (eps μ) hepspos
    refine ⟨max N₁ N₂, fun N' hN' => ⟨?_, ?_⟩⟩
    · intro G hG
      exact hN₁ N' (le_trans (le_max_left _ _) hN') G hG
    · intro G hG
      have h := hN₂ N' (le_trans (le_max_right _ _) hN') G hG
      rwa [hsum0] at h
  have hpI : PairI μ ((HM μ).N) := (hNmin μ ((HM μ).N) hPairExists (hNM μ)).1
  have hpII : PairII μ ((HM μ).N) := (hNmin μ ((HM μ).N) hPairExists (hNM μ)).2
  -- ## 6. the state data
  have hC1f_eval : C1f μ
      = (pinDirChi_le_kinFormB_unif (v := v) (h := h) (μ := μ) hav hμ hd hs hb heT0
          heT1).choose := by
    simp only [hC1fdef]
    exact dif_pos ⟨hμ, hd, hs, hb, heT0, heT1⟩
  have hC1fspec := (pinDirChi_le_kinFormB_unif (v := v) (h := h) (μ := μ) hav hμ hd hs hb
    heT0 heT1).choose_spec
  have hC1pos : 0 < C1f μ := by
    rw [hC1f_eval]
    exact hC1fspec.1
  have hC1bound : pinDirChi (Work.BoseBox.sideAt μ (BoseGases.a v))
      (fun x => ((Φ x : ℝ) : ℂ))
      ≤ C1f μ * (Work.BoseKinLoc.kinFormB n (Work.BoseBox.sideAt μ (BoseGases.a v))
            (Work.BoseBox.paramsAt μ (BoseGases.a v)).d
            (Work.BoseBox.paramsAt μ (BoseGases.a v)).s
            (Work.BoseBox.paramsAt μ (BoseGases.a v)).eT
            (Work.BoseBox.paramsAt μ (BoseGases.a v)).b
            (Φ : Submission.BoseGases.X n → ℝ)
          + (n : ℝ) * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)) := by
    rw [hC1f_eval]
    exact hC1fspec.2 n Φ
  -- the kinetic row (via `IsLowB` at the nonnegative threshold `max J 0`)
  have hKB3nonneg : 0 ≤ (Work.BoseBox.paramsAt μ (BoseGases.a v)).KB ^ 3 := by
    refine pow_nonneg ?_ 3
    simp only [Work.BoseBox.paramsAt, Work.BoseBox.fsParams]
    exact Work.BoseBox.fsXp_nonneg (by positivity)
  have hlow' : Work.BoseBoxFix.IsLowB v h (max J 0) μ n Φ :=
    isLowB_mono_J hμ hav (le_max_left J 0) hlow
  have hkin : Work.BoseKinLoc.kinFormB n (Work.BoseBox.sideAt μ (BoseGases.a v))
      (Work.BoseBox.paramsAt μ (BoseGases.a v)).d
      (Work.BoseBox.paramsAt μ (BoseGases.a v)).s
      (Work.BoseBox.paramsAt μ (BoseGases.a v)).eT
      (Work.BoseBox.paramsAt μ (BoseGases.a v)).b
      (Φ : Submission.BoseGases.X n → ℝ)
      ≤ kap * μ ^ 2 * (BoseGases.a v) * (Work.BoseBox.sideAt μ (BoseGases.a v)) ^ 3
          * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ) :=
    hkap μ hAdmκ (max J 0) (le_max_right J 0) (max_le hJ hKB3nonneg) n Φ hlow' hn
  have hNnn : (0 : ℝ) ≤ Work.BoseBoxFix.normB v μ n Φ := Work.BoseFixB1.normB_nonneg Φ
  have hpD : pinDirChi (ellH v μ) (fun x => ((Φ x : ℝ) : ℂ))
      ≤ C1f μ * (kap * μ ^ 2 * (BoseGases.a v) * (ellH v μ) ^ 3 + 2 * μ * (ellH v μ) ^ 3)
          * Work.BoseBoxFix.normB v μ n Φ := by
    have h1 : pinDirChi (ellH v μ) (fun x => ((Φ x : ℝ) : ℂ))
        = pinDirChi (Work.BoseBox.sideAt μ (BoseGases.a v)) (fun x => ((Φ x : ℝ) : ℂ)) := by
      rw [hℓeq]
    have hnN : (n : ℝ) * Work.BoseBoxFix.normB v μ n Φ
        ≤ (2 * μ * (Work.BoseBox.sideAt μ (BoseGases.a v)) ^ 3) * Work.BoseBoxFix.normB v μ n Φ :=
      mul_le_mul_of_nonneg_right hn hNnn
    have hsum : Work.BoseKinLoc.kinFormB n (Work.BoseBox.sideAt μ (BoseGases.a v))
          (Work.BoseBox.paramsAt μ (BoseGases.a v)).d
          (Work.BoseBox.paramsAt μ (BoseGases.a v)).s
          (Work.BoseBox.paramsAt μ (BoseGases.a v)).eT
          (Work.BoseBox.paramsAt μ (BoseGases.a v)).b
          (Φ : Submission.BoseGases.X n → ℝ)
        + (n : ℝ) * Work.BoseBoxFix.normB v μ n Φ
        ≤ (kap * μ ^ 2 * (BoseGases.a v) * (Work.BoseBox.sideAt μ (BoseGases.a v)) ^ 3
            + 2 * μ * (Work.BoseBox.sideAt μ (BoseGases.a v)) ^ 3)
              * Work.BoseBoxFix.normB v μ n Φ := by
      have hrw : (kap * μ ^ 2 * (BoseGases.a v) * (Work.BoseBox.sideAt μ (BoseGases.a v)) ^ 3
            + 2 * μ * (Work.BoseBox.sideAt μ (BoseGases.a v)) ^ 3)
              * Work.BoseBoxFix.normB v μ n Φ
          = kap * μ ^ 2 * (BoseGases.a v) * (Work.BoseBox.sideAt μ (BoseGases.a v)) ^ 3
              * Work.BoseBoxFix.normB v μ n Φ
            + (2 * μ * (Work.BoseBox.sideAt μ (BoseGases.a v)) ^ 3)
              * Work.BoseBoxFix.normB v μ n Φ := by ring
      rw [hrw]; linarith
    rw [h1]
    calc pinDirChi (Work.BoseBox.sideAt μ (BoseGases.a v)) (fun x => ((Φ x : ℝ) : ℂ))
        ≤ C1f μ * (Work.BoseKinLoc.kinFormB n (Work.BoseBox.sideAt μ (BoseGases.a v))
              (Work.BoseBox.paramsAt μ (BoseGases.a v)).d
              (Work.BoseBox.paramsAt μ (BoseGases.a v)).s
              (Work.BoseBox.paramsAt μ (BoseGases.a v)).eT
              (Work.BoseBox.paramsAt μ (BoseGases.a v)).b
              (Φ : Submission.BoseGases.X n → ℝ)
            + (n : ℝ) * Work.BoseBoxFix.normB v μ n Φ) := hC1bound
      _ ≤ C1f μ * ((kap * μ ^ 2 * (BoseGases.a v)
              * (Work.BoseBox.sideAt μ (BoseGases.a v)) ^ 3
            + 2 * μ * (Work.BoseBox.sideAt μ (BoseGases.a v)) ^ 3)
              * Work.BoseBoxFix.normB v μ n Φ) :=
          mul_le_mul_of_nonneg_left hsum hC1pos.le
      _ = C1f μ * (kap * μ ^ 2 * (BoseGases.a v) * (ellH v μ) ^ 3 + 2 * μ * (ellH v μ) ^ 3)
            * Work.BoseBoxFix.normB v μ n Φ := by rw [hℓeq]; ring
  -- the two mass identities
  have hpinL2 : pinL2 (ellH v μ) (fun x => ((Φ x : ℝ) : ℂ))
      = Work.BoseBoxFix.normB v μ n Φ := by
    rw [pinL2_ofReal_eq]
    unfold Work.BoseBoxFix.normB Work.BoseKinLoc.sqNormB
    rw [hℓeq]
  have hTheta2 : (∫ x : Submission.BoseGases.X n, ‖boxRestrictC (ellH v μ) Φ x‖ ^ 2)
      = Work.BoseBoxFix.normB v μ n Φ := by
    rw [integral_normSq_boxRestrictC]
    unfold Work.BoseBoxFix.normB Work.BoseKinLoc.sqNormB
    rw [hℓeq]
  have hcA2 : ‖c‖ ^ 2 = ((ellH v μ) ^ 3)⁻¹ := by
    have h1 : ((Complex.normSq c : ℝ) : ℂ) = ((((ellH v μ) ^ 3)⁻¹ : ℝ) : ℂ) := by
      rw [← Complex.mul_conj c, mul_comm]
      exact hc
    have h2 : Complex.normSq c = ((ellH v μ) ^ 3)⁻¹ := Complex.ofReal_inj.mp h1
    rwa [Complex.normSq_eq_norm_sq] at h2
  have hA2nn : (0 : ℝ) ≤ ∫ x : E3, ‖pinCond v μ c x‖ ^ 2 :=
    MeasureTheory.integral_nonneg fun x => by positivity
  have hL2nn : (0 : ℝ) ≤ ∫ x : Submission.BoseGases.X n, ‖boxRestrictC (ellH v μ) Φ x‖ ^ 2 :=
    MeasureTheory.integral_nonneg fun x => by positivity
  -- ## 7. the row bound
  have hrow := hCfRow (n := n) (ℓ := ellH v μ) (ε₁ := eps μ) (ε₂ := eps μ) hℓ
    (Θ := boxRestrictC (ellH v μ) Φ) (Θ₀ := fun x => ((Φ x : ℝ) : ℂ))
    (A := pinCond v μ c)
    (KI := K1exp v μ (HM μ).N (k1cfun fu (Work.BoseFixR.W1fun v h (ellH v μ))
      (Work.BoseFixR.W1omegaFun v h (ellH v μ)) (ellH v μ) (HM μ).N))
    (KII := K1exp v μ (HM μ).N (k1cfun fu (Work.BoseFixR.W1fun v h (ellH v μ)) 0
      (ellH v μ) (HM μ).N))
    (W₁' := fun x => Work.BoseFixR.W1fun v h (ellH v μ) x
      + Work.BoseFixR.W1omegaFun v h (ellH v μ) x)
    (W₂' := Work.BoseFixR.W1fun v h (ellH v μ))
    (cA := ‖c‖)
    (boxRestrictC_measurable_aux (ellH v μ) Φ.contDiff.continuous)
    (exists_bound_boxRestrictC hℓ Φ.contDiff.continuous)
    (support_boxRestrictC_boxPow hℓ Φ)
    (Complex.ofRealCLM.contDiff.comp Φ.contDiff)
    (fun x => indicator_boxRestrictC_aux (ellH v μ) Φ x)
    (by rw [show pinCond v μ c = fun x : E3 => c * Work.BoseK15.corpusBox.thetaFun (ellH v μ) x
          from rfl]
        exact measurable_const.mul (measurable_thetaFun (ellH v μ)))
    ⟨‖c‖, fun x => norm_pinCond_le v μ c x⟩
    (cutSmooth1_pinCond v μ c)
    (K1exp_meas_bdd (k1cfun fu (Work.BoseFixR.W1fun v h (ellH v μ))
      (Work.BoseFixR.W1omegaFun v h (ellH v μ)) (ellH v μ) (HM μ).N)).1
    (K1exp_meas_bdd (k1cfun fu (Work.BoseFixR.W1fun v h (ellH v μ))
      (Work.BoseFixR.W1omegaFun v h (ellH v μ)) (ellH v μ) (HM μ).N)).2
    (K1exp_meas_bdd (k1cfun fu (Work.BoseFixR.W1fun v h (ellH v μ)) 0
      (ellH v μ) (HM μ).N)).1
    (K1exp_meas_bdd (k1cfun fu (Work.BoseFixR.W1fun v h (ellH v μ)) 0
      (ellH v μ) (HM μ).N)).2
    (hW1i.add hW2i) hW1i
    hepspos.le hepspos.le (norm_nonneg c)
    (fun x => norm_pinCond_le v μ c x)
    (integrable_normSq_boxRestrictC hℓ Φ.contDiff)
    (integrable_normSq_pinCond v μ c)
    hpI hpII
  -- ## 8. the arithmetic
  have hA2L2 : (∫ x : E3, ‖pinCond v μ c x‖ ^ 2)
      * (∫ x : Submission.BoseGases.X n, ‖boxRestrictC (ellH v μ) Φ x‖ ^ 2)
      ≤ Work.BoseBoxFix.normB v μ n Φ := by
    rw [hTheta2, pinCond_norm_sq hc, one_mul]
  have harith := pairRowS2Arith (ℓ := ellH v μ) (μ := μ) (a := BoseGases.a v)
    (Cf := max (CfRow (ellH v μ)) 1) (Ckap := kap) (C := C1f μ) (ε := eps μ)
    (err := Work.BoseFixR.errKafz v R μ 16)
    (pDchi := pinDirChi (ellH v μ) (fun x => ((Φ x : ℝ) : ℂ)))
    (pL := Work.BoseBoxFix.normB v μ n Φ)
    (A2 := ∫ x : E3, ‖pinCond v μ c x‖ ^ 2)
    (L2 := ∫ x : Submission.BoseGases.X n, ‖boxRestrictC (ellH v μ) Φ x‖ ^ 2)
    hℓ hμ (le_trans zero_le_one (le_max_right _ _)) hkappos.le hC1pos.le hepspos.le hNnn
    hA2nn hL2nn (errKafz_nonneg hμ hav (by norm_num))
    (by rw [hℓeq]; exact hn)
    hTheta2 hpD hA2L2 (le_of_eq (heps_eq μ))
  -- ## 9. the assembly
  rw [hcA2, hpinL2] at hrow
  rw [show ((ellH v μ) ^ 3)⁻¹ * (Real.sqrt (Work.BoseBoxFix.normB v μ n Φ)
        * Real.sqrt (pinDirChi (ellH v μ) (fun x => ((Φ x : ℝ) : ℂ))
          + Work.BoseBoxFix.normB v μ n Φ))
      = ((ellH v μ) ^ 3)⁻¹ * Real.sqrt (Work.BoseBoxFix.normB v μ n Φ)
        * Real.sqrt (pinDirChi (ellH v μ) (fun x => ((Φ x : ℝ) : ℂ))
          + Work.BoseBoxFix.normB v μ n Φ) from by ring] at hrow
  set BR : ℝ := ((ellH v μ) ^ 3)⁻¹ * Real.sqrt (Work.BoseBoxFix.normB v μ n Φ)
      * Real.sqrt (pinDirChi (ellH v μ) (fun x => ((Φ x : ℝ) : ℂ))
        + Work.BoseBoxFix.normB v μ n Φ)
      + (∫ x : E3, ‖pinCond v μ c x‖ ^ 2)
        * ∫ x : Submission.BoseGases.X n, ‖boxRestrictC (ellH v μ) Φ x‖ ^ 2 with hBRdef
  have hBRnn : 0 ≤ BR := by
    rw [hBRdef]
    have h1 : 0 ≤ ((ellH v μ) ^ 3)⁻¹ := by positivity
    have h2 : 0 ≤ Real.sqrt (Work.BoseBoxFix.normB v μ n Φ) := Real.sqrt_nonneg _
    have h3 : 0 ≤ Real.sqrt (pinDirChi (ellH v μ) (fun x => ((Φ x : ℝ) : ℂ))
        + Work.BoseBoxFix.normB v μ n Φ) := Real.sqrt_nonneg _
    exact add_nonneg (mul_nonneg (mul_nonneg h1 h2) h3) (mul_nonneg hA2nn hL2nn)
  have hstep : 2 * ((ellH v μ) ^ 3)⁻¹ * max (eps μ) (eps μ)
        * (CfRow (ellH v μ) * ↑n * ↑n * BR)
      ≤ 2 * ((ellH v μ) ^ 3)⁻¹ * eps μ * max (CfRow (ellH v μ)) 1 * ↑n ^ 2 * BR := by
    rw [max_self]
    rw [show 2 * ((ellH v μ) ^ 3)⁻¹ * eps μ * max (CfRow (ellH v μ)) 1 * ↑n ^ 2 * BR
        = (2 * ((ellH v μ) ^ 3)⁻¹ * eps μ) * (max (CfRow (ellH v μ)) 1 * ↑n ^ 2 * BR)
        from by ring]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [show CfRow (ellH v μ) * ↑n * ↑n * BR = (CfRow (ellH v μ) * ↑n ^ 2) * BR from by ring]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg (n : ℝ))) hBRnn
  exact le_trans (le_trans hrow hstep) harith

end Work.BoseBoxFock
