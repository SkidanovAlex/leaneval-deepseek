import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseBoxFock.L1Tails.chiChiCoulAux
import Submission.Work.BoseFixB1S.integral_sq_le_measure_mul_integral_sq
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.L1Tails.psiM_mass_bound`

The mass (i.e. `ℓ⁻²`-weighted) bound for the auxiliary function `ψ_m` of the `χχ`-images pairing.
Under the hypothesis that the window at the image `ℓ • latVec m` can only see the part of the box
that is within `2R` of the boundary of its support (`hgap`, the "gap" assumption of the `L¹`-tail
chapter), the `w`-mass of `ψ_m` is bounded by `ε²ℓ⁵` times the mass part `pairMass'` of the energy
on the right-hand side of the `χχ`-images pairing estimate.

The mathematics is three steps:

* **Pointwise.**  For `‖z‖ ≤ 2R` the hypothesis `hgap` gives `χ_ℓ(y) ≤ ε` on the support of
  `χ_ℓ(z + y − ℓ•latVec m)`, whence
  `‖ψ_m z‖ ≤ ε ∫_{‖y‖ ≤ ℓ/2} χ_ℓ(z+y−ℓ•latVec m)·‖G (z+y−ℓ•latVec m) y‖ dy`.
* **Cauchy–Schwarz in `y`.**  `(∫ u)² ≤ volume(halfBall ℓ)·∫ u² ≤ ℓ³ ∫ u²`, using that the
  half-ball is contained in the corpus box `Λ(ℓ)` of volume `ℓ³`.
* **The `(z,y)` exchanges.**  Fubini on the product, substitution of `z + y − ℓ•latVec m`, and the
  vanishing of the weight off the corpus box; all three are done "per `y`", the `z`-domain being
  expanded to all of `ℝ³` (legitimate because the integrand is non-negative).
-/

noncomputable section

open MeasureTheory
open scoped BigOperators Real

namespace Work.BoseBoxFock.L1Tails

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false

/-- The corpus bump `χ_ℓ` is the `BoxData` localization function `chiLam ℓ` of the corpus box. -/
private lemma chiScale_eq_chiLam (ℓ : ℝ) :
    Submission.BoseGases.chiScale ℓ = Work.BoseK15.corpusBox.chiLam ℓ := by
  funext x
  rfl

/-- The `ℓ`-half-ball is contained in the corpus box `Λ(ℓ)`. -/
private lemma halfBall_subset_boxL {ℓ : ℝ} (hℓ : 0 < ℓ) :
    halfBall ℓ ⊆ Work.BoseK15.corpusBox.boxL ℓ := by
  intro y hy
  rw [Work.BoseBoxFock.mem_corpusBox_boxL hℓ]
  intro i
  have hy' : ‖y‖ ≤ ℓ / 2 := by
    simpa [halfBall, Metric.mem_closedBall, dist_eq_norm] using hy
  calc |y.ofLp i| = ‖y.ofLp i‖ := (Real.norm_eq_abs _).symm
    _ ≤ ‖y‖ := PiLp.norm_apply_le y i
    _ ≤ ℓ / 2 := hy'

/-- The support of the corpus bump `χ_ℓ` is contained in the corpus box. -/
private lemma support_chiScale_subset_boxL {ℓ : ℝ} (hℓ : 0 < ℓ) :
    Function.support (Submission.BoseGases.chiScale ℓ) ⊆ Work.BoseK15.corpusBox.boxL ℓ := by
  rw [chiScale_eq_chiLam ℓ]
  exact Work.BoseB4.BoxData.chiLam_supp Work.BoseK15.corpusBox hℓ

/-- **Cauchy–Schwarz for the `y`-integral over the half-ball.**  For a non-negative continuous
`u`, `(∫_{halfBall ℓ} u)² ≤ ℓ³ ∫_{halfBall ℓ} u²`: the Cauchy–Schwarz inequality against the
constant `1` on the half-ball, whose volume is at most the volume `ℓ³` of the corpus box. -/
private lemma sq_setIntegral_halfBall_le {ℓ : ℝ} (hℓ : 0 < ℓ) {u : E3 → ℝ}
    (hu : Continuous u) :
    (∫ y in halfBall ℓ, u y) ^ 2 ≤ ℓ ^ 3 * ∫ y in halfBall ℓ, u y ^ 2 := by
  have hHc : IsCompact (halfBall ℓ) := isCompact_closedBall 0 (ℓ / 2)
  have hHm : MeasurableSet (halfBall ℓ) := measurableSet_closedBall
  have hu_aesm : AEStronglyMeasurable u (volume.restrict (halfBall ℓ)) :=
    hu.aestronglyMeasurable.mono_measure Measure.restrict_le_self
  have hu2_int : IntegrableOn (fun y : E3 => u y ^ 2) (halfBall ℓ) volume :=
    ContinuousOn.integrableOn_compact hHc (hu.pow 2).continuousOn
  have hu_mem : MemLp u 2 (volume.restrict (halfBall ℓ)) :=
    (memLp_two_iff_integrable_sq hu_aesm).mpr (by simpa using hu2_int.integrable)
  have h1_int : IntegrableOn (fun _ : E3 => (1 : ℝ) ^ 2) (halfBall ℓ) volume :=
    ContinuousOn.integrableOn_compact hHc continuousOn_const
  have h1_mem : MemLp (fun _ : E3 => (1 : ℝ)) 2 (volume.restrict (halfBall ℓ)) :=
    (memLp_two_iff_integrable_sq aestronglyMeasurable_const).mpr
      (by simpa using h1_int.integrable)
  have hCS := Work.BoseFixB1S.integral_mul_sq_le_of_memLp hu_mem h1_mem
  have hL : (∫ x, u x * (1 : ℝ) ∂(volume.restrict (halfBall ℓ))) = ∫ x in halfBall ℓ, u x := by
    simp
  have hR1 : (∫ x, u x ^ 2 ∂(volume.restrict (halfBall ℓ))) = ∫ x in halfBall ℓ, u x ^ 2 := rfl
  have hR2 : (∫ x, (1 : ℝ) ^ 2 ∂(volume.restrict (halfBall ℓ)))
      = volume.real (halfBall ℓ) := by
    simp only [one_pow, MeasureTheory.integral_const, smul_eq_mul, mul_one, Measure.real_def,
      Measure.restrict_apply_univ]
  rw [hL, hR1, hR2] at hCS
  have hvol : volume.real (halfBall ℓ) ≤ ℓ ^ 3 := by
    have hsub : halfBall ℓ ⊆ Work.BoseK15.corpusBox.boxL ℓ := halfBall_subset_boxL hℓ
    have h1 : volume.real (halfBall ℓ) ≤ volume.real (Work.BoseK15.corpusBox.boxL ℓ) :=
      measureReal_mono hsub (by
        rw [Work.BoseB4.BoxData.volume_boxL Work.BoseK15.corpusBox hℓ]
        exact ENNReal.ofReal_ne_top)
    have h2 : volume.real (Work.BoseK15.corpusBox.boxL ℓ) = ℓ ^ 3 := by
      rw [Measure.real_def, Work.BoseB4.BoxData.volume_boxL Work.BoseK15.corpusBox hℓ,
        ENNReal.toReal_ofReal (by positivity)]
    linarith
  have hnn : 0 ≤ ∫ y in halfBall ℓ, u y ^ 2 :=
    setIntegral_nonneg hHm (fun y _ => sq_nonneg _)
  calc (∫ y in halfBall ℓ, u y) ^ 2
      ≤ (∫ y in halfBall ℓ, u y ^ 2) * volume.real (halfBall ℓ) := hCS
    _ ≤ (∫ y in halfBall ℓ, u y ^ 2) * ℓ ^ 3 := mul_le_mul_of_nonneg_left hvol hnn
    _ = ℓ ^ 3 * ∫ y in halfBall ℓ, u y ^ 2 := by ring

/-- **The per-`y` step: shift, expand and localise.**  For the weight
`f_y(w) = χ_ℓ(w)²‖G w y‖²` (which vanishes off the corpus box `Λ(ℓ)`), the `z`-integral over `K` of
the translated weight `f_y(z + c)` is at most the `w`-integral of `f_y` over the corpus box. -/
private lemma setIntegral_shift_le {ℓ : ℝ} (hℓ : 0 < ℓ) {K Bx : Set E3} (hKm : MeasurableSet K)
    (hBxm : MeasurableSet Bx) (hBxc : IsCompact Bx)
    (hBxsupp : Function.support (Submission.BoseGases.chiScale ℓ) ⊆ Bx)
    (c y : E3) (G : E3 → E3 → ℂ) (hG : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry G)) :
    (∫ z in K, (Submission.BoseGases.chiScale ℓ (z + c)) ^ 2 * ‖G (z + c) y‖ ^ 2)
      ≤ ∫ w in Bx, (Submission.BoseGases.chiScale ℓ w) ^ 2 * ‖G w y‖ ^ 2 := by
  have hcont : Continuous (fun w : E3 =>
      (Submission.BoseGases.chiScale ℓ w) ^ 2 * ‖G w y‖ ^ 2) := by
    have h1 : Continuous (fun w : E3 => (Submission.BoseGases.chiScale ℓ w) ^ 2) :=
      ((Submission.BoseGases.chiScale_contDiff (ne_of_gt hℓ)).continuous).pow 2
    have h2 : Continuous (fun w : E3 => ‖G w y‖ ^ 2) :=
      (hG.continuous.comp (continuous_id.prodMk continuous_const)).norm.pow 2
    exact h1.mul h2
  have hint : IntegrableOn (fun w : E3 =>
      (Submission.BoseGases.chiScale ℓ w) ^ 2 * ‖G w y‖ ^ 2) Bx volume :=
    ContinuousOn.integrableOn_compact hBxc hcont.continuousOn
  have hIntInd : Integrable (Bx.indicator (fun w : E3 =>
      (Submission.BoseGases.chiScale ℓ w) ^ 2 * ‖G w y‖ ^ 2)) volume :=
    (integrable_indicator_iff hBxm).mpr hint
  -- step 1: the set integral is the integral of the indicator
  have e1 : (∫ z in K, (Submission.BoseGases.chiScale ℓ (z + c)) ^ 2 * ‖G (z + c) y‖ ^ 2)
      = ∫ z, K.indicator (fun z : E3 =>
          (Submission.BoseGases.chiScale ℓ (z + c)) ^ 2 * ‖G (z + c) y‖ ^ 2) z :=
    (MeasureTheory.integral_indicator hKm).symm
  -- step 2: the substitution `z ↦ z − c` in the full-space integral
  have e2 : (∫ z, K.indicator (fun z : E3 =>
        (Submission.BoseGases.chiScale ℓ (z + c)) ^ 2 * ‖G (z + c) y‖ ^ 2) z)
      = ∫ w, K.indicator (fun z : E3 =>
          (Submission.BoseGases.chiScale ℓ (z + c)) ^ 2 * ‖G (z + c) y‖ ^ 2) (w - c) :=
    (MeasureTheory.integral_sub_right_eq_self _ c).symm
  -- step 3: pointwise domination by the box-indicator and monotonicity
  have e3 : (∫ w, K.indicator (fun z : E3 =>
        (Submission.BoseGases.chiScale ℓ (z + c)) ^ 2 * ‖G (z + c) y‖ ^ 2) (w - c))
      ≤ ∫ w, Bx.indicator (fun w : E3 =>
          (Submission.BoseGases.chiScale ℓ w) ^ 2 * ‖G w y‖ ^ 2) w := by
    refine integral_mono_of_nonneg
      (Filter.Eventually.of_forall (fun w => Set.indicator_nonneg
        (fun a _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)) (w - c))) hIntInd ?_
    refine Filter.Eventually.of_forall (fun w => ?_)
    dsimp only
    by_cases hw : w ∈ Bx
    · rw [Set.indicator_of_mem hw]
      by_cases hwk : w - c ∈ K
      · rw [Set.indicator_of_mem hwk]
        have h1 : (w - c) + c = w := sub_add_cancel w c
        rw [h1]
      · rw [Set.indicator_of_notMem hwk]
        exact mul_nonneg (sq_nonneg _) (sq_nonneg _)
    · rw [Set.indicator_of_notMem hw]
      have hzero : Submission.BoseGases.chiScale ℓ w = 0 := by
        by_contra hne
        exact hw (hBxsupp hne)
      have hf0 : (Submission.BoseGases.chiScale ℓ w) ^ 2 * ‖G w y‖ ^ 2 = 0 := by
        rw [hzero]; ring
      by_cases hwk : w - c ∈ K
      · rw [Set.indicator_of_mem hwk]
        have h1 : (w - c) + c = w := sub_add_cancel w c
        rw [h1, hf0]
      · rw [Set.indicator_of_notMem hwk]
  -- step 4: the indicator integral is the set integral
  have e4 : (∫ w, Bx.indicator (fun w : E3 =>
        (Submission.BoseGases.chiScale ℓ w) ^ 2 * ‖G w y‖ ^ 2) w)
      = ∫ w in Bx, (Submission.BoseGases.chiScale ℓ w) ^ 2 * ‖G w y‖ ^ 2 :=
    MeasureTheory.integral_indicator hBxm
  calc (∫ z in K, (Submission.BoseGases.chiScale ℓ (z + c)) ^ 2 * ‖G (z + c) y‖ ^ 2)
      = ∫ z, K.indicator (fun z : E3 =>
          (Submission.BoseGases.chiScale ℓ (z + c)) ^ 2 * ‖G (z + c) y‖ ^ 2) z := e1
    _ = ∫ w, K.indicator (fun z : E3 =>
          (Submission.BoseGases.chiScale ℓ (z + c)) ^ 2 * ‖G (z + c) y‖ ^ 2) (w - c) := e2
    _ ≤ ∫ w, Bx.indicator (fun w : E3 =>
          (Submission.BoseGases.chiScale ℓ w) ^ 2 * ‖G w y‖ ^ 2) w := e3
    _ = ∫ w in Bx, (Submission.BoseGases.chiScale ℓ w) ^ 2 * ‖G w y‖ ^ 2 := e4

/-- **The pointwise norm bound for `ψ_m`.**  For `‖z‖ ≤ 2R`, the gap hypothesis kills the `y`-window
on the support of the translated window, so `‖ψ_m z‖` is at most `ε` times the (unweighted) `y`-fold
of `χ_ℓ(z+y−ℓ•latVec m)·‖G (z+y−ℓ•latVec m) y‖`. -/
private lemma psiM_norm_le {ℓ R ε : ℝ} (hℓ : 0 < ℓ)
    {m : Fin 3 → ℤ} {G : E3 → E3 → ℂ} (hG : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry G))
    (hgap : ∀ {z y : E3}, ‖z‖ ≤ 2 * R →
      Submission.BoseGases.chiScale ℓ (z + y - ℓ • Work.BoseBoxFock.latVec m) ≠ 0 →
      Submission.BoseGases.chiScale ℓ y ≤ ε)
    {z : E3} (hz : ‖z‖ ≤ 2 * R) :
    ‖psiM ℓ m G z‖ ≤ ε * ∫ y in halfBall ℓ,
      Submission.BoseGases.chiScale ℓ (z + y - ℓ • Work.BoseBoxFock.latVec m)
        * ‖G (z + y - ℓ • Work.BoseBoxFock.latVec m) y‖ := by
  have hHc : IsCompact (halfBall ℓ) := isCompact_closedBall 0 (ℓ / 2)
  have hχ1 : Continuous (Submission.BoseGases.chiScale ℓ) :=
    (Submission.BoseGases.chiScale_contDiff (ne_of_gt hℓ)).continuous
  -- the norm of the integral is at most the integral of the norm
  have hnorm1 : ‖psiM ℓ m G z‖ ≤ ∫ y in halfBall ℓ,
      ‖chiC ℓ y * chiC ℓ (z + y - ℓ • Work.BoseBoxFock.latVec m)
        * G (z + y - ℓ • Work.BoseBoxFock.latVec m) y‖ := by
    simpa only [psiM] using
      norm_integral_le_integral_norm (μ := volume.restrict (halfBall ℓ))
        (fun y : E3 => chiC ℓ y * chiC ℓ (z + y - ℓ • Work.BoseBoxFock.latVec m)
          * G (z + y - ℓ • Work.BoseBoxFock.latVec m) y)
  -- pointwise evaluation of the norm of the complex integrand
  have hcongr : (fun y : E3 =>
        ‖chiC ℓ y * chiC ℓ (z + y - ℓ • Work.BoseBoxFock.latVec m)
          * G (z + y - ℓ • Work.BoseBoxFock.latVec m) y‖)
      = fun y : E3 => Submission.BoseGases.chiScale ℓ y
          * (Submission.BoseGases.chiScale ℓ (z + y - ℓ • Work.BoseBoxFock.latVec m)
            * ‖G (z + y - ℓ • Work.BoseBoxFock.latVec m) y‖) := by
    funext y
    simp only [chiC, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (Submission.BoseGases.chiScale_nonneg ℓ y),
      Real.norm_of_nonneg (Submission.BoseGases.chiScale_nonneg ℓ _), mul_assoc]
  -- the pointwise inequality `χ_ℓ(y)·X ≤ ε·X`
  have hpw : ∀ y : E3, Submission.BoseGases.chiScale ℓ y
        * (Submission.BoseGases.chiScale ℓ (z + y - ℓ • Work.BoseBoxFock.latVec m)
          * ‖G (z + y - ℓ • Work.BoseBoxFock.latVec m) y‖)
      ≤ ε * (Submission.BoseGases.chiScale ℓ (z + y - ℓ • Work.BoseBoxFock.latVec m)
          * ‖G (z + y - ℓ • Work.BoseBoxFock.latVec m) y‖) := by
    intro y
    have hXnn : 0 ≤ Submission.BoseGases.chiScale ℓ (z + y - ℓ • Work.BoseBoxFock.latVec m)
        * ‖G (z + y - ℓ • Work.BoseBoxFock.latVec m) y‖ :=
      mul_nonneg (Submission.BoseGases.chiScale_nonneg ℓ _) (norm_nonneg _)
    by_cases hX : Submission.BoseGases.chiScale ℓ (z + y - ℓ • Work.BoseBoxFock.latVec m)
        * ‖G (z + y - ℓ • Work.BoseBoxFock.latVec m) y‖ = 0
    · rw [hX, mul_zero, mul_zero]
    · have hχ : Submission.BoseGases.chiScale ℓ (z + y - ℓ • Work.BoseBoxFock.latVec m) ≠ 0 := by
        intro h0
        exact hX (by rw [h0, zero_mul])
      exact mul_le_mul_of_nonneg_right (hgap hz hχ) hXnn
  -- continuity of the two integrands
  have hu : Continuous (fun y : E3 =>
      Submission.BoseGases.chiScale ℓ (z + y - ℓ • Work.BoseBoxFock.latVec m)
        * ‖G (z + y - ℓ • Work.BoseBoxFock.latVec m) y‖) := by
    have hp1 : Continuous (fun y : E3 => z + y - ℓ • Work.BoseBoxFock.latVec m) :=
      (continuous_const.add continuous_id).sub continuous_const
    have hχ2 : Continuous (fun y : E3 =>
        Submission.BoseGases.chiScale ℓ (z + y - ℓ • Work.BoseBoxFock.latVec m)) :=
      hχ1.comp hp1
    have hG2 : Continuous (fun y : E3 =>
        ‖G (z + y - ℓ • Work.BoseBoxFock.latVec m) y‖) :=
      (hG.continuous.comp (hp1.prodMk continuous_id)).norm
    exact hχ2.mul hG2
  have hcont1 : Continuous (fun y : E3 => Submission.BoseGases.chiScale ℓ y
      * (Submission.BoseGases.chiScale ℓ (z + y - ℓ • Work.BoseBoxFock.latVec m)
        * ‖G (z + y - ℓ • Work.BoseBoxFock.latVec m) y‖)) := hχ1.mul hu
  have hInt1 : IntegrableOn (fun y : E3 => Submission.BoseGases.chiScale ℓ y
      * (Submission.BoseGases.chiScale ℓ (z + y - ℓ • Work.BoseBoxFock.latVec m)
        * ‖G (z + y - ℓ • Work.BoseBoxFock.latVec m) y‖)) (halfBall ℓ) volume :=
    ContinuousOn.integrableOn_compact hHc hcont1.continuousOn
  have hInt2 : IntegrableOn (fun y : E3 => ε
      * (Submission.BoseGases.chiScale ℓ (z + y - ℓ • Work.BoseBoxFock.latVec m)
        * ‖G (z + y - ℓ • Work.BoseBoxFock.latVec m) y‖)) (halfBall ℓ) volume :=
    ContinuousOn.integrableOn_compact hHc (continuous_const.mul hu).continuousOn
  have hmono : (∫ y in halfBall ℓ, Submission.BoseGases.chiScale ℓ y
        * (Submission.BoseGases.chiScale ℓ (z + y - ℓ • Work.BoseBoxFock.latVec m)
          * ‖G (z + y - ℓ • Work.BoseBoxFock.latVec m) y‖))
      ≤ ∫ y in halfBall ℓ, ε
        * (Submission.BoseGases.chiScale ℓ (z + y - ℓ • Work.BoseBoxFock.latVec m)
          * ‖G (z + y - ℓ • Work.BoseBoxFock.latVec m) y‖) :=
    setIntegral_mono_of_nonneg (fun y _ => mul_nonneg
        (Submission.BoseGases.chiScale_nonneg ℓ y)
        (mul_nonneg (Submission.BoseGases.chiScale_nonneg ℓ _) (norm_nonneg _)))
      (fun y _ => hpw y) hInt2
  calc ‖psiM ℓ m G z‖
      ≤ ∫ y in halfBall ℓ, ‖chiC ℓ y * chiC ℓ (z + y - ℓ • Work.BoseBoxFock.latVec m)
          * G (z + y - ℓ • Work.BoseBoxFock.latVec m) y‖ := hnorm1
    _ = ∫ y in halfBall ℓ, Submission.BoseGases.chiScale ℓ y
          * (Submission.BoseGases.chiScale ℓ (z + y - ℓ • Work.BoseBoxFock.latVec m)
            * ‖G (z + y - ℓ • Work.BoseBoxFock.latVec m) y‖) := by rw [hcongr]
    _ ≤ ∫ y in halfBall ℓ, ε
          * (Submission.BoseGases.chiScale ℓ (z + y - ℓ • Work.BoseBoxFock.latVec m)
            * ‖G (z + y - ℓ • Work.BoseBoxFock.latVec m) y‖) := hmono
    _ = ε * ∫ y in halfBall ℓ,
          Submission.BoseGases.chiScale ℓ (z + y - ℓ • Work.BoseBoxFock.latVec m)
          * ‖G (z + y - ℓ • Work.BoseBoxFock.latVec m) y‖ := by
        rw [MeasureTheory.integral_const_mul]

theorem psiM_mass_bound {ℓ R ε : ℝ} (hℓ : 0 < ℓ) (hεnn : 0 ≤ ε)
    {m : Fin 3 → ℤ} {G : EuclideanSpace ℝ (Fin 3) → EuclideanSpace ℝ (Fin 3) → ℂ}
    (hG : ContDiff ℝ (⊤ : ℕ∞) (Function.uncurry G))
    (hgap : ∀ {z y : EuclideanSpace ℝ (Fin 3)}, ‖z‖ ≤ 2 * R →
      Submission.BoseGases.chiScale ℓ (z + y - ℓ • Work.BoseBoxFock.latVec m) ≠ 0 →
      Submission.BoseGases.chiScale ℓ y ≤ ε) :
    ∫ z in Metric.closedBall (0 : EuclideanSpace ℝ (Fin 3)) (2 * R),
        ‖Work.BoseBoxFock.L1Tails.psiM ℓ m G z‖ ^ 2
      ≤ ε ^ 2 * ℓ ^ 5 * Work.BoseBoxFock.L1Tails.pairMass' ℓ G := by
  set K : Set E3 := Metric.closedBall 0 (2 * R) with hK
  set Bx : Set E3 := Work.BoseK15.corpusBox.boxL ℓ with hBx
  have hKc : IsCompact K := by rw [hK]; exact isCompact_closedBall 0 (2 * R)
  have hKm : MeasurableSet K := by rw [hK]; exact measurableSet_closedBall
  have hBxsub : halfBall ℓ ⊆ Bx := by rw [hBx]; exact halfBall_subset_boxL hℓ
  have hBxsupp : Function.support (Submission.BoseGases.chiScale ℓ) ⊆ Bx := by
    rw [hBx]; exact support_chiScale_subset_boxL hℓ
  have hBxc : IsCompact Bx := by rw [hBx]; exact Work.BoseB4.BoxData.boxL_compact _ _
  have hBxm : MeasurableSet Bx := hBxc.isClosed.measurableSet
  have hHc : IsCompact (halfBall ℓ) := isCompact_closedBall 0 (ℓ / 2)
  have hHm : MeasurableSet (halfBall ℓ) := measurableSet_closedBall
  have hχ1 : Continuous (Submission.BoseGases.chiScale ℓ) :=
    (Submission.BoseGases.chiScale_contDiff (ne_of_gt hℓ)).continuous
  -- continuity of the joint integrand `Φ`
  have hΦcont : Continuous (fun p : E3 × E3 =>
      (Submission.BoseGases.chiScale ℓ (p.1 + p.2 - ℓ • Work.BoseBoxFock.latVec m)) ^ 2
        * ‖G (p.1 + p.2 - ℓ • Work.BoseBoxFock.latVec m) p.2‖ ^ 2) := by
    have hp : Continuous (fun p : E3 × E3 => p.1 + p.2 - ℓ • Work.BoseBoxFock.latVec m) :=
      (continuous_fst.add continuous_snd).sub continuous_const
    exact (hχ1.comp hp).pow 2 |>.mul ((hG.continuous.comp (hp.prodMk continuous_snd)).norm.pow 2)
  have hΨcont : Continuous (fun p : E3 × E3 =>
      (Submission.BoseGases.chiScale ℓ p.1) ^ 2 * ‖G p.1 p.2‖ ^ 2) :=
    (hχ1.comp continuous_fst).pow 2 |>.mul ((hG.continuous.norm).pow 2)
  have hΨswcont : Continuous (fun p : E3 × E3 =>
      (Submission.BoseGases.chiScale ℓ p.2) ^ 2 * ‖G p.2 p.1‖ ^ 2) :=
    (hχ1.comp continuous_snd).pow 2 |>.mul
      ((hG.continuous.comp (continuous_snd.prodMk continuous_fst)).norm.pow 2)
  ---------------------------------------------------------------------------------------------
  -- (2) the pointwise bound and the monotonicity of the outer integral
  ---------------------------------------------------------------------------------------------
  have hpt : ∀ z ∈ K, ‖psiM ℓ m G z‖ ^ 2 ≤ ε ^ 2 * ℓ ^ 3 * ∫ y in halfBall ℓ,
      (Submission.BoseGases.chiScale ℓ (z + y - ℓ • Work.BoseBoxFock.latVec m)) ^ 2
        * ‖G (z + y - ℓ • Work.BoseBoxFock.latVec m) y‖ ^ 2 := by
    intro z hz
    have hz' : ‖z‖ ≤ 2 * R := by
      rw [hK, Metric.mem_closedBall, dist_eq_norm, sub_zero] at hz
      exact hz
    have hp1 : Continuous (fun y : E3 => z + y - ℓ • Work.BoseBoxFock.latVec m) :=
      (continuous_const.add continuous_id).sub continuous_const
    have hu : Continuous (fun y : E3 =>
        Submission.BoseGases.chiScale ℓ (z + y - ℓ • Work.BoseBoxFock.latVec m)
          * ‖G (z + y - ℓ • Work.BoseBoxFock.latVec m) y‖) :=
      (hχ1.comp hp1).mul ((hG.continuous.comp (hp1.prodMk continuous_id)).norm)
    have hCS := sq_setIntegral_halfBall_le hℓ hu
    have hsqfun : (fun y : E3 =>
          (Submission.BoseGases.chiScale ℓ (z + y - ℓ • Work.BoseBoxFock.latVec m)
            * ‖G (z + y - ℓ • Work.BoseBoxFock.latVec m) y‖) ^ 2)
        = fun y : E3 =>
          (Submission.BoseGases.chiScale ℓ (z + y - ℓ • Work.BoseBoxFock.latVec m)) ^ 2
            * ‖G (z + y - ℓ • Work.BoseBoxFock.latVec m) y‖ ^ 2 := by
      funext y
      ring
    have hsqint : (∫ y in halfBall ℓ,
          (Submission.BoseGases.chiScale ℓ (z + y - ℓ • Work.BoseBoxFock.latVec m)
            * ‖G (z + y - ℓ • Work.BoseBoxFock.latVec m) y‖) ^ 2)
        = ∫ y in halfBall ℓ,
          (Submission.BoseGases.chiScale ℓ (z + y - ℓ • Work.BoseBoxFock.latVec m)) ^ 2
            * ‖G (z + y - ℓ • Work.BoseBoxFock.latVec m) y‖ ^ 2 := by
      rw [hsqfun]
    have hnorm := psiM_norm_le hℓ hG hgap hz'
    calc ‖psiM ℓ m G z‖ ^ 2
        ≤ (ε * ∫ y in halfBall ℓ,
            Submission.BoseGases.chiScale ℓ (z + y - ℓ • Work.BoseBoxFock.latVec m)
              * ‖G (z + y - ℓ • Work.BoseBoxFock.latVec m) y‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hnorm 2
      _ = ε ^ 2 * (∫ y in halfBall ℓ,
            Submission.BoseGases.chiScale ℓ (z + y - ℓ • Work.BoseBoxFock.latVec m)
              * ‖G (z + y - ℓ • Work.BoseBoxFock.latVec m) y‖) ^ 2 := by ring
      _ ≤ ε ^ 2 * (ℓ ^ 3 * ∫ y in halfBall ℓ,
            (Submission.BoseGases.chiScale ℓ (z + y - ℓ • Work.BoseBoxFock.latVec m)
              * ‖G (z + y - ℓ • Work.BoseBoxFock.latVec m) y‖) ^ 2) :=
          mul_le_mul_of_nonneg_left hCS (sq_nonneg ε)
      _ = ε ^ 2 * (ℓ ^ 3 * ∫ y in halfBall ℓ,
            (Submission.BoseGases.chiScale ℓ (z + y - ℓ • Work.BoseBoxFock.latVec m)) ^ 2
              * ‖G (z + y - ℓ • Work.BoseBoxFock.latVec m) y‖ ^ 2) := by rw [hsqint]
      _ = ε ^ 2 * ℓ ^ 3 * ∫ y in halfBall ℓ,
            (Submission.BoseGases.chiScale ℓ (z + y - ℓ • Work.BoseBoxFock.latVec m)) ^ 2
              * ‖G (z + y - ℓ • Work.BoseBoxFock.latVec m) y‖ ^ 2 := by ring
  ---------------------------------------------------------------------------------------------
  -- integrability of the inner integral, as a function of `z`, on `K`
  ---------------------------------------------------------------------------------------------
  have hIntKH : IntegrableOn (fun p : E3 × E3 =>
      (Submission.BoseGases.chiScale ℓ (p.1 + p.2 - ℓ • Work.BoseBoxFock.latVec m)) ^ 2
        * ‖G (p.1 + p.2 - ℓ • Work.BoseBoxFock.latVec m) p.2‖ ^ 2)
      (K ×ˢ halfBall ℓ) (volume.prod volume) :=
    ContinuousOn.integrableOn_compact (hKc.prod hHc) hΦcont.continuousOn
  have hRho : IntegrableOn (fun z : E3 => ∫ y in halfBall ℓ,
      (Submission.BoseGases.chiScale ℓ (z + y - ℓ • Work.BoseBoxFock.latVec m)) ^ 2
        * ‖G (z + y - ℓ • Work.BoseBoxFock.latVec m) y‖ ^ 2) K volume := by
    have h := hIntKH.integrable
    rw [← Measure.prod_restrict] at h
    exact h.integral_prod_left
  have hstep2 : ∫ z in K, ‖psiM ℓ m G z‖ ^ 2 ≤ ∫ z in K,
      ε ^ 2 * ℓ ^ 3 * ∫ y in halfBall ℓ,
        (Submission.BoseGases.chiScale ℓ (z + y - ℓ • Work.BoseBoxFock.latVec m)) ^ 2
          * ‖G (z + y - ℓ • Work.BoseBoxFock.latVec m) y‖ ^ 2 :=
    setIntegral_mono_of_nonneg (fun z _ => sq_nonneg _) (fun z hz => hpt z hz)
      (hRho.const_mul (ε ^ 2 * ℓ ^ 3))
  have hstep2' : ∫ z in K, ε ^ 2 * ℓ ^ 3 * ∫ y in halfBall ℓ,
        (Submission.BoseGases.chiScale ℓ (z + y - ℓ • Work.BoseBoxFock.latVec m)) ^ 2
          * ‖G (z + y - ℓ • Work.BoseBoxFock.latVec m) y‖ ^ 2
      = ε ^ 2 * ℓ ^ 3 * ∫ z in K, ∫ y in halfBall ℓ,
        (Submission.BoseGases.chiScale ℓ (z + y - ℓ • Work.BoseBoxFock.latVec m)) ^ 2
          * ‖G (z + y - ℓ • Work.BoseBoxFock.latVec m) y‖ ^ 2 :=
    MeasureTheory.integral_const_mul _ _
  ---------------------------------------------------------------------------------------------
  -- (3) Fubini on the product `K × halfBall ℓ`
  ---------------------------------------------------------------------------------------------
  have hswap : ∫ z in K, ∫ y in halfBall ℓ,
      (Submission.BoseGases.chiScale ℓ (z + y - ℓ • Work.BoseBoxFock.latVec m)) ^ 2
        * ‖G (z + y - ℓ • Work.BoseBoxFock.latVec m) y‖ ^ 2
      = ∫ y in halfBall ℓ, ∫ z in K,
      (Submission.BoseGases.chiScale ℓ (z + y - ℓ • Work.BoseBoxFock.latVec m)) ^ 2
        * ‖G (z + y - ℓ • Work.BoseBoxFock.latVec m) y‖ ^ 2 := by
    have h1 : ∫ z in K, ∫ y in halfBall ℓ,
        (Submission.BoseGases.chiScale ℓ (z + y - ℓ • Work.BoseBoxFock.latVec m)) ^ 2
          * ‖G (z + y - ℓ • Work.BoseBoxFock.latVec m) y‖ ^ 2
        = ∫ p in K ×ˢ halfBall ℓ,
        (Submission.BoseGases.chiScale ℓ (p.1 + p.2 - ℓ • Work.BoseBoxFock.latVec m)) ^ 2
          * ‖G (p.1 + p.2 - ℓ • Work.BoseBoxFock.latVec m) p.2‖ ^ 2 :=
      (MeasureTheory.setIntegral_prod _ hIntKH).symm
    have h2 : ∫ p in K ×ˢ halfBall ℓ,
        (Submission.BoseGases.chiScale ℓ (p.1 + p.2 - ℓ • Work.BoseBoxFock.latVec m)) ^ 2
          * ‖G (p.1 + p.2 - ℓ • Work.BoseBoxFock.latVec m) p.2‖ ^ 2
        = ∫ p in halfBall ℓ ×ˢ K,
        (Submission.BoseGases.chiScale ℓ (p.2 + p.1 - ℓ • Work.BoseBoxFock.latVec m)) ^ 2
          * ‖G (p.2 + p.1 - ℓ • Work.BoseBoxFock.latVec m) p.1‖ ^ 2 := by
      have h := MeasureTheory.setIntegral_prod_swap (μ := (volume : Measure E3))
        (ν := (volume : Measure E3)) K (halfBall ℓ)
        (fun p : E3 × E3 =>
          (Submission.BoseGases.chiScale ℓ (p.1 + p.2 - ℓ • Work.BoseBoxFock.latVec m)) ^ 2
            * ‖G (p.1 + p.2 - ℓ • Work.BoseBoxFock.latVec m) p.2‖ ^ 2)
      exact h.symm
    have hIntHK : IntegrableOn (fun p : E3 × E3 =>
        (Submission.BoseGases.chiScale ℓ (p.2 + p.1 - ℓ • Work.BoseBoxFock.latVec m)) ^ 2
          * ‖G (p.2 + p.1 - ℓ • Work.BoseBoxFock.latVec m) p.1‖ ^ 2)
        (halfBall ℓ ×ˢ K) (volume.prod volume) :=
      ContinuousOn.integrableOn_compact (hHc.prod hKc) (hΦcont.comp continuous_swap).continuousOn
    have h3 : ∫ p in halfBall ℓ ×ˢ K,
        (Submission.BoseGases.chiScale ℓ (p.2 + p.1 - ℓ • Work.BoseBoxFock.latVec m)) ^ 2
          * ‖G (p.2 + p.1 - ℓ • Work.BoseBoxFock.latVec m) p.1‖ ^ 2
        = ∫ y in halfBall ℓ, ∫ z in K,
        (Submission.BoseGases.chiScale ℓ (z + y - ℓ • Work.BoseBoxFock.latVec m)) ^ 2
          * ‖G (z + y - ℓ • Work.BoseBoxFock.latVec m) y‖ ^ 2 :=
      MeasureTheory.setIntegral_prod _ hIntHK
    rw [h1, h2, h3]
  ---------------------------------------------------------------------------------------------
  -- (4) the per-`y` bound and the `y`-integration
  ---------------------------------------------------------------------------------------------
  have hperY : ∀ y ∈ halfBall ℓ, (∫ z in K,
      (Submission.BoseGases.chiScale ℓ (z + y - ℓ • Work.BoseBoxFock.latVec m)) ^ 2
        * ‖G (z + y - ℓ • Work.BoseBoxFock.latVec m) y‖ ^ 2)
      ≤ ∫ w in Bx, (Submission.BoseGases.chiScale ℓ w) ^ 2 * ‖G w y‖ ^ 2 := by
    intro y hy
    have hconv : (∫ z in K,
        (Submission.BoseGases.chiScale ℓ (z + y - ℓ • Work.BoseBoxFock.latVec m)) ^ 2
          * ‖G (z + y - ℓ • Work.BoseBoxFock.latVec m) y‖ ^ 2)
        = ∫ z in K,
        (Submission.BoseGases.chiScale ℓ (z + (y - ℓ • Work.BoseBoxFock.latVec m))) ^ 2
          * ‖G (z + (y - ℓ • Work.BoseBoxFock.latVec m)) y‖ ^ 2 :=
      MeasureTheory.setIntegral_congr_fun hKm (fun z _ => by
        have harg : z + (y - ℓ • Work.BoseBoxFock.latVec m)
            = z + y - ℓ • Work.BoseBoxFock.latVec m := by abel
        rw [harg])
    rw [hconv]
    exact setIntegral_shift_le hℓ hKm hBxm hBxc hBxsupp (y - ℓ • Work.BoseBoxFock.latVec m) y G hG
  have hIntBxH : IntegrableOn (fun p : E3 × E3 =>
      (Submission.BoseGases.chiScale ℓ p.1) ^ 2 * ‖G p.1 p.2‖ ^ 2)
      (Bx ×ˢ halfBall ℓ) (volume.prod volume) :=
    ContinuousOn.integrableOn_compact (hBxc.prod hHc) hΨcont.continuousOn
  have hintB : IntegrableOn (fun y : E3 =>
      ∫ w in Bx, (Submission.BoseGases.chiScale ℓ w) ^ 2 * ‖G w y‖ ^ 2) (halfBall ℓ) volume := by
    have h := hIntBxH.integrable
    rw [← Measure.prod_restrict] at h
    exact h.integral_prod_right
  have hstep34 : ∫ y in halfBall ℓ, ∫ z in K,
      (Submission.BoseGases.chiScale ℓ (z + y - ℓ • Work.BoseBoxFock.latVec m)) ^ 2
        * ‖G (z + y - ℓ • Work.BoseBoxFock.latVec m) y‖ ^ 2
      ≤ ∫ y in halfBall ℓ, ∫ w in Bx,
        (Submission.BoseGases.chiScale ℓ w) ^ 2 * ‖G w y‖ ^ 2 :=
    setIntegral_mono_of_nonneg (fun y _ => setIntegral_nonneg hKm
        (fun z _ => mul_nonneg (sq_nonneg _) (sq_nonneg _)))
      (fun y hy => hperY y hy) hintB
  have hstep5 : ∫ y in halfBall ℓ, ∫ w in Bx,
      (Submission.BoseGases.chiScale ℓ w) ^ 2 * ‖G w y‖ ^ 2
      ≤ ∫ y in Bx, ∫ w in Bx, (Submission.BoseGases.chiScale ℓ w) ^ 2 * ‖G w y‖ ^ 2 := by
    have hIntHBx : IntegrableOn (fun p : E3 × E3 =>
        (Submission.BoseGases.chiScale ℓ p.2) ^ 2 * ‖G p.2 p.1‖ ^ 2)
        (halfBall ℓ ×ˢ Bx) (volume.prod volume) :=
      ContinuousOn.integrableOn_compact (hHc.prod hBxc) hΨswcont.continuousOn
    have hIntBxBx : IntegrableOn (fun p : E3 × E3 =>
        (Submission.BoseGases.chiScale ℓ p.2) ^ 2 * ‖G p.2 p.1‖ ^ 2)
        (Bx ×ˢ Bx) (volume.prod volume) :=
      ContinuousOn.integrableOn_compact (hBxc.prod hBxc) hΨswcont.continuousOn
    have h1 : ∫ y in halfBall ℓ, ∫ w in Bx,
        (Submission.BoseGases.chiScale ℓ w) ^ 2 * ‖G w y‖ ^ 2
        = ∫ p in halfBall ℓ ×ˢ Bx,
        (Submission.BoseGases.chiScale ℓ p.2) ^ 2 * ‖G p.2 p.1‖ ^ 2 :=
      (MeasureTheory.setIntegral_prod _ hIntHBx).symm
    have h2 : ∫ p in halfBall ℓ ×ˢ Bx,
        (Submission.BoseGases.chiScale ℓ p.2) ^ 2 * ‖G p.2 p.1‖ ^ 2
        ≤ ∫ p in Bx ×ˢ Bx,
        (Submission.BoseGases.chiScale ℓ p.2) ^ 2 * ‖G p.2 p.1‖ ^ 2 :=
      setIntegral_mono_set hIntBxBx
        (Filter.Eventually.of_forall (fun p => mul_nonneg (sq_nonneg _) (sq_nonneg _)))
        (Filter.Eventually.of_forall (fun p hp => ⟨hBxsub hp.1, hp.2⟩))
    have h3 : ∫ p in Bx ×ˢ Bx,
        (Submission.BoseGases.chiScale ℓ p.2) ^ 2 * ‖G p.2 p.1‖ ^ 2
        = ∫ y in Bx, ∫ w in Bx, (Submission.BoseGases.chiScale ℓ w) ^ 2 * ‖G w y‖ ^ 2 :=
      MeasureTheory.setIntegral_prod _ hIntBxBx
    calc ∫ y in halfBall ℓ, ∫ w in Bx,
          (Submission.BoseGases.chiScale ℓ w) ^ 2 * ‖G w y‖ ^ 2
        = ∫ p in halfBall ℓ ×ˢ Bx,
          (Submission.BoseGases.chiScale ℓ p.2) ^ 2 * ‖G p.2 p.1‖ ^ 2 := h1
      _ ≤ ∫ p in Bx ×ˢ Bx,
          (Submission.BoseGases.chiScale ℓ p.2) ^ 2 * ‖G p.2 p.1‖ ^ 2 := h2
      _ = ∫ y in Bx, ∫ w in Bx, (Submission.BoseGases.chiScale ℓ w) ^ 2 * ‖G w y‖ ^ 2 := h3
  ---------------------------------------------------------------------------------------------
  -- (5) bookkeeping: identify the box integral with `ℓ² · pairMass'`
  ---------------------------------------------------------------------------------------------
  have hpt2 : ∀ w y : E3, ‖chiC ℓ w * G w y‖ ^ 2
      = (Submission.BoseGases.chiScale ℓ w) ^ 2 * ‖G w y‖ ^ 2 := by
    intro w y
    simp only [chiC, norm_mul, Complex.norm_real,
      Real.norm_of_nonneg (Submission.BoseGases.chiScale_nonneg ℓ w)]
    ring
  have hbook : ∫ y in Bx, ∫ w in Bx, (Submission.BoseGases.chiScale ℓ w) ^ 2 * ‖G w y‖ ^ 2
      = ℓ ^ 2 * pairMass' ℓ G := by
    rw [hBx]
    simp only [pairMass']
    simp_rw [hpt2]
    simp_rw [MeasureTheory.integral_const_mul]
    rw [mul_inv_cancel_left₀ (pow_ne_zero 2 (ne_of_gt hℓ))]
  ---------------------------------------------------------------------------------------------
  -- assembly
  ---------------------------------------------------------------------------------------------
  calc ∫ z in Metric.closedBall (0 : E3) (2 * R), ‖psiM ℓ m G z‖ ^ 2
      = ∫ z in K, ‖psiM ℓ m G z‖ ^ 2 := by rw [hK]
    _ ≤ ε ^ 2 * ℓ ^ 3 * ∫ z in K, ∫ y in halfBall ℓ,
          (Submission.BoseGases.chiScale ℓ (z + y - ℓ • Work.BoseBoxFock.latVec m)) ^ 2
            * ‖G (z + y - ℓ • Work.BoseBoxFock.latVec m) y‖ ^ 2 := by
        rw [← hstep2']; exact hstep2
    _ ≤ ε ^ 2 * ℓ ^ 3 * ∫ y in Bx, ∫ w in Bx,
          (Submission.BoseGases.chiScale ℓ w) ^ 2 * ‖G w y‖ ^ 2 := by
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        calc ∫ z in K, ∫ y in halfBall ℓ,
              (Submission.BoseGases.chiScale ℓ (z + y - ℓ • Work.BoseBoxFock.latVec m)) ^ 2
                * ‖G (z + y - ℓ • Work.BoseBoxFock.latVec m) y‖ ^ 2
            = ∫ y in halfBall ℓ, ∫ z in K,
              (Submission.BoseGases.chiScale ℓ (z + y - ℓ • Work.BoseBoxFock.latVec m)) ^ 2
                * ‖G (z + y - ℓ • Work.BoseBoxFock.latVec m) y‖ ^ 2 := hswap
          _ ≤ ∫ y in Bx, ∫ w in Bx,
              (Submission.BoseGases.chiScale ℓ w) ^ 2 * ‖G w y‖ ^ 2 :=
              le_trans hstep34 hstep5
    _ = ε ^ 2 * ℓ ^ 3 * (ℓ ^ 2 * pairMass' ℓ G) := by rw [hbook]
    _ = ε ^ 2 * ℓ ^ 5 * pairMass' ℓ G := by ring

end Work.BoseBoxFock.L1Tails
