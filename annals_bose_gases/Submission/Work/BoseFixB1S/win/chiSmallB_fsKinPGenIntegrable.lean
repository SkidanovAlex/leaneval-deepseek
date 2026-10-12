import Mathlib.Topology.UniformSpace.Uniformizable
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1B.pairRung.fsKinPGenIntegrable
import Submission.Work.BoseFixB1S.win.chiSmallB_kinFT_decay
import Submission.Work.BoseFixB1S.win.slotContentIntegrableC2
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1S.win.chiSmallB_fsKinPGenIntegrable`

`q`-integrability of the FS-weighted **sliding** windowed mode content

    q ↦ fsKinCoeff c ‖q‖ · boxWinModePGen ℓ |B(u)| (B(u)) (chiSmallB M ℓ d u) Ψ q .

## Route

The corpus's `Work.BoseFixB1B.pairRung.fsKinPGenIntegrable` proves exactly this for a window `χ`
that is `C^∞`, but the sliding window `chiSmallB M ℓ d u = χ(x/ℓ)·χ_M(x/(ℓd) − u)` is only
`C^{M−1}`, so the `C^∞` theorem cannot be instantiated at it.  The proof is therefore rebuilt from
the two ingredients that *are* available at the regularity the sliding window has:

* the smoothness-free pointwise slot Cauchy–Schwarz
  `Work.BoseFixB1B.pairRung.boxWinModePGen_le_slotSum_clean` (only `Continuous χ` is needed);

* the `C²` single-slot `q`-integrability
  `Work.BoseFixB1S.win.slotContentIntegrableC2` (a public copy of the private
  `slot_content_integrable` of `Submission/Work/BoseFixB1S/winModeContentLeWordC2.lean`).

Section 1 supplies the side conditions on the sliding window itself: `C^{M−1}` regularity
(`contDiff_chiSmall` for the `(ℓd)`-scale factor and `chiScale_contDiff` for the `ℓ`-scale one),
compact support (it is supported in the ball of radius `ℓ/2`), nonnegativity, and the support
containment `support ⊆ dlBox ℓ d u` (both factors vanish outside their boxes).  The remaining
bookkeeping — the box data `Ac = dlBox ℓ d u`, `volA = boxMass ℓ d u` — is in the corpus
(`measurableSet_dlBox`, `dlBox_subset_acube`, `boxMass_eq_measureReal`).
-/

namespace Work.BoseFixB1S.win

open MeasureTheory
open scoped Topology Real BigOperators ENNReal

local notation "E3" => EuclideanSpace ℝ (Fin 3)

noncomputable section

set_option maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option autoImplicit false

/-! ## 1. Side conditions on the sliding window -/

/-- **`chiSmallB M ℓ d u` is `C^N` whenever `N + 1 ≤ M`**: the product of the `C^∞` big-box factor
`χ(·/ℓ)` and the cosine-`M`-th-power small-box factor `χ_M((ℓd)⁻¹· − u)` (`C^{M−1}`). -/
lemma contDiff_chiSmallB (N M : ℕ) (hNM : N + 1 ≤ M) {ℓ d : ℝ} (hℓ : ℓ ≠ 0) (hd : d ≠ 0)
    (u : E3) : ContDiff ℝ (N : WithTop ℕ∞) (Submission.BoseGases.chiSmallB M ℓ d u) := by
  have h1 : ContDiff ℝ (N : WithTop ℕ∞) (Submission.BoseGases.chiScale ℓ) :=
    (Submission.BoseGases.chiScale_contDiff hℓ).of_le (by exact_mod_cast le_top)
  have h2 : ContDiff ℝ (N : WithTop ℕ∞) (Submission.BoseGases.chiSmall M) :=
    contDiff_chiSmall N M hNM
  have h3 : ContDiff ℝ (N : WithTop ℕ∞) (fun x : E3 => (ℓ * d)⁻¹ • x - u) := by
    have hlin : ContDiff ℝ (N : WithTop ℕ∞) (fun x : E3 => (ℓ * d)⁻¹ • x) :=
      ContinuousLinearMap.contDiff (((ℓ * d)⁻¹ : ℝ) • ContinuousLinearMap.id ℝ E3)
    simpa using hlin.sub contDiff_const
  have h4 : ContDiff ℝ (N : WithTop ℕ∞)
      (fun x : E3 => Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • x - u)) := h2.comp h3
  rw [show Submission.BoseGases.chiSmallB M ℓ d u
      = fun x : E3 => Submission.BoseGases.chiScale ℓ x
          * Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • x - u) from rfl]
  exact h1.mul h4

/-- **`chiSmallB M ℓ d u` is compactly supported**: its support is contained in the ball of radius
`ℓ/2` (the support of the big-box factor `χ(·/ℓ)`). -/
private lemma hcs_chiSmallB_priv (M : ℕ) {ℓ d : ℝ} (hℓ : 0 < ℓ) (u : E3) :
    HasCompactSupport (Submission.BoseGases.chiSmallB M ℓ d u) := by
  refine HasCompactSupport.of_support_subset_isCompact
    (isCompact_closedBall (0 : E3) (ℓ / 2)) ?_
  intro z hz
  rw [Function.mem_support] at hz
  rw [Metric.mem_closedBall, dist_eq_norm, sub_zero]
  have h1 : Submission.BoseGases.chiScale ℓ z ≠ 0 :=
    fun h => hz (by dsimp [Submission.BoseGases.chiSmallB]; rw [h, zero_mul])
  have h2 : Submission.BoseGases.chi (ℓ⁻¹ • z) ≠ 0 := h1
  have hlt : ‖ℓ⁻¹ • z‖ < 1 / 2 := by
    by_contra hcon
    exact h2 (Submission.BoseGases.chi_eq_zero_of_half_le_norm _ (le_of_not_gt hcon))
  have hnorm : ‖ℓ⁻¹ • z‖ = ‖z‖ / ℓ := by
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos hℓ, div_eq_inv_mul, mul_comm]
  rw [hnorm] at hlt
  have := (div_lt_iff₀ hℓ).mp hlt
  linarith

/-- **Nonnegativity** of the sliding window (product of two nonnegative bumps). -/
lemma chiSmallB_nonneg (M : ℕ) (ℓ d : ℝ) (u z : E3) :
    0 ≤ Submission.BoseGases.chiSmallB M ℓ d u z :=
  mul_nonneg (Submission.BoseGases.chi_nonneg _) (Submission.BoseGases.chiSmall_nonneg M _)

/-- **Continuity** of the sliding window (no differentiability needed). -/
lemma continuous_chiSmallB {M : ℕ} (hM : 1 ≤ M) (ℓ d : ℝ) (u : E3) :
    Continuous (Submission.BoseGases.chiSmallB M ℓ d u) := by
  have h1 : Continuous (Submission.BoseGases.chiScale ℓ) :=
    Submission.BoseGases.chi_contDiff.continuous.comp (by fun_prop)
  have h2 : Continuous
      (fun x : E3 => Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • x - u)) :=
    (Submission.BoseGases.chiSmall_continuous hM).comp (by fun_prop)
  exact h1.mul h2

/-- **Support of the sliding window inside the sliding box**: `chiSmallB M ℓ d u z ≠ 0` forces
`z ∈ acube ℓ` (big-box factor) and `z − (ℓd)•u ∈ acube (ℓd)` (small-box factor), i.e.
`z ∈ dlBox ℓ d u`.  Contrapositive of the two corpus support lemmas. -/
lemma chiSmallB_eq_zero_of_not_mem_dlBox {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ)
    (hd : 0 < d) (u z : E3) (hz : z ∉ Submission.BoseGases.dlBox ℓ d u) :
    Submission.BoseGases.chiSmallB M ℓ d u z = 0 := by
  have hld : 0 < ℓ * d := mul_pos hℓ hd
  have hbig : ∀ j : Fin 3, ℓ / 2 < |z.ofLp j| →
      Submission.BoseGases.chiSmallB M ℓ d u z = 0 := by
    intro j hj
    by_contra hne
    exact absurd (Submission.BoseGases.chiSmallB_support_big_box hM hℓ hne j) (not_le.mpr hj)
  have hsmall : ∀ j : Fin 3, ℓ * d / 2 < |(z - (ℓ * d) • u).ofLp j| →
      Submission.BoseGases.chiSmallB M ℓ d u z = 0 := by
    intro j hj
    by_contra hne
    exact absurd (Submission.BoseGases.chiSmallB_support_small_box_dist hM hℓ hd hne j)
      (not_le.mpr hj)
  rw [Submission.BoseGases.mem_dlBox_iff] at hz
  rw [not_and_or] at hz
  rcases hz with hz | hz
  · -- `z ∉ acube ℓ`: some coordinate exceeds `ℓ/2` in absolute value
    obtain ⟨j, hj⟩ := not_forall.mp (fun h => hz ((Submission.BoseGases.mem_acube_iff ℓ z).mpr h))
    rw [Set.mem_Icc] at hj
    rw [not_and_or] at hj
    refine hbig j ?_
    rcases hj with hj | hj
    · rw [abs_of_neg (by linarith)]; linarith
    · rw [abs_of_pos (by linarith)]; linarith
  · -- `z − (ℓd)•u ∉ acube (ℓd)`
    obtain ⟨j, hj⟩ :=
      not_forall.mp (fun h => hz ((Submission.BoseGases.mem_acube_iff (ℓ * d)
        (z - (ℓ * d) • u)).mpr h))
    rw [Set.mem_Icc] at hj
    rw [not_and_or] at hj
    refine hsmall j ?_
    rcases hj with hj | hj
    · rw [abs_of_neg (by linarith [hld])]; linarith [hld]
    · rw [abs_of_pos (by linarith [hld])]; linarith [hld]

/-- **A uniform upper bound** for the sliding window (continuity plus compact support). -/
lemma exists_bound_chiSmallB {M : ℕ} {ℓ d : ℝ} (hℓ : 0 < ℓ) (hM : 1 ≤ M) (u : E3) :
    ∃ κ : ℝ, 0 ≤ κ ∧ ∀ z : E3, Submission.BoseGases.chiSmallB M ℓ d u z ≤ κ := by
  have hcont : Continuous (Submission.BoseGases.chiSmallB M ℓ d u) :=
    continuous_chiSmallB hM ℓ d u
  obtain ⟨C, hC⟩ := (hcs_chiSmallB_priv M hℓ u).exists_bound_of_continuousOn
    hcont.continuousOn
  refine ⟨max C 0, le_max_right _ _, fun z => ?_⟩
  by_cases hz : z ∈ tsupport (Submission.BoseGases.chiSmallB M ℓ d u)
  · have h := hC z hz
    rw [Real.norm_eq_abs] at h
    exact le_trans (le_trans (le_abs_self _) h) (le_max_left _ _)
  · rw [image_eq_zero_of_notMem_tsupport hz]
    exact le_max_right _ _

/-! ## 2. The assembly: slot integrability ⟹ the `fsKin`-weighted box content is integrable -/

/-- Scalar bookkeeping: `f·(n·Σᵢ Tᵢ) = n·Σᵢ (f·Tᵢ)`. -/
private lemma mul_card_mul_sum (n : ℕ) (f : ℝ) (T : Fin n → ℝ) :
    f * ((n : ℝ) * ∑ i, T i) = (n : ℝ) * ∑ i, f * T i := by
  simp only [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun i _ => by ring)

/-- **The assembly.**  If every slot `i` of the sharp pointwise Cauchy–Schwarz bound
(`boxWinModePGen_le_slotSum_clean`) has an integrable `fsKinCoeff`-weighted `q`-integrand, then so
has the sliding window's box content itself.  No regularity of `χ` beyond continuity enters here;
this is the reduction that lets the target be fed by the `C²`-level slot integrability. -/
theorem fsKinPGenIntegrable_of_slotIntegrable {n : ℕ} {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    {M : ℕ} (hM : 1 ≤ M) (u : E3) (hVpos : 0 < Work.SmallBoxSliding.boxMass ℓ d u) {c : ℝ}
    {Ψ : Submission.BoseGases.X n → ℝ} (hΨc : ContDiff ℝ (⊤ : ℕ∞) Ψ)
    (hslot : ∀ i : Fin n, MeasureTheory.Integrable (fun q : E3 =>
      Submission.BoseGases.fsKinCoeff c ‖q‖ * ((ℓ ^ 3)⁻¹ *
        ∫ x in Submission.BoseGases.abox n ℓ,
          ‖Work.SmallBoxTBWord.tBamp (Submission.BoseGases.chiSmallB M ℓ d u) q
            (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
              (Submission.BoseGases.dlBox ℓ d u) i Ψ) i x‖ ^ 2))) :
    MeasureTheory.Integrable (fun q : E3 => Submission.BoseGases.fsKinCoeff c ‖q‖ *
      Work.BoseFixB1.boxWinModePGen ℓ (Work.SmallBoxSliding.boxMass ℓ d u)
        (Submission.BoseGases.dlBox ℓ d u) (Submission.BoseGases.chiSmallB M ℓ d u) Ψ q) := by
  classical
  -- abbreviation for the slot integral
  set J : Fin n → E3 → ℝ := fun i q => (ℓ ^ 3)⁻¹ *
      ∫ x in Submission.BoseGases.abox n ℓ,
        ‖Work.SmallBoxTBWord.tBamp (Submission.BoseGases.chiSmallB M ℓ d u) q
          (Work.UBBInputs8.boxQInd (Work.SmallBoxSliding.boxMass ℓ d u)
            (Submission.BoseGases.dlBox ℓ d u) i Ψ) i x‖ ^ 2 with hJ
  have hAcm : MeasurableSet (Submission.BoseGases.dlBox ℓ d u) :=
    Work.SmallBoxSliding.measurableSet_dlBox ℓ d u
  have hAcsub : Submission.BoseGases.dlBox ℓ d u ⊆ Submission.BoseGases.acube ℓ :=
    Work.SmallBoxSliding.dlBox_subset_acube ℓ d u
  have hvol : Work.SmallBoxSliding.boxMass ℓ d u
      = (MeasureTheory.volume (Submission.BoseGases.dlBox ℓ d u)).toReal :=
    Work.SmallBoxSliding.boxMass_eq_measureReal ℓ d u
  have hχc : Continuous (Submission.BoseGases.chiSmallB M ℓ d u) :=
    continuous_chiSmallB hM ℓ d u
  have hχs : HasCompactSupport (Submission.BoseGases.chiSmallB M ℓ d u) :=
    hcs_chiSmallB_priv M hℓ u
  have hχnn : ∀ z : E3, 0 ≤ Submission.BoseGases.chiSmallB M ℓ d u z :=
    fun z => chiSmallB_nonneg M ℓ d u z
  obtain ⟨κ, hκ0, hκ⟩ := exists_bound_chiSmallB hℓ hM u
  obtain ⟨CΨ, hCΨ0, hCΨ⟩ :=
    Work.BoseFixB1.exists_bound_abox_pos (N := n) (ℓ := ℓ) hℓ hΨc.continuous
  -- the smoothness-free pointwise slot bound
  have hP : ∀ q : E3, Work.BoseFixB1.boxWinModePGen ℓ (Work.SmallBoxSliding.boxMass ℓ d u)
        (Submission.BoseGases.dlBox ℓ d u) (Submission.BoseGases.chiSmallB M ℓ d u) Ψ q
      ≤ (n : ℝ) * ∑ i : Fin n, J i q := by
    intro q
    have h := Work.BoseFixB1B.pairRung.boxWinModePGen_le_slotSum_clean (n := n) (a := ℓ)
      (volA := Work.SmallBoxSliding.boxMass ℓ d u) (κ := κ) (CΨ := CΨ) hℓ hVpos hκ0 hAcm
      hAcsub hvol hχc hχs hχnn hκ hΨc.continuous hCΨ hCΨ0 q
    rw [hJ]
    exact h
  -- integrability of the slot integrands and of the dominating function
  have hslot' : ∀ i : Fin n, MeasureTheory.Integrable
      (fun q : E3 => Submission.BoseGases.fsKinCoeff c ‖q‖ * J i q) := by
    intro i
    rw [hJ]
    exact hslot i
  have hsumInt : MeasureTheory.Integrable (fun q : E3 =>
      ∑ i : Fin n, Submission.BoseGases.fsKinCoeff c ‖q‖ * J i q) :=
    integrable_finsetSum _ (fun i _ => hslot' i)
  have hdomInt : MeasureTheory.Integrable (fun q : E3 =>
      Submission.BoseGases.fsKinCoeff c ‖q‖ * ((n : ℝ) * ∑ i : Fin n, J i q)) := by
    refine (hsumInt.const_mul (n : ℝ)).congr (Filter.Eventually.of_forall (fun q => ?_))
    exact (mul_card_mul_sum n (Submission.BoseGases.fsKinCoeff c ‖q‖)
      (fun i => J i q)).symm
  -- a.e. strong measurability of the target integrand
  have haesm : AEStronglyMeasurable (fun q : E3 => Submission.BoseGases.fsKinCoeff c ‖q‖ *
      Work.BoseFixB1.boxWinModePGen ℓ (Work.SmallBoxSliding.boxMass ℓ d u)
        (Submission.BoseGases.dlBox ℓ d u) (Submission.BoseGases.chiSmallB M ℓ d u) Ψ q)
      (MeasureTheory.volume : MeasureTheory.Measure E3) := by
    have hcont : Continuous (fun q : E3 => Submission.BoseGases.fsKinCoeff c ‖q‖) := by
      simp only [Submission.BoseGases.fsKinCoeff]
      fun_prop
    exact hcont.aestronglyMeasurable.mul
      (Work.BoseFixB1B.pairRung.aeStronglyMeasurable_boxWinModePGen hAcm hχc hΨc.continuous)
  -- domination and conclusion
  refine MeasureTheory.Integrable.mono' hdomInt haesm ?_
  filter_upwards with q
  have hPnn : 0 ≤ Work.BoseFixB1.boxWinModePGen ℓ (Work.SmallBoxSliding.boxMass ℓ d u)
      (Submission.BoseGases.dlBox ℓ d u) (Submission.BoseGases.chiSmallB M ℓ d u) Ψ q := by
    simp only [Work.BoseFixB1.boxWinModePGen, Work.BoseFixB1.boxModePGen]
    exact add_nonneg (integral_nonneg fun x => sq_nonneg _)
      (integral_nonneg fun x => sq_nonneg _)
  rw [Real.norm_of_nonneg
    (mul_nonneg (Submission.BoseGases.fsKinCoeff_nonneg c ‖q‖) hPnn)]
  exact mul_le_mul_of_nonneg_left (hP q) (Submission.BoseGases.fsKinCoeff_nonneg c ‖q‖)

/-! ## 3. The target -/

theorem chiSmallB_fsKinPGenIntegrable {n : ℕ} {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) (hd1 : d ≤ 1)
    {M : ℕ} (hM : 5 ≤ M) (u : EuclideanSpace ℝ (Fin 3))
    (hVpos : 0 < Work.SmallBoxSliding.boxMass ℓ d u)
    {c : ℝ} (hc : 0 < c) {Ψ : Submission.BoseGases.X n → ℝ} (hΨc : ContDiff ℝ (⊤ : ℕ∞) Ψ) :
    MeasureTheory.Integrable (fun q : EuclideanSpace ℝ (Fin 3) => Submission.BoseGases.fsKinCoeff c ‖q‖ *
      Work.BoseFixB1.boxWinModePGen ℓ (Work.SmallBoxSliding.boxMass ℓ d u)
        (Submission.BoseGases.dlBox ℓ d u) (Submission.BoseGases.chiSmallB M ℓ d u) Ψ q) := by
  refine fsKinPGenIntegrable_of_slotIntegrable hℓ hd (by omega) u hVpos hΨc (fun i => ?_)
  exact slotContentIntegrableC2 hℓ (Work.SmallBoxSliding.measurableSet_dlBox ℓ d u)
    (Work.SmallBoxSliding.dlBox_subset_acube ℓ d u)
    (Work.SmallBoxSliding.boxMass_eq_measureReal ℓ d u) hVpos
    (contDiff_chiSmallB 2 M (by omega) (ne_of_gt hℓ) (ne_of_gt hd) u)
    (hcs_chiSmallB_priv M hℓ u)
    (fun z hz => chiSmallB_eq_zero_of_not_mem_dlBox (by omega) hℓ hd u z hz)
    (fun z => chiSmallB_nonneg M ℓ d u z) hc hΨc i

end

end Work.BoseFixB1S.win
