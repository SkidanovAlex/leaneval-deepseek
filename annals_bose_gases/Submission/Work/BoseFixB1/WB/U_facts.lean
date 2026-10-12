import ChallengeDeps
import Mathlib.Tactic.Have
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixB1.WB.Lead
import Submission.Work.FibreKinPot.Const.aestronglyMeasurable_wSmall1Pair_jointProd
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

namespace Work.BoseFixB1.WB

open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseBox Work.UBB
open Work.SmallBoxSliding

set_option autoImplicit false
set_option linter.unusedVariables false

/-!
# `Work.BoseFixB1.WB.U_facts`

The two defining facts about FS's `U` (`wbU`):

* the *exact identity* `∫_{Λ} U = W` (with `Λ = acube ℓ`, `W = wbW`), which makes the
  `P`-part of the slot operator `U(xᵢ)` equal to `(W/ℓ³)` times the identity;
* the *sup bound* `U(z) ≤ C (a v) chiSupAbs²` coming from the interface bound
  `wbMass u ≤ C (a v) chiMass u` (`hmassU`) divided by `chiMass u` and integrated
  against `χ_{B(u)}(z)²`.
-/

/-- **The `χ_{B(u)}²`-mass over the centred cube is the sliding mass `chiMass`**:
`χ_{B(u)}²` is supported in `acube ℓ` (`chiSmallB_support_big_box`), so restricting the
integral to the cube does not change it. -/
private theorem integral_acube_chiSmallB_sq {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ)
    (u : ℝ³) :
    (∫ z in acube ℓ, (chiSmallB M ℓ d u z) ^ 2) = chiMass M ℓ d u := by
  rw [chiMass_def]
  refine setIntegral_eq_integral_of_forall_compl_eq_zero (fun z hz => ?_)
  have hz0 : chiSmallB M ℓ d u z = 0 := by
    by_contra hc
    apply hz
    rw [mem_acube_iff]
    intro m
    have hb := chiSmallB_support_big_box hM hℓ hc m
    rw [Set.mem_Icc]
    have h2 := abs_le.mp hb
    exact ⟨by linarith [h2.1], h2.2⟩
  rw [hz0]
  ring

/-- **The sliding mass `chiMass` is a.e. strongly measurable in the centre `u`.**  It is the
`x`-section integral of the jointly continuous `(u,x) ↦ χ_{B(u)}(x)²`
(`AEStronglyMeasurable.integral_prod_right'`). -/
private theorem aestronglyMeasurable_chiMass {M : ℕ} (hM : 1 ≤ M) (ℓ d : ℝ) :
    AEStronglyMeasurable (fun u : ℝ³ => chiMass M ℓ d u) volume := by
  have hcont : Continuous (fun p : ℝ³ × ℝ³ => chiSmallB M ℓ d p.1 p.2) := by
    have h1 : Continuous (fun p : ℝ³ × ℝ³ => chiScale ℓ p.2) :=
      (chiScale_continuous ℓ).comp continuous_snd
    have h2 : Continuous (fun p : ℝ³ × ℝ³ => chiSmall M ((ℓ * d)⁻¹ • p.2 - p.1)) :=
      (chiSmall_continuous hM).comp
        ((continuous_snd.const_smul ((ℓ * d)⁻¹)).sub continuous_fst)
    have hgoal : (fun p : ℝ³ × ℝ³ => chiSmallB M ℓ d p.1 p.2)
        = fun p : ℝ³ × ℝ³ => chiScale ℓ p.2 * chiSmall M ((ℓ * d)⁻¹ • p.2 - p.1) := rfl
    rw [hgoal]
    exact h1.mul h2
  have haes : AEStronglyMeasurable (fun p : ℝ³ × ℝ³ => (chiSmallB M ℓ d p.1 p.2) ^ 2)
      ((volume : Measure ℝ³).prod (volume : Measure ℝ³)) :=
    (hcont.pow 2).aestronglyMeasurable
  have h := haes.integral_prod_right' (ν := (volume : Measure ℝ³))
  simpa only [chiMass_def] using h

/-- `χ_{B(u)}` vanishes off the centred cube `acube ℓ` (`chiSmallB_support_big_box`). -/
private theorem chiSmallB_eq_zero_of_notMem_acube {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ)
    {u x : ℝ³} (hx : x ∉ acube ℓ) : chiSmallB M ℓ d u x = 0 := by
  by_contra hc
  apply hx
  rw [mem_acube_iff]
  intro m
  have hb := chiSmallB_support_big_box hM hℓ hc m
  rw [Set.mem_Icc]
  have h2 := abs_le.mp hb
  exact ⟨by linarith [h2.1], h2.2⟩

/-- The localised one-body kernel vanishes when its *first* configuration slot leaves the
centred cube (the first `χ_{B(u)}` factor vanishes there). -/
private theorem wSmall1Pair_eq_zero_of_notMem_left {v : ℝ³ → ℝ} {h : Work.UBB.ScatSol v} {M : ℕ}
    (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) {u x : ℝ³} (hx : x ∉ acube ℓ) (y : ℝ³) :
    Submission.BoseGases.wSmall1Pair h M ℓ d u x y = 0 := by
  have hχ0 : chiSmallB M ℓ d u x = 0 := chiSmallB_eq_zero_of_notMem_acube hM hℓ hx
  simp only [Submission.BoseGases.wSmall1Pair, Submission.BoseGases.wSmallPair, hχ0, zero_mul]

/-- The localised one-body kernel vanishes when its *second* configuration slot leaves the
centred cube. -/
private theorem wSmall1Pair_eq_zero_of_notMem_right {v : ℝ³ → ℝ} {h : Work.UBB.ScatSol v} {M : ℕ}
    (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) {u y : ℝ³} (hy : y ∉ acube ℓ) (x : ℝ³) :
    Submission.BoseGases.wSmall1Pair h M ℓ d u x y = 0 := by
  have hχ0 : chiSmallB M ℓ d u y = 0 := chiSmallB_eq_zero_of_notMem_acube hM hℓ hy
  simp only [Submission.BoseGases.wSmall1Pair, Submission.BoseGases.wSmallPair, hχ0, mul_zero]

/-- **The localised one-body mass `wbMass` is a.e. strongly measurable in `u`.**  It is the
double `(x,y)`-section integral of `wSmall1Pair`; the kernel is a.e. strongly measurable on the
triple space (`Work.SmallBoxSliding.aestronglyMeasurable_wSmall1Pair_jointProd`, whose only
non-smooth input `g₀` is a.e. strongly measurable), so integrating out `y` and then `x`
(`AEStronglyMeasurable.integral_prod_right'`) gives a.e. strong measurability in `u`.  The
sibling gives the sections only over `acube ℓ`; the last two steps replace those restricted
integrals by the full ones, using that `wSmall1Pair` vanishes off `acube ℓ` in either slot. -/
private theorem aestronglyMeasurable_wbMass {v : ℝ³ → ℝ} {h : Work.UBB.ScatSol v} {R0 : ℝ}
    (hR0 : 0 < R0) (hv_supp : tsupport v ⊆ Metric.ball (0 : ℝ³) R0)
    {μ : ℝ} (hM : 1 ≤ (paramsAt μ (a v)).M) (hℓ : 0 < sideAt μ (a v))
    (hd : 0 < (paramsAt μ (a v)).d) :
    AEStronglyMeasurable (fun u : ℝ³ => wbMass v h μ u) volume := by
  have hjoint := Work.SmallBoxSliding.aestronglyMeasurable_wSmall1Pair_jointProd
    (h := h) (M := (paramsAt μ (a v)).M) (L := sideAt μ (a v)) (d := (paramsAt μ (a v)).d)
    (R := R0) hM hR0 hv_supp hℓ hd
  have h1 : AEStronglyMeasurable
      (fun q : ℝ³ × ℝ³ => ∫ y : ℝ³, Submission.BoseGases.wSmall1Pair h
        (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d q.1 q.2 y
        ∂((volume : Measure ℝ³).restrict (acube (sideAt μ (a v)))))
      ((volume : Measure ℝ³).prod
        ((volume : Measure ℝ³).restrict (acube (sideAt μ (a v))))) :=
    hjoint.integral_prod_right'
  have h2 : AEStronglyMeasurable
      (fun u : ℝ³ => ∫ x : ℝ³, (∫ y : ℝ³, Submission.BoseGases.wSmall1Pair h
        (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u x y
        ∂((volume : Measure ℝ³).restrict (acube (sideAt μ (a v)))))
        ∂((volume : Measure ℝ³).restrict (acube (sideAt μ (a v))))) volume :=
    h1.integral_prod_right'
  refine h2.congr (Filter.Eventually.of_forall (fun u => ?_))
  calc (∫ x : ℝ³, (∫ y : ℝ³, Submission.BoseGases.wSmall1Pair h
          (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u x y
          ∂((volume : Measure ℝ³).restrict (acube (sideAt μ (a v)))))
          ∂((volume : Measure ℝ³).restrict (acube (sideAt μ (a v)))))
      = ∫ x : ℝ³, (∫ y : ℝ³, Submission.BoseGases.wSmall1Pair h
          (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u x y ∂volume)
          ∂((volume : Measure ℝ³).restrict (acube (sideAt μ (a v)))) := by
        refine integral_congr_ae (Filter.Eventually.of_forall (fun x => ?_))
        exact setIntegral_eq_integral_of_forall_compl_eq_zero
          (fun y hy => wSmall1Pair_eq_zero_of_notMem_right hM hℓ hy x)
    _ = ∫ x : ℝ³, (∫ y : ℝ³, Submission.BoseGases.wSmall1Pair h
          (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u x y ∂volume) ∂volume :=
        setIntegral_eq_integral_of_forall_compl_eq_zero (fun x hx => by
          have h0 : ∀ y : ℝ³, Submission.BoseGases.wSmall1Pair h
              (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u x y = 0 :=
            fun y => wSmall1Pair_eq_zero_of_notMem_left hM hℓ hx y
          simp [h0])
    _ = wbMass v h μ u := rfl

theorem U_facts {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v} {R0 : ℝ}
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R0) (hR0 : 0 < R0)
    {μ : ℝ} (hμ : 0 < μ) (hM : 1 ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M)
    (hℓ : 0 < Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
    (hd : 0 < (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d)
    {C : ℝ} (hC : 0 ≤ C)
    (hmassU : ∀ u : EuclideanSpace ℝ (Fin 3), Work.BoseFixB1.wbMass v h μ u
      ≤ C * _root_.BoseGases.a v
        * Work.SmallBoxSliding.chiMass (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
          (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u) :
    ((∫ z in Submission.BoseGases.acube (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)),
        Work.BoseFixB1.wbU v h μ z) = Work.BoseFixB1.wbW v h μ)
      ∧ (∀ z : EuclideanSpace ℝ (Fin 3), Work.BoseFixB1.wbU v h μ z
          ≤ C * _root_.BoseGases.a v * Submission.BoseGases.chiSupAbs ^ 2) := by
  let M : ℕ := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
  let ℓ : ℝ := Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
  let d : ℝ := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d
  have hM' : 1 ≤ M := hM
  have hℓ' : 0 < ℓ := hℓ
  have hd' : 0 < d := hd
  have hmassU' : ∀ u : ℝ³, wbMass v h μ u ≤ C * a v * chiMass M ℓ d u := hmassU
  have hmnn : ∀ u : ℝ³, 0 ≤ wbMass v h μ u :=
    fun u => wbMass_nonneg hv hvrad hv_supp hR0 hM' hℓ' hd' u
  -- ### The cutoff mass is positive somewhere, hence `C (a v) ≥ 0`
  obtain ⟨u₀, hu₀⟩ : ∃ u : ℝ³, 0 < chiMass M ℓ d u := by
    by_contra hcon
    push Not at hcon
    have hzero : ∀ u : ℝ³, chiMass M ℓ d u = 0 :=
      fun u => le_antisymm (hcon u) (chiMass_nonneg M ℓ d u)
    have h0 : (∫ u : ℝ³, chiMass M ℓ d u) = 0 := by
      rw [show (fun u : ℝ³ => chiMass M ℓ d u) = fun _ => (0 : ℝ) from funext hzero]
      simp
    have hvol : (∫ u : ℝ³, chiMass M ℓ d u) = ℓ ^ 3 := integral_chiMass_eq hM' hℓ' hd'
    rw [hvol] at h0
    have hpos : 0 < ℓ ^ 3 := by positivity
    linarith
  have hCa : 0 ≤ C * a v := by
    have h1 : 0 ≤ (C * a v) * chiMass M ℓ d u₀ := le_trans (hmnn u₀) (hmassU' u₀)
    exact nonneg_of_mul_nonneg_left h1 hu₀
  -- ### The pointwise ratio bound
  have hratio : ∀ u : ℝ³, wbMass v h μ u / chiMass M ℓ d u ≤ C * a v := by
    intro u
    rcases eq_or_lt_of_le (chiMass_nonneg M ℓ d u) with h0 | hpos
    · have hm0 : wbMass v h μ u = 0 :=
        le_antisymm (by have hh := hmassU' u; rw [← h0, mul_zero] at hh; exact hh) (hmnn u)
      rw [← h0, hm0, zero_div]
      exact hCa
    · rw [div_le_iff₀ hpos]
      exact hmassU' u
  have hunit : ∀ u : ℝ³,
      (wbMass v h μ u / chiMass M ℓ d u) * chiMass M ℓ d u = wbMass v h μ u := by
    intro u
    rcases eq_or_lt_of_le (chiMass_nonneg M ℓ d u) with h0 | hpos
    · have hm0 : wbMass v h μ u = 0 :=
        le_antisymm (by have hh := hmassU' u; rw [← h0, mul_zero] at hh; exact hh) (hmnn u)
      rw [← h0, hm0, zero_div, zero_mul]
    · exact div_mul_cancel₀ _ (ne_of_gt hpos)
  refine ⟨?_, ?_⟩
  · -- ### `∫_Λ U = W`, by Fubini in the parameter `u` and the point `z`
    have hmass_meas : AEStronglyMeasurable (fun u : ℝ³ => wbMass v h μ u) volume :=
      aestronglyMeasurable_wbMass hR0 hv_supp hM hℓ hd
    have hχmeas : AEStronglyMeasurable (fun u : ℝ³ => chiMass M ℓ d u) volume :=
      aestronglyMeasurable_chiMass hM' ℓ d
    have hcontB : Continuous (fun p : ℝ³ × ℝ³ => chiSmallB M ℓ d p.1 p.2) := by
      have h1 : Continuous (fun p : ℝ³ × ℝ³ => chiScale ℓ p.2) :=
        (chiScale_continuous ℓ).comp continuous_snd
      have h2 : Continuous (fun p : ℝ³ × ℝ³ => chiSmall M ((ℓ * d)⁻¹ • p.2 - p.1)) :=
        (chiSmall_continuous hM').comp
          ((continuous_snd.const_smul ((ℓ * d)⁻¹)).sub continuous_fst)
      have hgoal : (fun p : ℝ³ × ℝ³ => chiSmallB M ℓ d p.1 p.2)
          = fun p : ℝ³ × ℝ³ => chiScale ℓ p.2 * chiSmall M ((ℓ * d)⁻¹ • p.2 - p.1) := rfl
      rw [hgoal]
      exact h1.mul h2
    -- measurability of the uncurried integrand on the product of the two restricted measures
    have hΦmeas : AEStronglyMeasurable
        (fun p : ℝ³ × ℝ³ =>
          (wbMass v h μ p.1 / chiMass M ℓ d p.1) * (chiSmallB M ℓ d p.1 p.2) ^ 2)
        ((volume.restrict (interiorSet ℓ d μ)).prod (volume.restrict (acube ℓ))) :=
      ((AEStronglyMeasurable.div₀
        (hmass_meas.mono_measure Measure.restrict_le_self)
        (hχmeas.mono_measure Measure.restrict_le_self)).comp_fst).mul
        ((hcontB.pow 2).aestronglyMeasurable)
    -- an integrable dominating function
    have hmeas_g : AEStronglyMeasurable
        (fun p : ℝ³ × ℝ³ => (C * a v) * (chiSmallB M ℓ d p.1 p.2) ^ 2)
        (volume.prod volume) :=
      (continuous_const.mul (hcontB.pow 2)).aestronglyMeasurable
    have hgfull : Integrable
        (fun p : ℝ³ × ℝ³ => (C * a v) * (chiSmallB M ℓ d p.1 p.2) ^ 2)
        (volume.prod volume) := by
      rw [integrable_prod_iff hmeas_g]
      refine ⟨?_, ?_⟩
      · filter_upwards with u
        exact (integrable_chiSmallB_sq_slice hM' hℓ' u).const_mul (C * a v)
      · have heq : (fun u : ℝ³ => ∫ z : ℝ³, ‖(C * a v) * (chiSmallB M ℓ d u z) ^ 2‖)
            = fun u : ℝ³ => (C * a v) * chiMass M ℓ d u := by
          funext u
          rw [show (fun z : ℝ³ => ‖(C * a v) * (chiSmallB M ℓ d u z) ^ 2‖)
              = fun z : ℝ³ => (C * a v) * (chiSmallB M ℓ d u z) ^ 2 from
                funext (fun z => by
                  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hCa,
                    abs_of_nonneg (sq_nonneg _)])]
          rw [integral_const_mul, chiMass_def]
        rw [heq]
        exact (integrable_chiSmallB_mass hM' hℓ' hd').const_mul (C * a v)
    have hgint : Integrable
        (fun p : ℝ³ × ℝ³ => (C * a v) * (chiSmallB M ℓ d p.1 p.2) ^ 2)
        ((volume.restrict (interiorSet ℓ d μ)).prod (volume.restrict (acube ℓ))) :=
      hgfull.mono_measure
        (Measure.prod_mono Measure.restrict_le_self Measure.restrict_le_self)
    have hΦint : Integrable
        (fun p : ℝ³ × ℝ³ =>
          (wbMass v h μ p.1 / chiMass M ℓ d p.1) * (chiSmallB M ℓ d p.1 p.2) ^ 2)
        ((volume.restrict (interiorSet ℓ d μ)).prod (volume.restrict (acube ℓ))) :=
      Integrable.mono' hgint hΦmeas (Filter.Eventually.of_forall (fun p => by
        rw [Real.norm_eq_abs, abs_mul,
          abs_of_nonneg (div_nonneg (hmnn p.1) (chiMass_nonneg M ℓ d p.1)),
          abs_of_nonneg (sq_nonneg _)]
        exact mul_le_mul_of_nonneg_right (hratio p.1) (sq_nonneg _)))
    have hswap := integral_integral_swap
      (μ := (volume : Measure ℝ³).restrict (interiorSet ℓ d μ))
      (ν := (volume : Measure ℝ³).restrict (acube ℓ))
      (f := fun u z : ℝ³ =>
        (wbMass v h μ u / chiMass M ℓ d u) * (chiSmallB M ℓ d u z) ^ 2) hΦint
    rw [show (∫ z in acube (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)), wbU v h μ z)
        = ∫ z, (∫ u, (wbMass v h μ u / chiMass M ℓ d u)
              * (chiSmallB M ℓ d u z) ^ 2
              ∂((volume : Measure ℝ³).restrict (interiorSet ℓ d μ)))
            ∂((volume : Measure ℝ³).restrict (acube ℓ)) from rfl]
    rw [← hswap]
    rw [show wbW v h μ
        = ∫ u, wbMass v h μ u ∂((volume : Measure ℝ³).restrict (interiorSet ℓ d μ))
        from rfl]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun u => ?_))
    change (∫ y in acube ℓ,
        (wbMass v h μ u / chiMass M ℓ d u) * (chiSmallB M ℓ d u y) ^ 2)
      = wbMass v h μ u
    rw [integral_const_mul, integral_acube_chiSmallB_sq hM' hℓ' u, hunit u]
  · -- ### The sup bound
    intro z
    have hpt : ∀ u : ℝ³, (wbMass v h μ u / chiMass M ℓ d u) * (chiSmallB M ℓ d u z) ^ 2
        ≤ (C * a v) * (chiSmallB M ℓ d u z) ^ 2 :=
      fun u => mul_le_mul_of_nonneg_right (hratio u) (sq_nonneg _)
    have hgint : Integrable
        (fun u : ℝ³ => (C * a v) * (chiSmallB M ℓ d u z) ^ 2)
        (volume.restrict (interiorSet ℓ d μ)) :=
      ((integrable_chiSmallB_sq_slice_u hM' z).const_mul (C * a v)).integrableOn
    have hfnn : 0 ≤ᵐ[volume.restrict (interiorSet ℓ d μ)]
        (fun u : ℝ³ => (wbMass v h μ u / chiMass M ℓ d u) * (chiSmallB M ℓ d u z) ^ 2) :=
      Filter.Eventually.of_forall (fun u => mul_nonneg
        (div_nonneg (hmnn u) (chiMass_nonneg M ℓ d u)) (sq_nonneg _))
    calc wbU v h μ z
        = ∫ u in interiorSet ℓ d μ,
            (wbMass v h μ u / chiMass M ℓ d u) * (chiSmallB M ℓ d u z) ^ 2 := rfl
      _ ≤ ∫ u in interiorSet ℓ d μ,
            (C * a v) * (chiSmallB M ℓ d u z) ^ 2 :=
          integral_mono_of_nonneg hfnn hgint (Filter.Eventually.of_forall hpt)
      _ = (C * a v) * ∫ u in interiorSet ℓ d μ, (chiSmallB M ℓ d u z) ^ 2 := by
          rw [integral_const_mul]
      _ ≤ (C * a v) * chiSupAbs ^ 2 :=
          mul_le_mul_of_nonneg_left (integral_interiorSet_chiSmallB_sq_le hM' z) hCa

end Work.BoseFixB1.WB
