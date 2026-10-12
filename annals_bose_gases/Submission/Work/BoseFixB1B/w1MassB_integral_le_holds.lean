import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Submission.Work.BoseFixB1.regime_sideAt_ge
import Submission.Work.BoseFixB1B.lintegral_swap_wSmall1Pair
import Submission.Work.BoseFixB1B.wPairC_g0_lintegral_eq
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1B.w1MassB_integral_le_holds`

FS `eq:appw1sliding` with error, at the level needed by the per-box integration:
there are `ε₀ > 0` and `C ≥ 0` with

    ∫_{I₋} ∬ w_{1,B(u)} ≤ 8π (a v) ℓ³ (1 + C K_B³ (μ(a v)³)^{1/2})

for every admissible `μ`.

The proof is the `lintegral` route: the `I₋`-mass is at most the full `u`-mass
(the mass density is nonnegative), the full `u`-mass is the `(x,y)`-integral of
the `u`-fibre (Tonelli), the fibre is exactly the corpus `wPairC ℓ (g₀)` kernel
(`chiSmallB_w1_pair_uint_cancel`), and that kernel has total mass
`ℓ³∫g₀ = 8π(a v)ℓ³` (`kernel_double_integral` + `g0_integral`).

Two inputs are proved in sibling modules of this directory:

* `Work.BoseFixB1B.lintegral_swap_wSmall1Pair` — the Tonelli exchange of the
  sliding variable `u` with the configuration variables `(x,y)`;
* `Work.BoseFixB1B.wPairC_g0_lintegral_eq` — the total mass of the `ℓ`-scale
  corpus kernel `wPairC ℓ (g₀ v h)`.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseFixB1B

open _root_.BoseGases Submission.BoseGases

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## 0. Two elementary inputs -/

/-- `ofReal` of an integral is at most the integral of the `ofReal`s, for an a.e.
nonnegative real function.  No integrability hypothesis is needed: if `f` is not
integrable the Bochner integral is `0`. -/
lemma ofReal_integral_le_lintegral_of_nonneg {α : Type*} [MeasurableSpace α]
    {μ : MeasureTheory.Measure α} {f : α → ℝ} (hf : 0 ≤ᵐ[μ] f) :
    ENNReal.ofReal (∫ a, f a ∂μ) ≤ ∫⁻ a, ENNReal.ofReal (f a) ∂μ := by
  by_cases hint : MeasureTheory.Integrable f μ
  · rw [MeasureTheory.integral_eq_lintegral_of_nonneg_ae hf hint.aestronglyMeasurable]
    exact ENNReal.ofReal_toReal_le
  · rw [MeasureTheory.integral_undef hint, ENNReal.ofReal_zero]
    exact bot_le

/-- The localised one-body kernel is nonnegative wherever the numerator `g₀` is:
every remaining factor is nonnegative pointwise. -/
lemma wSmall1Pair_nonneg_of_g0 {v : ℝ³ → ℝ} {h : Work.UBB.ScatSol v}
    {M : ℕ} {ℓ d : ℝ} {u x y : ℝ³}
    (hg : 0 ≤ Submission.BoseGases.g0 v h (x - y)) :
    0 ≤ Submission.BoseGases.wSmall1Pair h M ℓ d u x y := by
  simp only [Submission.BoseGases.wSmall1Pair, Submission.BoseGases.wSmallPair,
    Submission.BoseGases.wSmallScaled]
  exact mul_nonneg
    (mul_nonneg (Submission.BoseGases.chiSmallB_nonneg M ℓ d u x)
      (div_nonneg (div_nonneg hg (Work.SmallBoxSliding.convScaleSmall_nonneg M (ℓ * d) (x - y)))
        (Submission.BoseGases.convScale_nonneg ℓ (x - y))))
    (Submission.BoseGases.chiSmallB_nonneg M ℓ d u y)

/-! ## 1. The `I₋`-mass bound at FS's parameters -/

/-- The `I₋`-mass of the localised one-body kernel is at most `8π(a v)ℓ³`. -/
lemma w1MassB_I_minus_bound {v : ℝ³ → ℝ} (h : Work.UBB.ScatSol v) (hv : 0 ≤ v)
    (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : ℝ³) R) (hav : 0 < _root_.BoseGases.a v)
    {M : ℕ} {ℓ d μ : ℝ} (hM : 1 ≤ M) (hℓ : 0 < ℓ) (hd : 0 < d)
    (hR16 : R ≤ ℓ * d / 16) (hRχ : R ≤ ℓ * Submission.BoseGases.chiR0) :
    (∫ u in Work.SmallBoxSliding.interiorSet ℓ d μ,
        Work.BoseFixB1.w1MassB h M ℓ d u)
      ≤ 8 * Real.pi * _root_.BoseGases.a v * ℓ ^ 3 := by
  have hImeas : MeasurableSet (Work.SmallBoxSliding.interiorSet ℓ d μ) :=
    Work.SmallBoxSliding.measurableSet_interiorSet ℓ d μ
  -- `0 ≤ g₀ (x - y)` for a.e. `y`, for **every** `x`
  have hxy : ∀ x : ℝ³, ∀ᵐ y : ℝ³, 0 ≤ Submission.BoseGases.g0 v h (x - y) :=
    fun x => Work.SmallBoxSliding.ae_g0_comp_sub hv hvrad hv_supp hR h x
  have hxy' : ∀ᵐ x : ℝ³, ∀ᵐ y : ℝ³, 0 ≤ Submission.BoseGases.g0 v h (x - y) :=
    Eventually.of_forall hxy
  -- the per-`u` mass is nonnegative
  have hmass_nn : ∀ u : ℝ³, 0 ≤ Work.BoseFixB1.w1MassB h M ℓ d u := fun u =>
    Work.SmallBoxSliding.wSmall1Pair_mass_nonneg hv hvrad hv_supp hR h hM hℓ hd u
  -- the `u`-fibre of the kernel is the corpus `wPairC ℓ (g₀)`
  have hpoint : ∀ x y : ℝ³,
      (∫ u : ℝ³, Submission.BoseGases.wSmall1Pair h M ℓ d u x y)
        = Submission.BoseGases.wPairC ℓ (Submission.BoseGases.g0 v h) x y := by
    intro x y
    rw [Submission.BoseGases.chiSmallB_w1_pair_uint_cancel (v := v) hv_supp h hM hℓ hd hR16 x y]
    simp only [Submission.BoseGases.wPairC, Submission.BoseGases.wPair,
      Submission.BoseGases.wScaled]
    ring
  -- ### STEP 1: `ofReal` of the set integral is at most the set-`lintegral`
  have hstep1 : ENNReal.ofReal
      (∫ u in Work.SmallBoxSliding.interiorSet ℓ d μ, Work.BoseFixB1.w1MassB h M ℓ d u)
      ≤ ∫⁻ u in Work.SmallBoxSliding.interiorSet ℓ d μ,
          ENNReal.ofReal (Work.BoseFixB1.w1MassB h M ℓ d u) := by
    have hind : (fun u => ENNReal.ofReal
          ((Work.SmallBoxSliding.interiorSet ℓ d μ).indicator
            (fun u => Work.BoseFixB1.w1MassB h M ℓ d u) u))
        = (Work.SmallBoxSliding.interiorSet ℓ d μ).indicator
            (fun u => ENNReal.ofReal (Work.BoseFixB1.w1MassB h M ℓ d u)) := by
      funext u
      by_cases hu : u ∈ Work.SmallBoxSliding.interiorSet ℓ d μ
      · simp only [Set.indicator_of_mem hu]
      · simp only [Set.indicator_of_notMem hu, ENNReal.ofReal_zero]
    calc ENNReal.ofReal
          (∫ u in Work.SmallBoxSliding.interiorSet ℓ d μ, Work.BoseFixB1.w1MassB h M ℓ d u)
        = ENNReal.ofReal
            (∫ u, (Work.SmallBoxSliding.interiorSet ℓ d μ).indicator
              (fun u => Work.BoseFixB1.w1MassB h M ℓ d u) u) := by
          rw [MeasureTheory.integral_indicator hImeas]
      _ ≤ ∫⁻ u, ENNReal.ofReal
            ((Work.SmallBoxSliding.interiorSet ℓ d μ).indicator
              (fun u => Work.BoseFixB1.w1MassB h M ℓ d u) u) :=
          ofReal_integral_le_lintegral_of_nonneg (Eventually.of_forall fun u => by
            by_cases hu : u ∈ Work.SmallBoxSliding.interiorSet ℓ d μ
            · simp only [Set.indicator_of_mem hu]; exact hmass_nn u
            · simp only [Set.indicator_of_notMem hu]; exact le_refl 0)
      _ = ∫⁻ u in Work.SmallBoxSliding.interiorSet ℓ d μ,
            ENNReal.ofReal (Work.BoseFixB1.w1MassB h M ℓ d u) := by
          rw [hind, MeasureTheory.lintegral_indicator hImeas]
  -- ### STEP 2: enlarge `I₋` to all of `ℝ³`
  have hstep2 : (∫⁻ u in Work.SmallBoxSliding.interiorSet ℓ d μ,
          ENNReal.ofReal (Work.BoseFixB1.w1MassB h M ℓ d u))
      ≤ ∫⁻ u, ENNReal.ofReal (Work.BoseFixB1.w1MassB h M ℓ d u) := by
    simpa using MeasureTheory.lintegral_mono_set
      (Set.subset_univ (Work.SmallBoxSliding.interiorSet ℓ d μ))
  -- ### STEP 3: peel the two configuration integrals
  have hstep3 : (∫⁻ u, ENNReal.ofReal (Work.BoseFixB1.w1MassB h M ℓ d u))
      ≤ ∫⁻ u, ∫⁻ x, ∫⁻ y, ENNReal.ofReal
          (Submission.BoseGases.wSmall1Pair h M ℓ d u x y) := by
    apply MeasureTheory.lintegral_mono
    intro u
    simp only [Work.BoseFixB1.w1MassB]
    have hxy2 : ∀ᵐ x : ℝ³, ∀ᵐ y : ℝ³,
        0 ≤ Submission.BoseGases.wSmall1Pair h M ℓ d u x y :=
      hxy'.mono fun x hx => hx.mono fun y hy => wSmall1Pair_nonneg_of_g0 hy
    have hxnn : 0 ≤ᵐ[(volume : Measure ℝ³)] (fun x : ℝ³ =>
        ∫ y : ℝ³, Submission.BoseGases.wSmall1Pair h M ℓ d u x y) := by
      filter_upwards [hxy'] with x hx
      exact MeasureTheory.integral_nonneg_of_ae
        (hx.mono fun y hy => wSmall1Pair_nonneg_of_g0 hy)
    calc ENNReal.ofReal (∫ x : ℝ³, ∫ y : ℝ³,
            Submission.BoseGases.wSmall1Pair h M ℓ d u x y)
        ≤ ∫⁻ x, ENNReal.ofReal (∫ y : ℝ³,
            Submission.BoseGases.wSmall1Pair h M ℓ d u x y) :=
          ofReal_integral_le_lintegral_of_nonneg hxnn
      _ ≤ ∫⁻ x, ∫⁻ y, ENNReal.ofReal
            (Submission.BoseGases.wSmall1Pair h M ℓ d u x y) := by
          apply MeasureTheory.lintegral_mono_ae
          filter_upwards [hxy2] with x hx
          exact ofReal_integral_le_lintegral_of_nonneg hx
  -- ### STEP 4: Tonelli — move the `u`-integral inside
  have hstep4 : (∫⁻ u, ∫⁻ x, ∫⁻ y, ENNReal.ofReal
        (Submission.BoseGases.wSmall1Pair h M ℓ d u x y))
      = ∫⁻ x, ∫⁻ y, ∫⁻ u, ENNReal.ofReal
          (Submission.BoseGases.wSmall1Pair h M ℓ d u x y) :=
    lintegral_swap_wSmall1Pair h hR hv_supp hM hℓ hd
  -- ### STEP 5: the exact `u`-integral, fibre by fibre
  have hstep5 : (∫⁻ x, ∫⁻ y, ∫⁻ u, ENNReal.ofReal
        (Submission.BoseGases.wSmall1Pair h M ℓ d u x y))
      = ∫⁻ x, ∫⁻ y, ENNReal.ofReal
          (Submission.BoseGases.wPairC ℓ (Submission.BoseGases.g0 v h) x y) := by
    apply MeasureTheory.lintegral_congr_ae
    filter_upwards [hxy'] with x hx
    apply MeasureTheory.lintegral_congr_ae
    filter_upwards [hx] with y hy
    have hint : MeasureTheory.Integrable (fun u : ℝ³ =>
        Submission.BoseGases.wSmall1Pair h M ℓ d u x y) := by
      simpa only [Submission.BoseGases.wSmall1Pair] using
        Work.SmallBoxSliding.integrable_wSmallPair_u hM hℓ hd
          (Submission.BoseGases.g0 v h) x y
    have hnn : 0 ≤ᵐ[(volume : Measure ℝ³)] (fun u : ℝ³ =>
        Submission.BoseGases.wSmall1Pair h M ℓ d u x y) :=
      Eventually.of_forall (fun u => wSmall1Pair_nonneg_of_g0 hy)
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint hnn, hpoint x y]
  -- ### STEP 6: the total mass of the `ℓ`-scale kernel
  have hstep6 : (∫⁻ x, ∫⁻ y, ENNReal.ofReal
        (Submission.BoseGases.wPairC ℓ (Submission.BoseGases.g0 v h) x y))
      = ENNReal.ofReal (8 * Real.pi * _root_.BoseGases.a v * ℓ ^ 3) :=
    wPairC_g0_lintegral_eq h hv hvrad hR hv_supp hℓ hRχ
  have hmain : ENNReal.ofReal
      (∫ u in Work.SmallBoxSliding.interiorSet ℓ d μ, Work.BoseFixB1.w1MassB h M ℓ d u)
      ≤ ENNReal.ofReal (8 * Real.pi * _root_.BoseGases.a v * ℓ ^ 3) :=
    calc ENNReal.ofReal
          (∫ u in Work.SmallBoxSliding.interiorSet ℓ d μ, Work.BoseFixB1.w1MassB h M ℓ d u)
        ≤ (∫⁻ u in Work.SmallBoxSliding.interiorSet ℓ d μ,
            ENNReal.ofReal (Work.BoseFixB1.w1MassB h M ℓ d u)) := hstep1
      _ ≤ (∫⁻ u, ENNReal.ofReal (Work.BoseFixB1.w1MassB h M ℓ d u)) := hstep2
      _ ≤ (∫⁻ u, ∫⁻ x, ∫⁻ y, ENNReal.ofReal
            (Submission.BoseGases.wSmall1Pair h M ℓ d u x y)) := hstep3
      _ = (∫⁻ x, ∫⁻ y, ∫⁻ u, ENNReal.ofReal
            (Submission.BoseGases.wSmall1Pair h M ℓ d u x y)) := hstep4
      _ = (∫⁻ x, ∫⁻ y, ENNReal.ofReal
            (Submission.BoseGases.wPairC ℓ (Submission.BoseGases.g0 v h) x y)) := hstep5
      _ = ENNReal.ofReal (8 * Real.pi * _root_.BoseGases.a v * ℓ ^ 3) := hstep6
  have hbase : (0 : ℝ) ≤ 8 * Real.pi * _root_.BoseGases.a v * ℓ ^ 3 := by positivity
  exact (ENNReal.ofReal_le_ofReal_iff hbase).mp hmain

/-! ## 2. The requested theorem -/

theorem w1MassB_integral_le_holds {v : EuclideanSpace ℝ (Fin 3) → ℝ} (h : Work.UBB.ScatSol v)
    (hv : 0 ≤ v) (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ}
    (hR : 0 < R) (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R)
    (hav : 0 < _root_.BoseGases.a v) :
    ∃ ε₀ C : ℝ, 0 < ε₀ ∧ 0 ≤ C ∧ ∀ μ : ℝ, Work.BoseBoxFix.Adm v ε₀ μ →
      (∫ u in Work.SmallBoxSliding.interiorSet (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ,
          Work.BoseFixB1.w1MassB h (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
            (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
        ≤ 8 * Real.pi * (_root_.BoseGases.a v)
            * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 3
            * (1 + C * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB ^ 3
                * (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 2 : ℝ)) := by
  obtain ⟨ε₀, hε₀, hreg⟩ := Work.BoseFixB1.regime_sideAt_ge (v := v) hav hR
  refine ⟨ε₀, 1, hε₀, zero_le_one, ?_⟩
  intro μ hAdm
  have hμ : 0 < μ := Work.BoseFixB1.adm_mu_pos hAdm
  have hℓ : 0 < Work.BoseBox.sideAt μ (_root_.BoseGases.a v) :=
    Work.BoseFixB1.adm_ell_pos hAdm
  have hd : 0 < (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d :=
    Work.BoseFixB1.adm_d_pos hAdm
  have hM : 1 ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M := by
    rw [Work.BoseFixB1.paramsAt_eq_fsParams]
    norm_num [Work.BoseBox.fsParams, Work.BoseBox.mValue]
  have hKB : 0 < (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB :=
    Work.BoseFixB1.paramsAt_KB_pos hAdm
  obtain ⟨hR16, hRχ⟩ := hreg μ hμ (Work.BoseFixB1.adm_dilute hAdm)
  have hmass : (∫ u in Work.SmallBoxSliding.interiorSet
        (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ,
        Work.BoseFixB1.w1MassB h (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
          (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
      ≤ 8 * Real.pi * (_root_.BoseGases.a v)
          * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 3 :=
    w1MassB_I_minus_bound (v := v) h hv hvrad hR hv_supp hav hM hℓ hd hR16 hRχ
  have hYnn : 0 ≤ 1 * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB ^ 3
      * (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 2 : ℝ) := by
    refine mul_nonneg (mul_nonneg zero_le_one (pow_nonneg hKB.le 3)) ?_
    exact Real.rpow_nonneg (mul_pos hμ (pow_pos hav 3)).le _
  have hbase : 0 ≤ 8 * Real.pi * (_root_.BoseGases.a v)
      * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 3 := by positivity
  have hle : 8 * Real.pi * (_root_.BoseGases.a v)
        * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 3
      ≤ 8 * Real.pi * (_root_.BoseGases.a v)
        * (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)) ^ 3
        * (1 + 1 * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB ^ 3
            * (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 2 : ℝ)) := by
    nlinarith [mul_nonneg hbase hYnn]
  exact hmass.trans hle

end Work.BoseFixB1B
