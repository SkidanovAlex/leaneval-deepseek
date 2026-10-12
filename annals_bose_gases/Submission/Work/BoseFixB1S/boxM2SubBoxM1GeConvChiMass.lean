import ChallengeDeps
import Mathlib.MeasureTheory.Group.Integral
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseFixB1.integrable_sbMassKernel
import Submission.Work.BoseFixB1B.boxM2_sub_boxM1_eq_omegaMass
import Submission.Work.BoseFixB1S.wSmallScaledComparisonAlt
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1S.boxM2SubBoxM1GeConvChiMass`

The **lower bound for the sliding-box mass difference in terms of the fibre-shift hypothesis**:

    (1 − θ)·(g₀ω₀-mass)·(χ_B-mass)  ≤  boxM2 − boxM1 ,

where `boxM2 − boxM1 = ∬_{B(u)×B(u)} ω₀(x−y)·w_{1,B(u)}(x,y)` is FS `lm:w2>w1`
(`Work.BoseFixB1B.boxM2_sub_boxM1_eq_omegaMass`), the shift hypothesis is

    (1 − θ)·chiMass ≤ ∫ x, χ_B x · χ_B (x − z)      (‖z‖ ≤ R)          (S)

and `g0w0Mass = ∫ z, g₀ z · ω₀ z` is the scattering `g₀ω₀`-mass.

## The mathematics

Writing `χ = χ_B = chiSmallB M ℓ d u` and `g₀ = v(1−ω₀)`, the identity gives

    boxM2 − boxM1 = ∬ ω₀(x−y) w₁(x,y) .

Since `g₀` is supported in `ball 0 R` (`R ≤ ℓd/16`, `R ≤ ℓ·chiR0`), on the support both
renormalisation denominators are bounded below (`a ≥ smallConvLower M`, `b ≥ 1/2`) and above by
`1`, so the pointwise comparison

    χ x · χ y · g₀(x−y)  ≤  w₁(x,y)                                    (P)

holds a.e. (for `g₀(x−y) ≥ 0`).  As `0 ≤ ω₀ ≤ 1` a.e. (`scattering_bounds_ae`), multiplying
by `ω₀(x−y) ≥ 0` gives

    boxM2 − boxM1 ≥ ∬ ω₀(x−y) g₀(x−y) χ x χ y .

The **shear identity** `shear_integral_identity` (the map `(x,y) ↦ (x−y,y)` is
measure-preserving, `measurePreserving_add_prod`, followed by Fubini) evaluates the right-hand
side as the *single* integral

    ∬ ω₀(x−y) g₀(x−y) χ x χ y = ∫ z, (g₀ω₀)(z) · (∫ y, χ(z+y) χ y) ,

and translation invariance (`conv_shift_eq`) identifies the inner integral with
`∫ x, χ x χ(x−z)`; the shift hypothesis (S) then says it is `≥ (1−θ)·chiMass` for `‖z‖ ≤ R`,
while `(g₀ω₀)(z) = 0` for `‖z‖ > R` and `g₀ω₀ ≥ 0` a.e., so the last integral is at least
`(1−θ)·chiMass·∫(g₀ω₀) = (1−θ)·chiMass·g0w0Mass`.

## Where the shift hypothesis comes from

(S) is the *substitute* for FS's flatness of the `χ_B`-autocorrelation
(`FINDING_chiCorr_lipschitz_FALSE.md` records that the latter is false for the corpus's
ball-supported bump).  The caller supplies (S) as a hypothesis; this file needs nothing else from
the geometry of `χ_B` than positivity, boundedness and support in the sliding box.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Real BigOperators ENNReal Topology

namespace Work.BoseFixB1S

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option maxHeartbeats 3200000
set_option linter.unusedVariables false

/-! ## §1. The measure-theoretic core -/

/-- **The shear (change of variables) identity for the difference kernel.**  The map
`(x,y) ↦ (x−y,y)` preserves the product Lebesgue measure (`measurePreserving_add_prod`), so
Fubini turns the double integral of `h(x−y)X(x)X(y)` into the single integral of
`h z · ∫ y, X(z+y)X y`. -/
theorem shear_integral_identity (h X : E3 → ℝ)
    (hint : Integrable (fun q : E3 × E3 => h q.1 * (X (q.1 + q.2) * X q.2))
      ((volume : Measure E3).prod volume)) :
    (∫ p : E3 × E3, h (p.1 - p.2) * (X p.1 * X p.2) ∂((volume : Measure E3).prod volume))
      = ∫ z, h z * (∫ y, X (z + y) * X y ∂(volume : Measure E3)) ∂(volume : Measure E3) := by
  let e : E3 × E3 ≃ᵐ E3 × E3 :=
    { toEquiv := { toFun := fun z => (z.1 + z.2, z.2),
                   invFun := fun z => (z.1 - z.2, z.2),
                   left_inv := fun z => by simp,
                   right_inv := fun z => by simp }
      measurable_toFun := by
        show Measurable (fun z : E3 × E3 => (z.1 + z.2, z.2))
        exact (measurable_fst.add measurable_snd).prodMk measurable_snd
      measurable_invFun := by
        show Measurable (fun z : E3 × E3 => (z.1 - z.2, z.2))
        exact (measurable_fst.sub measurable_snd).prodMk measurable_snd }
  have hmp : MeasurePreserving (⇑e) ((volume : Measure E3).prod volume)
      ((volume : Measure E3).prod volume) := MeasureTheory.measurePreserving_add_prod _ _
  have h1 := hmp.integral_comp' (g := fun p : E3 × E3 => h (p.1 - p.2) * (X p.1 * X p.2))
  rw [← h1]
  rw [show (∫ x : E3 × E3, h ((e x).1 - (e x).2) * (X (e x).1 * X (e x).2)
        ∂((volume : Measure E3).prod volume))
      = ∫ q : E3 × E3, h q.1 * (X (q.1 + q.2) * X q.2) ∂((volume : Measure E3).prod volume)
      from integral_congr_ae (Eventually.of_forall fun x => by
        show h ((x.1 + x.2) - x.2) * (X (x.1 + x.2) * X x.2)
          = h x.1 * (X (x.1 + x.2) * X x.2)
        rw [add_sub_cancel_right])]
  rw [MeasureTheory.integral_prod _ hint]
  simp_rw [MeasureTheory.integral_const_mul]

/-- **Translation invariance of the fibre integral**: `∫ y, X(z+y)X y = ∫ x, X x X(x−z)`. -/
theorem conv_shift_eq (X : E3 → ℝ) (z : E3) :
    (∫ y, X (z + y) * X y ∂(volume : Measure E3))
      = ∫ x, X x * X (x - z) ∂(volume : Measure E3) := by
  have h1 : (∫ y, X (z + y) * X y ∂(volume : Measure E3))
      = ∫ y, (fun x : E3 => X x * X (x - z)) (y + z) ∂(volume : Measure E3) := by
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    show X (z + y) * X y = X (y + z) * X (y + z - z)
    rw [add_comm z y, add_sub_cancel_right]
  rw [h1, MeasureTheory.integral_add_right_eq_self (f := fun x : E3 => X x * X (x - z)) z]

/-! ## §2. The pointwise kernel comparison -/

/-- **Pointwise comparison of the localised kernel with `g₀ ⊗ χ_B ⊗ χ_B`.**

For `z = x − y` with `g₀ z ≥ 0` one has

    g₀ z · χ_B(x) · χ_B(y) ≤ w_{1,B(u)}(x,y) .

Indeed, if `‖z‖ < R ≤ ℓd/16` both renormalisation denominators are in `(0,1]`
(`smallConvLower M ≤ (χ_M⋆χ_M)(z/(ℓd)) ≤ 1` and `1/2 ≤ (χ⋆χ)(z/ℓ) ≤ 1`), so
`1/(ab) ≥ 1` and `g₀ z/(ab) ≥ g₀ z`; if `‖z‖ ≥ R` then `g₀ z = 0` and both sides vanish. -/
private lemma g0_mul_chi_le_wSmall1Pair {v : E3 → ℝ} {R : ℝ}
    (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R) (hR0 : 0 < R)
    (h : Work.UBB.ScatSol v) {M : ℕ} (hM : 1 ≤ M) {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (hR : R ≤ ℓ * d / 16) (hRχ : R ≤ ℓ * Submission.BoseGases.chiR0)
    (u x y : E3) (hg : 0 ≤ Submission.BoseGases.g0 v h (x - y)) :
    Submission.BoseGases.g0 v h (x - y) * Submission.BoseGases.chiSmallB M ℓ d u x
        * Submission.BoseGases.chiSmallB M ℓ d u y
      ≤ Submission.BoseGases.wSmall1Pair h M ℓ d u x y := by
  have hfac : Submission.BoseGases.wSmall1Pair h M ℓ d u x y
      = Submission.BoseGases.chiSmallB M ℓ d u x
        * (Submission.BoseGases.g0 v h (x - y)
            / (Submission.BoseGases.convScaleSmall M (ℓ * d) (x - y)
                * Submission.BoseGases.convScale ℓ (x - y)))
        * Submission.BoseGases.chiSmallB M ℓ d u y := by
    rw [Submission.BoseGases.wSmall1Pair, Submission.BoseGases.wSmallPair,
      Submission.BoseGases.wSmallScaled, div_div]
  have hXx : 0 ≤ Submission.BoseGases.chiSmallB M ℓ d u x :=
    Submission.BoseGases.chiSmallB_nonneg M ℓ d u x
  have hXy : 0 ≤ Submission.BoseGases.chiSmallB M ℓ d u y :=
    Submission.BoseGases.chiSmallB_nonneg M ℓ d u y
  by_cases hz : ‖x - y‖ < R
  · have hzR : ‖x - y‖ ≤ R := le_of_lt hz
    have hld : 0 < ℓ * d := mul_pos hℓ hd
    -- the `ℓd`-denominator is `≥ smallConvLower M`
    have hcoord : ∀ j : Fin 3, |(((ℓ * d)⁻¹) • (x - y)).ofLp j| ≤ 1 / 16 := by
      intro j
      have hnorm : ‖((ℓ * d)⁻¹) • (x - y)‖ ≤ 1 / 16 := by
        rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hld)]
        calc (ℓ * d)⁻¹ * ‖x - y‖ ≤ (ℓ * d)⁻¹ * R :=
              mul_le_mul_of_nonneg_left hzR (inv_pos.mpr hld).le
          _ ≤ (ℓ * d)⁻¹ * (ℓ * d / 16) := mul_le_mul_of_nonneg_left hR (inv_pos.mpr hld).le
          _ = 1 / 16 := by field_simp
      exact le_trans (Submission.BoseGases.coord_abs_le_norm _ j) hnorm
    have ha : Work.SmallBoxSliding.smallConvLower M
        ≤ Submission.BoseGases.convScaleSmall M (ℓ * d) (x - y) :=
      Work.SmallBoxSliding.conv3Small_coord_lower hM _ hcoord
    have hapos : 0 < Submission.BoseGases.convScaleSmall M (ℓ * d) (x - y) :=
      lt_of_lt_of_le (Work.SmallBoxSliding.smallConvLower_pos M) ha
    have ha1 : Submission.BoseGases.convScaleSmall M (ℓ * d) (x - y) ≤ 1 := by
      have h' := Submission.BoseGases.conv3Small_abs_le_one hM (((ℓ * d)⁻¹) • (x - y))
      rw [abs_le] at h'
      exact h'.2
    have hb : 1 / 2 ≤ Submission.BoseGases.convScale ℓ (x - y) :=
      Submission.BoseGases.convScale_ge_half_of_le hℓ hRχ hzR
    have hbpos : 0 < Submission.BoseGases.convScale ℓ (x - y) :=
      lt_of_lt_of_le (by norm_num) hb
    have hb1 : Submission.BoseGases.convScale ℓ (x - y) ≤ 1 :=
      Submission.BoseGases.conv3chi_le_one ((ℓ⁻¹) • (x - y))
    have hab : 0 < Submission.BoseGases.convScaleSmall M (ℓ * d) (x - y)
        * Submission.BoseGases.convScale ℓ (x - y) := mul_pos hapos hbpos
    have hab1 : Submission.BoseGases.convScaleSmall M (ℓ * d) (x - y)
        * Submission.BoseGases.convScale ℓ (x - y) ≤ 1 := by
      nlinarith [ha1, hb1, hapos.le, hbpos.le]
    have hmid : Submission.BoseGases.g0 v h (x - y)
        ≤ Submission.BoseGases.g0 v h (x - y)
            / (Submission.BoseGases.convScaleSmall M (ℓ * d) (x - y)
                * Submission.BoseGases.convScale ℓ (x - y)) := by
      rw [le_div_iff₀ hab]
      nlinarith [hg, hab1]
    rw [hfac]
    calc Submission.BoseGases.g0 v h (x - y) * Submission.BoseGases.chiSmallB M ℓ d u x
          * Submission.BoseGases.chiSmallB M ℓ d u y
        = Submission.BoseGases.chiSmallB M ℓ d u x * Submission.BoseGases.g0 v h (x - y)
            * Submission.BoseGases.chiSmallB M ℓ d u y := by ring
      _ ≤ Submission.BoseGases.chiSmallB M ℓ d u x
            * (Submission.BoseGases.g0 v h (x - y)
                / (Submission.BoseGases.convScaleSmall M (ℓ * d) (x - y)
                    * Submission.BoseGases.convScale ℓ (x - y)))
            * Submission.BoseGases.chiSmallB M ℓ d u y :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hmid hXx) hXy
  · have hg0 : Submission.BoseGases.g0 v h (x - y) = 0 :=
      Submission.BoseGases.g0_zero_of_norm_ge hv_supp (le_of_not_gt hz) h
    rw [hfac, hg0]
    simp

/-! ## §3. The target -/

/-- **The lower bound `boxM2 − boxM1 ≥ (1−θ)·g0w0Mass·chiMass`** under the shift hypothesis (S)
on the `chiSmallB`-autocorrelation. -/
theorem boxM2SubBoxM1GeConvChiMass {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R : ℝ}
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R) (hR0 : 0 < R)
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v) (hv1 : MeasureTheory.MemLp v 1)
    (h : Work.UBB.ScatSol v)
    {M : ℕ} (hM : 1 ≤ M) {ℓ d θ : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    (hR : R ≤ ℓ * d / 16) (hRχ : R ≤ ℓ * Submission.BoseGases.chiR0)
    (u : EuclideanSpace ℝ (Fin 3))
    (hshift : ∀ z : EuclideanSpace ℝ (Fin 3), ‖z‖ ≤ R →
      (1 - θ) * Work.SmallBoxSliding.chiMass M ℓ d u
        ≤ ∫ x : EuclideanSpace ℝ (Fin 3), Submission.BoseGases.chiSmallB M ℓ d u x
            * Submission.BoseGases.chiSmallB M ℓ d u (x - z)) :
    (1 - θ) * (Submission.BoseGases.g0w0Mass (v := v) h) * Work.SmallBoxSliding.chiMass M ℓ d u
      ≤ Work.BoseFixB1S.boxM2 (Work.SmallBoxSliding.boxMass ℓ d u)
            (Submission.BoseGases.dlBox ℓ d u)
            (Submission.BoseGases.wSmallPair M ℓ d u (Submission.BoseGases.g2 v h))
        - Work.BoseFixB1S.boxM1 ℓ (Submission.BoseGases.dlBox ℓ d u)
            (Submission.BoseGases.wSmall1Pair h M ℓ d u) := by
  classical
  -- ### Step 1: the `ω`-mass identity (FS `lm:w2>w1`)
  have hId := Work.BoseFixB1B.boxM2_sub_boxM1_eq_omegaMass (v := v) (R0 := R)
    hv_supp hR0 hv hvrad hv1 (h := h) (M := M) hM (ℓ := ℓ) (d := d) hℓ hd u
  rw [hId]
  -- ### Step 2: basic facts about the cutoff
  have hXcont : Continuous (fun x : E3 => Submission.BoseGases.chiSmallB M ℓ d u x) := by
    show Continuous fun x : E3 =>
      Submission.BoseGases.chiScale ℓ x * Submission.BoseGases.chiSmall M ((ℓ * d)⁻¹ • x - u)
    exact (Submission.BoseGases.chiScale_continuous ℓ).mul
      ((Submission.BoseGases.chiSmall_continuous hM).comp
        ((continuous_const_smul ((ℓ * d)⁻¹)).sub continuous_const))
  have hqmp : Measure.QuasiMeasurePreserving (fun p : E3 × E3 => p.1 - p.2)
      ((volume : Measure E3).prod volume) (volume : Measure E3) :=
    MeasureTheory.quasiMeasurePreserving_sub_of_right_invariant _ _
  have hCaesm : AEStronglyMeasurable (Classical.choose h) (volume : Measure E3) :=
    ((Classical.choose_spec h).2).lhs_integrable.aestronglyMeasurable
  have hgaesm : AEStronglyMeasurable (Submission.BoseGases.g0 v h) (volume : Measure E3) :=
    (Submission.BoseGases.g0_integrable hR0 hv_supp h).aestronglyMeasurable
  have hCaesm' : AEStronglyMeasurable (fun p : E3 × E3 => Classical.choose h (p.1 - p.2))
      ((volume : Measure E3).prod volume) := hCaesm.comp_quasiMeasurePreserving hqmp
  have hgaesm' : AEStronglyMeasurable (fun p : E3 × E3 => Submission.BoseGases.g0 v h (p.1 - p.2))
      ((volume : Measure E3).prod volume) := hgaesm.comp_quasiMeasurePreserving hqmp
  have hX1m : AEStronglyMeasurable
      (fun p : E3 × E3 => Submission.BoseGases.chiSmallB M ℓ d u p.1)
      ((volume : Measure E3).prod volume) :=
    (hXcont.measurable.comp measurable_fst).aestronglyMeasurable
  have hX2m : AEStronglyMeasurable
      (fun p : E3 × E3 => Submission.BoseGases.chiSmallB M ℓ d u p.2)
      ((volume : Measure E3).prod volume) :=
    (hXcont.measurable.comp measurable_snd).aestronglyMeasurable
  have haesmGf : AEStronglyMeasurable (fun p : E3 × E3 => Classical.choose h (p.1 - p.2)
      * Submission.BoseGases.g0 v h (p.1 - p.2)
      * Submission.BoseGases.chiSmallB M ℓ d u p.1
      * Submission.BoseGases.chiSmallB M ℓ d u p.2) ((volume : Measure E3).prod volume) :=
    ((hCaesm'.mul hgaesm').mul hX1m).mul hX2m
  have hXbdd : ∀ x : E3, |Submission.BoseGases.chiSmallB M ℓ d u x|
      ≤ Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M := by
    intro x
    refine le_trans (Work.SmallBoxSliding.abs_chiSmallB_le (M := M) hM (ℓ := ℓ) (d := d) u x) ?_
    have h := Submission.BoseGases.chiSmall_decay_coord_le_decay hM ((ℓ * d)⁻¹ • x - u)
    rw [abs_of_nonneg (Submission.BoseGases.chiSmall_nonneg M _)] at h
    exact mul_le_mul_of_nonneg_left h Submission.BoseGases.chiSupAbs_nonneg
  have hXzero : ∀ x : E3, x ∉ Submission.BoseGases.acube ℓ →
      Submission.BoseGases.chiSmallB M ℓ d u x = 0 := by
    intro x hx
    by_contra hne
    exact hx (Work.SmallBoxSliding.dlBox_subset_acube ℓ d u
      (Work.SlotWord.chiSmallB_support_mem_dlBox hM hℓ hd hne))
  have hXnonneg : ∀ x : E3, 0 ≤ Submission.BoseGases.chiSmallB M ℓ d u x :=
    Submission.BoseGases.chiSmallB_nonneg M ℓ d u
  -- ### Step 3: integrability of the cutoff and of the pair integrands
  have hIntX : Integrable (fun x : E3 => Submission.BoseGases.chiSmallB M ℓ d u x)
      (volume : Measure E3) := by
    have hKm : Integrable (fun x : E3 =>
        (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M)
          * (Submission.BoseGases.acube ℓ).indicator (fun _ => (1 : ℝ)) x)
        (volume : Measure E3) := by
      refine Integrable.const_mul ?_ _
      rw [MeasureTheory.integrable_indicator_iff (Submission.BoseGases.acube_measurable ℓ)]
      exact MeasureTheory.integrableOn_const (C := (1 : ℝ))
        (lt_top_iff_ne_top.mp (Submission.BoseGases.acube_lt_top ℓ hℓ.le))
    refine Integrable.mono' hKm hXcont.aestronglyMeasurable ?_
    filter_upwards with x
    by_cases hx : x ∈ Submission.BoseGases.acube ℓ
    · rw [Set.indicator_of_mem hx, mul_one, Real.norm_eq_abs]
      exact hXbdd x
    · rw [Set.indicator_of_notMem hx, mul_zero, Real.norm_eq_abs, hXzero x hx, abs_zero]
  have hDom : Integrable (fun p : E3 × E3 => Submission.BoseGases.chiSmallB M ℓ d u p.1
      * |Submission.BoseGases.g0 v h (p.1 - p.2)| * Submission.BoseGases.chiSmallB M ℓ d u p.2)
      ((volume : Measure E3).prod volume) := by
    refine (MeasureTheory.integrableOn_iff_integrable_of_support_subset ?_).mp
      (Work.BoseFixB1.integrable_sbMassKernel hv_supp hR0 h hM hℓ hd hR hRχ u)
    rintro ⟨x, y⟩ hp
    have hx : Submission.BoseGases.chiSmallB M ℓ d u x ≠ 0 := by
      intro h0; exact hp (by simp [h0])
    have hy : Submission.BoseGases.chiSmallB M ℓ d u y ≠ 0 := by
      intro h0; exact hp (by simp [h0])
    exact Set.mem_prod.mpr ⟨Work.SlotWord.chiSmallB_support_mem_dlBox hM hℓ hd hx,
      Work.SlotWord.chiSmallB_support_mem_dlBox hM hℓ hd hy⟩
  have hvanW1 : ∀ p : E3 × E3,
      p ∉ Submission.BoseGases.dlBox ℓ d u ×ˢ Submission.BoseGases.dlBox ℓ d u →
      Submission.BoseGases.wSmall1Pair h M ℓ d u p.1 p.2 = 0 := by
    rintro ⟨x, y⟩ hp
    by_cases hx : x ∈ Submission.BoseGases.dlBox ℓ d u <;>
      by_cases hy : y ∈ Submission.BoseGases.dlBox ℓ d u
    · exact absurd (Set.mem_prod.mpr ⟨hx, hy⟩) hp
    · exact Work.BoseFixB1S.wSmallPair_eq_zero_of_notMem_dlBox hM hℓ hd u (Or.inr hy)
    · exact Work.BoseFixB1S.wSmallPair_eq_zero_of_notMem_dlBox hM hℓ hd u (Or.inl hx)
    · exact Work.BoseFixB1S.wSmallPair_eq_zero_of_notMem_dlBox hM hℓ hd u (Or.inl hx)
  have hIntW1 : Integrable (fun p : E3 × E3 =>
      Submission.BoseGases.wSmall1Pair h M ℓ d u p.1 p.2) ((volume : Measure E3).prod volume) := by
    refine (MeasureTheory.integrableOn_iff_integrable_of_support_subset ?_).mp
      (Work.BoseFixB1.integrableOn_wSmallPair_cube (f := Submission.BoseGases.g0 v h)
        (Submission.BoseGases.g0_integrable hR0 hv_supp h) (R0 := R)
        (fun z hz => Submission.BoseGases.g0_zero_of_norm_ge hv_supp hz h) hM hℓ hd hR hRχ u)
    intro p hp
    have hpA : p ∈ Submission.BoseGases.dlBox ℓ d u ×ˢ Submission.BoseGases.dlBox ℓ d u := by
      by_contra hc
      exact hp (hvanW1 p hc)
    exact Set.mem_prod.mpr
      ⟨Work.SmallBoxSliding.dlBox_subset_acube ℓ d u (Set.mem_prod.mp hpA).1,
       Work.SmallBoxSliding.dlBox_subset_acube ℓ d u (Set.mem_prod.mp hpA).2⟩
  -- ### Step 4: a.e. bounds on `ω₀` and `g₀`
  have hw0nn : ∀ᵐ z ∂(volume : Measure E3), 0 ≤ Classical.choose h z :=
    (Submission.BoseGases.scattering_bounds_ae hR0 hv hvrad hv_supp (Classical.choose_spec h).1
      (Classical.choose_spec h).2).1
  have hw0le : ∀ᵐ z ∂(volume : Measure E3), Classical.choose h z ≤ 1 :=
    (Submission.BoseGases.scattering_bounds_ae hR0 hv hvrad hv_supp (Classical.choose_spec h).1
      (Classical.choose_spec h).2).2
  have hgnn : ∀ᵐ z ∂(volume : Measure E3), 0 ≤ Submission.BoseGases.g0 v h z :=
    Submission.BoseGases.g0_nonneg_ae hR0 hv hvrad hv_supp h
  have hae_absC : ∀ᵐ p ∂((volume : Measure E3).prod volume),
      |Classical.choose h (p.1 - p.2)| ≤ 1 := by
    filter_upwards [hqmp.ae hw0nn, hqmp.ae hw0le] with p h1 h2
    rw [abs_of_nonneg h1]; exact h2
  -- ### Step 5: integrability of the two pair integrands
  have hIntGf : Integrable (fun p : E3 × E3 => Classical.choose h (p.1 - p.2)
      * Submission.BoseGases.g0 v h (p.1 - p.2)
      * Submission.BoseGases.chiSmallB M ℓ d u p.1
      * Submission.BoseGases.chiSmallB M ℓ d u p.2) ((volume : Measure E3).prod volume) := by
    refine Integrable.mono' hDom haesmGf ?_
    filter_upwards [hae_absC, hqmp.ae hgnn] with p hC _
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_mul,
      abs_of_nonneg (hXnonneg p.1), abs_of_nonneg (hXnonneg p.2)]
    calc |Classical.choose h (p.1 - p.2)| * |Submission.BoseGases.g0 v h (p.1 - p.2)|
            * Submission.BoseGases.chiSmallB M ℓ d u p.1
            * Submission.BoseGases.chiSmallB M ℓ d u p.2
        ≤ 1 * |Submission.BoseGases.g0 v h (p.1 - p.2)|
            * Submission.BoseGases.chiSmallB M ℓ d u p.1
            * Submission.BoseGases.chiSmallB M ℓ d u p.2 :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hC (abs_nonneg _)) (hXnonneg p.1)) (hXnonneg p.2)
      _ = Submission.BoseGases.chiSmallB M ℓ d u p.1
            * |Submission.BoseGases.g0 v h (p.1 - p.2)|
            * Submission.BoseGases.chiSmallB M ℓ d u p.2 := by ring
  have hIntHf : Integrable (fun p : E3 × E3 => Classical.choose h (p.1 - p.2)
      * Submission.BoseGases.wSmall1Pair h M ℓ d u p.1 p.2) ((volume : Measure E3).prod volume) := by
    refine Integrable.mono' hIntW1.norm (hCaesm'.mul hIntW1.aestronglyMeasurable) ?_
    filter_upwards [hae_absC] with p hC
    rw [Real.norm_eq_abs, abs_mul, Real.norm_eq_abs]
    exact mul_le_of_le_one_left (abs_nonneg _) hC
  -- ### Step 6: the a.e. pointwise comparison `g₀χχ ≤ w₁`
  have hae_cmp : ∀ᵐ p ∂((volume : Measure E3).prod volume),
      Submission.BoseGases.g0 v h (p.1 - p.2) * Submission.BoseGases.chiSmallB M ℓ d u p.1
          * Submission.BoseGases.chiSmallB M ℓ d u p.2
        ≤ Submission.BoseGases.wSmall1Pair h M ℓ d u p.1 p.2 :=
    (hqmp.ae hgnn).mono fun p hp =>
      g0_mul_chi_le_wSmall1Pair hv_supp hR0 h hM hℓ hd hR hRχ u p.1 p.2 hp
  have haeB : ∀ᵐ p ∂((volume : Measure E3).prod volume),
      Classical.choose h (p.1 - p.2) * Submission.BoseGases.g0 v h (p.1 - p.2)
          * Submission.BoseGases.chiSmallB M ℓ d u p.1
          * Submission.BoseGases.chiSmallB M ℓ d u p.2
        ≤ Classical.choose h (p.1 - p.2)
          * Submission.BoseGases.wSmall1Pair h M ℓ d u p.1 p.2 := by
    filter_upwards [hqmp.ae hw0nn, hae_cmp] with p hw0 hcmp
    have h1 : Classical.choose h (p.1 - p.2)
        * (Submission.BoseGases.g0 v h (p.1 - p.2) * Submission.BoseGases.chiSmallB M ℓ d u p.1
            * Submission.BoseGases.chiSmallB M ℓ d u p.2)
        ≤ Classical.choose h (p.1 - p.2)
          * Submission.BoseGases.wSmall1Pair h M ℓ d u p.1 p.2 :=
      mul_le_mul_of_nonneg_left hcmp hw0
    calc Classical.choose h (p.1 - p.2) * Submission.BoseGases.g0 v h (p.1 - p.2)
          * Submission.BoseGases.chiSmallB M ℓ d u p.1
          * Submission.BoseGases.chiSmallB M ℓ d u p.2
        = Classical.choose h (p.1 - p.2)
          * (Submission.BoseGases.g0 v h (p.1 - p.2) * Submission.BoseGases.chiSmallB M ℓ d u p.1
            * Submission.BoseGases.chiSmallB M ℓ d u p.2) := by ring
      _ ≤ _ := h1
  -- ### Step 7: the shear identity
  have hint : Integrable (fun q : E3 × E3 =>
      (Submission.BoseGases.g0 v h q.1 * Classical.choose h q.1)
        * (Submission.BoseGases.chiSmallB M ℓ d u (q.1 + q.2)
            * Submission.BoseGases.chiSmallB M ℓ d u q.2)) ((volume : Measure E3).prod volume) := by
    have hmp : MeasurePreserving (fun z : E3 × E3 => (z.1 + z.2, z.2))
        ((volume : Measure E3).prod volume) ((volume : Measure E3).prod volume) :=
      MeasureTheory.measurePreserving_add_prod _ _
    have hcomp : Integrable ((fun p : E3 × E3 => Classical.choose h (p.1 - p.2)
        * Submission.BoseGases.g0 v h (p.1 - p.2)
        * Submission.BoseGases.chiSmallB M ℓ d u p.1
        * Submission.BoseGases.chiSmallB M ℓ d u p.2) ∘ (fun z : E3 × E3 => (z.1 + z.2, z.2)))
        ((volume : Measure E3).prod volume) :=
      (hmp.integrable_comp haesmGf).mpr hIntGf
    refine hcomp.congr (Eventually.of_forall fun q => ?_)
    simp only [Function.comp_apply]
    show Classical.choose h (q.1 + q.2 - q.2) * Submission.BoseGases.g0 v h (q.1 + q.2 - q.2)
        * Submission.BoseGases.chiSmallB M ℓ d u (q.1 + q.2)
        * Submission.BoseGases.chiSmallB M ℓ d u q.2
      = (Submission.BoseGases.g0 v h q.1 * Classical.choose h q.1)
        * (Submission.BoseGases.chiSmallB M ℓ d u (q.1 + q.2)
            * Submission.BoseGases.chiSmallB M ℓ d u q.2)
    rw [add_sub_cancel_right]
    ring
  have hShear : (∫ p : E3 × E3, Classical.choose h (p.1 - p.2)
        * Submission.BoseGases.g0 v h (p.1 - p.2)
        * Submission.BoseGases.chiSmallB M ℓ d u p.1
        * Submission.BoseGases.chiSmallB M ℓ d u p.2 ∂((volume : Measure E3).prod volume))
      = ∫ z, (Submission.BoseGases.g0 v h z * Classical.choose h z)
          * (∫ y, Submission.BoseGases.chiSmallB M ℓ d u (z + y)
              * Submission.BoseGases.chiSmallB M ℓ d u y ∂(volume : Measure E3))
          ∂(volume : Measure E3) := by
    rw [show (∫ p : E3 × E3, Classical.choose h (p.1 - p.2)
          * Submission.BoseGases.g0 v h (p.1 - p.2)
          * Submission.BoseGases.chiSmallB M ℓ d u p.1
          * Submission.BoseGases.chiSmallB M ℓ d u p.2 ∂((volume : Measure E3).prod volume))
        = ∫ p : E3 × E3, (Submission.BoseGases.g0 v h (p.1 - p.2)
            * Classical.choose h (p.1 - p.2))
            * (Submission.BoseGases.chiSmallB M ℓ d u p.1
                * Submission.BoseGases.chiSmallB M ℓ d u p.2)
          ∂((volume : Measure E3).prod volume) from
      integral_congr_ae (Eventually.of_forall fun p => by ring)]
    exact shear_integral_identity (fun z => Submission.BoseGases.g0 v h z * Classical.choose h z)
      (fun x => Submission.BoseGases.chiSmallB M ℓ d u x) hint
  -- ### Step 8: the pointwise comparison at the level of `z`
  have hFbdd : ∀ z : E3, |∫ y, Submission.BoseGases.chiSmallB M ℓ d u (z + y)
        * Submission.BoseGases.chiSmallB M ℓ d u y ∂(volume : Measure E3)|
      ≤ (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M)
        * ∫ x, Submission.BoseGases.chiSmallB M ℓ d u x ∂(volume : Measure E3) := by
    intro z
    have hXleK : ∀ w : E3, Submission.BoseGases.chiSmallB M ℓ d u w
        ≤ Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M := by
      intro w
      have h := hXbdd w
      rwa [abs_of_nonneg (hXnonneg w)] at h
    have hfib : Integrable (fun y : E3 => Submission.BoseGases.chiSmallB M ℓ d u (z + y)
        * Submission.BoseGases.chiSmallB M ℓ d u y) (volume : Measure E3) := by
      refine Integrable.mono' (hIntX.const_mul
        (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M)) ?_ ?_
      · exact (((hXcont.comp (continuous_const.add continuous_id)).measurable).mul
          hXcont.measurable).aestronglyMeasurable
      · filter_upwards with y
        rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hXnonneg (z + y)), abs_of_nonneg (hXnonneg y)]
        exact mul_le_mul_of_nonneg_right (hXleK (z + y)) (hXnonneg y)
    calc |∫ y, Submission.BoseGases.chiSmallB M ℓ d u (z + y)
            * Submission.BoseGases.chiSmallB M ℓ d u y ∂(volume : Measure E3)|
        ≤ ∫ y, |Submission.BoseGases.chiSmallB M ℓ d u (z + y)
            * Submission.BoseGases.chiSmallB M ℓ d u y| ∂(volume : Measure E3) :=
          MeasureTheory.abs_integral_le_integral_abs
      _ = ∫ y, Submission.BoseGases.chiSmallB M ℓ d u (z + y)
            * Submission.BoseGases.chiSmallB M ℓ d u y ∂(volume : Measure E3) := by
          refine integral_congr_ae (Eventually.of_forall fun y => ?_)
          show |Submission.BoseGases.chiSmallB M ℓ d u (z + y)
              * Submission.BoseGases.chiSmallB M ℓ d u y|
            = Submission.BoseGases.chiSmallB M ℓ d u (z + y)
              * Submission.BoseGases.chiSmallB M ℓ d u y
          rw [abs_of_nonneg (mul_nonneg (hXnonneg (z + y)) (hXnonneg y))]
      _ ≤ ∫ y, (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M)
            * Submission.BoseGases.chiSmallB M ℓ d u y ∂(volume : Measure E3) := by
          refine MeasureTheory.integral_mono hfib (hIntX.const_mul _) ?_
          intro y
          exact mul_le_mul_of_nonneg_right (hXleK (z + y)) (hXnonneg y)
      _ = (Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M)
            * ∫ x, Submission.BoseGases.chiSmallB M ℓ d u x ∂(volume : Measure E3) :=
          MeasureTheory.integral_const_mul _ _
  have haeD : ∀ᵐ z ∂(volume : Measure E3),
      (Submission.BoseGases.g0 v h z * Classical.choose h z)
          * ((1 - θ) * Work.SmallBoxSliding.chiMass M ℓ d u)
        ≤ (Submission.BoseGases.g0 v h z * Classical.choose h z)
          * (∫ y, Submission.BoseGases.chiSmallB M ℓ d u (z + y)
              * Submission.BoseGases.chiSmallB M ℓ d u y ∂(volume : Measure E3)) := by
    filter_upwards [hgnn, hw0nn] with z hgz hwz
    by_cases hzR : ‖z‖ ≤ R
    · have hcr : (1 - θ) * Work.SmallBoxSliding.chiMass M ℓ d u
          ≤ ∫ y, Submission.BoseGases.chiSmallB M ℓ d u (z + y)
              * Submission.BoseGases.chiSmallB M ℓ d u y ∂(volume : Measure E3) := by
        rw [conv_shift_eq]
        exact hshift z hzR
      exact mul_le_mul_of_nonneg_left hcr (mul_nonneg hgz hwz)
    · have hg0 : Submission.BoseGases.g0 v h z = 0 :=
        Submission.BoseGases.g0_zero_of_norm_ge hv_supp (le_of_not_ge hzR) h
      simp [hg0]
  -- ### Step 9: integrability of the `z`-integrands
  have hInthf : Integrable (fun z : E3 =>
      Submission.BoseGases.g0 v h z * Classical.choose h z) (volume : Measure E3) := by
    refine Integrable.mono' (Submission.BoseGases.g0_integrable hR0 hv_supp h)
      (hgaesm.mul hCaesm) ?_
    filter_upwards [hgnn, hw0nn, hw0le] with z hgz hw0n hw0l
    have hC : |Classical.choose h z| ≤ 1 := by rw [abs_of_nonneg hw0n]; exact hw0l
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hgz]
    calc Submission.BoseGases.g0 v h z * |Classical.choose h z|
        ≤ Submission.BoseGases.g0 v h z * 1 := mul_le_mul_of_nonneg_left hC hgz
      _ = Submission.BoseGases.g0 v h z := mul_one _
  have hIntA : Integrable (fun z : E3 =>
      (Submission.BoseGases.g0 v h z * Classical.choose h z)
        * ((1 - θ) * Work.SmallBoxSliding.chiMass M ℓ d u)) (volume : Measure E3) :=
    (hInthf.const_mul ((1 - θ) * Work.SmallBoxSliding.chiMass M ℓ d u)).congr
      (Eventually.of_forall fun z => by ring)
  have hInthfF : Integrable (fun z : E3 =>
      (Submission.BoseGases.g0 v h z * Classical.choose h z)
        * (∫ y, Submission.BoseGases.chiSmallB M ℓ d u (z + y)
            * Submission.BoseGases.chiSmallB M ℓ d u y ∂(volume : Measure E3)))
      (volume : Measure E3) := by
    have hFsm : StronglyMeasurable (fun z : E3 =>
        ∫ y, Submission.BoseGases.chiSmallB M ℓ d u (z + y)
          * Submission.BoseGases.chiSmallB M ℓ d u y ∂(volume : Measure E3)) :=
      StronglyMeasurable.integral_prod_right' (f := fun q : E3 × E3 =>
        Submission.BoseGases.chiSmallB M ℓ d u (q.1 + q.2)
          * Submission.BoseGases.chiSmallB M ℓ d u q.2)
        (((hXcont.comp (continuous_fst.add continuous_snd)).mul
          (hXcont.comp continuous_snd)).stronglyMeasurable)
    refine Integrable.mono' (hInthf.norm.const_mul
      ((Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M)
        * ∫ x, Submission.BoseGases.chiSmallB M ℓ d u x ∂(volume : Measure E3))) ?_ ?_
    · exact hInthf.aestronglyMeasurable.mul hFsm.aestronglyMeasurable
    · filter_upwards with z
      rw [Real.norm_eq_abs, abs_mul, Real.norm_eq_abs]
      calc |Submission.BoseGases.g0 v h z * Classical.choose h z|
              * |∫ y, Submission.BoseGases.chiSmallB M ℓ d u (z + y)
                  * Submission.BoseGases.chiSmallB M ℓ d u y ∂(volume : Measure E3)|
          ≤ |Submission.BoseGases.g0 v h z * Classical.choose h z|
              * ((Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M)
                  * ∫ x, Submission.BoseGases.chiSmallB M ℓ d u x ∂(volume : Measure E3)) :=
            mul_le_mul_of_nonneg_left (hFbdd z) (abs_nonneg _)
        _ = ((Submission.BoseGases.chiSupAbs * Submission.BoseGases.chiSmallDecay M)
                * ∫ x, Submission.BoseGases.chiSmallB M ℓ d u x ∂(volume : Measure E3))
              * |Submission.BoseGases.g0 v h z * Classical.choose h z| := by ring
  -- ### Step 10: the two monotonicity steps
  have hstepB : (∫ p : E3 × E3, Classical.choose h (p.1 - p.2)
        * Submission.BoseGases.g0 v h (p.1 - p.2)
        * Submission.BoseGases.chiSmallB M ℓ d u p.1
        * Submission.BoseGases.chiSmallB M ℓ d u p.2 ∂((volume : Measure E3).prod volume))
      ≤ ∫ p : E3 × E3, Classical.choose h (p.1 - p.2)
        * Submission.BoseGases.wSmall1Pair h M ℓ d u p.1 p.2
        ∂((volume : Measure E3).prod volume) :=
    MeasureTheory.integral_mono_ae hIntGf hIntHf haeB
  have hstepD : (∫ z : E3, (Submission.BoseGases.g0 v h z * Classical.choose h z)
        * ((1 - θ) * Work.SmallBoxSliding.chiMass M ℓ d u) ∂(volume : Measure E3))
      ≤ ∫ z : E3, (Submission.BoseGases.g0 v h z * Classical.choose h z)
        * (∫ y, Submission.BoseGases.chiSmallB M ℓ d u (z + y)
            * Submission.BoseGases.chiSmallB M ℓ d u y ∂(volume : Measure E3))
        ∂(volume : Measure E3) :=
    MeasureTheory.integral_mono_ae hIntA hInthfF haeD
  -- ### Step 11: convert the set integral to the full-space integral
  have hvanH : ∀ p : E3 × E3,
      p ∉ Submission.BoseGases.dlBox ℓ d u ×ˢ Submission.BoseGases.dlBox ℓ d u →
      Classical.choose h (p.1 - p.2)
        * Submission.BoseGases.wSmall1Pair h M ℓ d u p.1 p.2 = 0 := by
    intro p hp
    rw [hvanW1 p hp, mul_zero]
  have hset := MeasureTheory.setIntegral_eq_integral_of_forall_compl_eq_zero
    (s := Submission.BoseGases.dlBox ℓ d u ×ˢ Submission.BoseGases.dlBox ℓ d u)
    (f := fun p : E3 × E3 => Classical.choose h (p.1 - p.2)
      * Submission.BoseGases.wSmall1Pair h M ℓ d u p.1 p.2)
    (μ := (volume : Measure (E3 × E3))) hvanH
  -- ### Step 12: assemble
  rw [hset]
  have hGdef : (∫ z : E3, Submission.BoseGases.g0 v h z * Classical.choose h z
      ∂(volume : Measure E3)) = Submission.BoseGases.g0w0Mass (v := v) h := rfl
  calc (1 - θ) * (Submission.BoseGases.g0w0Mass (v := v) h)
        * Work.SmallBoxSliding.chiMass M ℓ d u
      = (1 - θ) * Work.SmallBoxSliding.chiMass M ℓ d u
        * (∫ z : E3, Submission.BoseGases.g0 v h z * Classical.choose h z
            ∂(volume : Measure E3)) := by
        rw [hGdef]; ring
    _ = ∫ z : E3, (Submission.BoseGases.g0 v h z * Classical.choose h z)
          * ((1 - θ) * Work.SmallBoxSliding.chiMass M ℓ d u) ∂(volume : Measure E3) := by
        rw [MeasureTheory.integral_mul_const]; ring
    _ ≤ ∫ z : E3, (Submission.BoseGases.g0 v h z * Classical.choose h z)
          * (∫ y, Submission.BoseGases.chiSmallB M ℓ d u (z + y)
              * Submission.BoseGases.chiSmallB M ℓ d u y ∂(volume : Measure E3))
          ∂(volume : Measure E3) := hstepD
    _ = ∫ p : E3 × E3, Classical.choose h (p.1 - p.2)
          * Submission.BoseGases.g0 v h (p.1 - p.2)
          * Submission.BoseGases.chiSmallB M ℓ d u p.1
          * Submission.BoseGases.chiSmallB M ℓ d u p.2
          ∂((volume : Measure E3).prod volume) := hShear.symm
    _ ≤ ∫ p : E3 × E3, Classical.choose h (p.1 - p.2)
          * Submission.BoseGases.wSmall1Pair h M ℓ d u p.1 p.2
          ∂((volume : Measure E3).prod volume) := hstepB

end Work.BoseFixB1S
