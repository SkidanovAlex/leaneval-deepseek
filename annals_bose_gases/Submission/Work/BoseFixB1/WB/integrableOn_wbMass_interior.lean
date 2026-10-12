import ChallengeDeps
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.BoseFixB1.WB.Lead
import Submission.Work.BoseFixB1.WB.aestronglyMeasurable_wSmall1Pair_triple
import Submission.Work.BoseFixB1.WB.integral_abs_wSmall1Pair_u_le
import Submission.Work.BoseFixB2.Pot.lintegral_wPairC_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixB1.WB.integrableOn_wbMass_interior`

The localised one-body mass `wbMass v h μ u = ∬ w_{1,B(u)}` is integrable on the
interior set `I₋` — with **no diluteness hypothesis** (`R0 ≤ ℓd/16`, `R0 ≤ ℓ·chiR0`
are *not* assumed): the estimate is the exact cancellation, in the *joint*
`(u,x,y)`-integral, of the two sliding cutoffs `χ_{B(u)}` against the `(ℓd)`-scale
renormalisation denominator `(χ_M⋆χ_M)(·/(ℓd))`, together with the `ℓ`-scale
cancellation of the corpus kernel `wPairC` (`Work.BoseFixB2.Pot.lintegral_wPairC_le`).

Route (all on the triple kernel `K p = w_{1,B(u)}(x,y)`, `p = (u,(x,y))`):

* `aestronglyMeasurable_wSmall1Pair_triple`: `K` is a.e. strongly measurable;
* Tonelli (`lintegral_prod`, `lintegral_lintegral_swap`) moves the `u`-integral
  innermost; at each `(x,y)` the `u`-slice is integrable
  (`Work.SmallBoxSliding.integrable_wSmallPair_u`), so the `u`-integral becomes a
  real Bochner integral;
* `integral_abs_wSmall1Pair_u_le` is the exact collapse
  `∫_u |w_{1,B(u)}(x,y)| ≤ χ(x/ℓ)χ(y/ℓ)|g₀(x−y)|/(χ⋆χ)((x−y)/ℓ)`;
* `Work.BoseFixB2.Pot.lintegral_wPairC_le` bounds the resulting `(x,y)`-integral by
  `ℓ³∫|g₀|` (the exact `ℓ`-scale cancellation).

Consequently `K` is (jointly) integrable, its `u`-marginal `u ↦ ∫_q K (u,q)` is
integrable by Fubini, `wbMass` is dominated by that marginal (norm of the integral
≤ integral of the norm) and `IntegrableOn` follows by restriction.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseFixB1.WB

open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseBox Work.UBB
open Work.SmallBoxSliding

set_option autoImplicit false
set_option linter.unusedVariables false

theorem integrableOn_wbMass_interior {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v} {R0 : ℝ}
    (hv : 0 ≤ v) (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : EuclideanSpace ℝ (Fin 3)) R0) (hR0 : 0 < R0)
    {μ : ℝ} (hμ : 0 < μ) (hav : 0 < _root_.BoseGases.a v)
    (hM : 1 ≤ (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M)
    (hℓ : 0 < Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
    (hd : 0 < (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d) :
    MeasureTheory.IntegrableOn (fun u : EuclideanSpace ℝ (Fin 3) => Work.BoseFixB1.wbMass v h μ u)
      (Work.SmallBoxSliding.interiorSet (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ) := by
  set M : ℕ := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M with hMdef
  set L : ℝ := Work.BoseBox.sideAt μ (_root_.BoseGases.a v) with hLdef
  set dd : ℝ := (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d with hddef
  have hM1 : 1 ≤ M := hM
  have hL0 : 0 < L := hℓ
  have hd0 : 0 < dd := hd
  -- ### the triple kernel
  set K : ℝ³ × (ℝ³ × ℝ³) → ℝ :=
    fun p => Submission.BoseGases.wSmall1Pair h M L dd p.1 p.2.1 p.2.2 with hKdef
  have hmeasK : AEStronglyMeasurable K
      ((volume : Measure ℝ³).prod ((volume : Measure ℝ³).prod (volume : Measure ℝ³))) :=
    aestronglyMeasurable_wSmall1Pair_triple (v := v) (h := h) (R0 := R0) (M := M) (ℓ := L)
      (d := dd) hv_supp hR0 hM1 hL0 hd0
  have hOfReal : AEMeasurable (fun p : ℝ³ × (ℝ³ × ℝ³) => ENNReal.ofReal ‖K p‖)
      ((volume : Measure ℝ³).prod ((volume : Measure ℝ³).prod (volume : Measure ℝ³))) := by
    have h := hmeasK.aemeasurable.enorm
    simpa only [Real.enorm_eq_ofReal_abs, Real.norm_eq_abs] using h
  -- ### the `u`-slices are integrable
  have hslice : ∀ q : ℝ³ × ℝ³, Integrable (fun u : ℝ³ => ‖K (u, q)‖) (volume : Measure ℝ³) := by
    intro q
    have h1 : Integrable (fun u : ℝ³ =>
        Submission.BoseGases.wSmallPair M L dd u (Submission.BoseGases.g0 v h) q.1 q.2)
        (volume : Measure ℝ³) :=
      Work.SmallBoxSliding.integrable_wSmallPair_u (M := M) hM1 (ℓ := L) (d := dd) hL0 hd0
        (Submission.BoseGases.g0 v h) q.1 q.2
    refine h1.abs.congr (Filter.Eventually.of_forall (fun u => ?_))
    simp only [hKdef, Submission.BoseGases.wSmall1Pair, Real.norm_eq_abs]
  -- ### the joint `L¹` bound
  have hL1 : (∫⁻ p : ℝ³ × (ℝ³ × ℝ³), ENNReal.ofReal ‖K p‖
        ∂((volume : Measure ℝ³).prod ((volume : Measure ℝ³).prod (volume : Measure ℝ³))))
      ≤ ENNReal.ofReal (L ^ 3 * ∫ z : ℝ³, |Submission.BoseGases.g0 v h z|) := by
    have hs1 := MeasureTheory.lintegral_prod (μ := (volume : Measure ℝ³))
      (ν := (volume : Measure ℝ³).prod (volume : Measure ℝ³))
      (f := fun p : ℝ³ × (ℝ³ × ℝ³) => ENNReal.ofReal ‖K p‖) hOfReal
    have hs2 := MeasureTheory.lintegral_lintegral_swap (μ := (volume : Measure ℝ³))
      (ν := (volume : Measure ℝ³).prod (volume : Measure ℝ³))
      (f := fun (u : ℝ³) (q : ℝ³ × ℝ³) => ENNReal.ofReal ‖K (u, q)‖) hOfReal
    have hs3 : (∫⁻ q : ℝ³ × ℝ³, ∫⁻ u : ℝ³, ENNReal.ofReal ‖K (u, q)‖ ∂(volume : Measure ℝ³)
          ∂((volume : Measure ℝ³).prod (volume : Measure ℝ³)))
        = ∫⁻ q : ℝ³ × ℝ³, ENNReal.ofReal (∫ u : ℝ³, ‖K (u, q)‖)
            ∂((volume : Measure ℝ³).prod (volume : Measure ℝ³)) := by
      refine lintegral_congr (fun q => ?_)
      exact (MeasureTheory.ofReal_integral_eq_lintegral_ofReal (hslice q)
        (Filter.Eventually.of_forall (fun u => norm_nonneg _))).symm
    have hs4 : (∫⁻ q : ℝ³ × ℝ³, ENNReal.ofReal (∫ u : ℝ³, ‖K (u, q)‖)
          ∂((volume : Measure ℝ³).prod (volume : Measure ℝ³)))
        ≤ ∫⁻ q : ℝ³ × ℝ³, ‖Submission.BoseGases.wPairC L (Submission.BoseGases.g0 v h) q.1 q.2‖ₑ
            ∂((volume : Measure ℝ³).prod (volume : Measure ℝ³)) := by
      refine lintegral_mono (fun q => ?_)
      have hB := Work.BoseFixB1.WB.integral_abs_wSmall1Pair_u_le (v := v) (h := h) (M := M)
        (ℓ := L) (d := dd) hM1 hL0 hd0 q.1 q.2
      have hreal : (∫ u : ℝ³, ‖K (u, q)‖)
          ≤ Submission.BoseGases.chiScale L q.1 * Submission.BoseGases.chiScale L q.2 *
              (|Submission.BoseGases.g0 v h (q.1 - q.2)|
                * (Submission.BoseGases.convScale L (q.1 - q.2))⁻¹) := by
        refine le_trans (le_of_eq ?_) hB
        simp only [hKdef, Real.norm_eq_abs]
      have hEq : ‖Submission.BoseGases.wPairC L (Submission.BoseGases.g0 v h) q.1 q.2‖ₑ
          = ENNReal.ofReal (Submission.BoseGases.chiScale L q.1
              * Submission.BoseGases.chiScale L q.2
              * (|Submission.BoseGases.g0 v h (q.1 - q.2)|
                * (Submission.BoseGases.convScale L (q.1 - q.2))⁻¹)) := by
        rw [Real.enorm_eq_ofReal_abs]
        congr 1
        rw [Submission.BoseGases.wPairC, Submission.BoseGases.wPair, Submission.BoseGases.wScaled]
        rw [abs_mul, abs_mul, abs_of_nonneg (Submission.BoseGases.chiScale_nonneg L q.1),
          abs_of_nonneg (Submission.BoseGases.chiScale_nonneg L q.2), abs_div,
          abs_of_nonneg (Submission.BoseGases.convScale_nonneg L (q.1 - q.2)), div_eq_mul_inv]
        ring
      rw [hEq]
      exact ENNReal.ofReal_le_ofReal hreal
    have hs5 : (∫⁻ q : ℝ³ × ℝ³, ‖Submission.BoseGases.wPairC L (Submission.BoseGases.g0 v h) q.1 q.2‖ₑ
          ∂((volume : Measure ℝ³).prod (volume : Measure ℝ³)))
        ≤ ENNReal.ofReal (L ^ 3 * ∫ z : ℝ³, |Submission.BoseGases.g0 v h z|) :=
      Work.BoseFixB2.Pot.lintegral_wPairC_le (h := Submission.BoseGases.g0 v h) (ℓ := L) hL0
        (Submission.BoseGases.g0_integrable hR0 hv_supp h)
    have hE : (∫⁻ p : ℝ³ × (ℝ³ × ℝ³), ENNReal.ofReal ‖K p‖
          ∂((volume : Measure ℝ³).prod ((volume : Measure ℝ³).prod (volume : Measure ℝ³))))
        = ∫⁻ q : ℝ³ × ℝ³, ENNReal.ofReal (∫ u : ℝ³, ‖K (u, q)‖)
            ∂((volume : Measure ℝ³).prod (volume : Measure ℝ³)) :=
      hs1.trans (hs2.trans hs3)
    exact hE.trans_le (hs4.trans hs5)
  -- ### joint integrability of the kernel
  have hIntK : Integrable K
      ((volume : Measure ℝ³).prod ((volume : Measure ℝ³).prod (volume : Measure ℝ³))) :=
    ⟨hmeasK, (MeasureTheory.hasFiniteIntegral_iff_norm K).mpr
      (lt_of_le_of_lt hL1 ENNReal.ofReal_lt_top)⟩
  -- ### Fubini: the `u`-marginal of the norm
  have hIntN : Integrable (fun u : ℝ³ => ∫ q : ℝ³ × ℝ³, ‖K (u, q)‖
      ∂((volume : Measure ℝ³).prod (volume : Measure ℝ³))) (volume : Measure ℝ³) :=
    MeasureTheory.Integrable.integral_norm_prod_left hIntK
  -- ### `wbMass` is a.e. the `q`-integral of the kernel
  have hae : ∀ᵐ u ∂(volume : Measure ℝ³),
      Work.BoseFixB1.wbMass v h μ u
        = ∫ q : ℝ³ × ℝ³, K (u, q) ∂((volume : Measure ℝ³).prod (volume : Measure ℝ³)) := by
    filter_upwards [MeasureTheory.Integrable.prod_right_ae hIntK] with u hu
    rw [MeasureTheory.integral_prod (fun q : ℝ³ × ℝ³ => K (u, q)) hu]
    simp only [Work.BoseFixB1.wbMass, Work.BoseFixB1.w1MassB, hKdef,
      Submission.BoseGases.wSmall1Pair, ← hMdef, ← hLdef, ← hddef]
  -- ### domination
  have hbound : ∀ᵐ u ∂(volume : Measure ℝ³),
      ‖Work.BoseFixB1.wbMass v h μ u‖ ≤ (fun u : ℝ³ => ∫ q : ℝ³ × ℝ³, ‖K (u, q)‖
        ∂((volume : Measure ℝ³).prod (volume : Measure ℝ³))) u := by
    filter_upwards [hae] with u hu
    rw [hu]
    exact MeasureTheory.norm_integral_le_integral_norm _
  have hIntQ : Integrable (fun u : ℝ³ => ∫ q : ℝ³ × ℝ³, K (u, q)
      ∂((volume : Measure ℝ³).prod (volume : Measure ℝ³))) (volume : Measure ℝ³) :=
    MeasureTheory.Integrable.integral_prod_left hIntK
  have hmeas_f : AEStronglyMeasurable (fun u : ℝ³ => Work.BoseFixB1.wbMass v h μ u)
      (volume : Measure ℝ³) :=
    hIntQ.aestronglyMeasurable.congr (hae.mono fun u hu => hu.symm)
  have hIntf : Integrable (fun u : ℝ³ => Work.BoseFixB1.wbMass v h μ u) (volume : Measure ℝ³) :=
    MeasureTheory.Integrable.mono' hIntN hmeas_f hbound
  exact hIntf.integrableOn

end Work.BoseFixB1.WB
