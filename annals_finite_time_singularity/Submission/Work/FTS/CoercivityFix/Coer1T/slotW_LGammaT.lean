import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.MeasureTheory.Function.L2Space
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.Vocab
import Submission.Work.Coercivity.Defs
import Submission.Work.Coercivity.Basic
import Submission.Work.Coercivity.L12_z_byparts
import Submission.Work.Coercivity.L2CoercivityTransport
import Submission.Work.Coercivity.L2TransportSharp
import Submission.Work.Coercivity.GamDivCSqInt_le_five
import Submission.Work.Coercivity.projCorr_sepIntegral_le_five
import Submission.Work.Coercivity.EL12z_le
import Submission.Work.Coercivity.wip_G_bound
import Submission.Work.Coercivity.integrableOn_GammaK_sq
import Submission.Work.Coercivity.L12f_continuousOn
import Submission.Work.Coercivity.wip_eq_integral_prod
import Submission.Work.FTS.CoercivityFix.Coer1.zIBP
import Submission.Work.FTS.CoercivityFix.Coer1.IntFacts
import Submission.Work.FTS.CoercivityFix.Coer1.Estimates
import Submission.Work.FTS.GalerkinFix.RegQ.regQ_mono

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.Coer1T

set_option autoImplicit false
set_option maxHeartbeats 1600000

/-! ## Integrability of the `L₁₂`-pairings in the interior class

The analytic chapter (`Work.Coercivity`) takes the joint integrability of the pairings of
`L₁₂(f)` against `f` as *hypotheses* (the fields `intK`, `intG` of `CoerciveData`).  Here we
prove them from the interior class `RegQ α 2 f` together with `HardyHyp f`, by the
two-step Cauchy–Schwarz that is the paper's own argument: write

  `w(z)/z · L₁₂(f)(z) · (c(θ) f(z,θ)) = (L₁₂(f)(z)/z · c(θ)) · (f(z,θ) w(z))`,

a product of two `L²`-functions of the product variable — `L₁₂(f)/z` is `L²` on `Iz` by
`HardyHyp.intA`, `c` is `L²` on `Iθ` by hypothesis, and `f w` is `L²` by `hfw`. -/

/-- The product of the two restricted measures is the restriction to the quadrant. -/
theorem prod_restrict_eq :
    (volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)
      = volume.restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
  rw [Measure.prod_restrict, Measure.volume_eq_prod]

/-- **The general integrability lemma of the `L₁₂`-pairings.**  For `f` satisfying the Hardy
hypotheses, with `(f w)²` jointly integrable and `f` a.e. strongly measurable, and for any
`c` with `c² ∈ L¹(Iθ)`, the product `(w/z) L₁₂(f) (c·f)` is jointly integrable on the
quadrant. -/
theorem intMul_L12_Q {f : ℝ → ℝ → ℝ} (hHH : Work.Coercivity.HardyHyp f)
    (hfw : MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => (f z θ * Work.Spaces.w z) ^ 2))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ))
    (hfaesm : MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ => f p.1 p.2)
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)))
    (c : ℝ → ℝ) (hc : MeasureTheory.Integrable (fun θ => (c θ) ^ 2)
      (volume.restrict Work.Spaces.Iθ))
    (hcm : MeasureTheory.AEStronglyMeasurable c (volume.restrict Work.Spaces.Iθ)) :
    MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => Work.Spaces.w z / z * Work.Coercivity.L12f f z
        * (c θ * f z θ))) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
  rw [MeasureTheory.IntegrableOn, ← prod_restrict_eq]
  -- ## `(L₁₂(f)/z)²` is integrable on `Iz`
  have hA : MeasureTheory.Integrable
      (fun z : ℝ => (Work.Coercivity.L12f f z / z) ^ 2) (volume.restrict Work.Spaces.Iz) := by
    have h0 := hHH.intA 1 (by norm_num : (1 : ℕ) ≤ 2)
    rw [Work.FTS.CoercivityFix.Coer1.iz_ae_restrict]
    refine h0.congr (Filter.Eventually.of_forall fun z => ?_)
    dsimp only
    rw [div_pow, Nat.cast_one, mul_one, Real.rpow_two]
  have hC : MeasureTheory.Integrable (fun θ : ℝ => (c θ) ^ 2)
      (volume.restrict Work.Spaces.Iθ) := hc
  -- ## a.e. strong measurability of `L₁₂(f)/z`
  have hL12aesm : MeasureTheory.AEStronglyMeasurable
      (fun z : ℝ => Work.Coercivity.L12f f z / z) (volume.restrict Work.Spaces.Iz) := by
    rw [Work.FTS.CoercivityFix.Coer1.iz_ae_restrict]
    exact ((Work.Coercivity.L12f_continuousOn f hHH).div continuousOn_id
      (fun z hz => ne_of_gt hz)).aestronglyMeasurable measurableSet_Ioi
  -- ## the first `L²`-factor
  have h1 : MeasureTheory.MemLp
      (fun p : ℝ × ℝ => Work.Coercivity.L12f f p.1 / p.1 * c p.2) 2
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) := by
    refine (MeasureTheory.memLp_two_iff_integrable_sq ?_).2 ?_
    · exact (hL12aesm.comp_fst).mul (hcm.comp_snd)
    · refine (Integrable.mul_prod hA hC).congr (Filter.Eventually.of_forall fun p => ?_)
      rcases p with ⟨z, θ⟩
      ring
  -- ## the second `L²`-factor: `f w`
  have hwaesm : MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ => Work.Spaces.w p.1)
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) :=
    Work.Spaces.aesm_of_continuousOn_Qd _ Work.Coercivity.continuousOn_w_quad
  have hfwP : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => (f p.1 p.2 * Work.Spaces.w p.1) ^ 2)
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) := by
    rw [prod_restrict_eq]
    exact hfw.congr (Filter.Eventually.of_forall fun p => by
      rcases p with ⟨z, θ⟩
      rfl)
  have h2 : MeasureTheory.MemLp (fun p : ℝ × ℝ => f p.1 p.2 * Work.Spaces.w p.1) 2
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) :=
    (MeasureTheory.memLp_two_iff_integrable_sq (hfaesm.mul hwaesm)).2 hfwP
  -- ## Hölder
  refine (h1.integrable_mul h2).congr (Filter.Eventually.of_forall fun p => ?_)
  rcases p with ⟨z, θ⟩
  simp only [Pi.mul_apply, Function.uncurry_apply_pair]
  ring

/-! ## The concrete integrability certificates -/

/-- `f ∈ RegQ α 2` is a.e. strongly measurable on the quadrant. -/
theorem aesm_f_Q {α : ℝ} {f : ℝ → ℝ → ℝ} (hf : Work.FTS.Nonlin.RegQ α 2 f) :
    MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ => f p.1 p.2)
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) :=
  Work.Spaces.aesm_of_continuousOn_Qd _ (Work.FTS.CoercivityFix.Coer1.continuousOn_f_Q hf.1)

/-- `(f w)²` is jointly integrable for `f ∈ RegQ α 2`. -/
theorem hfw_of_regQ {α : ℝ} (hα : 0 < α) {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.Nonlin.RegQ α 2 f) :
    MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => (f z θ * Work.Spaces.w z) ^ 2))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
  have hp := Work.FTS.CoercivityFix.Coer1.IntPkg_Q α hα hf
  refine (hp.sqDzOne 0 (by norm_num)).congr_fun ?_ (measurableSet_Ici.prod measurableSet_Icc)
  rintro ⟨z, θ⟩ _
  simp only [Function.uncurry_apply_pair, Work.Spaces.DzIter_zero]
  ring

/-- The `f²w²` form of the previous certificate, as used by `wip_G_bound`. -/
theorem hfw2_of_regQ {α : ℝ} (hα : 0 < α) {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.Nonlin.RegQ α 2 f) :
    MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => f z θ * f z θ * Work.Spaces.w z ^ 2))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
  refine (hfw_of_regQ hα hf).congr_fun ?_ (measurableSet_Ici.prod measurableSet_Icc)
  rintro ⟨z, θ⟩ _
  simp only [Function.uncurry_apply_pair]
  ring

/-- The `K`-part of the `L₁₂`-pairing is jointly integrable (interior class). -/
theorem intK_Q (α : ℝ) (hα : 0 < α) {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.Nonlin.RegQ α 2 f) (hHH : Work.Coercivity.HardyHyp f) :
    MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => Work.Spaces.w z / z * Work.Coercivity.L12f f z
        * (Work.Spaces.K θ * f z θ))) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
  intMul_L12_Q hHH (hfw_of_regQ hα hf) (aesm_f_Q hf) Work.Spaces.K
    Work.Coercivity.integrableOn_Kθ_sq
    (Work.Coercivity.continuousOn_Kθ.aestronglyMeasurable measurableSet_Icc)

/-- The `(Γ/c - K)`-part of the `L₁₂`-pairing is jointly integrable (interior class). -/
theorem intG_Q (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.Nonlin.RegQ α 2 f) (hHH : Work.Coercivity.HardyHyp f) :
    MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => Work.Spaces.w z / z * Work.Coercivity.L12f f z
        * ((Work.Spaces.Gam α θ / Work.Spaces.c α - Work.Spaces.K θ) * f z θ)))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
  intMul_L12_Q hHH (hfw_of_regQ hα hf) (aesm_f_Q hf)
    (fun θ => Work.Spaces.Gam α θ / Work.Spaces.c α - Work.Spaces.K θ)
    (Work.Coercivity.integrableOn_GammaK_sq α hα hα1)
    (((Work.Coercivity.continuousOn_Gam α hα).div_const (Work.Spaces.c α)).sub
      Work.Coercivity.continuousOn_Kθ |>.aestronglyMeasurable measurableSet_Icc)

/-- The `L₁₂`-term of `𝓛_Γ` against `f w²` is jointly integrable (interior class). -/
theorem intT1_w2_Q (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.Nonlin.RegQ α 2 f) (hHH : Work.Coercivity.HardyHyp f) :
    MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ =>
        (2 * z * Work.Spaces.Gam α θ / (Work.Spaces.c α * (1 + z) ^ 2))
          * Work.Coercivity.L12f f z * f z θ * Work.Spaces.w z ^ 2))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
  have hGam2 : MeasureTheory.Integrable
      (fun θ : ℝ => (2 * Work.Spaces.Gam α θ / Work.Spaces.c α) ^ 2)
      (volume.restrict Work.Spaces.Iθ) := by
    refine MeasureTheory.Integrable.of_bound ?_ 400 ?_
    · exact ((((Work.Coercivity.continuousOn_Gam α hα).const_mul
        (2 : ℝ)).div_const (Work.Spaces.c α)).pow 2).aestronglyMeasurable measurableSet_Icc
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Icc] with θ hθ
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
      have h1 : |Work.Spaces.Gam α θ / Work.Spaces.c α| ≤ 10 :=
        Work.Coercivity.Gam_div_c_bound hα hα1 hθ
      have h2 : |2 * Work.Spaces.Gam α θ / Work.Spaces.c α| ≤ 20 := by
        rw [show 2 * Work.Spaces.Gam α θ / Work.Spaces.c α
            = 2 * (Work.Spaces.Gam α θ / Work.Spaces.c α) by ring,
          abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
        linarith
      nlinarith [abs_nonneg (2 * Work.Spaces.Gam α θ / Work.Spaces.c α),
        sq_abs (2 * Work.Spaces.Gam α θ / Work.Spaces.c α)]
  have hcm : MeasureTheory.AEStronglyMeasurable
      (fun θ : ℝ => 2 * Work.Spaces.Gam α θ / Work.Spaces.c α)
      (volume.restrict Work.Spaces.Iθ) :=
    (((Work.Coercivity.continuousOn_Gam α hα).const_mul (2 : ℝ)).div_const
      (Work.Spaces.c α)).aestronglyMeasurable measurableSet_Icc
  refine (intMul_L12_Q hHH (hfw_of_regQ hα hf) (aesm_f_Q hf)
    (fun θ => 2 * Work.Spaces.Gam α θ / Work.Spaces.c α) hGam2 hcm).congr_fun ?_
    (measurableSet_Ici.prod measurableSet_Icc)
  rintro ⟨z, θ⟩ _
  simp only [Function.uncurry_apply_pair, Work.Spaces.w]
  rcases eq_or_ne z 0 with rfl | hz
  · norm_num
  · field_simp

/-! ## The interior-class port of `L2Coercivity` -/

/-- **Proposition `L2Coercivity` in the interior class**: for `f ∈ RegQ α 2` satisfying the
Hardy hypotheses, the weighted `L²` coercivity of `𝓛_Γ`,
`(𝓛_Γ(f) w, f w)_{L²} ≥ 1/4 |f w|²_{L²}`.

This is the same proof as `Work.Coercivity.L2Coercivity`, with the analytic hypothesis
package `IBP`/`CoerciveData` replaced by the interior class `RegQ α 2` + `IntPkg`
(`wip_L_self_Q` instead of `wip_L_self`), and with `intK`/`intG`/`intT1` proved above. -/
theorem LGamma_coercive_Q (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.Nonlin.RegQ α 2 f) (hHH : Work.Coercivity.HardyHyp f)
    (hΓ : Work.Coercivity.GammaL2Bnd α) :
    (1 / 4) * Work.Coercivity.Ef f
      ≤ Work.Coercivity.wip (fun z _ => Work.Spaces.w z ^ 2)
          (Work.Coercivity.LGamma α f) f := by
  set P : Measure (ℝ × ℝ) := (volume.restrict Work.Spaces.Iz).prod
    (volume.restrict Work.Spaces.Iθ) with hP
  have hp := Work.FTS.CoercivityFix.Coer1.IntPkg_Q α hα hf
  have hc : Work.Spaces.c α ≠ 0 := Work.Coercivity.c_ne_zero hα hα1
  -- ## integrability of the two halves of `𝓛_Γ`
  have hintL : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ =>
      Work.Coercivity.L f z θ * f z θ * Work.Spaces.w z ^ 2))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := hp.intL_f_one
  have hF1 : MeasureTheory.Integrable (fun p : ℝ × ℝ =>
      Work.Coercivity.L f p.1 p.2 * f p.1 p.2 * Work.Spaces.w p.1 ^ 2) P :=
    Work.Coercivity.integrableOn_prod hintL
  have hF4 : MeasureTheory.Integrable (fun p : ℝ × ℝ =>
      (2 * p.1 * Work.Spaces.Gam α p.2 / (Work.Spaces.c α * (1 + p.1) ^ 2))
        * Work.Coercivity.L12f f p.1 * f p.1 p.2 * Work.Spaces.w p.1 ^ 2) P :=
    Work.Coercivity.integrableOn_prod (intT1_w2_Q α hα hα1 hf hHH)
  -- ## the two halves of the `L₁₂`-term
  have hintK : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ =>
      2 * Work.Spaces.K θ * f z θ * (Work.Spaces.w z / z * Work.Coercivity.L12f f z)))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
    have h := intK_Q α hα hf hHH
    rw [MeasureTheory.IntegrableOn] at h ⊢
    exact (h.const_mul 2).congr (Filter.Eventually.of_forall fun p => by
      rcases p with ⟨z, θ⟩
      simp only [Function.uncurry_apply_pair]
      ring)
  have hintG : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ =>
      2 * (Work.Spaces.Gam α θ / Work.Spaces.c α - Work.Spaces.K θ) * f z θ
        * Work.Spaces.w z * (Work.Coercivity.L12f f z / z)))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
    have h := intG_Q α hα hα1 hf hHH
    rw [MeasureTheory.IntegrableOn] at h ⊢
    exact (h.const_mul 2).congr (Filter.Eventually.of_forall fun p => by
      rcases p with ⟨z, θ⟩
      simp only [Function.uncurry_apply_pair]
      ring)
  have hF5 : MeasureTheory.Integrable (fun p : ℝ × ℝ =>
      2 * Work.Spaces.K p.2 * f p.1 p.2 * (Work.Spaces.w p.1 / p.1
        * Work.Coercivity.L12f f p.1)) P :=
    Work.Coercivity.integrableOn_prod hintK
  have hF6 : MeasureTheory.Integrable (fun p : ℝ × ℝ =>
      2 * (Work.Spaces.Gam α p.2 / Work.Spaces.c α - Work.Spaces.K p.2) * f p.1 p.2
        * Work.Spaces.w p.1 * (Work.Coercivity.L12f f p.1 / p.1)) P :=
    Work.Coercivity.integrableOn_prod hintG
  -- ## integrability of `𝓛_Γ f · f w²`
  have hintLG : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ =>
      Work.Coercivity.LGamma α f z θ * f z θ * Work.Spaces.w z ^ 2))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
    have h := hintL.sub (intT1_w2_Q α hα hα1 hf hHH)
    rw [MeasureTheory.IntegrableOn] at h ⊢
    refine h.congr (Filter.Eventually.of_forall fun p => ?_)
    rcases p with ⟨z, θ⟩
    simp only [Function.uncurry_apply_pair, Pi.sub_apply, Work.Coercivity.LGamma]
    ring
  -- ## the `wip`s as product-measure integrals
  have hwipLG : Work.Coercivity.wip (fun z _ => Work.Spaces.w z ^ 2)
      (Work.Coercivity.LGamma α f) f
      = ∫ p, Work.Coercivity.LGamma α f p.1 p.2 * f p.1 p.2 * Work.Spaces.w p.1 ^ 2 ∂P := by
    rw [hP]
    exact Work.Coercivity.wip_eq_integral_prod (fun z _ => Work.Spaces.w z ^ 2)
      (Work.Coercivity.LGamma α f) f hintLG
  have hwipL : Work.Coercivity.wip (fun z _ => Work.Spaces.w z ^ 2) (Work.Coercivity.L f) f
      = ∫ p, Work.Coercivity.L f p.1 p.2 * f p.1 p.2 * Work.Spaces.w p.1 ^ 2 ∂P := by
    rw [hP]
    exact Work.Coercivity.wip_eq_integral_prod (fun z _ => Work.Spaces.w z ^ 2)
      (Work.Coercivity.L f) f hintL
  -- ## `𝓛_Γ = 𝓛 - (2zΓ/(c(1+z)²))L₁₂(f)`
  have hsplit : (∫ p, Work.Coercivity.LGamma α f p.1 p.2 * f p.1 p.2
        * Work.Spaces.w p.1 ^ 2 ∂P)
      = (∫ p, Work.Coercivity.L f p.1 p.2 * f p.1 p.2 * Work.Spaces.w p.1 ^ 2 ∂P)
        - (∫ p, (2 * p.1 * Work.Spaces.Gam α p.2
            / (Work.Spaces.c α * (1 + p.1) ^ 2)) * Work.Coercivity.L12f f p.1
            * f p.1 p.2 * Work.Spaces.w p.1 ^ 2 ∂P) := by
    rw [← MeasureTheory.integral_sub hF1 hF4]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    simp only [Work.Coercivity.LGamma]
    ring
  -- ## the paper's identity `(LW)`: `(𝓛 f, f)_{w²} = ½|f w|²`
  have hLhalf : (∫ p, Work.Coercivity.L f p.1 p.2 * f p.1 p.2 * Work.Spaces.w p.1 ^ 2 ∂P)
      = (1 / 2) * Work.Coercivity.Ef f := by
    rw [← hwipL]
    have h1 : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ =>
        f z θ ^ 2 * Work.Spaces.w z ^ 2 * (fun _ => (1 : ℝ)) θ))
        (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
      refine (hp.sqDzOne 0 (by norm_num)).congr_fun ?_
        (measurableSet_Ici.prod measurableSet_Icc)
      rintro ⟨z, θ⟩ _
      simp only [Function.uncurry_apply_pair, Work.Spaces.DzIter_zero]
      ring
    have h2 : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ =>
        Work.Coercivity.L f z θ * f z θ * Work.Spaces.w z ^ 2 * (fun _ => (1 : ℝ)) θ))
        (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
      refine hintL.congr_fun ?_ (measurableSet_Ici.prod measurableSet_Icc)
      rintro ⟨z, θ⟩ _
      simp only [Function.uncurry_apply_pair]
      ring
    have h := Work.FTS.CoercivityFix.Coer1.wip_L_self_Q f hp.zibp_f
      (fun _ => (1 : ℝ)) h1 h2
    have hw : (fun z θ : ℝ => Work.Spaces.w z ^ 2 * (1 : ℝ))
        = fun z _ => Work.Spaces.w z ^ 2 := by funext z θ; ring
    rw [hw] at h
    rw [h, Work.FTS.CoercivityFix.Coer1.wip_one_self,
      Work.FTS.CoercivityFix.Coer1.Ef_eq_EnOne]
  -- ## splitting `Γ/c = K + (Γ/c - K)`
  have hTsum : (∫ p, (2 * p.1 * Work.Spaces.Gam α p.2
          / (Work.Spaces.c α * (1 + p.1) ^ 2)) * Work.Coercivity.L12f f p.1
          * f p.1 p.2 * Work.Spaces.w p.1 ^ 2 ∂P)
      = (∫ p, 2 * Work.Spaces.K p.2 * f p.1 p.2
          * (Work.Spaces.w p.1 / p.1 * Work.Coercivity.L12f f p.1) ∂P)
        + (∫ p, 2 * (Work.Spaces.Gam α p.2 / Work.Spaces.c α - Work.Spaces.K p.2)
            * f p.1 p.2 * Work.Spaces.w p.1
            * (Work.Coercivity.L12f f p.1 / p.1) ∂P) := by
    rw [← MeasureTheory.integral_add hF5 hF6]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    show 2 * p.1 * Work.Spaces.Gam α p.2 / (Work.Spaces.c α * (1 + p.1) ^ 2)
        * Work.Coercivity.L12f f p.1 * f p.1 p.2 * Work.Spaces.w p.1 ^ 2
      = 2 * Work.Spaces.K p.2 * f p.1 p.2
          * (Work.Spaces.w p.1 / p.1 * Work.Coercivity.L12f f p.1)
        + 2 * (Work.Spaces.Gam α p.2 / Work.Spaces.c α - Work.Spaces.K p.2)
            * f p.1 p.2 * Work.Spaces.w p.1
            * (Work.Coercivity.L12f f p.1 / p.1)
    by_cases hz : p.1 = 0
    · rw [hz]; simp [Work.Spaces.w]
    · simp only [Work.Spaces.w]
      field_simp
      ring
  -- ## the two radial integrals of the paper
  set Y : ℝ := ∫ z in Set.Ioi (0 : ℝ),
    (1 + z) / z ^ 3 * (Work.Coercivity.L12f f z) ^ 2 with hY
  set Z : ℝ := ∫ z in Set.Ioi (0 : ℝ),
    (Work.Coercivity.L12f f z) ^ 2 / z ^ 2 with hZ
  have hEL : Work.Coercivity.EL12z f = Z := by
    rw [hZ]
    simp only [Work.Coercivity.EL12z, Work.Coercivity.L2Sqz, Work.Spaces.Iz]
    rw [MeasureTheory.integral_Ici_eq_integral_Ioi]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    exact div_pow (Work.Coercivity.L12f f z) z 2
  have hWK : (∫ p, 2 * Work.Spaces.K p.2 * f p.1 p.2
        * (Work.Spaces.w p.1 / p.1 * Work.Coercivity.L12f f p.1) ∂P) = -2 * Y := by
    rw [hP, hY]
    exact Work.Coercivity.wip_K_part_eq f hHH hintK
  have hBsq : MeasureTheory.IntegrableOn
      (fun θ : ℝ => (Work.Spaces.Gam α θ / Work.Spaces.c α - Work.Spaces.K θ) ^ 2)
      Work.Spaces.Iθ := Work.Coercivity.integrableOn_GammaK_sq α hα hα1
  have hWG : (∫ p, 2 * (Work.Spaces.Gam α p.2 / Work.Spaces.c α - Work.Spaces.K p.2)
        * f p.1 p.2 * Work.Spaces.w p.1
        * (Work.Coercivity.L12f f p.1 / p.1) ∂P)
      ≤ (7 / 5) * Real.sqrt (Work.Coercivity.Ef f) * Real.sqrt Z := by
    have h := (abs_le.mp (Work.Coercivity.wip_G_bound α hα hα1 f hHH
      (hfw2_of_regQ hα hf) hΓ hBsq hintG)).2
    rw [hEL] at h
    exact h
  have hZY : Z ≤ Y := by
    rw [hZ, hY]
    refine MeasureTheory.integral_mono_ae ?_ (Work.Coercivity.L12_z_byparts_rhs_integrable f hHH) ?_
    · refine (hHH.intA 1 (by norm_num)).congr_fun ?_ measurableSet_Ioi
      intro z _
      norm_num
    · filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with z hz
      have hz0 : 0 < z := hz
      rw [← sub_nonneg]
      have hsub : (1 + z) / z ^ 3 * (Work.Coercivity.L12f f z) ^ 2
          - (Work.Coercivity.L12f f z) ^ 2 / z ^ 2
          = (Work.Coercivity.L12f f z) ^ 2 / z ^ 3 := by
        field_simp
        ring
      rw [hsub]
      positivity
  -- ## the numerical conclusion `½x² + 2y² - (7/5)xy ≥ ¼x²`
  have hEfnn : 0 ≤ Work.Coercivity.Ef f := by
    rw [Work.Coercivity.Ef, Work.Spaces.L2Sq]
    exact integral_nonneg fun z => integral_nonneg fun θ => sq_nonneg _
  have hZnn : 0 ≤ Z := by
    rw [hZ]
    exact integral_nonneg fun z => div_nonneg (sq_nonneg _) (sq_nonneg _)
  have hnum : (1 / 2) * Work.Coercivity.Ef f + 2 * Z
      - (7 / 5) * Real.sqrt (Work.Coercivity.Ef f) * Real.sqrt Z
      ≥ (1 / 4) * Work.Coercivity.Ef f := by
    nlinarith [Real.sq_sqrt hEfnn, Real.sq_sqrt hZnn,
      sq_nonneg (Real.sqrt (Work.Coercivity.Ef f) - 14 / 5 * Real.sqrt Z),
      sq_nonneg (Real.sqrt Z)]
  calc Work.Coercivity.wip (fun z _ => Work.Spaces.w z ^ 2) (Work.Coercivity.LGamma α f) f
      = (1 / 2) * Work.Coercivity.Ef f
          - (∫ p, 2 * Work.Spaces.K p.2 * f p.1 p.2
              * (Work.Spaces.w p.1 / p.1 * Work.Coercivity.L12f f p.1) ∂P)
          - (∫ p, 2 * (Work.Spaces.Gam α p.2 / Work.Spaces.c α - Work.Spaces.K p.2)
              * f p.1 p.2 * Work.Spaces.w p.1
              * (Work.Coercivity.L12f f p.1 / p.1) ∂P) := by
        rw [hwipLG, hsplit, hLhalf, hTsum]; ring
    _ = (1 / 2) * Work.Coercivity.Ef f + 2 * Y
          - (∫ p, 2 * (Work.Spaces.Gam α p.2 / Work.Spaces.c α - Work.Spaces.K p.2)
              * f p.1 p.2 * Work.Spaces.w p.1
              * (Work.Coercivity.L12f f p.1 / p.1) ∂P) := by
        rw [hWK]; ring
    _ ≥ (1 / 2) * Work.Coercivity.Ef f + 2 * Z
          - (7 / 5) * Real.sqrt (Work.Coercivity.Ef f) * Real.sqrt Z := by
        linarith [hWG, hZY]
    _ ≥ (1 / 4) * Work.Coercivity.Ef f := hnum

/-! ## The sharp projector bound in the interior class -/

/-- `(D_θ f)² w²` is jointly integrable for `f ∈ RegQ α 2` (the `D_θ·D_θ` form). -/
theorem intDth2_Q (α : ℝ) (hα : 0 < α) {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.Nonlin.RegQ α 2 f) :
    MeasureTheory.IntegrableOn
      (Function.uncurry (fun z θ => Work.Spaces.Dth f z θ * Work.Spaces.Dth f z θ
        * Work.Spaces.w z ^ 2)) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
  have hp := Work.FTS.CoercivityFix.Coer1.IntPkg_Q α hα hf
  refine (hp.sqMixedOne 1 0 (by norm_num) (by norm_num)).congr_fun ?_
    (measurableSet_Ici.prod measurableSet_Icc)
  rintro ⟨z, θ⟩ _
  simp only [Function.uncurry_apply_pair, Work.Spaces.mixed, Work.Spaces.DzIter_zero,
    Work.Spaces.DthIter_zero, Work.Spaces.DthIter_succ]
  ring

/-- The a.e. strong measurability of `D_θ f · w` in the interior class. -/
theorem aesm_dth_mul_w_swQ (α : ℝ) (hα : 0 < α) {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.Nonlin.RegQ α 2 f) :
    MeasureTheory.AEStronglyMeasurable
      (fun p : ℝ × ℝ => Work.Spaces.Dth f p.1 p.2 * Work.Spaces.w p.1)
      ((volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ)) := by
  refine Work.Spaces.aesm_of_continuousOn_Qd _ ?_
  have h1 : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.Dth f p.1 p.2)
      Work.FTS.CoercivityFix.Coer1.Qd := by
    have h := Work.FTS.CoercivityFix.Coer1.continuousOn_mixed_Q hf.1 0 1
    simpa only [Work.Spaces.mixed_zero_left, Work.Spaces.DthIter_succ,
      Work.Spaces.DthIter_zero] using h
  exact h1.mul Work.Coercivity.continuousOn_w_quad

/-- **The bound `(C0 f)² ≤ EDthW f` in the interior class**: `L₁₂(Transport f)(0)` is a linear
functional of `D_θ f · w` whose kernel `3 K(θ) z/(1+z)³` has `L²`-norm at most `1`.  This is
the interior port of `Work.Coercivity.C0_sq_le_EDthW`. -/
theorem C0_sq_le_EDthW_swQ (α : ℝ) (hα : 0 < α) {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.Nonlin.RegQ α 2 f) :
    (Work.Coercivity.C0 f) ^ 2 ≤ Work.Coercivity.EDthW f := by
  set P : Measure (ℝ × ℝ) := (volume.restrict Work.Spaces.Iz).prod
    (volume.restrict Work.Spaces.Iθ) with hP
  set u : ℝ × ℝ → ℝ :=
    fun p => Work.Spaces.Dth f p.1 p.2 * Work.Spaces.w p.1 with hu
  set v : ℝ × ℝ → ℝ :=
    fun p => 3 * Work.Spaces.K p.2 * p.1 / (1 + p.1) ^ 3 with hv
  have hint := intDth2_Q α hα hf
  have hu2 : MeasureTheory.Integrable (fun p : ℝ × ℝ => u p ^ 2) P := by
    have h := Work.Coercivity.integrableOn_prod (g := fun z θ => Work.Spaces.Dth f z θ
      * Work.Spaces.Dth f z θ * Work.Spaces.w z ^ 2) hint
    exact h.congr (Filter.Eventually.of_forall fun p => by
      rcases p with ⟨z, θ⟩
      simp only [hu]
      ring)
  have hv2 : MeasureTheory.Integrable (fun p : ℝ × ℝ => v p ^ 2) P := by
    have hran : MeasureTheory.Integrable (fun z : ℝ => 9 * (z ^ 2 / (1 + z) ^ 6))
        (volume.restrict Work.Spaces.Iz) :=
      Work.Coercivity.integrable_Iz_zsq_div_six.const_mul 9
    have hmul : MeasureTheory.Integrable (fun p : ℝ × ℝ =>
        (9 * (p.1 ^ 2 / (1 + p.1) ^ 6)) * ((Work.Spaces.K p.2) ^ 2)) P :=
      hran.mul_prod Work.Coercivity.integrableOn_Kθ_sq
    refine hmul.congr ?_
    filter_upwards [Work.Coercivity.ae_prod_pos] with p hp
    have hp1 : 1 + p.1 ≠ 0 := ne_of_gt (by linarith [show (0 : ℝ) < p.1 from hp])
    simp only [hv]
    field_simp
    ring
  have huA : MeasureTheory.MemLp u 2 P :=
    (MeasureTheory.memLp_two_iff_integrable_sq (aesm_dth_mul_w_swQ α hα hf)).2 hu2
  have hvA : MeasureTheory.MemLp v 2 P := by
    refine (MeasureTheory.memLp_two_iff_integrable_sq ?_).2 hv2
    rw [hv]
    apply Measurable.aestronglyMeasurable
    simp only [Work.Spaces.K]
    fun_prop
  have hC0id : Work.Coercivity.C0 f = ∫ p, u p * v p ∂P := by
    have hdef : Work.Coercivity.C0 f = ∫ s in Set.Ioi (0 : ℝ), ∫ θ in Work.Spaces.Iθ,
        Work.Spaces.K θ * Work.Coercivity.Transport f s θ / s := by
      simp only [Work.Coercivity.C0, Work.Coercivity.L12f, Work.FM.L12, Work.FM.L12dens,
        Work.Spaces.Iθ]
    rw [hdef]
    have h1 : (∫ s in Set.Ioi (0 : ℝ), ∫ θ in Work.Spaces.Iθ,
          Work.Spaces.K θ * Work.Coercivity.Transport f s θ / s)
        = ∫ s in Set.Ioi (0 : ℝ), ∫ θ in Work.Spaces.Iθ, u (s, θ) * v (s, θ) := by
      refine MeasureTheory.integral_congr_ae ?_
      filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with s hs
      refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun θ => ?_)
      simp only [hu, hv, Work.Coercivity.Transport, Work.Spaces.w]
      have hs0 : s ≠ 0 := ne_of_gt hs
      have hs1 : 1 + s ≠ 0 := ne_of_gt (by linarith [show (0 : ℝ) < s from hs])
      field_simp
    rw [h1]
    rw [MeasureTheory.setIntegral_congr_set (MeasureTheory.Ioi_ae_eq_Ici (a := (0 : ℝ)))]
    exact (MeasureTheory.integral_prod (fun p : ℝ × ℝ => u p * v p)
      (huA.integrable_mul hvA)).symm
  have hunorm : ∫ p, u p ^ 2 ∂P = Work.Coercivity.EDthW f := by
    rw [Work.FTS.CoercivityFix.Coer1.EDthW_eq_prod hint]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    rcases p with ⟨z, θ⟩
    simp only [hu]
    ring
  have hsep : ∫ p, v p ^ 2 ∂P
      = (∫ z in Work.Spaces.Iz, 9 * (z ^ 2 / (1 + z) ^ 6))
        * (∫ θ in Work.Spaces.Iθ, (Work.Spaces.K θ) ^ 2) := by
    have hcongr : (fun p : ℝ × ℝ => v p ^ 2)
        =ᵐ[P] fun p : ℝ × ℝ => (9 * (p.1 ^ 2 / (1 + p.1) ^ 6))
            * ((Work.Spaces.K p.2) ^ 2) := by
      filter_upwards [Work.Coercivity.ae_prod_pos] with p hp
      have hp1 : 1 + p.1 ≠ 0 := ne_of_gt (by linarith [show (0 : ℝ) < p.1 from hp])
      simp only [hv]; field_simp; ring
    rw [MeasureTheory.integral_congr_ae hcongr]
    have hran : MeasureTheory.Integrable (fun z : ℝ => 9 * (z ^ 2 / (1 + z) ^ 6))
        (volume.restrict Work.Spaces.Iz) :=
      Work.Coercivity.integrable_Iz_zsq_div_six.const_mul 9
    exact Work.Coercivity.integral_prod_sep _ _ hran Work.Coercivity.integrableOn_Kθ_sq
  have hvnorm : ∫ p, v p ^ 2 ∂P ≤ 1 := by
    rw [hsep]
    have h1 : (∫ z in Work.Spaces.Iz, 9 * (z ^ 2 / (1 + z) ^ 6)) = 3 / 10 := by
      rw [MeasureTheory.integral_const_mul, Work.Coercivity.integral_Iz_zsq_div_six]
      norm_num
    have h2 : (∫ θ in Work.Spaces.Iθ, (Work.Spaces.K θ) ^ 2) ≤ 9 / 4 :=
      Work.Coercivity.integral_Iθ_Ksq_le
    have hnn : 0 ≤ ∫ θ in Work.Spaces.Iθ, (Work.Spaces.K θ) ^ 2 :=
      integral_nonneg fun θ => sq_nonneg _
    rw [h1]
    nlinarith [h2, hnn]
  calc (Work.Coercivity.C0 f) ^ 2 = (∫ p, u p * v p ∂P) ^ 2 := by rw [hC0id]
    _ ≤ (∫ p, u p ^ 2 ∂P) * (∫ p, v p ^ 2 ∂P) :=
        Work.Coercivity.cs_integral_mul huA hvA
    _ ≤ Work.Coercivity.EDthW f * 1 := by
        rw [hunorm]
        exact mul_le_mul_of_nonneg_left hvnorm
          (by rw [← hunorm]; exact integral_nonneg fun p => sq_nonneg _)
    _ = Work.Coercivity.EDthW f := mul_one _

/-- **The sharp projector bound in the interior class**, with the integrability certificate:
`|⟨𝕡(Transport f), f⟩_{w²}| ≤ √58·√EDthW·√Ef ≤ Ef/20 + 1000·EDthW`, and the pairing is an
honest (absolutely convergent) integral. -/
theorem proj_pair_conj (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.Nonlin.RegQ α 2 f) (hΓ : Work.Coercivity.GammaL2Bnd α) :
    MeasureTheory.IntegrableOn (Function.uncurry (fun z θ =>
      Work.Coercivity.Proj α (Work.Coercivity.Transport f) z θ * f z θ
        * Work.Spaces.w z ^ 2)) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)
      ∧ |Work.Coercivity.wip (fun z _ => Work.Spaces.w z ^ 2)
          (Work.Coercivity.Proj α (Work.Coercivity.Transport f)) f|
        ≤ (1 / 20) * Work.Coercivity.Ef f + 1000 * Work.Coercivity.EDthW f := by
  set P : Measure (ℝ × ℝ) := (volume.restrict Work.Spaces.Iz).prod
    (volume.restrict Work.Spaces.Iθ) with hP
  set U : ℝ × ℝ → ℝ := fun p =>
    Work.Coercivity.Proj α (Work.Coercivity.Transport f) p.1 p.2 * Work.Spaces.w p.1 with hU
  set V : ℝ × ℝ → ℝ := fun p => f p.1 p.2 * Work.Spaces.w p.1 with hV
  set Wt : ℝ × ℝ → ℝ := fun p => 18 * (Work.Spaces.Dth f p.1 p.2 * Work.Spaces.w p.1) ^ 2
      + 8 * (Work.Spaces.Gam α p.2 / Work.Spaces.c α) ^ 2 * (Work.Coercivity.C0 f) ^ 2
        / (1 + p.1) ^ 2 with hWt
  have hDth2 := intDth2_Q α hα hf
  have hDth2P : MeasureTheory.Integrable (fun p : ℝ × ℝ => Work.Spaces.Dth f p.1 p.2
      * Work.Spaces.Dth f p.1 p.2 * Work.Spaces.w p.1 ^ 2) P :=
    Work.Coercivity.integrableOn_prod hDth2
  have hfwP : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => (f p.1 p.2 * Work.Spaces.w p.1) ^ 2) P :=
    Work.Coercivity.integrableOn_prod (hfw_of_regQ hα hf)
  have hC0 : (Work.Coercivity.C0 f) ^ 2 ≤ Work.Coercivity.EDthW f :=
    C0_sq_le_EDthW_swQ α hα hf
  have hEdnn : 0 ≤ Work.Coercivity.EDthW f := by
    rw [Work.Coercivity.EDthW, Work.Coercivity.wip]
    exact integral_nonneg fun z => integral_nonneg fun θ =>
      mul_nonneg (mul_self_nonneg _) (sq_nonneg _)
  -- ## the pointwise bound `U² ≤ Wt`
  have hpt : ∀ᵐ p ∂P, (U p) ^ 2 ≤ Wt p := by
    filter_upwards [Work.Coercivity.ae_prod_pos] with p hp
    have hid : U p = (1 / (1 + p.1)) *
        (3 * (Work.Spaces.Dth f p.1 p.2 * Work.Spaces.w p.1)
          - 2 * (Work.Spaces.Gam α p.2 / Work.Spaces.c α) * Work.Coercivity.C0 f) := by
      simp only [hU, Work.Coercivity.Proj, Work.Coercivity.Transport, Work.Spaces.w,
        Work.Coercivity.C0]
      have hz0 : p.1 ≠ 0 := ne_of_gt hp
      have hz1 : 1 + p.1 ≠ 0 := ne_of_gt (by linarith)
      field_simp
    set g : ℝ := Work.Spaces.Gam α p.2 / Work.Spaces.c α with hg
    set Gw : ℝ := Work.Spaces.Dth f p.1 p.2 * Work.Spaces.w p.1 with hGw
    have hquad : (3 * Gw - 2 * g * Work.Coercivity.C0 f) ^ 2
        ≤ 18 * Gw ^ 2 + 8 * g ^ 2 * (Work.Coercivity.C0 f) ^ 2 := by
      have h1 : (3 * Gw - 2 * g * Work.Coercivity.C0 f) ^ 2
          ≤ 2 * ((3 * Gw) ^ 2 + (2 * g * Work.Coercivity.C0 f) ^ 2) := by
        nlinarith [sq_nonneg (3 * Gw + 2 * g * Work.Coercivity.C0 f)]
      have h2 : 2 * ((3 * Gw) ^ 2 + (2 * g * Work.Coercivity.C0 f) ^ 2)
          = 18 * Gw ^ 2 + 8 * g ^ 2 * (Work.Coercivity.C0 f) ^ 2 := by ring
      linarith
    calc (U p) ^ 2
        = (1 / (1 + p.1)) ^ 2 * (3 * Gw - 2 * g * Work.Coercivity.C0 f) ^ 2 := by
          rw [hid, hGw, hg]; ring
      _ ≤ (1 / (1 + p.1)) ^ 2
            * (18 * Gw ^ 2 + 8 * g ^ 2 * (Work.Coercivity.C0 f) ^ 2) :=
          mul_le_mul_of_nonneg_left hquad (by positivity)
      _ ≤ 18 * Gw ^ 2 + 8 * g ^ 2 * (Work.Coercivity.C0 f) ^ 2 / (1 + p.1) ^ 2 := by
          have hp1 : (0 : ℝ) < (1 + p.1) ^ 2 := pow_pos (by linarith) 2
          have heq : (1 / (1 + p.1)) ^ 2
                * (18 * Gw ^ 2 + 8 * g ^ 2 * (Work.Coercivity.C0 f) ^ 2)
              = 18 * Gw ^ 2 / (1 + p.1) ^ 2
                + 8 * g ^ 2 * (Work.Coercivity.C0 f) ^ 2 / (1 + p.1) ^ 2 := by
            field_simp
          rw [heq]
          have h2z : 18 * Gw ^ 2 / (1 + p.1) ^ 2 ≤ 18 * Gw ^ 2 := by
            rw [div_le_iff₀ hp1]
            nlinarith [sq_nonneg Gw, sq_nonneg p.1, hp]
          linarith [h2z]
      _ = Wt p := by rw [hWt, hGw, hg]
  -- ## integrability of the majorant `Wt`
  have hW1 : MeasureTheory.Integrable
      (fun p : ℝ × ℝ => 18 * (Work.Spaces.Dth f p.1 p.2 * Work.Spaces.w p.1) ^ 2) P := by
    have h := hDth2P.const_mul 18
    exact h.congr (Filter.Eventually.of_forall fun p => by
      rcases p with ⟨z, θ⟩; ring)
  have hGamCont : ContinuousOn (fun θ : ℝ => Work.Spaces.Gam α θ) Work.Spaces.Iθ :=
    Work.Coercivity.continuousOn_Gam α hα
  have hG2int : MeasureTheory.Integrable
      (fun θ : ℝ => (Work.Spaces.Gam α θ / Work.Spaces.c α) ^ 2)
      (volume.restrict Work.Spaces.Iθ) := by
    have hcont : ContinuousOn
        (fun θ : ℝ => (Work.Spaces.Gam α θ / Work.Spaces.c α) ^ 2) Work.Spaces.Iθ :=
      ((hGamCont.div_const (Work.Spaces.c α)).pow 2)
    exact hcont.integrableOn_Icc
  have hCorrInt : MeasureTheory.Integrable (fun p : ℝ × ℝ =>
      (Work.Spaces.Gam α p.2 / Work.Spaces.c α) ^ 2 / (1 + p.1) ^ 2) P := by
    have h := Work.Coercivity.integrable_Iz_one_div_sq.mul_prod hG2int
    rw [hP]
    refine h.congr (Filter.Eventually.of_forall fun p => ?_)
    simp only [Pi.mul_apply]
    ring
  have hW2 : MeasureTheory.Integrable (fun p : ℝ × ℝ =>
      8 * (Work.Spaces.Gam α p.2 / Work.Spaces.c α) ^ 2
        * (Work.Coercivity.C0 f) ^ 2 / (1 + p.1) ^ 2) P := by
    have h := hCorrInt.const_mul (8 * (Work.Coercivity.C0 f) ^ 2)
    refine h.congr (Filter.Eventually.of_forall fun p => ?_)
    simp only [Pi.mul_apply]
    ring
  have hWint : MeasureTheory.Integrable Wt P := by
    rw [hWt]; exact hW1.add hW2
  have hUAesm : MeasureTheory.AEStronglyMeasurable U P := by
    rw [hU]
    refine Work.Spaces.aesm_of_continuousOn_Qd _ ?_
    have hProj : ContinuousOn (fun p : ℝ × ℝ =>
        Work.Coercivity.Proj α (Work.Coercivity.Transport f) p.1 p.2)
        Work.FTS.CoercivityFix.Coer1.Qd := by
      have hDth : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.Dth f p.1 p.2)
          Work.FTS.CoercivityFix.Coer1.Qd := by
        have h := Work.FTS.CoercivityFix.Coer1.continuousOn_mixed_Q hf.1 0 1
        simpa only [Work.Spaces.mixed_zero_left, Work.Spaces.DthIter_succ,
          Work.Spaces.DthIter_zero] using h
      have hTrans : ContinuousOn (fun p : ℝ × ℝ =>
          Work.Coercivity.Transport f p.1 p.2) Work.FTS.CoercivityFix.Coer1.Qd := by
        change ContinuousOn (fun p : ℝ × ℝ =>
          3 * Work.Spaces.Dth f p.1 p.2 / (1 + p.1)) Work.FTS.CoercivityFix.Coer1.Qd
        exact (continuousOn_const.mul hDth).div
          ((continuous_const.add continuous_fst).continuousOn)
          (fun p hp => ne_of_gt (by linarith [show (0 : ℝ) < p.1 from hp.1]))
      have hGam : ContinuousOn (fun p : ℝ × ℝ =>
          Work.Spaces.Gam α p.2 / Work.Spaces.c α) Work.FTS.CoercivityFix.Coer1.Qd :=
        ((Work.Coercivity.continuousOn_Gam α hα).div_const (Work.Spaces.c α)).comp
          ((continuous_snd.continuousOn).mono (Set.subset_univ _))
          (fun p hp => ⟨le_of_lt hp.2.1, le_of_lt hp.2.2⟩)
      have hratio : ContinuousOn (fun p : ℝ × ℝ =>
          2 * p.1 ^ 2 / (1 + p.1) ^ 3) Work.FTS.CoercivityFix.Coer1.Qd := by
        refine ContinuousOn.div ((continuousOn_const.mul (continuous_fst.continuousOn.pow 2)))
          ((continuous_const.add continuous_fst).continuousOn.pow 3)
          (fun p hp => pow_ne_zero 3 (by linarith [show (0 : ℝ) < p.1 from hp.1]))
      have hCorr : ContinuousOn (fun p : ℝ × ℝ =>
          (Work.Spaces.Gam α p.2 / Work.Spaces.c α) * (2 * p.1 ^ 2 / (1 + p.1) ^ 3)
            * Work.Coercivity.C0 f) Work.FTS.CoercivityFix.Coer1.Qd :=
        (hGam.mul hratio).mul continuousOn_const
      have hmain : ContinuousOn (fun p : ℝ × ℝ =>
          Work.Coercivity.Transport f p.1 p.2
            - (Work.Spaces.Gam α p.2 / Work.Spaces.c α) * (2 * p.1 ^ 2 / (1 + p.1) ^ 3)
              * Work.Coercivity.C0 f) Work.FTS.CoercivityFix.Coer1.Qd :=
        hTrans.sub hCorr
      have hfun : (fun p : ℝ × ℝ => Work.Coercivity.Proj α (Work.Coercivity.Transport f)
          p.1 p.2) = fun p : ℝ × ℝ => Work.Coercivity.Transport f p.1 p.2
            - (Work.Spaces.Gam α p.2 / Work.Spaces.c α) * (2 * p.1 ^ 2 / (1 + p.1) ^ 3)
              * Work.Coercivity.C0 f := by
        funext p
        simp only [Work.Coercivity.Proj, Work.Coercivity.C0]
      rw [hfun]
      exact hmain
    exact hProj.mul Work.Coercivity.continuousOn_w_quad
  have hUaesm : MeasureTheory.AEStronglyMeasurable (fun p : ℝ × ℝ => (U p) ^ 2) P := by
    refine (hUAesm.mul hUAesm).congr (Filter.Eventually.of_forall fun p => ?_)
    simp only [Pi.mul_apply, pow_two]
  have hUint : MeasureTheory.Integrable (fun p : ℝ × ℝ => (U p) ^ 2) P :=
    hWint.mono' hUaesm (hpt.mono fun p hp => by
      rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]; exact hp)
  have hUA : MeasureTheory.MemLp U 2 P :=
    (MeasureTheory.memLp_two_iff_integrable_sq hUAesm).2 hUint
  -- ## the two normalisations
  have hunorm : ∫ p, (Work.Spaces.Dth f p.1 p.2 * Work.Spaces.w p.1) ^ 2 ∂P
      = Work.Coercivity.EDthW f := by
    rw [Work.FTS.CoercivityFix.Coer1.EDthW_eq_prod hDth2]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun p => by
      rcases p with ⟨z, θ⟩; ring)
  have hG5 : ∫ θ in Work.Spaces.Iθ, (Work.Spaces.Gam α θ / Work.Spaces.c α) ^ 2 ≤ 5 :=
    Work.Coercivity.GamDivCSqInt_le_five α hα hα1 hΓ
  have hCorrLe : ∫ p, (Work.Spaces.Gam α p.2 / Work.Spaces.c α) ^ 2 / (1 + p.1) ^ 2 ∂P
      ≤ 5 := Work.Coercivity.projCorr_sepIntegral_le_five α hα hα1 hG5
  have hWexp : ∫ p, Wt p ∂P
      = 18 * (∫ p, (Work.Spaces.Dth f p.1 p.2 * Work.Spaces.w p.1) ^ 2 ∂P)
        + (8 * (Work.Coercivity.C0 f) ^ 2)
          * (∫ p, (Work.Spaces.Gam α p.2 / Work.Spaces.c α) ^ 2 / (1 + p.1) ^ 2 ∂P) := by
    rw [hWt, MeasureTheory.integral_add hW1 hW2, MeasureTheory.integral_const_mul]
    congr 1
    rw [show (fun p : ℝ × ℝ =>
        8 * (Work.Spaces.Gam α p.2 / Work.Spaces.c α) ^ 2
          * (Work.Coercivity.C0 f) ^ 2 / (1 + p.1) ^ 2)
        = fun p => (8 * (Work.Coercivity.C0 f) ^ 2)
            * ((Work.Spaces.Gam α p.2 / Work.Spaces.c α) ^ 2 / (1 + p.1) ^ 2) from by
      funext p; ring]
    rw [MeasureTheory.integral_const_mul]
  have hWle : ∫ p, Wt p ∂P ≤ 58 * Work.Coercivity.EDthW f := by
    rw [hWexp, hunorm]
    have hkey : (8 * (Work.Coercivity.C0 f) ^ 2)
        * (∫ p, (Work.Spaces.Gam α p.2 / Work.Spaces.c α) ^ 2 / (1 + p.1) ^ 2 ∂P)
        ≤ 40 * Work.Coercivity.EDthW f := by
      have h3 : (8 * (Work.Coercivity.C0 f) ^ 2)
          * (∫ p, (Work.Spaces.Gam α p.2 / Work.Spaces.c α) ^ 2
              / (1 + p.1) ^ 2 ∂P) ≤ (8 * (Work.Coercivity.C0 f) ^ 2) * 5 :=
        mul_le_mul_of_nonneg_left hCorrLe (by positivity)
      have h4 : (8 * (Work.Coercivity.C0 f) ^ 2) * 5
          ≤ 40 * Work.Coercivity.EDthW f := by nlinarith [hC0]
      linarith
    linarith [hkey, hEdnn]
  have hU2le : ∫ p, (U p) ^ 2 ∂P ≤ 58 * Work.Coercivity.EDthW f :=
    le_trans (MeasureTheory.integral_mono_ae hUint hWint hpt) hWle
  -- ## the two `L²`-functions and Cauchy–Schwarz
  have hVnorm : ∫ p, (V p) ^ 2 ∂P = Work.Coercivity.Ef f := by
    have h := Work.Coercivity.wip_eq_integral_prod (fun z _ => Work.Spaces.w z ^ 2) f f
      (hfw2_of_regQ hα hf)
    rw [hP]
    have hcongr : (∫ p, V p ^ 2 ∂(volume.restrict Work.Spaces.Iz).prod
          (volume.restrict Work.Spaces.Iθ))
        = ∫ p, f p.1 p.2 * f p.1 p.2 * Work.Spaces.w p.1 ^ 2
            ∂(volume.restrict Work.Spaces.Iz).prod (volume.restrict Work.Spaces.Iθ) :=
      MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun p => by
        simp only [hV]; ring)
    rw [hcongr, ← h, Work.Coercivity.Ef_eq_wip]
  have hVA : MeasureTheory.MemLp V 2 P := by
    refine (MeasureTheory.memLp_two_iff_integrable_sq ?_).2 ?_
    · rw [hV]
      exact (aesm_f_Q hf).mul (Work.Spaces.aesm_of_continuousOn_Qd _
        Work.Coercivity.continuousOn_w_quad)
    · exact hfwP.congr (Filter.Eventually.of_forall fun p => by
        simp only [hV])
  have hcs := Work.Coercivity.cs_integral_mul hUA hVA
  have hV2 : (∫ p, V p ^ 2 ∂P) = Work.Coercivity.Ef f := hVnorm
  have hU2 : (∫ p, U p ^ 2 ∂P) ≤ 58 * Work.Coercivity.EDthW f := hU2le
  have hUVint : MeasureTheory.Integrable (fun p : ℝ × ℝ => U p * V p) P :=
    hUA.integrable_mul hVA
  have hEfnn : 0 ≤ Work.Coercivity.Ef f := by
    rw [Work.Coercivity.Ef, Work.Spaces.L2Sq]
    exact integral_nonneg fun z => integral_nonneg fun θ => sq_nonneg _
  have hbound : |∫ p, U p * V p ∂P|
      ≤ Real.sqrt 58 * Real.sqrt (Work.Coercivity.EDthW f) * Real.sqrt (Work.Coercivity.Ef f) := by
    have h1 : (∫ p, U p * V p ∂P) ^ 2
        ≤ (58 * Work.Coercivity.EDthW f) * Work.Coercivity.Ef f := by
      rw [hV2] at hcs
      exact le_trans hcs (mul_le_mul_of_nonneg_right hU2 hEfnn)
    have h2 : Real.sqrt ((58 * Work.Coercivity.EDthW f) * Work.Coercivity.Ef f)
        = Real.sqrt 58 * Real.sqrt (Work.Coercivity.EDthW f) * Real.sqrt (Work.Coercivity.Ef f) := by
      rw [Real.sqrt_mul (by positivity : (0 : ℝ) ≤ 58 * Work.Coercivity.EDthW f),
        Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 58)]
    calc |∫ p, U p * V p ∂P|
        = Real.sqrt ((∫ p, U p * V p ∂P) ^ 2) := (Real.sqrt_sq_eq_abs _).symm
      _ ≤ Real.sqrt ((58 * Work.Coercivity.EDthW f) * Work.Coercivity.Ef f) :=
          Real.sqrt_le_sqrt h1
      _ = Real.sqrt 58 * Real.sqrt (Work.Coercivity.EDthW f)
            * Real.sqrt (Work.Coercivity.Ef f) := h2
  have hnum : Real.sqrt 58 * Real.sqrt (Work.Coercivity.EDthW f) * Real.sqrt (Work.Coercivity.Ef f)
      ≤ (1 / 20) * Work.Coercivity.Ef f + 1000 * Work.Coercivity.EDthW f := by
    have h := Work.Coercivity.sqrt58_amgm (Real.sqrt (Work.Coercivity.Ef f))
      (Real.sqrt (Work.Coercivity.EDthW f)) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
    rw [Real.sq_sqrt hEfnn, Real.sq_sqrt hEdnn] at h
    rw [show Work.Coercivity.Ef f / 20 = (1 / 20) * Work.Coercivity.Ef f by ring] at h
    have hcomm : Real.sqrt 58 * Real.sqrt (Work.Coercivity.EDthW f)
        * Real.sqrt (Work.Coercivity.Ef f)
        = Real.sqrt 58 * Real.sqrt (Work.Coercivity.Ef f)
          * Real.sqrt (Work.Coercivity.EDthW f) := by ring
    rw [hcomm]
    exact h
  -- ## transport the `wip` to the product measure
  have hUVon : MeasureTheory.IntegrableOn (Function.uncurry (fun z θ =>
      Work.Coercivity.Proj α (Work.Coercivity.Transport f) z θ * f z θ
        * Work.Spaces.w z ^ 2)) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
    rw [MeasureTheory.IntegrableOn, ← prod_restrict_eq]
    refine hUVint.congr (Filter.Eventually.of_forall fun p => ?_)
    rcases p with ⟨z, θ⟩
    simp only [hU, hV, Function.uncurry_apply_pair]
    ring
  have hwip : Work.Coercivity.wip (fun z _ => Work.Spaces.w z ^ 2)
      (Work.Coercivity.Proj α (Work.Coercivity.Transport f)) f
      = ∫ p, U p * V p ∂P := by
    rw [Work.Coercivity.wip_eq_integral_prod (fun z _ => Work.Spaces.w z ^ 2)
      (Work.Coercivity.Proj α (Work.Coercivity.Transport f)) f hUVon, hP]
    refine MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    simp only [hU, hV, Function.uncurry_apply_pair]
    ring
  refine ⟨hUVon, ?_⟩
  rw [hwip]
  exact le_trans hbound hnum

/-- The integrability certificate of the projector pairing (interior class). -/
theorem intProj_w2_Q (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.Nonlin.RegQ α 2 f) (hΓ : Work.Coercivity.GammaL2Bnd α) :
    MeasureTheory.IntegrableOn (Function.uncurry (fun z θ =>
      Work.Coercivity.Proj α (Work.Coercivity.Transport f) z θ * f z θ
        * Work.Spaces.w z ^ 2)) (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) :=
  (proj_pair_conj α hα hα1 hf hΓ).1

/-- **The sharp projector pairing bound in the interior class.** -/
theorem proj_pair_le_Q (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.Nonlin.RegQ α 2 f) (hΓ : Work.Coercivity.GammaL2Bnd α) :
    |Work.Coercivity.wip (fun z _ => Work.Spaces.w z ^ 2)
        (Work.Coercivity.Proj α (Work.Coercivity.Transport f)) f|
      ≤ (1 / 20) * Work.Coercivity.Ef f + 1000 * Work.Coercivity.EDthW f :=
  (proj_pair_conj α hα hα1 hf hΓ).2

/-- The integrability of `𝓛_Γ f · f w²` in the interior class. -/
theorem intLG_Q (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1) {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.Nonlin.RegQ α 2 f) (hHH : Work.Coercivity.HardyHyp f) :
    MeasureTheory.IntegrableOn (Function.uncurry (fun z θ =>
      Work.Coercivity.LGamma α f z θ * f z θ * Work.Spaces.w z ^ 2))
      (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ) := by
  have h := (show MeasureTheory.Integrable (Function.uncurry (fun z θ =>
      Work.Coercivity.L f z θ * f z θ * Work.Spaces.w z ^ 2))
      (volume.restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) from
      (Work.FTS.CoercivityFix.Coer1.IntPkg_Q α hα hf).intL_f_one).sub
    (show MeasureTheory.Integrable (Function.uncurry (fun z θ =>
      (2 * z * Work.Spaces.Gam α θ / (Work.Spaces.c α * (1 + z) ^ 2))
        * Work.Coercivity.L12f f z * f z θ * Work.Spaces.w z ^ 2))
      (volume.restrict (Work.Spaces.Iz ×ˢ Work.Spaces.Iθ)) from intT1_w2_Q α hα hα1 hf hHH)
  rw [MeasureTheory.IntegrableOn]
  refine h.congr (Filter.Eventually.of_forall fun p => ?_)
  rcases p with ⟨z, θ⟩
  simp only [Function.uncurry_apply_pair, Pi.sub_apply, Work.Coercivity.LGamma]
  ring

theorem slotW_LGammaT (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1 / 10 ^ 14) {f : ℝ → ℝ → ℝ}
    (hf : Work.FTS.Nonlin.CoerAdm α f) (hHH : Work.Coercivity.HardyHyp f)
    (hG : Work.Coercivity.GammaL2Bnd α) :
    (1 / 5) * Work.Coercivity.Ef f - 1000 * Work.Coercivity.EDthW f
      ≤ Work.Coercivity.wip (fun z _ => Work.Spaces.w z ^ 2)
          (Work.Coercivity.LGammaT α f) f := by
  have hα1' : α ≤ 1 := by linarith [hα1]
  have hf2 : Work.FTS.Nonlin.RegQ α 2 f :=
    Work.FTS.GalerkinFix.RegQ.regQ_mono hf.reg (by norm_num : 2 ≤ 5)
  have hA := LGamma_coercive_Q α hα hα1' hf2 hHH hG
  have hB := proj_pair_le_Q α hα hα1' hf2 hG
  have hB' : Work.Coercivity.wip (fun z _ => Work.Spaces.w z ^ 2)
      (Work.Coercivity.Proj α (Work.Coercivity.Transport f)) f
      ≤ (1 / 20) * Work.Coercivity.Ef f + 1000 * Work.Coercivity.EDthW f :=
    le_trans (le_abs_self _) hB
  have hsub := Work.FTS.CoercivityFix.Coer1.wip_sub_left
    (ρ := fun z _ => Work.Spaces.w z ^ 2) (A := Work.Coercivity.LGamma α f)
    (B := Work.Coercivity.Proj α (Work.Coercivity.Transport f)) (C := f)
    (intLG_Q α hα hα1' hf2 hHH) (intProj_w2_Q α hα hα1' hf2 hG)
  have hLGT : Work.Coercivity.LGammaT α f
      = (fun z θ => Work.Coercivity.LGamma α f z θ
          - Work.Coercivity.Proj α (Work.Coercivity.Transport f) z θ) := rfl
  rw [hLGT, hsub]
  linarith [hA, hB']

end Work.FTS.CoercivityFix.Coer1T
