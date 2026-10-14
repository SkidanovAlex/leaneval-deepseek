import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Submission.Work.FTS.TransportS.SlotT2.supThetaIntOpen
import Submission.Work.FTS.TransportS.t2SupF
import Submission.Work.GalerkinFix.RegQ.HkMem_mono_Q
import Submission.Work.LWP.VorticityAPI
import Submission.Work.Spaces.mixed_mul_le
import Submission.Work.Spaces.sq_mul_div_rpow

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.TransportS.T2SupB2

set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false

/-- On the open quadrant, `D_z^j D_θ^{i+1} f = sin(2θ)·∂_θ(D_z^j D_θ^i f)`. -/
theorem mixed_succ_eq_sin_mul_pth {f : ℝ → ℝ → ℝ}
    (hF : Work.FTS.EllipticEst.SmoothOpen f) (j i : ℕ) {z θ : ℝ}
    (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    Work.Spaces.mixed j (i + 1) f z θ
      = Real.sin (2 * θ) * Work.Spaces.pth (Work.Spaces.mixed j i f) z θ := by
  have h := Work.FTS.TransportS.SlotT2.supOpen_mixed_eq_sin_pth
    (f := Work.Spaces.DthIter i f) (hF.DthIter i) j hz hθ
  simpa only [Work.Spaces.mixed, Work.Spaces.DthIter_succ, Work.Spaces.DthIter_zero] using h

/-- **The pointwise angular slice bound.**  For `z > 0`, an interior angle `θ` and a mixed
derivative `D_z^j D_θ^i f` with `i ≥ 1`, `i + j + 1 ≤ 4`, the radial slice of
`(D_z^j D_θ^i f)² w²` at the angle `θ` is bounded by `5` times the angular slice of the
`ℋ⁴`-integrand.

This is the angular total-variation device of `NOTES_t2SupF_b2_analysis.md` (T), localised to
the subinterval `[θ/2, θ/2 + π/4] ∋ θ` of `(0,π/2)`: with `Ξ := (D_z^jD_θ^if)²w²` and
`Ξ₁ := (D_z^jD_θ^{i+1}f)²w²` the identity `Ξ' = 2·sin(2θ)⁻¹·√(ΞΞ₁)` follows from
`mixed_succ_eq_sin_mul_pth`, and the two weighted profiles are the `(i,j)`- and `(i+1,j)`-slots
of `HkIntegrand`, the first with the exponent `c = γ` and the second with `c = 2 - γ`; both are
admissible because `γ ≥ 1`. -/
theorem slice_bound {α : ℝ} {f : ℝ → ℝ → ℝ} (hα : 0 < α) (hα1 : α ≤ 1)
    (hF : Work.FTS.EllipticEst.SmoothOpen f) (hmem : Work.Spaces.HkMem α 4 f)
    {j i : ℕ} (hi : 1 ≤ i) (hij : i + j + 1 ≤ 4)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    (Work.Spaces.mixed j i f z θ) ^ 2 * (Work.Spaces.w z) ^ 2
      ≤ 5 * (∫ θ' in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f z θ') := by
  have hγ1 : 1 ≤ Work.Spaces.gam α := by
    have h := Work.Spaces.gam_sub_one α
    nlinarith
  have hzIz : z ∈ Work.Spaces.Iz := le_of_lt hz
  let Ξ : ℝ → ℝ := fun t => (Work.Spaces.mixed j i f z t) ^ 2 * (Work.Spaces.w z) ^ 2
  let Ξ₁ : ℝ → ℝ := fun t => (Work.Spaces.mixed j (i + 1) f z t) ^ 2 * (Work.Spaces.w z) ^ 2
  -- the interval `[θ/2, θ/2 + π/4]`
  have ha_pos : 0 < θ / 2 := by linarith [hθ.1]
  have hab : θ / 2 < θ / 2 + π / 4 := by linarith [Real.pi_pos]
  have hb_lt : θ / 2 + π / 4 < π / 2 := by linarith [hθ.2, Real.pi_pos]
  have hθmem : θ ∈ Set.Icc (θ / 2) (θ / 2 + π / 4) :=
    ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
  have hsub : Set.Icc (θ / 2) (θ / 2 + π / 4) ⊆ Work.Spaces.Iθ := fun t ht =>
    ⟨by linarith [ht.1, hθ.1], by linarith [ht.2, hθ.2, Real.pi_pos]⟩
  have hsinpos : ∀ t ∈ Set.Icc (θ / 2) (θ / 2 + π / 4), 0 < Real.sin (2 * t) := by
    intro t ht
    refine Real.sin_pos_of_pos_of_lt_pi (by linarith [ht.1, hθ.1]) ?_
    linarith [ht.2, hθ.2, Real.pi_pos]
  -- continuity of the two profiles
  have hcontΞ : ContinuousOn Ξ (Set.Icc (θ / 2) (θ / 2 + π / 4)) := by
    show ContinuousOn
      (fun t : ℝ => (Work.Spaces.mixed j i f z t) ^ 2 * (Work.Spaces.w z) ^ 2) _
    refine ContinuousOn.mul (ContinuousOn.pow ?_ 2) continuousOn_const
    exact (((hF.mixed j i).curry_θ hz).continuousOn).mono fun t ht =>
      ⟨by linarith [ht.1, hθ.1], by linarith [ht.2, hθ.2, Real.pi_pos]⟩
  have hcontΞ₁ : ContinuousOn Ξ₁ (Set.Icc (θ / 2) (θ / 2 + π / 4)) := by
    show ContinuousOn
      (fun t : ℝ => (Work.Spaces.mixed j (i + 1) f z t) ^ 2 * (Work.Spaces.w z) ^ 2) _
    refine ContinuousOn.mul (ContinuousOn.pow ?_ 2) continuousOn_const
    exact (((hF.mixed j (i + 1)).curry_θ hz).continuousOn).mono fun t ht =>
      ⟨by linarith [ht.1, hθ.1], by linarith [ht.2, hθ.2, Real.pi_pos]⟩
  have hΞnn : ∀ t ∈ Set.Icc (θ / 2) (θ / 2 + π / 4), 0 ≤ Ξ t := by
    intro t ht
    show 0 ≤ (Work.Spaces.mixed j i f z t) ^ 2 * (Work.Spaces.w z) ^ 2
    positivity
  have hΞ₁nn : ∀ t ∈ Set.Icc (θ / 2) (θ / 2 + π / 4), 0 ≤ Ξ₁ t := by
    intro t ht
    show 0 ≤ (Work.Spaces.mixed j (i + 1) f z t) ^ 2 * (Work.Spaces.w z) ^ 2
    positivity
  -- the integrability of the three profiles on the compact interval
  have hintΞ : MeasureTheory.IntegrableOn Ξ (Set.Icc (θ / 2) (θ / 2 + π / 4)) :=
    hcontΞ.integrableOn_compact isCompact_Icc
  have hsincont : ContinuousOn (fun t : ℝ => Real.sin (2 * t))
      (Set.Icc (θ / 2) (θ / 2 + π / 4)) :=
    (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn
  have hintA : MeasureTheory.IntegrableOn
      (fun t : ℝ => Ξ t * (Real.sin (2 * t)) ^ (-(Work.Spaces.gam α)))
      (Set.Icc (θ / 2) (θ / 2 + π / 4)) :=
    (hcontΞ.mul (hsincont.rpow_const fun t ht => Or.inl (ne_of_gt (hsinpos t ht)))).integrableOn_compact
      isCompact_Icc
  have hintB : MeasureTheory.IntegrableOn
      (fun t : ℝ => Ξ₁ t * (Real.sin (2 * t)) ^ (Work.Spaces.gam α - 2))
      (Set.Icc (θ / 2) (θ / 2 + π / 4)) :=
    (hcontΞ₁.mul (hsincont.rpow_const fun t ht => Or.inl (ne_of_gt (hsinpos t ht)))).integrableOn_compact
      isCompact_Icc
  -- the total-variation hypothesis
  have hTV : ∀ u v : ℝ, θ / 2 ≤ u → u ≤ v → v ≤ θ / 2 + π / 4 →
      |Ξ v - Ξ u| ≤ ∫ t in u..v, 2 * (Real.sin (2 * t))⁻¹ * Real.sqrt (Ξ t * Ξ₁ t) := by
    intro u v hau huv hvb
    have hIcc : Set.uIcc u v ⊆ Set.Ioo (0 : ℝ) (π / 2) := by
      intro t ht
      rw [Set.mem_uIcc] at ht
      rcases ht with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact ⟨by linarith [h1, hθ.1], by linarith [h2, hθ.2, Real.pi_pos]⟩
      · exact ⟨by linarith [h1, hθ.1], by linarith [h2, hθ.2, Real.pi_pos]⟩
    have hderiv : ∀ t ∈ Set.uIcc u v,
        HasDerivAt Ξ (2 * Work.Spaces.mixed j i f z t
          * Work.Spaces.pth (Work.Spaces.mixed j i f) z t * (Work.Spaces.w z) ^ 2) t := by
      intro t ht
      obtain ⟨ht0, ht1⟩ := hIcc ht
      have hdiff : DifferentiableAt ℝ (fun t' : ℝ => Work.Spaces.mixed j i f z t') t :=
        (((hF.mixed j i).curry_θ hz).differentiableOn
          Work.FTS.LocData.smoothOrder_ne_zero).differentiableAt
          (isOpen_Ioo.mem_nhds ⟨ht0, ht1⟩)
      have hp := (hdiff.hasDerivAt.pow 2).mul_const ((Work.Spaces.w z) ^ 2)
      show HasDerivAt (fun y : ℝ =>
          (Work.Spaces.mixed j i f z y) ^ 2 * (Work.Spaces.w z) ^ 2)
        (2 * Work.Spaces.mixed j i f z t
          * deriv (fun y' : ℝ => Work.Spaces.mixed j i f z y') t
          * (Work.Spaces.w z) ^ 2) t
      simpa only [pow_one, Pi.pow_apply, Nat.cast_ofNat, show (2 : ℕ) - 1 = 1 from rfl] using hp
    have hInt : IntervalIntegrable (fun t : ℝ => 2 * Work.Spaces.mixed j i f z t
        * Work.Spaces.pth (Work.Spaces.mixed j i f) z t * (Work.Spaces.w z) ^ 2)
        volume u v := by
      refine ContinuousOn.intervalIntegrable ?_
      rw [Set.uIcc_of_le huv]
      have h1 : ContinuousOn (fun t : ℝ => Work.Spaces.mixed j i f z t) (Set.Icc u v) :=
        (((hF.mixed j i).curry_θ hz).continuousOn).mono fun t ht =>
          hIcc (Set.Icc_subset_uIcc ht)
      have h2 : ContinuousOn
          (fun t : ℝ => Work.Spaces.pth (Work.Spaces.mixed j i f) z t) (Set.Icc u v) :=
        (((hF.mixed j i).pth).curry_θ hz).continuousOn |>.mono fun t ht =>
          hIcc (Set.Icc_subset_uIcc ht)
      exact ((h1.const_mul 2).mul h2).mul_const ((Work.Spaces.w z) ^ 2)
    have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hInt
    calc |Ξ v - Ξ u|
        = |∫ t in u..v, 2 * Work.Spaces.mixed j i f z t
            * Work.Spaces.pth (Work.Spaces.mixed j i f) z t * (Work.Spaces.w z) ^ 2| := by
          rw [← hFTC]
      _ ≤ ∫ t in u..v, |2 * Work.Spaces.mixed j i f z t
            * Work.Spaces.pth (Work.Spaces.mixed j i f) z t * (Work.Spaces.w z) ^ 2| :=
          intervalIntegral.abs_integral_le_integral_abs huv
      _ = ∫ t in u..v, 2 * (Real.sin (2 * t))⁻¹ * Real.sqrt (Ξ t * Ξ₁ t) := by
          refine intervalIntegral.integral_congr ?_
          intro t ht
          show |2 * Work.Spaces.mixed j i f z t
              * Work.Spaces.pth (Work.Spaces.mixed j i f) z t * (Work.Spaces.w z) ^ 2|
            = 2 * (Real.sin (2 * t))⁻¹ * Real.sqrt (Ξ t * Ξ₁ t)
          obtain ⟨ht0, ht1⟩ := hIcc ht
          have hs : 0 < Real.sin (2 * t) :=
            Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith [Real.pi_pos])
          have hsucc := mixed_succ_eq_sin_mul_pth hF j i hz ⟨ht0, ht1⟩
          have hid : Work.Spaces.pth (Work.Spaces.mixed j i f) z t
              = Work.Spaces.mixed j (i + 1) f z t * (Real.sin (2 * t))⁻¹ := by
            rw [eq_mul_inv_iff_mul_eq₀ (ne_of_gt hs), mul_comm]
            exact hsucc.symm
          have hΞt : Ξ t = (Work.Spaces.mixed j i f z t * Work.Spaces.w z) ^ 2 := by
            simp only [Ξ]; ring
          have hΞ₁t : Ξ₁ t = (Work.Spaces.mixed j (i + 1) f z t * Work.Spaces.w z) ^ 2 := by
            simp only [Ξ₁]; ring
          have hsqrt : Real.sqrt (Ξ t * Ξ₁ t)
              = |Work.Spaces.mixed j i f z t * Work.Spaces.w z|
                * |Work.Spaces.mixed j (i + 1) f z t * Work.Spaces.w z| := by
            rw [hΞt, hΞ₁t, ← mul_pow, Real.sqrt_sq_eq_abs, abs_mul]
          have hprod : 2 * Work.Spaces.mixed j i f z t
                * Work.Spaces.pth (Work.Spaces.mixed j i f) z t * (Work.Spaces.w z) ^ 2
              = 2 * ((Work.Spaces.mixed j i f z t * Work.Spaces.w z)
                  * (Work.Spaces.mixed j (i + 1) f z t * Work.Spaces.w z))
                * (Real.sin (2 * t))⁻¹ := by
            rw [hid]; ring
          rw [hprod, hsqrt]
          simp only [abs_mul, abs_inv, abs_of_pos hs,
            abs_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num)]
          ring
  -- the device
  have hdev := Work.FTS.TransportS.T2SupB2.TvSub.tv_bound_subinterval (Ξ := Ξ) (Ξ₁ := Ξ₁)
    (c := Work.Spaces.gam α)
    (a := θ / 2) (b := θ / 2 + π / 4) (x := θ) hab ha_pos hb_lt hθmem hcontΞ hΞnn hΞ₁nn
    hTV hintΞ hintA hintB
  -- pointwise slot domination on the interval
  have hdomA : ∀ t ∈ Set.Icc (θ / 2) (θ / 2 + π / 4),
      Ξ t * (Real.sin (2 * t)) ^ (-(Work.Spaces.gam α))
        ≤ Work.Spaces.HkIntegrand α 4 f z t := by
    intro t ht
    have hs := hsinpos t ht
    show (Work.Spaces.mixed j i f z t) ^ 2 * (Work.Spaces.w z) ^ 2
        * (Real.sin (2 * t)) ^ (-(Work.Spaces.gam α)) ≤ Work.Spaces.HkIntegrand α 4 f z t
    exact Work.FTS.TransportS.mixed_sq_w_rpow_le_HkIntegrand α f hs le_rfl i j hi (by omega)
  have hdomB : ∀ t ∈ Set.Icc (θ / 2) (θ / 2 + π / 4),
      Ξ₁ t * (Real.sin (2 * t)) ^ (Work.Spaces.gam α - 2)
        ≤ Work.Spaces.HkIntegrand α 4 f z t := by
    intro t ht
    have hs := hsinpos t ht
    have hc : 2 - Work.Spaces.gam α ≤ Work.Spaces.gam α := by linarith
    have h : (Work.Spaces.mixed j (i + 1) f z t) ^ 2 * (Work.Spaces.w z) ^ 2
        * (Real.sin (2 * t)) ^ (-(2 - Work.Spaces.gam α)) ≤ Work.Spaces.HkIntegrand α 4 f z t :=
      Work.FTS.TransportS.mixed_sq_w_rpow_le_HkIntegrand α f hs hc (i + 1) j
        (by omega) (by omega)
    show (Work.Spaces.mixed j (i + 1) f z t) ^ 2 * (Work.Spaces.w z) ^ 2
        * (Real.sin (2 * t)) ^ (Work.Spaces.gam α - 2) ≤ Work.Spaces.HkIntegrand α 4 f z t
    simpa only [neg_sub] using h
  have hHkIcc : MeasureTheory.IntegrableOn (fun t : ℝ => Work.Spaces.HkIntegrand α 4 f z t)
      (Set.Icc (θ / 2) (θ / 2 + π / 4)) :=
    (hmem.1 z hzIz).mono_set hsub
  have hA : (∫ t in Set.Icc (θ / 2) (θ / 2 + π / 4),
      Ξ t * (Real.sin (2 * t)) ^ (-(Work.Spaces.gam α)))
      ≤ ∫ θ' in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f z θ' := by
    refine le_trans (MeasureTheory.setIntegral_mono_on hintA hHkIcc measurableSet_Icc hdomA) ?_
    exact MeasureTheory.setIntegral_mono_set (hmem.1 z hzIz)
      (Eventually.of_forall fun t => Work.Spaces.HkIntegrand_nonneg α 4 f z t)
      (Eventually.of_forall fun t ht => hsub ht)
  have hB : (∫ t in Set.Icc (θ / 2) (θ / 2 + π / 4),
      Ξ₁ t * (Real.sin (2 * t)) ^ (Work.Spaces.gam α - 2))
      ≤ ∫ θ' in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f z θ' := by
    refine le_trans (MeasureTheory.setIntegral_mono_on hintB hHkIcc measurableSet_Icc hdomB) ?_
    exact MeasureTheory.setIntegral_mono_set (hmem.1 z hzIz)
      (Eventually.of_forall fun t => Work.Spaces.HkIntegrand_nonneg α 4 f z t)
      (Eventually.of_forall fun t ht => hsub ht)
  have hΞint : (∫ t in Set.Icc (θ / 2) (θ / 2 + π / 4), Ξ t)
      ≤ ∫ θ' in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f z θ' := by
    have hone : ∀ t ∈ Set.Icc (θ / 2) (θ / 2 + π / 4),
        1 ≤ (Real.sin (2 * t)) ^ (-(Work.Spaces.gam α)) := fun t ht =>
      Real.one_le_rpow_of_pos_of_le_one_of_nonpos (hsinpos t ht) (Real.sin_le_one _)
        (by linarith)
    have h1 : (∫ t in Set.Icc (θ / 2) (θ / 2 + π / 4), Ξ t)
        ≤ ∫ t in Set.Icc (θ / 2) (θ / 2 + π / 4),
            Ξ t * (Real.sin (2 * t)) ^ (-(Work.Spaces.gam α)) :=
      MeasureTheory.setIntegral_mono_on hintΞ hintA measurableSet_Icc fun t ht =>
        le_mul_of_one_le_right (hΞnn t ht) (hone t ht)
    exact le_trans h1 hA
  -- the numerical constants
  have hHknn : 0 ≤ ∫ θ' in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f z θ' :=
    integral_nonneg fun θ' => Work.Spaces.HkIntegrand_nonneg α 4 f z θ'
  have hAnn : 0 ≤ ∫ t in Set.Icc (θ / 2) (θ / 2 + π / 4),
      Ξ t * (Real.sin (2 * t)) ^ (-(Work.Spaces.gam α)) :=
    setIntegral_nonneg measurableSet_Icc fun t ht => mul_nonneg (hΞnn t ht)
      (Real.rpow_nonneg (le_of_lt (hsinpos t ht)) _)
  have hBnn : 0 ≤ ∫ t in Set.Icc (θ / 2) (θ / 2 + π / 4),
      Ξ₁ t * (Real.sin (2 * t)) ^ (Work.Spaces.gam α - 2) :=
    setIntegral_nonneg measurableSet_Icc fun t ht => mul_nonneg (hΞ₁nn t ht)
      (Real.rpow_nonneg (le_of_lt (hsinpos t ht)) _)
  have hXnn : 0 ≤ ∫ t in Set.Icc (θ / 2) (θ / 2 + π / 4), Ξ t :=
    setIntegral_nonneg measurableSet_Icc fun t ht => hΞnn t ht
  have hsq : Real.sqrt ((∫ t in Set.Icc (θ / 2) (θ / 2 + π / 4),
        Ξ t * (Real.sin (2 * t)) ^ (-(Work.Spaces.gam α)))
      * (∫ t in Set.Icc (θ / 2) (θ / 2 + π / 4),
        Ξ₁ t * (Real.sin (2 * t)) ^ (Work.Spaces.gam α - 2)))
      ≤ ∫ θ' in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f z θ' := by
    refine le_trans (Real.sqrt_le_sqrt (mul_le_mul hA hB hBnn hHknn)) ?_
    rw [Real.sqrt_mul_self hHknn]
  have hcoef : 2 / ((θ / 2 + π / 4) - θ / 2) ≤ 3 := by
    have hden : (θ / 2 + π / 4) - θ / 2 = π / 4 := by ring
    rw [hden, div_le_iff₀ (by positivity : (0 : ℝ) < π / 4)]
    linarith [Real.pi_gt_three]
  change Ξ θ ≤ 5 * (∫ θ' in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f z θ')
  calc Ξ θ ≤ (2 / ((θ / 2 + π / 4) - θ / 2))
        * (∫ t in Set.Icc (θ / 2) (θ / 2 + π / 4), Ξ t)
        + 2 * Real.sqrt ((∫ t in Set.Icc (θ / 2) (θ / 2 + π / 4),
            Ξ t * (Real.sin (2 * t)) ^ (-(Work.Spaces.gam α)))
          * (∫ t in Set.Icc (θ / 2) (θ / 2 + π / 4),
            Ξ₁ t * (Real.sin (2 * t)) ^ (Work.Spaces.gam α - 2))) := hdev
    _ ≤ 3 * (∫ θ' in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f z θ')
        + 2 * (∫ θ' in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f z θ') :=
        add_le_add (mul_le_mul hcoef hΞint hXnn (by norm_num)) (by linarith)
    _ = 5 * (∫ θ' in Work.Spaces.Iθ, Work.Spaces.HkIntegrand α 4 f z θ') := by ring


end Work.FTS.TransportS.T2SupB2
