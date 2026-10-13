/-
# `Work.FTS.EllSol.EllPkgAux.mollKernelAux`

Auxiliary lemmas for the two-dimensional kernel-moment limit `mollKernelLimit`: the parabolic
change of variables for the derivative kernel `sKerd t`, the elementary fact
`z ∉ [-1,1] → 1 ≤ |z|`, and the main analytic estimate `mollKernel_aux` (the double
convolution of a `C²` function against `sKerd t ⊗ sKerd t` converges to the mixed second
partial derivative).

The proof of `mollKernel_aux` is an explicit second-order Taylor expansion; the two moment
identities `∫ sKerd t = 0` and `∫ u * sKerd t u = -1` (from `sKerdFacts`) make the `u²`- and
`v²`-terms of the expansion die and leave exactly the mixed term, while the Taylor remainder
is `o(t²)` uniformly on the compact support of the kernel (`secondOrderRem_real`).
-/
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Submission.Work.FTS.EllSol.EllPkgAux.MollFatouAux
import Submission.Work.FTS.EllSol.EllPkgAux.sKerdFacts
import Submission.Work.FTS.EllSol.EllPkgAux.secondOrderRem

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.EllSol.EllPkgAux

set_option maxHeartbeats 1000000

lemma sKerd_scale_int {t : ℝ} (ht : 0 < t)
    (hsc : ∀ t : ℝ, 0 < t → ∀ u : ℝ, sKerd t u = (1 / t ^ 2) * sKerd 1 (u / t)) (Φ : ℝ → ℝ) :
    (∫ u : ℝ, sKerd t u * Φ u) = (1 / t) * ∫ w : ℝ, sKerd 1 w * Φ (t * w) := by
  have h1 : ∀ u : ℝ, sKerd t u * Φ u
      = (1 / t ^ 2) * (sKerd 1 (t⁻¹ * u) * Φ (t * (t⁻¹ * u))) := by
    intro u
    have hdiv : u / t = t⁻¹ * u := by rw [div_eq_inv_mul]
    have htu : t * (t⁻¹ * u) = u := by field_simp
    rw [hsc t ht u, hdiv, htu]
    ring
  have h2 : (∫ u : ℝ, (1 / t ^ 2) * (sKerd 1 (t⁻¹ * u) * Φ (t * (t⁻¹ * u))))
      = (1 / t ^ 2) * (∫ u : ℝ, sKerd 1 (t⁻¹ * u) * Φ (t * (t⁻¹ * u))) := by
    rw [MeasureTheory.integral_const_mul]
  have h3 : (∫ u : ℝ, sKerd 1 (t⁻¹ * u) * Φ (t * (t⁻¹ * u)))
      = |(t⁻¹)⁻¹| • ∫ w : ℝ, sKerd 1 w * Φ (t * w) :=
    MeasureTheory.Measure.integral_comp_mul_left (fun w : ℝ => sKerd 1 w * Φ (t * w)) (t⁻¹)
  have h4 : (1 / t ^ 2) * (|(t⁻¹)⁻¹| • ∫ w : ℝ, sKerd 1 w * Φ (t * w))
      = (1 / t) * ∫ w : ℝ, sKerd 1 w * Φ (t * w) := by
    rw [inv_inv, abs_of_pos ht, smul_eq_mul]
    have : t * t⁻¹ ^ 2 = t⁻¹ := by rw [sq, ← mul_assoc, mul_inv_cancel₀ (ne_of_gt ht), one_mul]
    rw [show (1 / t ^ 2) * (t * ∫ w : ℝ, sKerd 1 w * Φ (t * w)) = t * t⁻¹ ^ 2 * (∫ w : ℝ, sKerd 1 w * Φ (t * w)) by
          rw [div_eq_mul_inv, inv_pow]; ring, this, one_div]
  calc (∫ u : ℝ, sKerd t u * Φ u)
      = ∫ u : ℝ, (1 / t ^ 2) * (sKerd 1 (t⁻¹ * u) * Φ (t * (t⁻¹ * u))) :=
        integral_congr_ae (Eventually.of_forall h1)
    _ = (1 / t ^ 2) * (∫ u : ℝ, sKerd 1 (t⁻¹ * u) * Φ (t * (t⁻¹ * u))) := h2
    _ = (1 / t ^ 2) * (|(t⁻¹)⁻¹| • ∫ w : ℝ, sKerd 1 w * Φ (t * w)) := by rw [h3]
    _ = (1 / t) * ∫ w : ℝ, sKerd 1 w * Φ (t * w) := h4

/-- `z ∉ [-1,1]` implies `1 ≤ |z|`. -/
lemma one_le_abs_of_notMem_Icc {z : ℝ} (hz : z ∉ Set.Icc (-1:ℝ) 1) : 1 ≤ |z| := by
  rw [Set.mem_Icc] at hz
  by_cases h : z < -1
  · rw [abs_of_nonpos (by linarith)]; linarith
  · have h2 : 1 < z := by
      by_contra hc
      exact hz ⟨by linarith, by linarith⟩
    rw [abs_of_pos (by linarith)]; linarith


lemma mollKernel_aux
    {F : ℝ × ℝ → ℝ} {U : Set (ℝ × ℝ)} {x y : ℝ} (hU : IsOpen U) (hxy : (x, y) ∈ U)
    (hF : ContDiffOn ℝ 2 F U) :
    Tendsto (fun t : ℝ => ∫ u : ℝ, sKerd t u * (∫ v : ℝ, sKerd t v * F (x-u, y-v)))
      (nhdsWithin (0:ℝ) (Ioi 0)) (nhds ((fderiv ℝ (fderiv ℝ F) (x,y) (1,0)) (0,1))) := by
  obtain ⟨hηcont, hηcpt, hηvan, hη0, hη1, hηI, hηI1, hηI2, hηscale⟩ := sKerdFacts
  set p : ℝ × ℝ := (x, y) with hp
  have hpU : U ∈ 𝓝 p := by rw [hp]; exact hU.mem_nhds hxy
  have hF2 : ContDiffAt ℝ 2 F p := hF.contDiffAt hpU
  have hsym : IsSymmSndFDerivAt ℝ F p := hF2.isSymmSndFDerivAt (by simp)
  have hFcontU : ContinuousOn F U := hF.continuousOn
  obtain ⟨r, hr0, hru⟩ : ∃ r : ℝ, 0 < r ∧ Metric.ball p r ⊆ U := Metric.mem_nhds_iff.mp hpU
  set c1 : ℝ := (fderiv ℝ F p) ((1:ℝ),(0:ℝ)) with hc1
  set c2 : ℝ := (fderiv ℝ F p) ((0:ℝ),(1:ℝ)) with hc2
  set Aa : ℝ := ((fderiv ℝ (fderiv ℝ F) p) ((1:ℝ),(0:ℝ))) ((1:ℝ),(0:ℝ)) with hAa
  set Bb : ℝ := ((fderiv ℝ (fderiv ℝ F) p) ((1:ℝ),(0:ℝ))) ((0:ℝ),(1:ℝ)) with hBb
  set Dd : ℝ := ((fderiv ℝ (fderiv ℝ F) p) ((0:ℝ),(1:ℝ))) ((0:ℝ),(1:ℝ)) with hDd
  set M0 : ℝ := ∫ u : ℝ, sKerd 1 u with hM0
  set M1 : ℝ := ∫ u : ℝ, u * sKerd 1 u with hM1
  set M2 : ℝ := ∫ u : ℝ, u ^ 2 * sKerd 1 u with hM2
  have hM0v : M0 = 0 := hM0.trans hη0
  have hM1v : M1 = -1 := hM1.trans hη1
  set A0 : ℝ := ∫ w : ℝ, |sKerd 1 w| with hA0
  set A2 : ℝ := ∫ w : ℝ, w ^ 2 * |sKerd 1 w| with hA2
  have hA0int : Integrable (fun w : ℝ => |sKerd 1 w|) := hηI.abs
  have hA2int : Integrable (fun w : ℝ => w ^ 2 * |sKerd 1 w|) := by
    refine hηI2.abs.congr ?_
    filter_upwards with u
    rw [abs_mul, abs_of_nonneg (sq_nonneg u)]
  have hA0nn : 0 ≤ A0 := integral_nonneg fun w => abs_nonneg (sKerd 1 w)
  have hA2nn : 0 ≤ A2 := integral_nonneg fun w => mul_nonneg (sq_nonneg w) (abs_nonneg (sKerd 1 w))
  have poly_intble : ∀ (α β γ : ℝ), Integrable (fun z : ℝ => sKerd 1 z * (α + β * z + γ * z^2)) := by
    intro α β γ
    have h1 : Integrable (fun z : ℝ => α * sKerd 1 z) := hηI.const_mul α
    have h2 : Integrable (fun z : ℝ => β * (z * sKerd 1 z)) := hηI1.const_mul β
    have h3 : Integrable (fun z : ℝ => γ * (z^2 * sKerd 1 z)) := hηI2.const_mul γ
    have h := h1.add (h2.add h3)
    refine h.congr ?_
    filter_upwards with z
    simp only [Pi.add_apply]
    ring
  have poly_int : ∀ (α β γ : ℝ),
      (∫ z : ℝ, sKerd 1 z * (α + β * z + γ * z^2)) = α * M0 + β * M1 + γ * M2 := by
    intro α β γ
    have h1 : Integrable (fun z : ℝ => α * sKerd 1 z) := hηI.const_mul α
    have h2 : Integrable (fun z : ℝ => β * (z * sKerd 1 z)) := hηI1.const_mul β
    have h3 : Integrable (fun z : ℝ => γ * (z^2 * sKerd 1 z)) := hηI2.const_mul γ
    have hfunc : (∫ z : ℝ, sKerd 1 z * (α + β * z + γ * z^2))
        = ∫ z : ℝ, α * sKerd 1 z + (β * (z * sKerd 1 z) + γ * (z^2 * sKerd 1 z)) := by
      refine integral_congr_ae (Eventually.of_forall fun z => ?_)
      ring
    have hstep2 : (∫ z : ℝ, α * sKerd 1 z + (β * (z * sKerd 1 z) + γ * (z^2 * sKerd 1 z)))
        = (∫ z : ℝ, α * sKerd 1 z)
          + (∫ z : ℝ, β * (z * sKerd 1 z) + γ * (z^2 * sKerd 1 z)) := by
      simpa using MeasureTheory.integral_add h1 (h2.add h3)
    have hstep3 : (∫ z : ℝ, β * (z * sKerd 1 z) + γ * (z^2 * sKerd 1 z))
        = (∫ z : ℝ, β * (z * sKerd 1 z)) + (∫ z : ℝ, γ * (z^2 * sKerd 1 z)) := by
      simpa using MeasureTheory.integral_add h2 h3
    have hsum : (∫ z : ℝ, sKerd 1 z * (α + β * z + γ * z^2))
        = (∫ z : ℝ, α * sKerd 1 z)
          + ((∫ z : ℝ, β * (z * sKerd 1 z)) + (∫ z : ℝ, γ * (z^2 * sKerd 1 z))) := by
      rw [hfunc, hstep2, hstep3]
    rw [hsum, MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul,
      MeasureTheory.integral_const_mul, ← hM0, ← hM1, ← hM2]
    ring
  rw [Metric.tendsto_nhdsWithin_nhds]
  intro ε hε
  set Kc : ℝ := 4 * A0 * A2 + 1 with hKc
  have hKcpos : 0 < Kc := by
    rw [hKc]
    have : 0 ≤ 4 * A0 * A2 := by positivity
    linarith
  set εt : ℝ := ε / (2 * Kc) with hεt
  have hεtpos : 0 < εt := by rw [hεt]; positivity
  obtain ⟨δ0, hδ0pos, hδ0⟩ := secondOrderRem_real (f := F) hF2 εt hεtpos
  refine ⟨min r δ0, lt_min hr0 hδ0pos, ?_⟩
  intro t ht htdist
  have ht0 : 0 < t := ht
  have htmin : t < min r δ0 := by rwa [Real.dist_eq, sub_zero, abs_of_pos ht0] at htdist
  have htr : t < r := lt_of_lt_of_le htmin (min_le_left _ _)
  have htδ : t < δ0 := lt_of_lt_of_le htmin (min_le_right _ _)
  have habs1 : ∀ w : ℝ, sKerd 1 w ≠ 0 → |w| < 1 := fun w hw => not_le.mp fun h => hw (hηvan w h)
  -- Taylor polynomial and remainder
  obtain ⟨Tayl, hTayl⟩ : ∃ T : ℝ → ℝ → ℝ, T = fun w z => F p + (-(t*w))*c1 + (-(t*z))*c2
      + (1/2)*(t^2*w^2*Aa + 2*t^2*w*z*Bb + t^2*z^2*Dd) := ⟨_, rfl⟩
  obtain ⟨Rm, hRm⟩ : ∃ R : ℝ → ℝ → ℝ, R = fun w z => F (x - t*w, y - t*z) - Tayl w z := ⟨_, rfl⟩
  -- expansions
  have hlin (w z : ℝ) : (fderiv ℝ F p) (-(t*w), -(t*z)) = (-(t*w))*c1 + (-(t*z))*c2 := by
    have hξe : (-(t*w), -(t*z)) = (-(t*w)) • ((1:ℝ),(0:ℝ)) + (-(t*z)) • ((0:ℝ),(1:ℝ)) := by
      ext <;> simp
    rw [hξe, map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul, ← hc1, ← hc2]
  have hquad (w z : ℝ) : ((fderiv ℝ (fderiv ℝ F) p) (-(t*w), -(t*z))) (-(t*w), -(t*z))
      = t^2*w^2*Aa + 2*(t^2*w*z*Bb) + t^2*z^2*Dd := by
    have hexp : ((fderiv ℝ (fderiv ℝ F) p) (-(t*w), -(t*z))) (-(t*w), -(t*z))
        = t^2*w^2 * (((fderiv ℝ (fderiv ℝ F) p) ((1:ℝ),(0:ℝ))) ((1:ℝ),(0:ℝ)))
          + t^2*w*z * (((fderiv ℝ (fderiv ℝ F) p) ((1:ℝ),(0:ℝ))) ((0:ℝ),(1:ℝ)))
          + t^2*z*w * (((fderiv ℝ (fderiv ℝ F) p) ((0:ℝ),(1:ℝ))) ((1:ℝ),(0:ℝ)))
          + t^2*z^2 * (((fderiv ℝ (fderiv ℝ F) p) ((0:ℝ),(1:ℝ))) ((0:ℝ),(1:ℝ))) := by
      have hξe : (-(t*w), -(t*z)) = (-(t*w)) • ((1:ℝ),(0:ℝ)) + (-(t*z)) • ((0:ℝ),(1:ℝ)) := by
        ext <;> simp
      simp only [hξe, map_add, map_smul, add_apply, smul_apply, smul_eq_mul]
      ring_nf
    rw [hexp, hsym.eq ((0:ℝ),(1:ℝ)) ((1:ℝ),(0:ℝ)), ← hAa, ← hBb, ← hDd]
    ring
  have hTay_eq (w z : ℝ) : Rm w z = F (x - t*w, y - t*z) - F p
      - ((-(t*w))*c1 + (-(t*z))*c2)
      - (1/2)*(t^2*w^2*Aa + 2*(t^2*w*z*Bb) + t^2*z^2*Dd) := by
    simp only [hRm, hTayl]; ring
  have hξnorm (w z : ℝ) : ‖((-(t*w), -(t*z)) : ℝ × ℝ)‖^2 ≤ (2 * t^2) * (w^2 + z^2) := by
    rw [Prod.norm_def]
    simp only [Real.norm_eq_abs, abs_neg, abs_mul, abs_of_pos ht0]
    have h1 : max (t*|w|) (t*|z|) ≤ t * (|w| + |z|) := by
      rw [max_le_iff]
      constructor <;> nlinarith [abs_nonneg w, abs_nonneg z, ht0.le]
    have h1nn : 0 ≤ max (t*|w|) (t*|z|) :=
      le_trans (by positivity) (le_max_left _ _)
    have h3 : (|w| + |z|)^2 ≤ 2 * (w^2 + z^2) := by
      nlinarith [sq_nonneg (|w| - |z|), sq_abs w, sq_abs z, abs_nonneg w, abs_nonneg z]
    have h2 : (t * (|w| + |z|))^2 ≤ 2 * t^2 * (w^2 + z^2) := by
      have h := mul_le_mul_of_nonneg_left h3 (sq_nonneg t)
      nlinarith [h]
    calc (max (t*|w|) (t*|z|))^2 ≤ (t * (|w| + |z|))^2 := by
          simpa [sq] using mul_self_le_mul_self h1nn h1
      _ ≤ 2 * t^2 * (w^2 + z^2) := h2
  have hRmb : ∀ w z : ℝ, |w| < 1 → |z| < 1 → |Rm w z| ≤ (2 * εt * t^2) * (w^2 + z^2) := by
    intro w z hw hz
    have hξ : ‖((-(t*w), -(t*z)) : ℝ × ℝ)‖ < δ0 := by
      rw [Prod.norm_def]
      simp only [Real.norm_eq_abs, abs_neg, abs_mul, abs_of_pos ht0]
      rw [max_lt_iff]
      constructor
      · have h := mul_lt_mul_of_pos_left hw ht0
        rw [mul_one] at h
        linarith
      · have h := mul_lt_mul_of_pos_left hz ht0
        rw [mul_one] at h
        linarith
    have hkey := hδ0 (-(t*w), -(t*z)) hξ
    have hpt : p + (-(t*w), -(t*z)) = (x - t*w, y - t*z) := by
      rw [hp]; ext <;> simp [sub_eq_add_neg]
    rw [hpt, hlin w z, hquad w z] at hkey
    have hnn : ‖((-(t*w), -(t*z)) : ℝ × ℝ)‖^2 ≤ (2 * t^2) * (w^2 + z^2) := hξnorm w z
    have hfin : ‖F (x - t*w, y - t*z) - F p - ((-(t*w))*c1 + (-(t*z))*c2)
        - (1/2)*(t^2*w^2*Aa + 2*(t^2*w*z*Bb) + t^2*z^2*Dd)‖
        ≤ (2 * εt * t^2) * (w^2 + z^2) := by
      have h1 : εt * ‖((-(t*w), -(t*z)) : ℝ × ℝ)‖^2 ≤ εt * ((2 * t^2) * (w^2 + z^2)) :=
        mul_le_mul_of_nonneg_left hnn hεtpos.le
      rw [show (2 * εt * t^2) * (w^2 + z^2) = εt * (2 * t^2 * (w^2 + z^2)) by ring]
      exact hkey.trans h1
    rw [hTay_eq w z, ← Real.norm_eq_abs]
    exact hfin
  -- integrability of the Taylor part (inner) and its integral
  have hTint (w : ℝ) : Integrable (fun z : ℝ => sKerd 1 z * Tayl w z) := by
    have h := poly_intble (F p + (-(t*w))*c1 + (1/2)*(t^2*w^2*Aa))
      ((-(t))*c2 + (1/2)*(2*t^2*w*Bb)) ((1/2)*(t^2*Dd))
    refine h.congr ?_
    filter_upwards with z
    simp only [hTayl]
    ring
  have hTayl_eval (w : ℝ) :
      (∫ z : ℝ, sKerd 1 z * Tayl w z) = t*c2 - t^2*w*Bb + (1/2)*t^2*Dd*M2 := by
    have h := poly_int (F p + (-(t*w))*c1 + (1/2)*(t^2*w^2*Aa))
      ((-(t))*c2 + (1/2)*(2*t^2*w*Bb)) ((1/2)*(t^2*Dd))
    have heq : (fun z : ℝ => sKerd 1 z * Tayl w z)
        = fun z : ℝ => sKerd 1 z * ((F p + (-(t*w))*c1 + (1/2)*(t^2*w^2*Aa))
            + ((-(t))*c2 + (1/2)*(2*t^2*w*Bb)) * z + ((1/2)*(t^2*Dd)) * z^2) := by
      funext z; simp only [hTayl]; ring
    rw [heq, h, hM0v, hM1v]
    ring
  -- continuity of the `F`-pullback on the box
  have hbox_cont (w : ℝ) (hw : |w| < 1) :
      ContinuousOn (fun z : ℝ => F (x - t*w, y - t*z)) (Set.Icc (-1:ℝ) 1) := by
    have himg : Set.MapsTo (fun z : ℝ => ((x - t*w), (y - t*z))) (Set.Icc (-1:ℝ) 1) (Metric.ball p r) := by
      intro z hz
      have hzw : |z| ≤ 1 := abs_le.mpr hz
      rw [Metric.mem_ball, dist_eq_norm, Prod.norm_def, hp]
      simp only [Prod.fst_sub, Prod.snd_sub, sub_self, sub_zero, Real.norm_eq_abs]
      rw [max_lt_iff]
      constructor
      · rw [show x - t*w - x = -(t*w) by ring, abs_neg, abs_mul, abs_of_pos ht0]
        have h := mul_lt_mul_of_pos_left hw ht0
        rw [mul_one] at h
        linarith
      · rw [show y - t*z - y = -(t*z) by ring, abs_neg, abs_mul, abs_of_pos ht0]
        nlinarith [abs_nonneg z, ht0, htr]
    have hmap : ContinuousOn (fun z : ℝ => ((x - t*w), (y - t*z))) (Set.Icc (-1:ℝ) 1) := by fun_prop
    have h2 := (hFcontU.mono hru).comp hmap himg
    simpa [Function.comp_def] using h2
  -- integrability of the remainder against η
  have hRint (w : ℝ) (hw : |w| < 1) : Integrable (fun z : ℝ => sKerd 1 z * Rm w z) := by
    have hdom : Integrable (fun z : ℝ => |sKerd 1 z| * ((2 * εt * t^2) * (w^2 + z^2))) := by
      have heq : (fun z : ℝ => |sKerd 1 z| * ((2 * εt * t^2) * (w^2 + z^2)))
          = fun z : ℝ => ((2 * εt * t^2) * w^2) * |sKerd 1 z| + (2 * εt * t^2) * (z^2 * |sKerd 1 z|) := by
        funext z; ring
      rw [heq]
      exact (hA0int.const_mul _).add (hA2int.const_mul _)
    refine Integrable.mono' hdom ?_ ?_
    · have hcontOn' : ContinuousOn (fun z : ℝ => sKerd 1 z * (F (x - t*w, y - t*z) - Tayl w z))
          (Set.Icc (-1:ℝ) 1) :=
        hηcont.continuousOn.mul ((hbox_cont w hw).sub (by simp only [hTayl]; fun_prop))
      have hcontOn : ContinuousOn (fun z : ℝ => sKerd 1 z * Rm w z) (Set.Icc (-1:ℝ) 1) := by
        have hEq : (fun z : ℝ => sKerd 1 z * Rm w z)
            = fun z : ℝ => sKerd 1 z * (F (x - t*w, y - t*z) - Tayl w z) := by
          funext z; simp only [hRm]
        rw [hEq]; exact hcontOn'
      have h1 : AEStronglyMeasurable
          (Set.indicator (Set.Icc (-1:ℝ) 1) (fun z : ℝ => sKerd 1 z * Rm w z)) volume :=
        (aestronglyMeasurable_indicator_iff measurableSet_Icc).mpr
          (hcontOn.aestronglyMeasurable (μ := volume) measurableSet_Icc)
      refine h1.congr ?_
      filter_upwards with z
      by_cases hz : z ∈ Set.Icc (-1:ℝ) 1
      · rw [Set.indicator_of_mem hz]
      · rw [Set.indicator_of_notMem hz, hηvan z (one_le_abs_of_notMem_Icc hz), zero_mul]
    · filter_upwards with z
      by_cases hz : |z| < 1
      · rw [norm_mul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left (hRmb w z hw hz) (abs_nonneg _)
      · rw [hηvan z (not_lt.mp hz), zero_mul, norm_zero]
        exact mul_nonneg (abs_nonneg _) (by positivity)
  -- inner decomposition and the inner bound
  have hinner_eq (w : ℝ) (hw : |w| < 1) :
      (∫ z : ℝ, sKerd 1 z * F (x - t*w, y - t*z))
        = (∫ z : ℝ, sKerd 1 z * Tayl w z) + (∫ z : ℝ, sKerd 1 z * Rm w z) := by
    have hpt : (∫ z : ℝ, sKerd 1 z * F (x - t*w, y - t*z))
        = ∫ z : ℝ, sKerd 1 z * Tayl w z + sKerd 1 z * Rm w z := by
      refine integral_congr_ae (Eventually.of_forall fun z => ?_)
      simp only [hRm]; ring
    rw [hpt]
    simpa using MeasureTheory.integral_add (hTint w) (hRint w hw)
  have hRmIn (w : ℝ) (hw : |w| < 1) :
      ‖∫ z : ℝ, sKerd 1 z * Rm w z‖ ≤ (2 * εt * t^2) * (A0 * w^2 + A2) := by
    have hdom : Integrable (fun z : ℝ => |sKerd 1 z| * ((2 * εt * t^2) * (w^2 + z^2))) := by
      have heq : (fun z : ℝ => |sKerd 1 z| * ((2 * εt * t^2) * (w^2 + z^2)))
          = fun z : ℝ => ((2 * εt * t^2) * w^2) * |sKerd 1 z| + (2 * εt * t^2) * (z^2 * |sKerd 1 z|) := by
        funext z; ring
      rw [heq]
      exact (hA0int.const_mul _).add (hA2int.const_mul _)
    calc ‖∫ z : ℝ, sKerd 1 z * Rm w z‖
        ≤ ∫ z : ℝ, ‖sKerd 1 z * Rm w z‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ z : ℝ, |sKerd 1 z| * ((2 * εt * t^2) * (w^2 + z^2)) := by
          refine MeasureTheory.integral_mono_of_nonneg ?_ hdom ?_
          · filter_upwards with z; exact norm_nonneg _
          · filter_upwards with z
            by_cases hz : |z| < 1
            · rw [norm_mul, Real.norm_eq_abs]
              exact mul_le_mul_of_nonneg_left (hRmb w z hw hz) (abs_nonneg _)
            · rw [hηvan z (not_lt.mp hz), zero_mul, norm_zero]
              exact mul_nonneg (abs_nonneg _) (by positivity)
      _ = (2 * εt * t^2) * (A0 * w^2 + A2) := by
          rw [show (fun z : ℝ => |sKerd 1 z| * ((2 * εt * t^2) * (w^2 + z^2)))
              = fun z : ℝ => ((2 * εt * t^2) * w^2) * |sKerd 1 z| + (2 * εt * t^2) * (z^2 * |sKerd 1 z|) from by
                funext z; ring]
          rw [MeasureTheory.integral_add (hA0int.const_mul _) (hA2int.const_mul _),
            MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul, ← hA0, ← hA2]
          ring
  -- continuity on the square, measurability of the pair function
  have hsq_cont : ContinuousOn (fun q : ℝ × ℝ => F (x - t*q.1, y - t*q.2))
      (Set.Icc (-1:ℝ) 1 ×ˢ Set.Icc (-1:ℝ) 1) := by
    have himg : Set.MapsTo (fun q : ℝ × ℝ => ((x - t*q.1), (y - t*q.2)))
        (Set.Icc (-1:ℝ) 1 ×ˢ Set.Icc (-1:ℝ) 1) (Metric.ball p r) := by
      intro q hq
      rw [Set.mem_prod] at hq
      rw [Metric.mem_ball, dist_eq_norm, Prod.norm_def, hp]
      simp only [Prod.fst_sub, Prod.snd_sub, sub_self, sub_zero, Real.norm_eq_abs]
      rw [max_lt_iff]
      constructor
      · rw [show x - t*q.1 - x = -(t*q.1) by ring, abs_neg, abs_mul, abs_of_pos ht0]
        have hq1 : |q.1| ≤ 1 := abs_le.mpr hq.1
        nlinarith [abs_nonneg q.1, ht0, htr]
      · rw [show y - t*q.2 - y = -(t*q.2) by ring, abs_neg, abs_mul, abs_of_pos ht0]
        have hq2 : |q.2| ≤ 1 := abs_le.mpr hq.2
        nlinarith [abs_nonneg q.2, ht0, htr]
    have hmap : ContinuousOn (fun q : ℝ × ℝ => ((x - t*q.1), (y - t*q.2)))
        (Set.Icc (-1:ℝ) 1 ×ˢ Set.Icc (-1:ℝ) 1) := by fun_prop
    have h2 := (hFcontU.mono hru).comp hmap himg
    simpa [Function.comp_def] using h2
  have hpair_meas : AEStronglyMeasurable
      (fun q : ℝ × ℝ => sKerd 1 q.1 * (sKerd 1 q.2 * Rm q.1 q.2)) (volume.prod volume) := by
    have hcont : ContinuousOn (fun q : ℝ × ℝ => sKerd 1 q.1 * (sKerd 1 q.2 * Rm q.1 q.2))
        (Set.Icc (-1:ℝ) 1 ×ˢ Set.Icc (-1:ℝ) 1) := by
      refine ContinuousOn.mul ((hηcont.comp continuous_fst).continuousOn) ?_
      refine ContinuousOn.mul ((hηcont.comp continuous_snd).continuousOn) ?_
      have hRmq : (fun q : ℝ × ℝ => Rm q.1 q.2)
          = fun q : ℝ × ℝ => F (x - t*q.1, y - t*q.2) - Tayl q.1 q.2 := by
        funext q; simp only [hRm]
      rw [hRmq]
      exact hsq_cont.sub (by simp only [hTayl]; fun_prop)
    have h1 : AEStronglyMeasurable
        (Set.indicator (Set.Icc (-1:ℝ) 1 ×ˢ Set.Icc (-1:ℝ) 1)
          (fun q : ℝ × ℝ => sKerd 1 q.1 * (sKerd 1 q.2 * Rm q.1 q.2))) (volume.prod volume) :=
      (aestronglyMeasurable_indicator_iff (measurableSet_Icc.prod measurableSet_Icc)).mpr
        (hcont.aestronglyMeasurable (μ := volume.prod volume) (measurableSet_Icc.prod measurableSet_Icc))
    refine h1.congr ?_
    filter_upwards with q
    by_cases hq : q ∈ Set.Icc (-1:ℝ) 1 ×ˢ Set.Icc (-1:ℝ) 1
    · rw [Set.indicator_of_mem hq]
    · rw [Set.indicator_of_notMem hq]
      rw [Set.mem_prod] at hq
      by_cases hq1 : q.1 ∈ Set.Icc (-1:ℝ) 1
      · have hq2 : q.2 ∉ Set.Icc (-1:ℝ) 1 := fun hc => hq ⟨hq1, hc⟩
        have h1 : 1 ≤ |q.2| := one_le_abs_of_notMem_Icc hq2
        rw [hηvan q.2 h1]; ring
      · have h1 : 1 ≤ |q.1| := one_le_abs_of_notMem_Icc hq1
        rw [hηvan q.1 h1, zero_mul]
  -- integrability at the outer level
  have hTaylwint : Integrable (fun w : ℝ => sKerd 1 w * (t*c2 - t^2*w*Bb + (1/2)*t^2*Dd*M2)) := by
    have h := poly_intble (t*c2 + (1/2)*t^2*Dd*M2) (-(t^2*Bb)) 0
    have h' : Integrable (fun w : ℝ => sKerd 1 w * (t*c2 + (1/2)*t^2*Dd*M2 + -(t^2*Bb) * w)) := by
      simpa using h
    refine h'.congr ?_
    filter_upwards with w; ring
  have constD : Integrable (fun w : ℝ => |sKerd 1 w| * ((2 * εt * t^2) * (A0 * w^2 + A2))) := by
    have heq : (fun w : ℝ => |sKerd 1 w| * ((2 * εt * t^2) * (A0 * w^2 + A2)))
        = fun w : ℝ => ((2 * εt * t^2) * A0) * (w^2 * |sKerd 1 w|)
            + ((2 * εt * t^2) * A2) * |sKerd 1 w| := by
      funext w; ring
    rw [heq]
    exact (hA2int.const_mul _).add (hA0int.const_mul _)
  have hRwint : Integrable (fun w : ℝ => sKerd 1 w * (∫ z : ℝ, sKerd 1 z * Rm w z)) := by
    refine Integrable.mono' constD ?_ ?_
    · have hpi := hpair_meas.integral_prod_right' (μ := volume) (ν := volume)
      refine hpi.congr ?_
      filter_upwards with w
      rw [MeasureTheory.integral_const_mul]
    · filter_upwards with w
      by_cases hw : |w| < 1
      · rw [norm_mul, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left (hRmIn w hw) (abs_nonneg _)
      · rw [hηvan w (not_lt.mp hw), zero_mul, norm_zero]
        exact mul_nonneg (abs_nonneg _) (by positivity)
  have heval : (∫ w : ℝ, sKerd 1 w * (t*c2 - t^2*w*Bb + (1/2)*t^2*Dd*M2)) = t^2*Bb := by
    have h := poly_int (t*c2 + (1/2)*t^2*Dd*M2) (-(t^2*Bb)) 0
    have h' : (∫ w : ℝ, sKerd 1 w * (t*c2 + (1/2)*t^2*Dd*M2 + -(t^2*Bb) * w))
        = (t*c2 + (1/2)*t^2*Dd*M2) * M0 + (-(t^2*Bb)) * M1 := by
      simpa using h
    have heq : (fun w : ℝ => sKerd 1 w * (t*c2 - t^2*w*Bb + (1/2)*t^2*Dd*M2))
        = fun w : ℝ => sKerd 1 w * (t*c2 + (1/2)*t^2*Dd*M2 + -(t^2*Bb) * w) := by
      funext w; ring
    rw [heq, h', hM0v, hM1v]
    ring
  -- the decomposition
  have hdec : (∫ w : ℝ, sKerd 1 w * (∫ z : ℝ, sKerd 1 z * F (x - t*w, y - t*z)))
      = t^2 * Bb + (∫ w : ℝ, sKerd 1 w * (∫ z : ℝ, sKerd 1 z * Rm w z)) := by
    have hpt : ∀ w : ℝ, sKerd 1 w * (∫ z : ℝ, sKerd 1 z * F (x - t*w, y - t*z))
        = sKerd 1 w * (t*c2 - t^2*w*Bb + (1/2)*t^2*Dd*M2)
          + sKerd 1 w * (∫ z : ℝ, sKerd 1 z * Rm w z) := by
      intro w
      by_cases hw : |w| < 1
      · rw [hinner_eq w hw, hTayl_eval w]; ring
      · rw [hηvan w (not_lt.mp hw)]; ring
    have hmid : (∫ w : ℝ, sKerd 1 w * (∫ z : ℝ, sKerd 1 z * F (x - t*w, y - t*z)))
        = ∫ w : ℝ, (sKerd 1 w * (t*c2 - t^2*w*Bb + (1/2)*t^2*Dd*M2)
            + sKerd 1 w * (∫ z : ℝ, sKerd 1 z * Rm w z)) :=
      MeasureTheory.integral_congr_ae (μ := volume) (Eventually.of_forall hpt)
    have hsplit : (∫ w : ℝ, (sKerd 1 w * (t*c2 - t^2*w*Bb + (1/2)*t^2*Dd*M2)
            + sKerd 1 w * (∫ z : ℝ, sKerd 1 z * Rm w z)))
        = (∫ w : ℝ, sKerd 1 w * (t*c2 - t^2*w*Bb + (1/2)*t^2*Dd*M2))
          + (∫ w : ℝ, sKerd 1 w * (∫ z : ℝ, sKerd 1 z * Rm w z)) := by
      simpa using MeasureTheory.integral_add hTaylwint hRwint
    rw [hmid, hsplit, heval]
  -- the outer bound
  have hRwbd : ‖∫ w : ℝ, sKerd 1 w * (∫ z : ℝ, sKerd 1 z * Rm w z)‖
      ≤ (2 * εt * t^2) * (2 * (A0 * A2)) := by
    calc ‖∫ w : ℝ, sKerd 1 w * (∫ z : ℝ, sKerd 1 z * Rm w z)‖
        ≤ ∫ w : ℝ, ‖sKerd 1 w * (∫ z : ℝ, sKerd 1 z * Rm w z)‖ :=
          norm_integral_le_integral_norm _
      _ ≤ ∫ w : ℝ, |sKerd 1 w| * ((2 * εt * t^2) * (A0 * w^2 + A2)) := by
          refine MeasureTheory.integral_mono_of_nonneg ?_ constD ?_
          · filter_upwards with w; exact norm_nonneg _
          · filter_upwards with w
            by_cases hw : |w| < 1
            · rw [norm_mul, Real.norm_eq_abs]
              exact mul_le_mul_of_nonneg_left (hRmIn w hw) (abs_nonneg _)
            · rw [hηvan w (not_lt.mp hw), zero_mul, norm_zero]
              exact mul_nonneg (abs_nonneg _) (by positivity)
      _ = (2 * εt * t^2) * (2 * (A0 * A2)) := by
          rw [show (fun w : ℝ => |sKerd 1 w| * ((2 * εt * t^2) * (A0 * w^2 + A2)))
              = fun w : ℝ => ((2 * εt * t^2) * A0) * (w^2 * |sKerd 1 w|)
                  + ((2 * εt * t^2) * A2) * |sKerd 1 w| from by funext w; ring]
          rw [MeasureTheory.integral_add (hA2int.const_mul _) (hA0int.const_mul _),
            MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul, ← hA0, ← hA2]
          ring
  -- the scaling identity
  have hI1 : (∫ u : ℝ, sKerd t u * (∫ v : ℝ, sKerd t v * F (x-u, y-v)))
      = (1 / t^2) * ∫ w : ℝ, sKerd 1 w * (∫ z : ℝ, sKerd 1 z * F (x - t*w, y - t*z)) := by
    have hs1 : (∫ u : ℝ, sKerd t u * (∫ v : ℝ, sKerd t v * F (x-u, y-v)))
        = (1/t) * ∫ w : ℝ, sKerd 1 w * (∫ v : ℝ, sKerd t v * F (x - t*w, y - v)) := by
      simpa using sKerd_scale_int ht0 hηscale (fun u => ∫ v : ℝ, sKerd t v * F (x-u, y-v))
    rw [hs1]
    have h2 : (∫ w : ℝ, sKerd 1 w * (∫ v : ℝ, sKerd t v * F (x - t*w, y - v)))
        = ∫ w : ℝ, sKerd 1 w * ((1/t) * ∫ z : ℝ, sKerd 1 z * F (x - t*w, y - t*z)) := by
      refine integral_congr_ae (Eventually.of_forall fun w => ?_)
      have hs2 : (∫ v : ℝ, sKerd t v * F (x - t*w, y - v))
          = (1/t) * ∫ z : ℝ, sKerd 1 z * F (x - t*w, y - t*z) := by
        simpa using sKerd_scale_int ht0 hηscale (fun v => F (x - t*w, y - v))
      show sKerd 1 w * (∫ v : ℝ, sKerd t v * F (x - t*w, y - v))
        = sKerd 1 w * ((1/t) * ∫ z : ℝ, sKerd 1 z * F (x - t*w, y - t*z))
      rw [hs2]
    rw [h2]
    have h2' : (∫ w : ℝ, sKerd 1 w * ((1/t) * ∫ z : ℝ, sKerd 1 z * F (x - t*w, y - t*z)))
        = ∫ w : ℝ, (1/t) * (sKerd 1 w * (∫ z : ℝ, sKerd 1 z * F (x - t*w, y - t*z))) := by
      refine integral_congr_ae (Eventually.of_forall fun w => ?_)
      show sKerd 1 w * ((1/t) * (∫ z : ℝ, sKerd 1 z * F (x - t*w, y - t*z)))
        = (1/t) * (sKerd 1 w * (∫ z : ℝ, sKerd 1 z * F (x - t*w, y - t*z)))
      ring
    rw [h2']
    have h3 : (∫ w : ℝ, (1/t) * (sKerd 1 w * (∫ z : ℝ, sKerd 1 z * F (x - t*w, y - t*z))))
        = (1/t) * ∫ w : ℝ, sKerd 1 w * (∫ z : ℝ, sKerd 1 z * F (x - t*w, y - t*z)) := by
      simpa using MeasureTheory.integral_const_mul (1/t)
        (fun w : ℝ => sKerd 1 w * (∫ z : ℝ, sKerd 1 z * F (x - t*w, y - t*z)))
    rw [h3]
    have hcomb : (1/t) * ((1/t) * ∫ w : ℝ, sKerd 1 w * (∫ z : ℝ, sKerd 1 z * F (x - t*w, y - t*z)))
        = (1/t^2) * ∫ w : ℝ, sKerd 1 w * (∫ z : ℝ, sKerd 1 z * F (x - t*w, y - t*z)) := by
      field_simp
    exact hcomb
  -- conclusion
  rw [hI1, hdec]
  have hfin : (1/t^2) * (t^2*Bb + (∫ w : ℝ, sKerd 1 w * (∫ z : ℝ, sKerd 1 z * Rm w z)))
      = Bb + (1/t^2) * (∫ w : ℝ, sKerd 1 w * (∫ z : ℝ, sKerd 1 z * Rm w z)) := by
    field_simp
  rw [hfin, dist_eq_norm, add_sub_cancel_left, norm_mul, Real.norm_eq_abs,
      abs_of_nonneg (by positivity : (0:ℝ) ≤ 1 / t^2)]
  have hb : (1/t^2) * ‖∫ w : ℝ, sKerd 1 w * (∫ z : ℝ, sKerd 1 z * Rm w z)‖
      ≤ (1/t^2) * ((2 * εt * t^2) * (2 * (A0 * A2))) :=
    mul_le_mul_of_nonneg_left hRwbd (by positivity)
  have hA0A2 : 0 ≤ A0 * A2 := mul_nonneg hA0nn hA2nn
  refine lt_of_le_of_lt hb ?_
  have heq2 : (1/t^2) * ((2 * εt * t^2) * (2 * (A0 * A2))) = 4 * εt * (A0 * A2) := by
    field_simp
    ring
  rw [heq2]
  have hlt : 4 * (A0 * A2) / (2 * (4 * A0 * A2 + 1)) < 1 := by
    rw [div_lt_one (by linarith : (0:ℝ) < 2 * (4 * A0 * A2 + 1))]
    linarith
  have hkey : 4 * (ε / (2 * (4 * A0 * A2 + 1))) * (A0 * A2)
      = ε * (4 * (A0 * A2) / (2 * (4 * A0 * A2 + 1))) := by ring
  rw [hεt, hKc, hkey]
  calc ε * (4 * (A0 * A2) / (2 * (4 * A0 * A2 + 1))) < ε * 1 := mul_lt_mul_of_pos_left hlt hε
    _ = ε := by ring



end Work.FTS.EllSol.EllPkgAux
