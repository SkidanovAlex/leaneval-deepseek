import Mathlib
import Submission.Work.Drive.CurveRatioAux

/-!
# The local behaviour of the diagonal-chord ratio at a regular point

Let `G : ℝ → ℝ × ℝ` be a plane curve with `G'(0) = V ≠ 0`.  For `ε > 0` consider the two points
`p± = G 0 ± ε • rot90 V` on the perpendicular to the tangent line at `G 0`, and the ratio
`x ↦ ratioMap G p₊ p₋ x = (G x - p₊)/(G x - p₋)`, as a complex number the quotient of the two chords
from `p₊` and `p₋` to the point `G x` of the curve.

The lemma below computes the local behaviour of that ratio at `x = 0`:

* just to the right of `0` the ratio has negative imaginary part, just to the left it has positive
  imaginary part (the ratio crosses the negative real axis at `-1`);
* accordingly its argument tends to `-π` from the right and to `π` from the left.

This is the local input for the winding-number computation of the diagonal family of a closed curve.
-/

namespace Work.Drive

open Filter Topology
open scoped Topology ComplexConjugate

theorem curve_ratio_local {G : ℝ → ℝ × ℝ} {V : ℝ × ℝ} (hV : V ≠ 0)
    (hder : HasDerivAt G V 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧
      (∀ x : ℝ, 0 < x → x < δ →
        (ratioMap G (G 0 + ε • rot90 V) (G 0 - ε • rot90 V) x).im < 0) ∧
      (∀ x : ℝ, -δ < x → x < 0 →
        0 < (ratioMap G (G 0 + ε • rot90 V) (G 0 - ε • rot90 V) x).im) ∧
      Filter.Tendsto (fun x : ℝ => (ratioMap G (G 0 + ε • rot90 V) (G 0 - ε • rot90 V) x).arg)
        (nhdsWithin (0:ℝ) (Set.Ioi 0)) (nhds (-Real.pi)) ∧
      Filter.Tendsto (fun x : ℝ => (ratioMap G (G 0 + ε • rot90 V) (G 0 - ε • rot90 V) x).arg)
        (nhdsWithin (0:ℝ) (Set.Iio 0)) (nhds Real.pi) := by
  have hv0 : cpx V ≠ 0 := cpx_ne_zero_iff.mpr hV
  have hεC : (ε : ℂ) ≠ 0 := by exact_mod_cast hε.ne'
  have hεv : (ε:ℂ) * cpx V ≠ 0 := mul_ne_zero hεC hv0
  have hnorm : 0 < Complex.normSq (cpx V) := Complex.normSq_pos.mpr hv0
  set A : ℝ → ℂ := fun x => cpx (G x - G 0) with hA
  set W : ℝ → ℂ := fun x => A x / ((ε:ℂ) * cpx V) with hW
  set S : ℝ → ℝ := fun x => (A x * conj (cpx V)).re with hS
  have hA0 : A 0 = 0 := by simp [hA]
  -- the derivative of `A` at `0`
  have hA_deriv : HasDerivAt A (cpx V) 0 := by
    have h1 : HasDerivAt (fun x : ℝ => G x - G 0) V 0 := hder.sub_const (G 0)
    have h2 := (ContinuousLinearMap.hasFDerivAt cpxCLM).comp_hasDerivAt (0:ℝ) h1
    simpa only [hA, Function.comp_def, cpxCLM_apply] using h2
  -- the derivative of the real pairing `S` at `0`
  have hS_deriv : HasDerivAt S (Complex.normSq (cpx V)) 0 := by
    have h1 := hA_deriv.mul_const (conj (cpx V))
    have h2 := (Complex.reCLM.hasFDerivAt).comp_hasDerivAt (0:ℝ) h1
    have h3 : (cpx V * conj (cpx V)).re = Complex.normSq (cpx V) := by
      rw [Complex.mul_conj, Complex.ofReal_re]
    simpa only [hS, Function.comp_def, Complex.reCLM_apply, h3] using h2
  have hS0 : S 0 = 0 := by simp [hS, hA]
  -- the sign of `S` on the two sides of `0`
  have hSlope : Tendsto (fun t : ℝ => t⁻¹ * S t) (𝓝[≠] (0:ℝ))
      (𝓝 (Complex.normSq (cpx V))) := by
    simpa only [hS0, smul_eq_mul, zero_add, sub_zero] using hS_deriv.tendsto_slope_zero
  have hSlope_pos : ∀ᶠ t in 𝓝[≠] (0:ℝ), 0 < t⁻¹ * S t := by
    have hhalf : Complex.normSq (cpx V)/2 < Complex.normSq (cpx V) := by linarith
    filter_upwards [hSlope.eventually (isOpen_Ioi.mem_nhds hhalf)] with t ht
    linarith
  have hS_pos : ∀ᶠ t in 𝓝[>] (0:ℝ), 0 < S t :=
    eventually_pos_nhdsGT_of_inv_mul_pos hSlope_pos
  have hS_neg : ∀ᶠ t in 𝓝[<] (0:ℝ), S t < 0 :=
    eventually_neg_nhdsLT_of_inv_mul_pos hSlope_pos
  -- `A` and `W` tend to `0`
  have hA_cont : Tendsto A (𝓝 0) (𝓝 0) := by
    have h : Tendsto A (𝓝 0) (𝓝 (A 0)) := hA_deriv.continuousAt
    rwa [hA0] at h
  have hW0 : Tendsto W (𝓝 0) (𝓝 0) := by
    have h : Tendsto (fun x : ℝ => A x / ((ε:ℂ) * cpx V)) (𝓝 0)
        (𝓝 (0 / ((ε:ℂ) * cpx V))) := hA_cont.div tendsto_const_nhds hεv
    rw [zero_div] at h
    rwa [hW]
  -- the normalised ratio tends to `-1`
  have hR_tendsto : Tendsto (fun x => (W x - Complex.I)/(W x + Complex.I)) (𝓝 0) (𝓝 (-1)) := by
    have hct : ContinuousAt (fun w : ℂ => (w - Complex.I)/(w + Complex.I)) 0 :=
      (continuousAt_id.sub continuousAt_const).div (continuousAt_id.add continuousAt_const)
        (by simp)
    have h : Tendsto ((fun w : ℂ => (w - Complex.I)/(w + Complex.I)) ∘ W) (𝓝 0)
        (𝓝 (((0:ℂ) - Complex.I)/((0:ℂ) + Complex.I))) := hct.tendsto.comp hW0
    have hval : ((0:ℂ) - Complex.I)/((0:ℂ) + Complex.I) = -1 := by simp
    rw [hval] at h
    simpa only [Function.comp_def] using h
  -- eventually the denominator does not vanish
  have hev_ne : ∀ᶠ x in 𝓝 (0:ℝ), W x + Complex.I ≠ 0 := by
    have hb : ∀ᶠ x in 𝓝 (0:ℝ), W x ∈ Metric.ball (0:ℂ) 1 :=
      hW0.eventually (Metric.ball_mem_nhds (0:ℂ) one_pos)
    filter_upwards [hb] with x hx h
    have h2 : W x = -Complex.I := by simpa using (add_eq_zero_iff_eq_neg.mp h)
    have h3 : ‖W x‖ < 1 := by simpa [Metric.mem_ball, dist_eq_norm] using hx
    have h4 : ‖W x‖ = 1 := by rw [h2]; simp
    linarith
  -- the two identities used in the computation
  have hratio : ∀ x : ℝ, ratioMap G (G 0 + ε • rot90 V) (G 0 - ε • rot90 V) x
      = (W x - Complex.I)/(W x + Complex.I) := by
    intro x
    rw [curveRatioModel G hv0 hεC x,
      show W x = cpx (G x - G 0)/((ε:ℂ) * cpx V) from by simp [hW, hA]]
  have hReW : ∀ x : ℝ, (W x).re = S x/(ε * Complex.normSq (cpx V)) := by
    intro x
    have h1 : W x = cpx (G x - G 0)/((ε:ℂ) * cpx V) := by simp [hW, hA]
    have h2 : S x = (cpx (G x - G 0) * conj (cpx V)).re := by simp [hS, hA]
    rw [h1, h2]
    exact re_div_ofReal_mul _ hv0 hε.ne'
  -- the sign of the imaginary part on the two sides
  have h_ev_im_neg : ∀ᶠ x in 𝓝[>] (0:ℝ),
      (ratioMap G (G 0 + ε • rot90 V) (G 0 - ε • rot90 V) x).im < 0 := by
    filter_upwards [hS_pos, hev_ne.filter_mono nhdsWithin_le_nhds] with x hSx hne
    rw [hratio x, sub_I_div_add_I_im, hReW x]
    have hden : 0 < Complex.normSq (W x + Complex.I) := Complex.normSq_pos.mpr hne
    have hpos : 0 < S x / (ε * Complex.normSq (cpx V)) := div_pos hSx (mul_pos hε hnorm)
    exact div_neg_of_neg_of_pos (by linarith) hden
  have h_ev_im_pos : ∀ᶠ x in 𝓝[<] (0:ℝ),
      0 < (ratioMap G (G 0 + ε • rot90 V) (G 0 - ε • rot90 V) x).im := by
    filter_upwards [hS_neg, hev_ne.filter_mono nhdsWithin_le_nhds] with x hSx hne
    rw [hratio x, sub_I_div_add_I_im, hReW x]
    have hden : 0 < Complex.normSq (W x + Complex.I) := Complex.normSq_pos.mpr hne
    have hneg : S x / (ε * Complex.normSq (cpx V)) < 0 :=
      div_neg_of_neg_of_pos hSx (mul_pos hε hnorm)
    exact div_pos (by linarith) hden
  -- the two limits of the argument
  have hR_ratio : Tendsto (fun x => ratioMap G (G 0 + ε • rot90 V) (G 0 - ε • rot90 V) x)
      (𝓝 0) (𝓝 (-1)) :=
    Filter.Tendsto.congr' (Eventually.of_forall fun x => (hratio x).symm) hR_tendsto
  have hT1 : Tendsto (fun x => (ratioMap G (G 0 + ε • rot90 V) (G 0 - ε • rot90 V) x).arg)
      (𝓝[>] (0:ℝ)) (𝓝 (-Real.pi)) :=
    tendsto_arg_nhdsGT_of_tendsto hR_ratio h_ev_im_neg
  have hT2 : Tendsto (fun x => (ratioMap G (G 0 + ε • rot90 V) (G 0 - ε • rot90 V) x).arg)
      (𝓝[<] (0:ℝ)) (𝓝 Real.pi) :=
    tendsto_arg_nhdsLT_of_tendsto hR_ratio h_ev_im_pos
  obtain ⟨δ₁, hδ₁, hP⟩ := exists_pos_forall_of_eventually_nhdsGT h_ev_im_neg
  obtain ⟨δ₂, hδ₂, hQ⟩ := exists_pos_forall_of_eventually_nhdsLT h_ev_im_pos
  refine ⟨min δ₁ δ₂, lt_min hδ₁ hδ₂, ?_, ?_, hT1, hT2⟩
  · intro x hx hxδ
    exact hP x hx (lt_of_lt_of_le hxδ (min_le_left _ _))
  · intro x hx hx0
    refine hQ x ?_ hx0
    have hle : -δ₂ ≤ -(min δ₁ δ₂) := neg_le_neg (min_le_right _ _)
    linarith

end Work.Drive
