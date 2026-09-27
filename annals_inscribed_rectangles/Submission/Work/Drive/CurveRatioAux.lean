import Mathlib
import Submission.Work.Drive.SeparationBase

/-!
# Elementary tools for the local behaviour of the chord-ratio map

This module collects small, reusable facts used in `Submission.Work.Drive.curve_ratio_local`:

* `cpx` as a continuous linear map, and the identity `cpx (rot90 v) = I * cpx v`;
* the algebraic normal form `(A - c*I)/(A + c*I) = (A/c - I)/(A/c + I)` of the ratio of a chord to the
  rotated chord, the real part of a ratio `A/(c*v)`, and the imaginary part of `(w - I)/(w + I)`;
* two filter lemmas turning the positivity of the slope of a real function at `0` into one-sided
  positivity/negativity;
* the extraction of an explicit `δ > 0` from an `∀ᶠ` statement along `𝓝[>] 0` or `𝓝[<] 0`;
* the limits of `Complex.arg` at `-1` along the two sides of the negative real axis.
-/

namespace Work.Drive

open Filter Topology
open scoped Topology ComplexConjugate

noncomputable section

/-- `cpx : ℝ × ℝ → ℂ` as a continuous linear map. -/
noncomputable def cpxCLM : (ℝ × ℝ) →L[ℝ] ℂ := Complex.equivRealProdCLM.symm

lemma cpxCLM_apply (p : ℝ × ℝ) : cpxCLM p = cpx p := by
  show Complex.equivRealProdCLM.symm p = cpx p
  rw [Complex.equivRealProdCLM_symm_apply]
  exact Complex.ext (by simp [cpx]) (by simp [cpx])

/-- Rotating by a right angle rotates the corresponding complex number by `I`. -/
lemma cpx_rot90_I (v : ℝ × ℝ) : cpx (rot90 v) = Complex.I * cpx v := by
  exact Complex.ext (by simp [cpx, rot90, Complex.mul_re]) (by simp [cpx, rot90, Complex.mul_im])

/-- Dividing the numerator and the denominator of `(A - cI)/(A + cI)` by the common factor `c`. -/
lemma sub_I_div_add_I_eq (A c : ℂ) (hc : c ≠ 0) :
    (A - c * Complex.I)/(A + c * Complex.I) = (A/c - Complex.I)/(A/c + Complex.I) := by
  have h1 : A - c * Complex.I = c * (A/c - Complex.I) := by field_simp
  have h2 : A + c * Complex.I = c * (A/c + Complex.I) := by field_simp
  rw [h1, h2, mul_div_mul_left _ _ hc]

/-- The ratio of the two chords from the centre `G 0` towards `G 0 ± ε • rot90 V`, in the normal form
`(w - I)/(w + I)` with `w = cpx (G x - G 0)/(ε * cpx V)`. -/
lemma curveRatioModel (G : ℝ → ℝ × ℝ) {V : ℝ × ℝ} (hV : cpx V ≠ 0) {ε : ℝ} (hε : (ε:ℂ) ≠ 0)
    (x : ℝ) :
    ratioMap G (G 0 + ε • rot90 V) (G 0 - ε • rot90 V) x
      = ((cpx (G x - G 0)/((ε:ℂ) * cpx V)) - Complex.I)
        /((cpx (G x - G 0)/((ε:ℂ) * cpx V)) + Complex.I) := by
  rw [ratioMap_apply]
  have h1 : G x - (G 0 + ε • rot90 V) = (G x - G 0) - ε • rot90 V := by abel
  have h2 : G x - (G 0 - ε • rot90 V) = (G x - G 0) + ε • rot90 V := by abel
  rw [h1, h2, cpx_sub, cpx_add, cpx_smul, cpx_rot90_I]
  simp only [Complex.real_smul]
  have hc : (ε:ℂ) * cpx V ≠ 0 := mul_ne_zero hε hV
  rw [show (↑ε : ℂ) * (Complex.I * cpx V) = ((ε:ℂ) * cpx V) * Complex.I from by ring]
  exact sub_I_div_add_I_eq _ _ hc

/-- The imaginary part of `(w - I)/(w + I)`: the sign is the opposite of the sign of `Re w`. -/
lemma sub_I_div_add_I_im (w : ℂ) :
    ((w - Complex.I)/(w + Complex.I)).im = -2 * w.re / Complex.normSq (w + Complex.I) := by
  rw [Complex.div_im]
  simp only [Complex.sub_im, Complex.sub_re, Complex.add_re, Complex.add_im, Complex.I_re,
    Complex.I_im]
  ring

/-- The real part of `A/(ε * v)` in terms of the pairing of `A` with `v`. -/
lemma re_div_ofReal_mul (A : ℂ) {v : ℂ} (hv : v ≠ 0) {ε : ℝ} (hε : ε ≠ 0) :
    (A / ((ε:ℂ) * v)).re = (A * conj v).re / (ε * Complex.normSq v) := by
  rw [Complex.div_re, Complex.mul_re, Complex.normSq_mul, Complex.normSq_ofReal]
  simp only [Complex.conj_re, Complex.conj_im, Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
    Complex.ofReal_im]
  have hnv : Complex.normSq v ≠ 0 := fun h => hv (Complex.normSq_eq_zero.mp h)
  have hεC : (ε:ℂ) ≠ 0 := by exact_mod_cast hε
  field_simp
  ring

/-- Positivity of the slope of `f` at `0` gives positivity of `f` just to the right of `0`. -/
lemma eventually_pos_nhdsGT_of_inv_mul_pos {f : ℝ → ℝ}
    (h : ∀ᶠ t in 𝓝[≠] (0:ℝ), 0 < t⁻¹ * f t) :
    ∀ᶠ t in 𝓝[>] (0:ℝ), 0 < f t := by
  filter_upwards [h.filter_mono (nhdsGT_le_nhdsNE 0), self_mem_nhdsWithin] with t ht htpos
  have hinv : 0 < t⁻¹ := inv_pos.mpr (Set.mem_Ioi.mp htpos)
  exact pos_of_mul_pos_left (by rwa [mul_comm]) hinv.le

/-- Positivity of the slope of `f` at `0` gives negativity of `f` just to the left of `0`. -/
lemma eventually_neg_nhdsLT_of_inv_mul_pos {f : ℝ → ℝ}
    (h : ∀ᶠ t in 𝓝[≠] (0:ℝ), 0 < t⁻¹ * f t) :
    ∀ᶠ t in 𝓝[<] (0:ℝ), f t < 0 := by
  filter_upwards [h.filter_mono (nhdsLT_le_nhdsNE 0), self_mem_nhdsWithin] with t ht htneg
  have hinv : t⁻¹ < 0 := inv_neg''.mpr (Set.mem_Iio.mp htneg)
  rcases mul_pos_iff.mp ht with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact absurd (lt_trans hinv h1) (lt_irrefl _)
  · exact h2

/-- An `∀ᶠ` statement along `𝓝[>] 0` gives an explicit right half-neighbourhood. -/
lemma exists_pos_forall_of_eventually_nhdsGT {p : ℝ → Prop}
    (h : ∀ᶠ x in 𝓝[>] (0:ℝ), p x) : ∃ δ : ℝ, 0 < δ ∧ ∀ x, 0 < x → x < δ → p x := by
  rw [eventually_nhdsWithin_iff] at h
  obtain ⟨δ, hδ, hδ'⟩ := Metric.eventually_nhds_iff.mp h
  exact ⟨δ, hδ, fun x hx hxδ =>
    hδ' (by rw [Real.dist_eq, sub_zero, abs_lt]; exact ⟨by linarith, hxδ⟩) hx⟩

/-- An `∀ᶠ` statement along `𝓝[<] 0` gives an explicit left half-neighbourhood. -/
lemma exists_pos_forall_of_eventually_nhdsLT {p : ℝ → Prop}
    (h : ∀ᶠ x in 𝓝[<] (0:ℝ), p x) : ∃ δ : ℝ, 0 < δ ∧ ∀ x, -δ < x → x < 0 → p x := by
  rw [eventually_nhdsWithin_iff] at h
  obtain ⟨δ, hδ, hδ'⟩ := Metric.eventually_nhds_iff.mp h
  exact ⟨δ, hδ, fun x hx hx0 =>
    hδ' (by rw [Real.dist_eq, sub_zero, abs_lt]; exact ⟨hx, by linarith⟩) hx0⟩

/-- A curve in `ℂ` tending to `-1` from below has argument tending to `-π`. -/
lemma tendsto_arg_nhdsGT_of_tendsto {R : ℝ → ℂ} (hR : Tendsto R (𝓝 0) (𝓝 (-1)))
    (he : ∀ᶠ x in 𝓝[>] (0:ℝ), (R x).im < 0) :
    Tendsto (fun x => (R x).arg) (𝓝[>] (0:ℝ)) (𝓝 (-Real.pi)) := by
  have hcont : ContinuousAt (fun z : ℂ => -Real.arccos (z.re/‖z‖)) (-1) := by
    refine (Real.continuous_arccos.continuousAt.comp ?_).neg
    refine (Complex.continuous_re.continuousAt.div continuous_norm.continuousAt ?_)
    norm_num
  have hcomp : Tendsto (fun x => -Real.arccos ((R x).re/‖R x‖)) (𝓝 0) (𝓝 (-Real.pi)) := by
    have := hcont.tendsto.comp hR
    simpa [Function.comp_def, Real.arccos_neg_one] using this
  have hev : (fun x => -Real.arccos ((R x).re/‖R x‖)) =ᶠ[𝓝[>] (0:ℝ)] (fun x => (R x).arg) := by
    filter_upwards [he] with x hx
    exact (Complex.arg_of_im_neg hx).symm
  exact Filter.Tendsto.congr' hev (hcomp.mono_left nhdsWithin_le_nhds)

/-- A curve in `ℂ` tending to `-1` from above has argument tending to `π`. -/
lemma tendsto_arg_nhdsLT_of_tendsto {R : ℝ → ℂ} (hR : Tendsto R (𝓝 0) (𝓝 (-1)))
    (he : ∀ᶠ x in 𝓝[<] (0:ℝ), 0 < (R x).im) :
    Tendsto (fun x => (R x).arg) (𝓝[<] (0:ℝ)) (𝓝 Real.pi) := by
  have hcont : ContinuousAt (fun z : ℂ => Real.arccos (z.re/‖z‖)) (-1) := by
    refine Real.continuous_arccos.continuousAt.comp ?_
    refine (Complex.continuous_re.continuousAt.div continuous_norm.continuousAt ?_)
    norm_num
  have hcomp : Tendsto (fun x => Real.arccos ((R x).re/‖R x‖)) (𝓝 0) (𝓝 Real.pi) := by
    have := hcont.tendsto.comp hR
    simpa [Function.comp_def, Real.arccos_neg_one] using this
  have hev : (fun x => Real.arccos ((R x).re/‖R x‖)) =ᶠ[𝓝[<] (0:ℝ)] (fun x => (R x).arg) := by
    filter_upwards [he] with x hx
    exact (Complex.arg_of_im_pos hx).symm
  exact Filter.Tendsto.congr' hev (hcomp.mono_left nhdsWithin_le_nhds)

end

end Work.Drive
