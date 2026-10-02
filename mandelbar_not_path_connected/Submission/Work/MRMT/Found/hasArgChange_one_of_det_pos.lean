import Mathlib
import Submission.Work.MRMT.QC.plane_surjective
import Submission.Work.MRMT.Found.hasArgChange_of_homotopy
import Submission.Work.MRMT.Found.exists_linRep_of_det_pos

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The argument change of the image of a circle under an injective `C¹` map

Let `F : ℂ → ℂ` be injective and continuously real-differentiable, and let `c : ℂ` be a point where
the Jacobian `(fderiv ℝ F c).det` is positive (so `F` is orientation preserving *at* `c`).  Then
for every `ρ > 0` the loop

`t ↦ F (c + ρ * exp (2 * π * i * t)) - F c`

has argument change `1`.

The strategy is the standard linearisation one.  Since `F` is injective, all the loops
`s ↦ (F (c + s ρ e^{2πit}) - F c)/s` (`0 < s ≤ 1`) avoid `0`, so by homotopy invariance of the
argument change (`hasArgChange_of_homotopy`) they all have the same argument change; for small `s`
they are uniformly close to the linearised loop `t ↦ (fderiv ℝ F c) (ρ e^{2πit})`, whose argument
change is `1` by `hasArgChange_linear_of_repr`.
-/

namespace Work.MRMT.Found

open Filter
open scoped Topology

noncomputable section

/-- The parametrised unit circle `t ↦ exp (2 π i t)`. -/
def circlePt (t : ℝ) : ℂ := Complex.exp (2 * Real.pi * t * Complex.I)

@[simp] lemma circlePt_zero : circlePt 0 = 1 := by simp [circlePt]

@[simp] lemma circlePt_one : circlePt 1 = 1 := by
  rw [circlePt, show (2 * Real.pi * (1 : ℝ) * Complex.I) = 2 * (Real.pi : ℂ) * Complex.I by
    push_cast; ring]
  exact Complex.exp_two_pi_mul_I

lemma norm_circlePt (t : ℝ) : ‖circlePt t‖ = 1 := by
  rw [circlePt, show (2 * Real.pi * t * Complex.I) = ((2 * Real.pi * t : ℝ) : ℂ) * Complex.I by
    push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

lemma continuous_circlePt : Continuous circlePt := by unfold circlePt; fun_prop

lemma circlePt_ne_zero (t : ℝ) : circlePt t ≠ 0 := by
  simpa using norm_pos_iff.mp (by rw [norm_circlePt]; norm_num : (0:ℝ) < ‖circlePt t‖)

/-- Multiplication by a real scalar commutes with a real-linear map `ℂ → ℂ`. -/
lemma clm_apply_real_mul (A : ℂ →L[ℝ] ℂ) (s : ℝ) (z : ℂ) :
    A ((s : ℂ) * z) = (s : ℂ) * A z := by
  rw [show ((s : ℂ) * z) = s • z from rfl, map_smul]
  rfl

/-- The circle itself has argument change `1`. -/
lemma hasArgChange_circlePt : Work.MRMT.QC.HasArgChange circlePt 1 := by
  refine ⟨fun t => 2 * Real.pi * t, ⟨by fun_prop, fun t _ => ?_⟩, by push_cast; ring⟩
  rw [norm_circlePt, Complex.ofReal_one, one_mul]
  simp only [circlePt]
  congr 1
  push_cast; ring

/-- A non-zero constant multiple of the circle has argument change `1`. -/
lemma hasArgChange_scalar_mul_circlePt (z : ℂ) (hz : z ≠ 0) :
    Work.MRMT.QC.HasArgChange (fun t : ℝ => z * circlePt t) 1 := by
  have h := Work.MRMT.QC.hasArgChange_mul (Work.MRMT.QC.hasArgChange_const z hz)
    hasArgChange_circlePt
  simpa using h

/-- A loop which is a small perturbation of the constant loop `1` has argument change `0`. -/
lemma hasArgChange_one_add_small_exp (c : ℂ) (hc : ‖c‖ < 1) :
    Work.MRMT.QC.HasArgChange
      (fun t : ℝ => 1 + c * Complex.exp (-(4 * Real.pi * t * Complex.I))) 0 := by
  refine Work.MRMT.QC.hasArgChange_of_close (Work.MRMT.QC.hasArgChange_const 1 one_ne_zero) ?_ ?_
    continuousOn_const ?_ ?_
  · simp
  · -- loop condition
    have h1 : Complex.exp (-(4 * Real.pi * (1 : ℝ) * Complex.I)) = 1 :=
      Complex.exp_eq_one_iff.mpr ⟨-2, by push_cast; ring⟩
    have h0 : Complex.exp (-(4 * Real.pi * (0 : ℝ) * Complex.I)) = 1 := by
      rw [show -(4 * Real.pi * (0 : ℝ) * Complex.I) = 0 by push_cast; ring, Complex.exp_zero]
    rw [h1, h0, mul_one]
  · refine (continuous_const.add (continuous_const.mul ?_)).continuousOn
    fun_prop
  · intro t _
    have h1 : (1 + c * Complex.exp (-(4 * Real.pi * t * Complex.I)) - 1)
        = c * Complex.exp (-(4 * Real.pi * t * Complex.I)) := by ring
    rw [h1, norm_mul, Complex.norm_exp, norm_one]
    have hre : (-(4 * Real.pi * t * Complex.I)).re = 0 := by
      simp [Complex.mul_re, Complex.mul_im]
    rw [hre, Real.exp_zero, mul_one]
    exact hc

/-- **The linearised statement.**  If the real-linear map `A` is orientation preserving, expressed
through its `(α, β)` decomposition as `A z = α z + β z̄` with `‖β‖ < ‖α‖` (which is equivalent to
`0 < A.det`), then the image of the circle of any radius under `A` has argument change `1`. -/
lemma hasArgChange_linear_of_repr {A : ℂ →L[ℝ] ℂ} {α β : ℂ} (hβ : ‖β‖ < ‖α‖)
    (hrep : ∀ z : ℂ, A z = α * z + β * (starRingEnd ℂ) z) {ρ : ℝ} (hρ : 0 < ρ) :
    Work.MRMT.QC.HasArgChange (fun t : ℝ => A (ρ * circlePt t)) 1 := by
  have hα : α ≠ 0 := by
    intro h; rw [h, norm_zero] at hβ; exact absurd hβ (not_lt_of_ge (norm_nonneg β))
  have hc₁ : ‖β / α‖ < 1 := by
    rw [norm_div, div_lt_one (norm_pos_iff.mpr hα)]; exact hβ
  have h1 : Work.MRMT.QC.HasArgChange (fun t : ℝ => (α * ρ) * circlePt t) 1 :=
    hasArgChange_scalar_mul_circlePt (α * ρ)
      (mul_ne_zero hα (by exact_mod_cast ne_of_gt hρ))
  have h2 := hasArgChange_one_add_small_exp (β / α) hc₁
  have h12 := Work.MRMT.QC.hasArgChange_mul h1 h2
  refine Work.MRMT.QC.hasArgChange_congr h12 (fun t => ?_)
  have hconj : (starRingEnd ℂ) (circlePt t)
      = circlePt t * Complex.exp (-(4 * Real.pi * t * Complex.I)) := by
    rw [circlePt, ← Complex.exp_conj]
    have hXY : (starRingEnd ℂ) (2 * (Real.pi : ℂ) * (t : ℂ) * Complex.I)
        = 2 * (Real.pi : ℂ) * (t : ℂ) * Complex.I + (-(4 * Real.pi * t * Complex.I)) := by
      simp only [map_mul, Complex.conj_ofReal, Complex.conj_ofNat, Complex.conj_I]
      ring
    rw [hXY, ← Complex.exp_add]
  have hconj2 : (starRingEnd ℂ) (ρ * circlePt t)
      = (ρ * circlePt t) * Complex.exp (-(4 * Real.pi * t * Complex.I)) := by
    rw [map_mul, Complex.conj_ofReal, hconj]; ring
  rw [hrep, hconj2]
  field_simp
  try ring

/-- If `A z = α z + β z̄` with `‖β‖ < ‖α‖` then `A` has no non-zero kernel. -/
lemma eq_zero_of_repr {A : ℂ →L[ℝ] ℂ} {α β : ℂ} (hβ : ‖β‖ < ‖α‖)
    (hrep : ∀ z : ℂ, A z = α * z + β * (starRingEnd ℂ) z) {z : ℂ} (h : A z = 0) : z = 0 := by
  have hα0 : (0 : ℝ) < ‖α‖ := lt_of_le_of_lt (norm_nonneg β) hβ
  have h1 : α * z + β * (starRingEnd ℂ) z = 0 := by rw [← hrep z]; exact h
  have h2 : α * z = -(β * (starRingEnd ℂ) z) := eq_neg_of_add_eq_zero_left h1
  have h3 : ‖α‖ * ‖z‖ = ‖β‖ * ‖z‖ := by
    have h4 := congrArg norm h2
    rw [norm_neg, norm_mul, norm_mul, Complex.norm_conj] at h4
    linarith [h4]
  have h4 : (‖α‖ - ‖β‖) * ‖z‖ = 0 := by linarith
  rcases mul_eq_zero.mp h4 with h5 | h5
  · exfalso; linarith [hα0, hβ]
  · exact norm_eq_zero.mp h5

theorem hasArgChange_one_of_det_pos {F : ℂ → ℂ} (hF : ContDiff ℝ 1 F) (hinj : Function.Injective F)
    {c : ℂ} (hc : 0 < (fderiv ℝ F c).det) {ρ : ℝ} (hρ : 0 < ρ) :
    Work.MRMT.QC.HasArgChange
      (fun t : ℝ => F (c + ρ * Complex.exp (2 * Real.pi * t * Complex.I)) - F c) 1 := by
  set A : ℂ →L[ℝ] ℂ := fderiv ℝ F c with hA
  have hFA : HasFDerivAt F A c := by
    rw [hA]
    exact (hF.differentiable (by norm_num)).differentiableAt.hasFDerivAt
  have hdet : 0 < A.det := hc
  -- the real-linear representation of `A`
  obtain ⟨α, β, hβ, hrep⟩ := exists_linRep_of_det_pos hdet
  have hAinj : ∀ z : ℂ, A z = 0 → z = 0 := fun z h => eq_zero_of_repr hβ hrep h
  have hlin : Work.MRMT.QC.HasArgChange (fun t : ℝ => A (ρ * circlePt t)) 1 :=
    hasArgChange_linear_of_repr hβ hrep hρ
  -- the linearised loop is continuous and non-vanishing on `[0,1]`
  have hlincont : ContinuousOn (fun t : ℝ => A (ρ * circlePt t)) (Set.Icc 0 1) :=
    ((A.continuous.comp (continuous_const.mul continuous_circlePt))).continuousOn
  have hlin_ne : ∀ t ∈ Set.Icc (0 : ℝ) 1, A (ρ * circlePt t) ≠ 0 := by
    intro t _ h0
    exact mul_ne_zero (by exact_mod_cast ne_of_gt hρ) (circlePt_ne_zero t) (hAinj _ h0)
  obtain ⟨t₀, ht₀, hmin⟩ := isCompact_Icc.exists_isMinOn ⟨0, by norm_num⟩ hlincont.norm
  set δ : ℝ := ‖A (ρ * circlePt t₀)‖ with hδdef
  have hδpos : 0 < δ := norm_pos_iff.mpr (hlin_ne t₀ ht₀)
  -- the derivative estimate
  have hlo : (fun h : ℂ => F (c + h) - F c - A h) =o[𝓝 0] fun h : ℂ => h :=
    hasFDerivAt_iff_isLittleO_nhds_zero.mp hFA
  have hev : ∀ᶠ h : ℂ in 𝓝 0, ‖F (c + h) - F c - A h‖ ≤ (δ / (2 * ρ)) * ‖h‖ :=
    hlo.def (by positivity)
  rw [Metric.eventually_nhds_iff] at hev
  obtain ⟨η, hη, hη'⟩ := hev
  -- the parameter of the intermediate loop
  set ε : ℝ := min 1 (η / (2 * ρ)) with hεdef
  have hεpos : 0 < ε := lt_min one_pos (by positivity)
  have hεle1 : ε ≤ 1 := min_le_left _ _
  have hεη : ε ≤ η / (2 * ρ) := min_le_right _ _
  -- the homotopy family
  set H : ℝ → ℝ → ℂ := fun s t => (F (c + s * ρ * circlePt t) - F c) / s with hHdef
  have hHcont : ContinuousOn (fun p : ℝ × ℝ => H p.1 p.2)
      (Set.Icc ε 1 ×ˢ Set.Icc (0 : ℝ) 1) := by
    rw [hHdef]
    refine ContinuousOn.div ?_ (Complex.continuous_ofReal.comp_continuousOn continuousOn_fst) ?_
    · refine ContinuousOn.sub ?_ continuousOn_const
      refine hF.continuous.comp_continuousOn ?_
      refine ContinuousOn.add continuousOn_const ?_
      refine ContinuousOn.mul ?_ ?_
      · exact ContinuousOn.mul (Complex.continuous_ofReal.comp_continuousOn continuousOn_fst)
          continuousOn_const
      · exact continuous_circlePt.comp_continuousOn continuousOn_snd
    · intro p hp
      have : (0 : ℝ) < p.1 := lt_of_lt_of_le hεpos hp.1.1
      exact_mod_cast ne_of_gt this
  have hHloop : ∀ s ∈ Set.Icc ε 1, H s 1 = H s 0 := by
    intro s _
    rw [hHdef]
    simp only [circlePt_one, circlePt_zero]
  have hHne : ∀ s ∈ Set.Icc ε 1, ∀ t ∈ Set.Icc (0 : ℝ) 1, H s t ≠ 0 := by
    intro s hs t _ h0
    have hspos : 0 < s := lt_of_lt_of_le hεpos hs.1
    have hsne : (s : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hspos
    have h1 : F (c + s * ρ * circlePt t) = F c := by
      rw [hHdef] at h0
      simp only [] at h0
      rw [div_eq_zero_iff] at h0
      rcases h0 with h0 | h0
      · exact sub_eq_zero.mp h0
      · exact absurd h0 hsne
    have h2 : c + s * ρ * circlePt t = c := hinj h1
    have h3 : s * ρ * circlePt t = 0 := by
      have h4 : c + s * ρ * circlePt t - c = 0 := by rw [h2]; ring
      simpa using h4
    rcases mul_eq_zero.mp h3 with h5 | h5
    · rcases mul_eq_zero.mp h5 with h6 | h6
      · exact absurd h6 (by exact_mod_cast ne_of_gt hspos)
      · exact absurd h6 (by exact_mod_cast ne_of_gt hρ)
    · exact circlePt_ne_zero t h5
  -- the intermediate loop is close to the linearised one
  have hclose : ∀ t ∈ Set.Icc (0 : ℝ) 1, ‖H ε t - A (ρ * circlePt t)‖ < ‖A (ρ * circlePt t)‖ := by
    intro t ht
    have hδle : δ ≤ ‖A (ρ * circlePt t)‖ := hmin ht
    have hynorm : ‖(((ε * ρ : ℝ)) : ℂ) * circlePt t‖ = ε * ρ := by
      rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (by positivity), norm_circlePt, mul_one]
    have hy_lt : dist ((((ε * ρ : ℝ)) : ℂ) * circlePt t) 0 < η := by
      rw [dist_zero_right, hynorm]
      have h3 : ε * ρ ≤ (η / (2 * ρ)) * ρ := mul_le_mul_of_nonneg_right hεη hρ.le
      have h4 : (η / (2 * ρ)) * ρ = η / 2 := by field_simp; try ring
      linarith
    have hbnd := hη' hy_lt
    rw [hynorm] at hbnd
    have hhalf : (δ / (2 * ρ)) * (ε * ρ) = δ * ε / 2 := by field_simp; try ring
    rw [hhalf] at hbnd
    have hyy : (↑ε * ↑ρ * circlePt t : ℂ) = ((ε * ρ : ℝ) : ℂ) * circlePt t := by
      push_cast; ring
    have hAc : A (((ε * ρ : ℝ) : ℂ) * circlePt t) = (ε : ℂ) * A (↑ρ * circlePt t) := by
      rw [clm_apply_real_mul A (ε * ρ) (circlePt t), clm_apply_real_mul A ρ (circlePt t),
        Complex.ofReal_mul]
      ring
    have hkey : (F (c + ↑ε * ↑ρ * circlePt t) - F c) / ↑ε - A (↑ρ * circlePt t)
        = (F (c + ((ε * ρ : ℝ) : ℂ) * circlePt t) - F c
            - A (((ε * ρ : ℝ) : ℂ) * circlePt t)) / ↑ε := by
      rw [hyy, hAc]
      have hεne : (ε : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hεpos
      field_simp
      try ring
    rw [hkey, norm_div, Complex.norm_real, Real.norm_of_nonneg hεpos.le, div_lt_iff₀ hεpos]
    nlinarith [hbnd, hδle, hεpos, hδpos]
  have hslice : ContinuousOn (fun t : ℝ => H ε t) (Set.Icc 0 1) := by
    rw [hHdef]
    refine ContinuousOn.div ?_ (Complex.continuous_ofReal.comp_continuousOn continuousOn_const) ?_
    · refine ContinuousOn.sub ?_ continuousOn_const
      refine hF.continuous.comp_continuousOn ?_
      refine ContinuousOn.add continuousOn_const ?_
      exact ContinuousOn.mul continuousOn_const continuous_circlePt.continuousOn
    · intro t _
      exact_mod_cast ne_of_gt hεpos
  have hacε : Work.MRMT.QC.HasArgChange (fun t : ℝ => H ε t) 1 := by
    refine Work.MRMT.QC.hasArgChange_of_close (γ := fun t : ℝ => A (ρ * circlePt t))
      (γ' := fun t : ℝ => H ε t) (k := 1) hlin ?_ ?_ hlincont hslice hclose
    · simp only [circlePt_one, circlePt_zero]
    · rw [hHdef]; simp only [circlePt_one, circlePt_zero]
  -- homotopy invariance moves the argument change to the parameter `1`
  have hab : ε ≤ 1 := hεle1
  have hhom : Work.MRMT.QC.HasArgChange (fun t : ℝ => H 1 t) 1 :=
    hasArgChange_of_homotopy (a := ε) (b := 1) hab hHcont hHloop hHne hacε
  have hfinal : ∀ t : ℝ, H 1 t = F (c + ρ * Complex.exp (2 * Real.pi * t * Complex.I)) - F c := by
    intro t
    rw [hHdef]
    simp only [circlePt, Complex.ofReal_one, one_mul, div_one]
  exact Work.MRMT.QC.hasArgChange_congr hhom hfinal

end

end Work.MRMT.Found
