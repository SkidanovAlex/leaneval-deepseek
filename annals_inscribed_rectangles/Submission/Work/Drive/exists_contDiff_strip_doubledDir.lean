import Mathlib
import Submission.Work.Drive.contDiffOn_chordUnitDir
import Submission.Work.Drive.exists_continuous_chordDir
import Submission.Work.Drive.DirCTools
import Submission.Work.Drive.exists_secant_dir_contDiff
import Submission.Work.Drive.curve_deriv_ne_zero

namespace Work.Drive

open Manifold
open scoped Manifold ContDiff Topology

/-! ## Elementary complex/real facts used below -/

/-- `toC` is the identification `(x, y) ↦ x + i y`, read as the complex number with components. -/
lemma stripToC_mk (p : ℝ × ℝ) : toC p = (⟨p.1, p.2⟩ : ℂ) :=
  Complex.ext (by simp [toC]) (by simp [toC])

/-- `z * (1 / ‖z‖) = z / ‖z‖`, both read in `ℂ`. -/
lemma stripMulOneDivNorm (z : ℂ) : z * (((1:ℝ)/‖z‖ : ℝ) : ℂ) = z / ((‖z‖:ℝ):ℂ) := by
  have h : (((1:ℝ)/‖z‖ : ℝ) : ℂ) = ((‖z‖:ℝ):ℂ)⁻¹ := by
    rw [one_div, Complex.ofReal_inv]
  rw [h, div_eq_mul_inv]

/-- **The doubled direction of a vector, read through `circleOf`, is the square of its unit
complexification.**  For `v ≠ 0`, `circleOf (dirC v) = (toC v / ‖toC v‖) ^ 2`. -/
lemma stripCircleOf_dirC (v : ℝ × ℝ) (hv : toC v ≠ 0) :
    circleOf (Submission.Collision.dirC v) =
      (toC v / ((‖toC v‖ : ℝ) : ℂ)) ^ 2 := by
  rw [stripToC_mk v] at hv
  have h := circleOf_arg_div_pi (⟨v.1, v.2⟩ : ℂ) hv
  rw [Submission.Collision.dirC, h, stripToC_mk v]

/-- `(z / ‖z‖) ^ 2 = z / star z` for `z ≠ 0`. -/
private lemma stripSqDivNorm (z : ℂ) (hz : z ≠ 0) :
    (z / ((‖z‖ : ℝ) : ℂ)) ^ 2 = z / star z := by
  have hnorm : ((‖z‖ : ℝ) : ℂ) ^ 2 = z * star z := by
    have h1 : ((‖z‖ : ℝ) : ℂ) ^ 2 = ((‖z‖ ^ 2 : ℝ) : ℂ) := by push_cast; ring
    rw [h1, ← Complex.normSq_eq_norm_sq, ← Complex.mul_conj z, starRingEnd_apply]
  have hstar : star z ≠ 0 := by rw [star_ne_zero]; exact hz
  rw [div_pow, hnorm]
  field_simp

/-- The squared unit direction is insensitive to a non-zero real factor. -/
lemma stripDivNormRadial (r : ℝ) (hr : r ≠ 0) (z : ℂ) (hz : z ≠ 0) :
    ((r : ℂ) * z / ((‖(r : ℂ) * z‖ : ℝ) : ℂ)) ^ 2 = (z / ((‖z‖ : ℝ) : ℂ)) ^ 2 := by
  rw [stripSqDivNorm _ (mul_ne_zero (Complex.ofReal_ne_zero.mpr hr) hz),
      stripSqDivNorm _ hz]
  have hz' : star z ≠ 0 := by rw [star_ne_zero]; exact hz
  have hr' : ((r : ℂ)) ≠ 0 := Complex.ofReal_ne_zero.mpr hr
  rw [star_mul, Complex.star_def, Complex.conj_ofReal, starRingEnd_apply]
  field_simp

/-- **The collision condition in the strip.** `Circle.exp (σ + s) = Circle.exp (σ - s)` exactly when
`s` is an integer multiple of `π`. -/
lemma stripExpAddEqIff (σ s : ℝ) :
    Circle.exp (σ + s) = Circle.exp (σ - s) ↔ ∃ k : ℤ, s = Real.pi * k := by
  constructor
  · intro h
    obtain ⟨m, hm⟩ := Circle.exp_eq_exp.mp h
    refine ⟨m, ?_⟩
    have h2 : 2 * s = (↑m : ℝ) * (2 * Real.pi) := by linarith [hm]
    have : s = (↑m : ℝ) * Real.pi := by linarith [h2]
    rw [this]; ring
  · rintro ⟨k, hk⟩
    rw [hk, Circle.exp_eq_exp]
    exact ⟨k, by ring⟩

/-- If `x` is an integer multiple of `π` and `|x - π k| < π`, then `x = π k`. -/
lemma stripEqOfIntMulPi {x : ℝ} {k : ℤ} (hx : ∃ j : ℤ, x = Real.pi * j)
    (h : |x - Real.pi * k| < Real.pi) : x = Real.pi * k := by
  obtain ⟨j, rfl⟩ := hx
  have hπ : (0:ℝ) < Real.pi := Real.pi_pos
  have h1 : |((j:ℝ) - (k:ℝ))| * Real.pi < Real.pi := by
    have he : |Real.pi * (j:ℝ) - Real.pi * (k:ℝ)| = |((j:ℝ) - (k:ℝ))| * Real.pi := by
      rw [← mul_sub, abs_mul, abs_of_pos hπ, mul_comm]
    rw [← he]
    exact h
  have h2 : |((j:ℝ) - (k:ℝ))| < 1 := by nlinarith [hπ, h1]
  have h3 : j - k = 0 := by
    have h5 : (-1:ℤ) < j - k := by
      rw [← Int.cast_lt (R := ℝ)]; push_cast
      have := (abs_lt.mp h2).1; linarith
    have h6 : j - k < (1:ℤ) := by
      rw [← Int.cast_lt (R := ℝ)]; push_cast
      have := (abs_lt.mp h2).2; linarith
    omega
  have hjk : j = k := sub_eq_zero.mp h3
  rw [hjk]

/-- The derivative of the plane curve is `2π`-periodic, hence invariant under a shift by `2π k`. -/
lemma stripDerivCurve_zsmul (γ : Circle → ℝ × ℝ)
    (hγ : Manifold.IsSmoothEmbedding (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
      (modelWithCornersSelf ℝ (ℝ × ℝ)) ((⊤ : ℕ∞) : WithTop ℕ∞) γ) (t : ℝ) (m : ℤ) :
    deriv (curve γ) (t + (m : ℝ) * (2 * Real.pi)) = deriv (curve γ) t := by
  have hper : Function.Periodic (deriv (curve γ)) (2 * Real.pi) := deriv_curve_periodic γ hγ
  simpa [zsmul_eq_mul] using hper.zsmul m t

/-- Swapping the two arguments of the unit chord direction negates it. -/
lemma stripChordUnitDir_swap (γ : Circle → ℝ × ℝ) (a b : ℝ) :
    chordUnitDir γ (b, a) = - chordUnitDir γ (a, b) := by
  unfold chordUnitDir
  have h : chordC γ (b, a) = - chordC γ (a, b) := by
    rw [chordC_eq_toC, chordC_eq_toC, ← toC_neg, neg_sub]
  rw [h, norm_neg, neg_div]

/-- **The divided difference of the plane curve is non-zero on a window of length `< π`.**
`secantW (curve γ) (a, b) ≠ 0` whenever `|a - b| < π`: for `a = b` it is the (non-zero) tangent
derivative, and for `a ≠ b` it vanishes only if `curve γ a = curve γ b`, which forces
`a - b ∈ 2π ℤ`, hence `|a - b| ≥ 2π > π`. -/
lemma stripSecantW_ne_zero (γ : Circle → ℝ × ℝ)
    (hγ : Manifold.IsSmoothEmbedding (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
      (modelWithCornersSelf ℝ (ℝ × ℝ)) ((⊤ : ℕ∞) : WithTop ℕ∞) γ)
    {a b : ℝ} (hab : |a - b| < Real.pi) : secantW (curve γ) (a, b) ≠ 0 := by
  have hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (curve γ) :=
    contMDiff_iff_contDiff.mp (hγ.contMDiff.comp (contMDiff_circleExp (m := ∞)))
  intro hzero
  by_cases hab' : a = b
  · subst hab'
    rw [secantW_self] at hzero
    exact curve_deriv_ne_zero γ hγ a hzero
  · have hsub : curve γ a - curve γ b = (a - b) • secantW (curve γ) (a, b) :=
      sub_eq_smul_secantW (hF.of_le (by norm_num)) a b
    rw [hzero, smul_zero, sub_eq_zero] at hsub
    have hinj : Function.Injective γ := hγ.isEmbedding.injective
    have hexp : Circle.exp a = Circle.exp b := hinj hsub
    obtain ⟨m, hm⟩ := Circle.exp_eq_exp.mp hexp
    have hmab : a - b = (↑m : ℝ) * (2 * Real.pi) := by linarith [hm]
    have hab2 : |(↑m : ℝ) * (2 * Real.pi)| < Real.pi := by rw [← hmab]; exact hab
    have hab3 : |(↑m : ℝ)| * (2 * Real.pi) < Real.pi := by
      rwa [abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2 * Real.pi)] at hab2
    have h3 : |(↑m : ℝ)| < 1 / 2 := by nlinarith [Real.pi_pos]
    have h3a : -(1:ℝ) < (↑m : ℝ) := by have := (abs_lt.mp h3).1; linarith
    have h3b : (↑m : ℝ) < 1 := by have := (abs_lt.mp h3).2; linarith
    have hm0 : m = 0 := by
      have h5 : (-1:ℤ) < m := by rw [← Int.cast_lt (R := ℝ)]; push_cast; exact h3a
      have h6 : m < (1:ℤ) := by rw [← Int.cast_lt (R := ℝ)]; push_cast; exact h3b
      omega
    exact hab' (by rw [hm0] at hm; simpa using hm)

/-! ## The auxiliary functions -/

/-- The shifted secant slope used to extend the chord direction across the collision line
`s = π k`: the mean of `deriv (curve γ)` over the interval joining `σ - s` and `σ + s - 2π k`. -/
noncomputable def stripSecant (γ : Circle → ℝ × ℝ) (k : ℤ) (p : ℝ × ℝ) : ℝ × ℝ :=
  secantW (curve γ) (p.1 + p.2 - Real.pi * (k:ℝ) * 2, p.1 - p.2)

@[simp] lemma stripSecant_def (γ : Circle → ℝ × ℝ) (k : ℤ) (p : ℝ × ℝ) :
    stripSecant γ k p = secantW (curve γ) (p.1 + p.2 - Real.pi * (k:ℝ) * 2, p.1 - p.2) := rfl

/-- The doubled chord direction of the symmetric chord of the strip, extended to the collision
lines `s ∈ π ℤ` by the doubled tangent direction. -/
noncomputable def stripDoubledDir (γ : Circle → ℝ × ℝ) : ℝ × ℝ → ℂ := by
  classical
  exact fun p =>
    if _h : ∃ k : ℤ, p.2 = Real.pi * k then
      circleOf (Submission.Collision.dirC (deriv (curve γ) (p.1 - p.2)))
    else (chordUnitDir γ (p.1 + p.2, p.1 - p.2)) ^ 2

theorem exists_contDiff_strip_doubledDir (γ : Circle → ℝ × ℝ)
    (hγ : Manifold.IsSmoothEmbedding (modelWithCornersSelf ℝ (EuclideanSpace ℝ (Fin 1)))
      (modelWithCornersSelf ℝ (ℝ × ℝ)) ((⊤ : ℕ∞) : WithTop ℕ∞) γ) :
    ∃ F : ℝ × ℝ → ℂ, ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) F ∧
      (∀ σ s : ℝ, F (σ, -s) = F (σ, s)) ∧
      (∀ σ s : ℝ, Circle.exp (σ + s) ≠ Circle.exp (σ - s) →
        F (σ, s) = Work.Drive.circleOf (Submission.Collision.dirC
          (γ (Circle.exp (σ + s)) - γ (Circle.exp (σ - s))))) ∧
      (∀ σ : ℝ, F (σ, 0) = Work.Drive.circleOf (Work.Drive.tangentDirC γ (Circle.exp σ))) := by
  classical
  have hγc : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (curve γ) :=
    contMDiff_iff_contDiff.mp (hγ.contMDiff.comp (contMDiff_circleExp (m := ∞)))
  have hder : ∀ t : ℝ, deriv (curve γ) t ≠ 0 := curve_deriv_ne_zero γ hγ
  have htoC : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) toC := by
    unfold toC
    have h1 : ContDiff ℝ ((⊤:ℕ∞):WithTop ℕ∞) (fun p : ℝ × ℝ => (p.1 : ℂ)) :=
      Complex.ofRealCLM.contDiff.comp contDiff_fst
    have h2 : ContDiff ℝ ((⊤:ℕ∞):WithTop ℕ∞) (fun p : ℝ × ℝ => (p.2 : ℂ) * Complex.I) :=
      (Complex.ofRealCLM.contDiff.comp contDiff_snd).mul contDiff_const
    exact h1.add h2
  refine ⟨stripDoubledDir γ, ?_, ?_, ?_, ?_⟩
  · rw [contDiff_iff_contDiffAt]
    rintro ⟨σ, s⟩
    by_cases hs : ∃ k : ℤ, s = Real.pi * k
    · -- ### on a collision line
      obtain ⟨k, hk⟩ := hs
      have hNopen : IsOpen {p : ℝ × ℝ | |p.2 - Real.pi * (k:ℝ)| < Real.pi / 2} := by
        have heq : {p : ℝ × ℝ | |p.2 - Real.pi * (k:ℝ)| < Real.pi / 2}
            = {p : ℝ × ℝ |
                p.2 ∈ Set.Ioo (Real.pi * (k:ℝ) - Real.pi/2) (Real.pi * (k:ℝ) + Real.pi/2)} := by
          ext p; simp only [Set.mem_setOf_eq, Set.mem_Ioo, abs_lt]
          constructor <;> intro h <;> exact ⟨by linarith [h.1], by linarith [h.2]⟩
        rw [heq]
        exact isOpen_Ioo.preimage continuous_snd
      have hqN : (σ, s) ∈ {p : ℝ × ℝ | |p.2 - Real.pi * (k:ℝ)| < Real.pi / 2} := by
        simp only [Set.mem_setOf_eq]
        rw [hk, sub_self, abs_zero]
        positivity
      have hHcd : ContDiff ℝ ((⊤:ℕ∞):WithTop ℕ∞)
          (fun p : ℝ × ℝ => toC (stripSecant γ k p)) := by
        have hsec : ContDiff ℝ ((⊤:ℕ∞):WithTop ℕ∞) (secantW (curve γ)) :=
          contDiff_secantW hγc
        have hmap : ContDiff ℝ ((⊤:ℕ∞):WithTop ℕ∞)
            (fun p : ℝ × ℝ => (p.1 + p.2 - Real.pi*(k:ℝ)*2, p.1 - p.2)) := by fun_prop
        have hcomp : ContDiff ℝ ((⊤:ℕ∞):WithTop ℕ∞)
            (fun p : ℝ × ℝ => secantW (curve γ) (p.1 + p.2 - Real.pi*(k:ℝ)*2, p.1 - p.2)) :=
          hsec.comp hmap
        exact htoC.comp hcomp
      have hHne : ∀ p ∈ {p : ℝ × ℝ | |p.2 - Real.pi * (k:ℝ)| < Real.pi / 2},
          toC (stripSecant γ k p) ≠ 0 := by
        intro p hp
        simp only [Set.mem_setOf_eq] at hp
        rw [toC_ne_zero_iff]
        apply stripSecantW_ne_zero γ hγ
        have he : (p.1 + p.2 - Real.pi*(k:ℝ)*2) - (p.1 - p.2)
            = 2 * (p.2 - Real.pi*(k:ℝ)) := by ring
        rw [he, abs_mul]
        rw [abs_of_pos (by norm_num : (0:ℝ) < 2)]
        linarith [hp]
      have hHsm : ContDiffAt ℝ ((⊤:ℕ∞):WithTop ℕ∞)
          (fun p : ℝ × ℝ => (toC (stripSecant γ k p)
            * (((1:ℝ)/‖toC (stripSecant γ k p)‖ : ℝ) : ℂ)) ^ 2) (σ, s) := by
        have hne : toC (stripSecant γ k (σ, s)) ≠ 0 := hHne (σ, s) hqN
        have hnorm : ContDiffAt ℝ ((⊤:ℕ∞):WithTop ℕ∞)
            (fun p : ℝ × ℝ => ‖toC (stripSecant γ k p)‖) (σ, s) :=
          ContDiffAt.norm ℂ hHcd.contDiffAt hne
        have hdivn : ContDiffAt ℝ ((⊤:ℕ∞):WithTop ℕ∞)
            (fun p : ℝ × ℝ => (1:ℝ)/‖toC (stripSecant γ k p)‖) (σ, s) :=
          ContDiffAt.div (f := fun _ : ℝ × ℝ => (1:ℝ))
            (g := fun p : ℝ × ℝ => ‖toC (stripSecant γ k p)‖)
            contDiffAt_const hnorm (norm_ne_zero_iff.mpr hne)
        exact (hHcd.contDiffAt.mul
          (Complex.ofRealCLM.contDiff.contDiffAt.comp (σ, s) hdivn)).pow 2
      refine hHsm.congr_of_eventuallyEq ?_
      refine Filter.eventuallyEq_of_mem (hNopen.mem_nhds hqN) ?_
      intro p hp
      simp only [Set.mem_setOf_eq] at hp
      change stripDoubledDir γ p =
        (toC (stripSecant γ k p) * (((1:ℝ)/‖toC (stripSecant γ k p)‖:ℝ):ℂ))^2
      by_cases hline : ∃ j : ℤ, p.2 = Real.pi * j
      · have hp2 : p.2 = Real.pi * (k:ℝ) :=
          stripEqOfIntMulPi hline (by linarith [hp, Real.pi_pos])
        have hsec : stripSecant γ k p = deriv (curve γ) (p.1 - p.2) := by
          rw [stripSecant_def]
          have : p.1 + p.2 - Real.pi * (k:ℝ) * 2 = p.1 - p.2 := by rw [hp2]; ring
          rw [this, secantW_self]
        simp only [stripDoubledDir]
        rw [dif_pos hline, hsec, stripMulOneDivNorm]
        exact stripCircleOf_dirC _ (by rw [toC_ne_zero_iff]; exact hder _)
      · simp only [stripDoubledDir]
        rw [dif_neg hline]
        have hper : Function.Periodic (curve γ) (2 * Real.pi) := fun t => by
          simp only [curve]; rw [Circle.exp_add_two_pi]
        have hcurve : curve γ (p.1 + p.2) = curve γ (p.1 + p.2 - Real.pi*(k:ℝ)*2) := by
          have h := hper.zsmul k (p.1 + p.2 - Real.pi*(k:ℝ)*2)
          rw [zsmul_eq_mul] at h
          rw [← h]; congr 1; ring
        have hfac : curve γ (p.1 + p.2) - curve γ (p.1 - p.2)
            = (2 * (p.2 - Real.pi*(k:ℝ))) •
                secantW (curve γ) (p.1 + p.2 - Real.pi*(k:ℝ)*2, p.1 - p.2) := by
          rw [hcurve, sub_eq_smul_secantW (hγc.of_le (by norm_num))]
          congr 1; ring
        have hchordC : chordC γ (p.1 + p.2, p.1 - p.2)
            = ((2 * (p.2 - Real.pi*(k:ℝ)) : ℝ) : ℂ) * toC (stripSecant γ k p) := by
          rw [stripSecant_def, chordC_eq_toC]
          change toC (curve γ (p.1 + p.2) - curve γ (p.1 - p.2)) = _
          rw [hfac, toC_smul]
        rw [chordUnitDir, hchordC, stripMulOneDivNorm]
        have hr : 2 * (p.2 - Real.pi*(k:ℝ)) ≠ 0 := by
          have hp2 : p.2 ≠ Real.pi * (k:ℝ) := fun h => hline ⟨k, h⟩
          intro h; exact hp2 (by linarith)
        exact stripDivNormRadial (2 * (p.2 - Real.pi*(k:ℝ))) hr (toC (stripSecant γ k p))
          (hHne p hp)
    · -- ### off the collision lines: pick the integer band in `s` containing the point
      set m : ℤ := ⌊s / Real.pi⌋ with hm
      have hm1 : Real.pi * (m:ℝ) ≤ s := by
        have h := Int.floor_le (s / Real.pi)
        rw [← hm] at h
        have h2 := mul_le_mul_of_nonneg_left h (le_of_lt Real.pi_pos)
        rwa [mul_div_cancel₀ s (ne_of_gt Real.pi_pos)] at h2
      have hm2 : s < Real.pi * ((m:ℝ) + 1) := by
        have h := Int.lt_floor_add_one (s / Real.pi)
        rw [← hm] at h
        have h2 := mul_lt_mul_of_pos_left h Real.pi_pos
        rwa [mul_div_cancel₀ s (ne_of_gt Real.pi_pos)] at h2
      have hml : Real.pi * (m:ℝ) < s := by
        rcases lt_or_eq_of_le hm1 with h | h
        · exact h
        · exact absurd ⟨m, h.symm⟩ hs
      have hNopen : IsOpen {p : ℝ × ℝ |
          Real.pi * (m:ℝ) < p.2 ∧ p.2 < Real.pi * ((m:ℝ) + 1)} := by
        have h := (isOpen_lt (continuous_const : Continuous fun _ : ℝ × ℝ => Real.pi * (m:ℝ))
            continuous_snd).inter
          (isOpen_lt continuous_snd
            (continuous_const : Continuous fun _ : ℝ × ℝ => Real.pi * ((m:ℝ) + 1)))
        simpa only [Set.setOf_and] using h
      have hqN : (σ, s) ∈ {p : ℝ × ℝ |
          Real.pi * (m:ℝ) < p.2 ∧ p.2 < Real.pi * ((m:ℝ) + 1)} := ⟨hml, hm2⟩
      have hpos : ∀ p ∈ {p : ℝ × ℝ |
          Real.pi * (m:ℝ) < p.2 ∧ p.2 < Real.pi * ((m:ℝ) + 1)},
          ¬ (∃ k : ℤ, p.2 = Real.pi * k) := by
        rintro p ⟨hp1, hp2⟩ ⟨j, hj⟩
        rw [hj] at hp1 hp2
        have h1 : (m:ℝ) < (j:ℝ) := by nlinarith [Real.pi_pos, hp1]
        have h2 : (j:ℝ) < (m:ℝ) + 1 := by nlinarith [Real.pi_pos, hp2]
        have h1' : m < j := by rw [← Int.cast_lt (R := ℝ)]; push_cast; exact h1
        have h2' : j < m + 1 := by
          have : (↑j : ℝ) < (↑(m+1) : ℝ) := by push_cast; linarith
          exact Int.cast_lt.mp this
        omega
      have hcu : ContDiffOn ℝ ((⊤:ℕ∞):WithTop ℕ∞) (chordUnitDir γ)
          {q : ℝ × ℝ | Circle.exp q.1 ≠ Circle.exp q.2} := (contDiffOn_chordUnitDir γ hγ).1
      have hmapcd : ContDiff ℝ ((⊤:ℕ∞):WithTop ℕ∞)
          (fun p : ℝ × ℝ => (p.1 + p.2, p.1 - p.2)) := by fun_prop
      have hmaps : Set.MapsTo (fun p : ℝ × ℝ => (p.1 + p.2, p.1 - p.2))
          {p : ℝ × ℝ | Real.pi * (m:ℝ) < p.2 ∧ p.2 < Real.pi * ((m:ℝ) + 1)}
          {q : ℝ × ℝ | Circle.exp q.1 ≠ Circle.exp q.2} := by
        intro p hp
        simp only [Set.mem_setOf_eq]
        intro hcon
        exact hpos p hp ((stripExpAddEqIff p.1 p.2).mp hcon)
      have hcomp : ContDiffOn ℝ ((⊤:ℕ∞):WithTop ℕ∞)
          (fun p : ℝ × ℝ => chordUnitDir γ (p.1 + p.2, p.1 - p.2))
          {p : ℝ × ℝ | Real.pi * (m:ℝ) < p.2 ∧ p.2 < Real.pi * ((m:ℝ) + 1)} :=
        ContDiffOn.comp hcu hmapcd.contDiffOn hmaps
      have hpow := hcomp.pow 2
      refine (hpow.contDiffAt (hNopen.mem_nhds hqN)).congr_of_eventuallyEq ?_
      refine Filter.eventuallyEq_of_mem (hNopen.mem_nhds hqN) ?_
      intro p hp
      rw [stripDoubledDir, dif_neg (hpos p hp)]
  · -- ### evenness in `s`
    intro σ s
    simp only [stripDoubledDir]
    by_cases hs : ∃ k : ℤ, s = Real.pi * k
    · obtain ⟨k, hk⟩ := hs
      have hs' : ∃ k : ℤ, (-s) = Real.pi * k := by
        exact ⟨-k, by rw [hk]; push_cast; ring⟩
      rw [dif_pos hs', dif_pos (show ∃ k : ℤ, s = Real.pi * k from ⟨k, hk⟩)]
      have h2s : 2 * s = (↑k : ℝ) * (2 * Real.pi) := by rw [hk]; ring
      have harg : σ - -s = (σ - s) + (↑k : ℝ) * (2 * Real.pi) := by linarith [h2s]
      rw [harg, stripDerivCurve_zsmul γ hγ]
    · have hs' : ¬ ∃ k : ℤ, (-s) = Real.pi * k := by
        intro h
        obtain ⟨k, hk⟩ := h
        exact hs ⟨-k, by rw [← neg_neg s, hk]; push_cast; ring⟩
      rw [dif_neg hs', dif_neg hs]
      have harg : ((σ:ℝ) + -s, σ - -s) = (σ - s, σ + s) := by ext <;> ring
      rw [harg, stripChordUnitDir_swap γ (σ - s) (σ + s)]
      ring
  · -- ### off the collision set
    intro σ s hne
    simp only [stripDoubledDir]
    rw [dif_neg (fun h => hne ((stripExpAddEqIff σ s).mpr h))]
    exact ((contDiffOn_chordUnitDir γ hγ).2.1 (σ + s, σ - s) hne).symm
  · -- ### the seam `s = 0`
    intro σ
    simp only [stripDoubledDir]
    have h0 : ∃ k : ℤ, (σ, (0:ℝ)).2 = Real.pi * k := ⟨0, by simp⟩
    rw [dif_pos h0, tangentDirC_exp γ hγ σ]
    simp

end Work.Drive
