import Mathlib
import Submission.Work.Asymptotics.DomainD
import Submission.Work.Asymptotics.contourLeftDefs
import Submission.Work.Asymptotics.KaxisMid.Classify
import Submission.Work.Asymptotics.F2LayerDefs
import Submission.Work.HFN.kernelTransform_seminorm_on_compact
import Submission.Work.HFN.HalfFunnel.lowRegion_badLine
import Submission.Work.HFN.HalfFunnel.lowBad_Aexp_tail
import Submission.Work.Asymptotics.HalfFunnel.lowBad_PhiSpike_deriv
import Submission.Work.HFN.BadLine.kernel_spike
import Submission.Work.HFN.BadLine.off_bound
import Submission.Work.HFN.HalfFunnel.lowBad_Phi12_deriv
import Submission.Work.HFN.HalfFunnel.lowF2_eq_paperLayer

namespace Work.HFN
open Work.Asymptotics  -- ck-hfn-fix: fork moved out of Work.Asymptotics

set_option maxHeartbeats 4000000

open UpperHalfPlane ModularGroup ModularForm
open scoped MatrixGroups UpperHalfPlane Topology ContDiff

noncomputable section

/-- The bad-line region around `n + i` (`n = ±1`). -/
def BLregion (n : ℤ) : Set ℍ :=
  {w | w ∈ DomainD ∧ (1 : ℝ) / 2 ≤ (ModularGroup.S • w).im ∧ (ModularGroup.S • w).im ≤ 2 ∧
    ‖(w : ℂ) - ((n : ℂ) + Complex.I)‖ < 1 / 10}

lemma mem_BLregion {n : ℤ} {w : ℍ} :
    w ∈ BLregion n ↔ w ∈ DomainD ∧ (1 : ℝ) / 2 ≤ (ModularGroup.S • w).im ∧
      (ModularGroup.S • w).im ≤ 2 ∧ ‖(w : ℂ) - ((n : ℂ) + Complex.I)‖ < 1 / 10 := Iff.rfl

/-- The imaginary part of a point of `BLregion n` lies in `(9/10, 11/10)`. -/
lemma BLregion_im_bounds {n : ℤ} {w : ℍ} (hw : w ∈ BLregion n) :
    (9 : ℝ) / 10 < w.im ∧ w.im < 11 / 10 := by
  have h := (mem_BLregion.mp hw).2.2.2
  have h1 : |w.im - 1| ≤ ‖(w : ℂ) - ((n : ℂ) + Complex.I)‖ := by
    have h2 : ((w : ℂ) - ((n : ℂ) + Complex.I)).im = w.im - 1 := by
      simp [Complex.sub_im, Complex.add_im]
    calc |w.im - 1| = |((w : ℂ) - ((n : ℂ) + Complex.I)).im| := by rw [h2]
      _ ≤ ‖(w : ℂ) - ((n : ℂ) + Complex.I)‖ := Complex.abs_im_le_norm _
  have h3 := abs_lt.mp (lt_of_le_of_lt h1 h)
  exact ⟨by linarith [h3.1], by linarith [h3.2]⟩

/-- For `n = 1` the real part of a point of `BLregion n` lies in `(9/10, 1)`. -/
lemma BLregion_re_bounds_one {w : ℍ} (hw : w ∈ BLregion 1) :
    (9 : ℝ) / 10 < w.re ∧ w.re < 1 := by
  have h := mem_BLregion.mp hw
  have h1 : |w.re - 1| ≤ ‖(w : ℂ) - (((1 : ℤ) : ℂ) + Complex.I)‖ := by
    have h2 : ((w : ℂ) - (((1 : ℤ) : ℂ) + Complex.I)).re = w.re - 1 := by
      simp [Complex.sub_re, Complex.add_re]
    calc |w.re - 1| = |((w : ℂ) - (((1 : ℤ) : ℂ) + Complex.I)).re| := by rw [h2]
      _ ≤ ‖(w : ℂ) - (((1 : ℤ) : ℂ) + Complex.I)‖ := Complex.abs_re_le_norm _
  have h3 := abs_lt.mp (lt_of_le_of_lt h1 h.2.2.2)
  exact ⟨by linarith [h3.1], h.1.2.1⟩

/-- For `n = -1` the real part of a point of `BLregion n` lies in `(-1, -9/10)`. -/
lemma BLregion_re_bounds_neg_one {w : ℍ} (hw : w ∈ BLregion (-1)) :
    -1 < w.re ∧ w.re < -(9 : ℝ) / 10 := by
  have h := mem_BLregion.mp hw
  have h1 : |w.re + 1| ≤ ‖(w : ℂ) - (((-1 : ℤ) : ℂ) + Complex.I)‖ := by
    have h2 : ((w : ℂ) - (((-1 : ℤ) : ℂ) + Complex.I)).re = w.re + 1 := by
      simp [Complex.sub_re, Complex.add_re]
    calc |w.re + 1| = |((w : ℂ) - (((-1 : ℤ) : ℂ) + Complex.I)).re| := by rw [h2]
      _ ≤ ‖(w : ℂ) - (((-1 : ℤ) : ℂ) + Complex.I)‖ := Complex.abs_re_le_norm _
  have h3 := abs_lt.mp (lt_of_le_of_lt h1 h.2.2.2)
  exact ⟨h.1.1, by linarith [h3.2]⟩

/-- The translate `w - n` of a point of `ℍ` (`n = ±1`), with the same imaginary part. -/
def blShift (n : ℤ) (w : ℍ) : ℍ :=
  ⟨(w : ℂ) - (n : ℂ), by
    have h : (((w : ℂ) - (n : ℂ)).im) = w.im := by simp [Complex.sub_im]
    rw [h]; exact w.im_pos⟩

lemma blShift_coe (n : ℤ) (w : ℍ) : ((blShift n w : ℍ) : ℂ) = (w : ℂ) - n := rfl

lemma blShift_re (n : ℤ) (w : ℍ) : (blShift n w).re = w.re - n := by
  rw [← UpperHalfPlane.coe_re, blShift_coe]; simp [Complex.sub_re]

lemma blShift_im (n : ℤ) (w : ℍ) : (blShift n w).im = w.im := by
  rw [← UpperHalfPlane.coe_im, blShift_coe]; simp [Complex.sub_im]

lemma blShift_eq_vadd (n : ℤ) (w : ℍ) : blShift n w = (-(n : ℝ)) +ᵥ w := by
  apply UpperHalfPlane.ext
  rw [blShift_coe, UpperHalfPlane.coe_vadd]
  push_cast
  ring

/-- **The translate `w - n` of a point of `BLregion n` lies in the fundamental domain `𝒟`.** -/
lemma BLregion_sub_mem_DomainD {n : ℤ} (hn : n = 1 ∨ n = -1) {w : ℍ} (hw : w ∈ BLregion n) :
    blShift n w ∈ DomainD := by
  obtain ⟨him1, him2⟩ := BLregion_im_bounds hw
  have habs : w.im = |w.im| := (abs_of_pos w.im_pos).symm
  have him : w.im ≤ ‖(w : ℂ) - (n : ℂ)‖ := by
    calc w.im = |w.im| := habs
      _ = |((w : ℂ) - (n : ℂ)).im| := by simp [Complex.sub_im]
      _ ≤ ‖(w : ℂ) - (n : ℂ)‖ := Complex.abs_im_le_norm _
  have him12 : w.im ≤ ‖((w : ℂ) - (n : ℂ)) - (1 / 2 : ℂ)‖ := by
    calc w.im = |w.im| := habs
      _ = |(((w : ℂ) - (n : ℂ)) - (1 / 2 : ℂ)).im| := by simp [Complex.sub_im]
      _ ≤ ‖((w : ℂ) - (n : ℂ)) - (1 / 2 : ℂ)‖ := Complex.abs_im_le_norm _
  have him12' : w.im ≤ ‖((w : ℂ) - (n : ℂ)) + (1 / 2 : ℂ)‖ := by
    calc w.im = |w.im| := habs
      _ = |(((w : ℂ) - (n : ℂ)) + (1 / 2 : ℂ)).im| := by simp [Complex.add_im, Complex.sub_im]
      _ ≤ ‖((w : ℂ) - (n : ℂ)) + (1 / 2 : ℂ)‖ := Complex.abs_im_le_norm _
  obtain ⟨hre1, hre2⟩ : -1 < w.re - (n : ℝ) ∧ w.re - (n : ℝ) < 1 := by
    rcases hn with h | h
    · subst h
      have hr := BLregion_re_bounds_one hw
      push_cast
      exact ⟨by linarith [hr.1], by linarith [hr.2]⟩
    · subst h
      have hr := BLregion_re_bounds_neg_one hw
      push_cast
      exact ⟨by linarith [hr.1], by linarith [hr.2]⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [blShift_re]; exact hre1
  · rw [blShift_re]; exact hre2
  · have hce : ((blShift n w : ℍ) : ℂ) = ((w : ℂ) - (n : ℂ)) := blShift_coe n w
    rw [hce]
    linarith
  · have hce : ((blShift n w : ℍ) : ℂ) = ((w : ℂ) - (n : ℂ)) := blShift_coe n w
    rw [hce]
    linarith

/-- The real part of `S • z` in terms of `z`. -/
lemma S_smul_re (z : ℍ) : (ModularGroup.S • z).re = -z.re / ‖(z : ℂ)‖ ^ 2 := by
  have hcoe : (((ModularGroup.S • z : ℍ)) : ℂ) = -((z : ℂ))⁻¹ := by
    rw [UpperHalfPlane.modular_S_smul, UpperHalfPlane.coe_mk, inv_neg]
  rw [← UpperHalfPlane.coe_re, hcoe, Complex.neg_re, Complex.inv_re, Complex.normSq_eq_norm_sq]
  rw [UpperHalfPlane.coe_re]
  ring

/-- The `j`-invariance under translation by `-1`. -/
lemma bl_jInvariantFun_vadd_neg_one (τ : ℍ) :
    Work.Kernels.jInvariantFun ((-1 : ℝ) +ᵥ τ) = Work.Kernels.jInvariantFun τ := by
  have h3 : (1 : ℝ) +ᵥ ((-1 : ℝ) +ᵥ τ) = τ := by
    apply UpperHalfPlane.ext
    rw [UpperHalfPlane.coe_vadd, UpperHalfPlane.coe_vadd]
    push_cast; ring
  have h2 := Work.Kernels.KernelFacts.jInvariantFun_vadd_one ((-1 : ℝ) +ᵥ τ)
  rw [h3] at h2
  exact h2.symm

lemma bl_jInvariantFun_neg_vadd (τ : ℍ) (n : ℤ) (hn : n = 1 ∨ n = -1) :
    Work.Kernels.jInvariantFun ((-(n : ℝ)) +ᵥ τ) = Work.Kernels.jInvariantFun τ := by
  rcases hn with h | h
  · subst h
    simpa using bl_jInvariantFun_vadd_neg_one τ
  · subst h
    simpa using Work.Kernels.KernelFacts.jInvariantFun_vadd_one τ

/-- **Cleanliness of the contour near the bad lines.**  For `w ∈ BLregion n` the contour `z = it`
carries no pole of `z ↦ K(w,z)`: `j w ≠ j (it)` for every `t > 0`. -/
theorem BLregion_clean {n : ℤ} (hn : n = 1 ∨ n = -1) {w : ℍ} (hw : w ∈ BLregion n)
    (t : ℝ) (ht : 0 < t) :
    Work.Kernels.jInvariantFun w ≠ Work.Kernels.jInvariantFun (Work.Kernels.imagAxis t ht) := by
  intro hjeq
  have hsub := BLregion_sub_mem_DomainD hn hw
  have hj : Work.Kernels.jInvariantFun (blShift n w) = Work.Kernels.jInvariantFun w := by
    rw [blShift_eq_vadd]
    exact bl_jInvariantFun_neg_vadd w n hn
  have hzre : ((Work.Kernels.imagAxis t ht : ℍ) : ℂ).re = 0 := by
    simp [Work.Kernels.imagAxis]
  have hre0 : (blShift n w).re = 0 := by
    rcases Work.Asymptotics.KaxisMid.eq_or_eq_S_of_re_eq_zero hsub hzre
        (by rw [hj]; exact hjeq) with h | h
    · have hc : ((blShift n w : ℍ) : ℂ).re = 0 := by rw [← h]; exact hzre
      simpa using hc
    · have hc : ((ModularGroup.S • blShift n w : ℍ) : ℂ).re = 0 := by rw [← h]; exact hzre
      have hc' : (ModularGroup.S • blShift n w).re = 0 := by simpa using hc
      rw [S_smul_re] at hc'
      have h2 : ‖(blShift n w : ℂ)‖ ^ 2 ≠ 0 :=
        pow_ne_zero _ (norm_ne_zero_iff.mpr (UpperHalfPlane.ne_zero _))
      have h3 : -((blShift n w).re) = 0 := by
        rcases div_eq_zero_iff.mp (by simpa using hc' :
          -((blShift n w).re) / ‖(blShift n w : ℂ)‖ ^ 2 = 0) with h4 | h4
        · exact h4
        · exact absurd h4 h2
      linarith
  rw [blShift_re] at hre0
  rcases hn with hh | hh
  · subst hh
    have hr := BLregion_re_bounds_one hw
    push_cast at hre0
    linarith [hr.2]
  · subst hh
    have hr := BLregion_re_bounds_neg_one hw
    push_cast at hre0
    linarith [hr.1]



/-- The Möbius action of `g ∈ SL(2,ℤ)` in coordinates (local copy). -/
lemma bl_coe_smul_eq (g : Matrix.SpecialLinearGroup (Fin 2) ℤ) (z : ℍ) :
    ((g • z : ℍ) : ℂ) =
      (((g 0 0 : ℤ) : ℂ) * (z : ℂ) + ((g 0 1 : ℤ) : ℂ)) /
      (((g 1 0 : ℤ) : ℂ) * (z : ℂ) + ((g 1 1 : ℤ) : ℂ)) := by
  rw [UpperHalfPlane.coe_specialLinearGroup_apply]
  simp only [algebraMap_int_eq]
  simp

lemma bl_im_smul_eq (g : Matrix.SpecialLinearGroup (Fin 2) ℤ) (z : ℍ) :
    (g • z).im = z.im / ‖((g 1 0 : ℤ) : ℂ) * (z : ℂ) + ((g 1 1 : ℤ) : ℂ)‖ ^ 2 := by
  rw [ModularGroup.im_smul_eq_div_normSq, ModularGroup.denom_apply, Complex.normSq_eq_norm_sq]

/-- The detour rectangle of the bad-line contour:
`{z : n·Re z ∈ [0,1/3], Im z ∈ [17/20,23/20]}`. -/
def blRect (n : ℤ) : Set ℂ :=
  {z | 0 ≤ (n : ℝ) * z.re ∧ (n : ℝ) * z.re ≤ 1 / 3 ∧ 17 / 20 ≤ z.im ∧ z.im ≤ 23 / 20}

lemma mem_blRect {n : ℤ} {z : ℂ} :
    z ∈ blRect n ↔ 0 ≤ (n : ℝ) * z.re ∧ (n : ℝ) * z.re ≤ 1 / 3 ∧ 17 / 20 ≤ z.im ∧
      z.im ≤ 23 / 20 := Iff.rfl

lemma blTau_im {n : ℤ} {w : ℍ} (hw : w ∈ BLregion n) :
    (9 : ℝ) / 10 < (blShift n w).im ∧ (blShift n w).im < 11 / 10 := by
  rw [blShift_im]; exact BLregion_im_bounds hw

lemma blTau_re_abs {n : ℤ} (hn : n = 1 ∨ n = -1) {w : ℍ} (hw : w ∈ BLregion n) :
    |(blShift n w).re| < 1 / 10 := by
  rw [blShift_re]
  rcases hn with h | h
  · subst h
    have hr := BLregion_re_bounds_one hw
    rw [abs_lt]; push_cast; constructor <;> linarith [hr.1, hr.2]
  · subst h
    have hr := BLregion_re_bounds_neg_one hw
    rw [abs_lt]; push_cast; constructor <;> linarith [hr.1, hr.2]

lemma blTau_re_mul {n : ℤ} (hn : n = 1 ∨ n = -1) {w : ℍ} (hw : w ∈ BLregion n) :
    -1 / 10 < (n : ℝ) * (blShift n w).re ∧ (n : ℝ) * (blShift n w).re < 0 := by
  rw [blShift_re]
  rcases hn with h | h
  · subst h
    have hr := BLregion_re_bounds_one hw
    constructor <;> push_cast <;> linarith [hr.1, hr.2]
  · subst h
    have hr := BLregion_re_bounds_neg_one hw
    constructor <;> push_cast <;> linarith [hr.1, hr.2]

lemma blTau_jInvariantFun {n : ℤ} (hn : n = 1 ∨ n = -1) (w : ℍ) :
    Work.Kernels.jInvariantFun (blShift n w) = Work.Kernels.jInvariantFun w := by
  rw [blShift_eq_vadd]
  exact bl_jInvariantFun_neg_vadd w n hn

/-- **Classification of the orbit points in the bad-line rectangle.**  If `z` lies in the closed
rectangle `blRect n` and `j z = j w` for some `w ∈ BLregion n`, then `z` is the *removable*
coincidence `S • (w - n)`. -/
theorem blRect_orbit_classify {n : ℤ} (hn : n = 1 ∨ n = -1) {w : ℍ} (hw : w ∈ BLregion n)
    {z : ℍ} (hz : (z : ℂ) ∈ blRect n)
    (hjeq : Work.Kernels.jInvariantFun z = Work.Kernels.jInvariantFun w) :
    z = ModularGroup.S • blShift n w := by
  obtain ⟨himlo, himhi⟩ := blTau_im hw
  obtain ⟨hrelo, hrehi⟩ := blTau_re_mul hn hw
  have hreabs : |(blShift n w).re| < 1 / 10 := blTau_re_abs hn hw
  obtain ⟨hzre_lo, hzre_hi, hzim_lo, hzim_hi⟩ := mem_blRect.mp hz
  obtain ⟨σ, hσ⟩ := Work.Asymptotics.jInvariantFun_eq_smul_of_eq
    (τ := z) (w := blShift n w) (by rw [blTau_jInvariantFun hn w]; exact hjeq)
  have hzσ : z = σ • blShift n w := hσ.symm
  set c : ℤ := σ 1 0 with hc
  set d : ℤ := σ 1 1 with hd
  set a : ℤ := σ 0 0 with ha
  set b : ℤ := σ 0 1 with hb
  have hdet : a * d - b * c = 1 := by
    have hh := σ.2
    rw [Matrix.det_fin_two] at hh
    rw [ha, hb, hc, hd]
    exact_mod_cast hh
  have hzC : (z : ℂ)
      = ((a : ℂ) * (blShift n w : ℂ) + (b : ℂ)) / ((c : ℂ) * (blShift n w : ℂ) + (d : ℂ)) := by
    rw [hzσ, bl_coe_smul_eq, ha, hb, hc, hd]
  set τ : ℍ := blShift n w with hτdef
  have himeq : (z : ℂ).im = τ.im / ‖(c : ℂ) * (τ : ℂ) + (d : ℂ)‖ ^ 2 := by
    rw [hzσ, hτdef]
    exact bl_im_smul_eq σ (blShift n w)
  have hdenne : ‖(c : ℂ) * (τ : ℂ) + (d : ℂ)‖ ≠ 0 := by
    intro h0
    have h1 : (z : ℂ).im = 0 := by rw [himeq, h0]; simp
    rw [UpperHalfPlane.coe_im] at h1
    linarith [z.im_pos]
  have hnorm_re : ((c : ℂ) * (τ : ℂ) + (d : ℂ)).re = (c : ℝ) * τ.re + (d : ℝ) := by
    simp [Complex.add_re, Complex.mul_re, UpperHalfPlane.coe_re]
  have hnorm_im : ((c : ℂ) * (τ : ℂ) + (d : ℂ)).im = (c : ℝ) * τ.im := by
    simp [Complex.add_im, Complex.mul_im, UpperHalfPlane.coe_im]
  have hnorm_sq : ‖(c : ℂ) * (τ : ℂ) + (d : ℂ)‖ ^ 2
      = ((c : ℝ) * τ.re + (d : ℝ)) ^ 2 + ((c : ℝ) * τ.im) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hnorm_re, hnorm_im]
    ring
  have hzpos : (0:ℝ) < (z : ℂ).im := by rw [UpperHalfPlane.coe_im]; exact z.im_pos
  have hden_eq : ‖(c : ℂ) * (τ : ℂ) + (d : ℂ)‖ ^ 2 = τ.im / (z : ℂ).im := by
    have hD : ‖(c : ℂ) * (τ : ℂ) + (d : ℂ)‖ ^ 2 ≠ 0 := pow_ne_zero 2 hdenne
    rw [eq_div_iff (ne_of_gt hzpos), himeq]
    exact mul_div_cancel₀ _ hD
  have hden_hi : ‖(c : ℂ) * (τ : ℂ) + (d : ℂ)‖ ^ 2 ≤ (22 : ℝ) / 17 := by
    rw [hden_eq, div_le_iff₀ hzpos]
    nlinarith [himhi, hzim_lo, τ.im_pos, hzpos]
  have hc2 : (c : ℝ) ^ 2 ≤ 1 := by
    have hkey : (c : ℝ) ^ 2 * (81 / 100 : ℝ) ≤ (22 : ℝ) / 17 := by
      have h1 : (81 / 100 : ℝ) < τ.im ^ 2 := by nlinarith [himlo]
      calc (c : ℝ) ^ 2 * (81 / 100 : ℝ) ≤ (c : ℝ) ^ 2 * τ.im ^ 2 :=
            mul_le_mul_of_nonneg_left (le_of_lt h1) (sq_nonneg _)
        _ = ((c : ℝ) * τ.im) ^ 2 := by ring
        _ ≤ ((c : ℝ) * τ.re + (d : ℝ)) ^ 2 + ((c : ℝ) * τ.im) ^ 2 := by
            nlinarith [sq_nonneg ((c : ℝ) * τ.re + (d : ℝ))]
        _ = ‖(c : ℂ) * (τ : ℂ) + (d : ℂ)‖ ^ 2 := hnorm_sq.symm
        _ ≤ (22 : ℝ) / 17 := hden_hi
    have h2 : ((c ^ 2 : ℤ) : ℝ) < 2 := by push_cast; nlinarith [hkey]
    have h3 : (c ^ 2 : ℤ) < 2 := by exact_mod_cast h2
    have h4 : (c ^ 2 : ℤ) ≤ 1 := by omega
    have h5 : ((c ^ 2 : ℤ) : ℝ) ≤ 1 := by exact_mod_cast h4
    push_cast at h5
    exact h5
  have hc_le : c ≤ 1 := by
    by_contra hcon
    push_neg at hcon
    have h2 : (2 : ℤ) ≤ c := by omega
    have h2' : (2 : ℝ) ≤ (c : ℝ) := by exact_mod_cast h2
    nlinarith [hc2]
  have hc_ge : -1 ≤ c := by
    by_contra hcon
    push_neg at hcon
    have h2 : c ≤ -2 := by omega
    have h2' : (c : ℝ) ≤ -2 := by exact_mod_cast h2
    nlinarith [hc2]
  have hc_cases : c = -1 ∨ c = 0 ∨ c = 1 := by omega
  -- Step 1: `c ≠ 0`, since `c = 0` would force `z = τ + k` and contradict the real-part bound
  have hcne : c ≠ 0 := by
    intro hcz
    have had : a * d = 1 := by
      have hh := hdet
      rw [hcz] at hh
      linarith
    have hd1 : d = 1 ∨ d = -1 := by
      rcases Int.eq_one_or_neg_one_of_mul_eq_one' had with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact Or.inl h2
      · exact Or.inr h2
    have hzk : ∃ k : ℤ, (z : ℂ) = (τ : ℂ) + (k : ℂ) := by
      rcases hd1 with hd1' | hd1'
      · have ha1 : a = 1 := by rw [hd1'] at had; omega
        refine ⟨b, ?_⟩
        rw [hzC, hcz, ha1, hd1']
        norm_num
      · have ha1 : a = -1 := by rw [hd1'] at had; omega
        refine ⟨-b, ?_⟩
        rw [hzC, hcz, ha1, hd1']
        simp only [Int.cast_zero, Int.cast_neg, Int.cast_one, zero_mul, zero_add]
        rw [div_neg]
        ring
    obtain ⟨k, hk⟩ := hzk
    have hre : (n : ℝ) * (z : ℂ).re = (n : ℝ) * τ.re + (n : ℝ) * (k : ℝ) := by
      have h := congrArg (fun u : ℂ => (n : ℝ) * u.re) hk
      rw [Complex.add_re, UpperHalfPlane.coe_re, Complex.intCast_re, mul_add] at h
      exact h
    have hge1 : (1 : ℤ) ≤ n * k := by
      have hlt : 0 < (n : ℝ) * (k : ℝ) := by
        have h2 := hzre_lo
        rw [hre] at h2
        linarith [hrelo]
      by_contra hcon
      push_neg at hcon
      have h3 : n * k ≤ 0 := by omega
      have h4 : (((n * k : ℤ)) : ℝ) ≤ 0 := by exact_mod_cast h3
      have h5 : (((n * k : ℤ)) : ℝ) = (n : ℝ) * (k : ℝ) := by push_cast; ring
      rw [h5] at h4
      linarith
    have hge1' : (1 : ℝ) ≤ (n : ℝ) * (k : ℝ) := by
      have h5 : (((n * k : ℤ)) : ℝ) = (n : ℝ) * (k : ℝ) := by push_cast; ring
      have h6 : (1 : ℝ) ≤ (((n * k : ℤ)) : ℝ) := by exact_mod_cast hge1
      rwa [h5] at h6
    have h2 := hzre_hi
    rw [hre] at h2
    linarith [hge1', hrelo, h2]
  have hcase : c = -1 ∨ c = 1 := by
    rcases hc_cases with h | h | h
    · exact Or.inl h
    · exact absurd h hcne
    · exact Or.inr h
  -- Step 2: for `c = ±1` the point is `S τ + k`
  have him1 : ((c : ℝ) * τ.im) ^ 2 ≥ (81 : ℝ) / 100 := by
    have h1 : (c : ℝ) ^ 2 = 1 := by rcases hcase with h | h <;> rw [h] <;> norm_num
    rw [mul_pow, h1, one_mul]
    nlinarith [himlo]
  have hsmall : ((c : ℝ) * τ.re + (d : ℝ)) ^ 2 ≤ (823 : ℝ) / 1700 := by
    nlinarith [hnorm_sq, hden_hi, him1]
  have hd0 : d = 0 := by
    have h4 : |(c : ℝ) * τ.re + (d : ℝ)| < 7 / 10 := by
      have h7 : (823 : ℝ) / 1700 < (7 / 10 : ℝ) ^ 2 := by norm_num
      have hA : ((c : ℝ) * τ.re + (d : ℝ)) ^ 2 < (7 / 10 : ℝ) ^ 2 :=
        lt_of_le_of_lt hsmall h7
      rw [abs_lt]
      constructor <;> nlinarith [hA]
    have h1 : |(c : ℝ) * τ.re| ≤ |(c : ℝ)| * |τ.re| := le_of_eq (abs_mul _ _)
    have h2 : |(c : ℝ)| = 1 := by rcases hcase with h | h <;> rw [h] <;> norm_num
    rw [h2, one_mul] at h1
    have h3 : |(d : ℝ)| ≤ |(c : ℝ) * τ.re + (d : ℝ)| + |(c : ℝ) * τ.re| := by
      calc |(d : ℝ)| = |((c : ℝ) * τ.re + (d : ℝ)) - ((c : ℝ) * τ.re)| := by
              congr 1; ring
        _ ≤ |((c : ℝ) * τ.re + (d : ℝ))| + |((c : ℝ) * τ.re)| := abs_sub _ _
    have h6 : |(d : ℝ)| < 1 := by linarith [h3, h4, hreabs]
    have h6' : -(1 : ℝ) < (d : ℝ) ∧ (d : ℝ) < 1 := abs_lt.mp h6
    have h6a : (-1 : ℤ) < d := by exact_mod_cast h6'.1
    have h6b : d < (1 : ℤ) := by exact_mod_cast h6'.2
    omega
  have hbc : b = -c := by
    have hh : b * c = -1 := by
      have h1 := hdet
      rw [hd0] at h1
      ring_nf at h1
      linarith
    have h3 : c * c = 1 := by rcases hcase with h | h <;> rw [h] <;> norm_num
    calc b = b * (c * c) := by rw [h3, mul_one]
      _ = (b * c) * c := by ring
      _ = -c := by rw [hh]; ring
  have hc2c : (c : ℂ) * (c : ℂ) = 1 := by rcases hcase with h | h <;> rw [h] <;> norm_num
  have h3c : (c : ℂ) * ((a : ℂ) * (c : ℂ)) = (a : ℂ) := by
    rw [mul_comm (c : ℂ) ((a : ℂ) * (c : ℂ)), mul_assoc, hc2c, mul_one]
  have hval : ((a : ℂ) * (τ : ℂ) + (b : ℂ)) / ((c : ℂ) * (τ : ℂ) + (d : ℂ))
      = -1 / (τ : ℂ) + ((a * c : ℤ) : ℂ) := by
    rw [hd0, hbc]
    have hnum : (a : ℂ) * (τ : ℂ) + (↑(-c) : ℂ)
        = (c : ℂ) * ((a : ℂ) * (c : ℂ) * (τ : ℂ) - 1) := by
      have hL : (a : ℂ) * (τ : ℂ) = ((c : ℂ) * ((a : ℂ) * (c : ℂ))) * (τ : ℂ) := by rw [h3c]
      rw [hL]; push_cast; ring
    rw [hnum]
    have hcneH : (c : ℂ) ≠ 0 := by rcases hcase with h | h <;> rw [h] <;> norm_num
    have hτneH : (τ : ℂ) ≠ 0 := UpperHalfPlane.ne_zero τ
    field_simp
    push_cast
    ring
  have hSτ : ((ModularGroup.S • τ : ℍ) : ℂ) = -1 / (τ : ℂ) := by
    have h1 : ((ModularGroup.S • τ : ℍ) : ℂ) = -((τ : ℂ))⁻¹ := by
      rw [UpperHalfPlane.modular_S_smul, UpperHalfPlane.coe_mk, inv_neg]
    rw [h1, div_eq_mul_inv]
    ring
  have key : ∃ k : ℤ, (z : ℂ) = ((ModularGroup.S • τ : ℍ) : ℂ) + (k : ℂ) :=
    ⟨a * c, by rw [hzC, hval, hSτ]⟩
  obtain ⟨k, hk⟩ := key
  -- Step 3: the real-part constraint forces `k = 0`
  have hzeq : z = (k : ℝ) +ᵥ (ModularGroup.S • τ) := by
    apply UpperHalfPlane.ext
    rw [UpperHalfPlane.coe_vadd, hk]
    push_cast; ring
  have hSre : (ModularGroup.S • τ).re = -τ.re / ‖(τ : ℂ)‖ ^ 2 := S_smul_re τ
  have hnorm2pos : (0:ℝ) < ‖(τ : ℂ)‖ ^ 2 := by
    have h1 : (0:ℝ) < τ.im := τ.im_pos
    have h2 : τ.im ≤ ‖(τ : ℂ)‖ := by
      calc τ.im = |τ.im| := (abs_of_pos h1).symm
        _ = |(τ : ℂ).im| := by rw [UpperHalfPlane.coe_im]
        _ ≤ ‖(τ : ℂ)‖ := Complex.abs_im_le_norm _
    nlinarith
  have hnz : (n : ℝ) * (z : ℂ).re
      = (n : ℝ) * ((ModularGroup.S • τ : ℍ) : ℂ).re + (n : ℝ) * (k : ℝ) := by
    have h := congrArg (fun u : ℂ => (n : ℝ) * u.re) hk
    have hk2 : ((k : ℂ)).re = (k : ℝ) := by simp
    simp only [Complex.add_re, UpperHalfPlane.coe_re, hk2, mul_add] at h
    exact h
  have hSbound : (0 : ℝ) < (n : ℝ) * ((ModularGroup.S • τ : ℍ) : ℂ).re
      ∧ (n : ℝ) * ((ModularGroup.S • τ : ℍ) : ℂ).re < 1 / 3 := by
    have hcoe : ((ModularGroup.S • τ : ℍ) : ℂ).re = -τ.re / ‖(τ : ℂ)‖ ^ 2 := by
      rw [show ((ModularGroup.S • τ : ℍ) : ℂ).re = (ModularGroup.S • τ).re from rfl, hSre]
    rw [hcoe]
    have hval : (n : ℝ) * (-τ.re / ‖(τ : ℂ)‖ ^ 2) = -((n : ℝ) * τ.re) / ‖(τ : ℂ)‖ ^ 2 := by
      have hden : ‖(τ : ℂ)‖ ^ 2 ≠ 0 := ne_of_gt hnorm2pos
      field_simp
    rw [hval]
    have h3 : (81 : ℝ) / 100 < ‖(τ : ℂ)‖ ^ 2 := by
      have h4 : |(τ : ℂ).im| = τ.im := by rw [UpperHalfPlane.coe_im, abs_of_pos τ.im_pos]
      nlinarith [norm_nonneg (τ : ℂ), Complex.abs_im_le_norm (τ : ℂ), himlo, h4]
    constructor
    · exact div_pos (by linarith [hrehi]) hnorm2pos
    · have h1 : -((n : ℝ) * τ.re) < 1 / 10 := by linarith [hrelo]
      rw [div_lt_iff₀ hnorm2pos]
      nlinarith [h1, h3]
  have hkint : (n : ℝ) * (k : ℝ) = 0 := by
    have hlo := hzre_lo
    have hhi := hzre_hi
    rw [hnz] at hlo hhi
    have hkZ : n * k = 0 := by
      have hnk_le : n * k ≤ 0 := by
        by_contra hcon
        push_neg at hcon
        have h2 : (1 : ℤ) ≤ n * k := by omega
        have h2' : (1 : ℝ) ≤ (((n * k : ℤ)) : ℝ) := by exact_mod_cast h2
        push_cast at h2'
        linarith [hhi, hSbound.2]
      have hnk_ge : 0 ≤ n * k := by
        by_contra hcon
        push_neg at hcon
        have h2 : n * k ≤ -1 := by omega
        have h2' : (((n * k : ℤ)) : ℝ) ≤ -1 := by exact_mod_cast h2
        push_cast at h2'
        linarith [hlo, hSbound.1]
      exact le_antisymm hnk_le hnk_ge
    have : ((n * k : ℤ) : ℝ) = (n : ℝ) * (k : ℝ) := by push_cast; ring
    rw [← this, hkZ]; norm_num
  have hk0 : k = 0 := by
    rcases hn with h | h
    · rw [h] at hkint; simpa using hkint
    · rw [h] at hkint; simpa using hkint
  rw [hk0] at hzeq
  simpa using hzeq

/-! ## Remaining work: the layer, the piece seminorm bounds and the transfer

The classification `blRect_orbit_classify` (above) together with the two proved companions

* `Work.Asymptotics.BadLine.flat_blregion` — flatness at the cusp `0` on `BLregion n`, `t ≤ 17/20`;
* `Work.Asymptotics.BadLine.tail_blregion` — the cusp-`∞` expansion `K ≈ Aexp G` for `t ≥ 23/20`
  (with `G` of moderate growth on `𝒟` and `G 1 j = 0` for `d = 8`),

and the still-to-be-proved

* `Work.Asymptotics.BadLine.bulk_blregion` — the uniform bound on `K` on the three *edges* of the
  rectangle `blRect n` (the deformation contour),
* `Work.Asymptotics.BadLine.detour_blregion` — the deformation identity
  `∫_{(17/20,23/20)} Kaxis (w, t) e^{-π r² t} dt = detourRight ℓ d r 1 (3/20) (1/3) w`
  (Cauchy–Goursat on `blRect n` via `Work.Asymptotics.rectInt_eq_residue` with residue `0`;
  the classification above is exactly the input saying that the only `SL(2,ℤ)`-orbit point of `w`
  in the closed rectangle is the removable coincidence `S • (w - n)`),

are the inputs of the following assembly.  Define the layer

  `F₂ w r = sinSqC r * ( ∫_{(0,17/20)} + detourRight(1,3/20,1/3) + ∫_{(23/20,∞)} (Kaxis - Aexp) )
              + highPartT₀ G w r`,

for which `F₂ = kernelTransform (Kfun ℓ d) w ·` wherever the latter's integrand is integrable
(the deformation identity plus `sinSqC r * ∫_{(23/20,∞)}Aexp = highPartT₀`), and whose
`r`-seminorms are bounded on `BLregion n` by differentiating under the integral sign:
the first piece uses `flat_blregion` (super-polynomial decay in `r`), the detour piece is an
integral over the fixed compact contour with `|e^{π i r² z}| = e^{-π r² Im z} ≤ e^{-17π r²/20}`,
the `(23/20,∞)` piece uses `tail_blregion`, and the explicit high part is handled as in
`Work.Asymptotics.highPart_local_seminorm`.  A `BLregion`-restricted copy of
`Work.Asymptotics.kernelTransform_seminorm_of_layer` (same proof, with the `τ`-quantifier
restricted to `BLregion n`) then yields the seminorm bound for `kernelTransform` itself, and
`seminormK_cusp0_badline` follows by taking the union over `n = 1` and `n = -1`.
-/

/-- **`BLregion n` is contained in the low bad-line set `HalfFunnel.lowBadSet`** (`n = ±1`):
`BLregion_im_bounds` gives `9/10 < Im w < 11/10 ⊂ [1/2,2]`, and `BLregion_re_bounds_one` /
`BLregion_re_bounds_neg_one` give `|Re w| > 9/10 > 3/4`. -/
lemma BLregion_subset_lowBadSet {n : ℤ} (hn : n = 1 ∨ n = -1) {w : ℍ} (hw : w ∈ BLregion n) :
    Work.Asymptotics.HalfFunnel.lowBadSet w := by
  obtain ⟨him1, him2⟩ := BLregion_im_bounds hw
  refine ⟨(mem_BLregion.mp hw).1, by linarith, by linarith, ?_⟩
  rcases hn with h | h
  · subst h
    exact Or.inl (by have hr := BLregion_re_bounds_one hw; linarith [hr.1])
  · subst h
    exact Or.inr (by have hr := BLregion_re_bounds_neg_one hw; linarith [hr.2])

/-!
## State of this file (handoff note)

Everything in this file is proved and `seminormK_cusp0_badline` depends only on
`propext, Classical.choice, Quot.sound`.  The analytic inputs on the bad-line set `lowBadSet` are

* `Work.Asymptotics.BadLine.kernel_spike` — the pointwise translate-pole decomposition
  `‖K^{(d)}(τ,it) - tpole τ t‖ ≤ C` on `lowBadSet` (file
  `Submission/Work/Asymptotics/BadLine/kernel_spike.lean`, with its companion
  `Work.Asymptotics.BadLine.off_bound` bounding `K` away from the spike window),
* `Work.Asymptotics.HalfFunnel.lowBad_Aexp_tail` (cusp-`i∞` expansion on `lowBadSet`),
* `Work.Asymptotics.HalfFunnel.lowBad_PhiSpike_deriv` (the explicit spike integral),
* `Work.Asymptotics.HalfFunnel.lowBad_Phi12_deriv` (the spike-removed amplitudes),
* `Work.Asymptotics.HalfFunnel.lowBad_hsemi_of_bounds` (the `r`-seminorm bound for `lowF2`),
* `Work.Asymptotics.HalfFunnel.lowF2_eq_paperLayer`, `Work.Asymptotics.Compact.local_agreement`,
* `Work.Asymptotics.kernelTransform_seminorm_of_layer_on_compact`.

(NB: the older route through `Work.Asymptotics.HalfFunnel.lowBad_spike_decomp` is *not* used: that
module declares `norm_tpole_le_of_sep` under the same name as
`Work.Asymptotics.HalfFunnel.lowBad_kernel_spike_b`, so importing it clashes with the current
`lowRegion_badLine` chain.)

The missing input is the pointwise decomposition (verified numerically, see below)

`‖K^{(d)}(τ,it) - tpole τ t‖ ≤ C`  for `τ ∈ lowBadSet`, `0 < t ≤ lowT = 3`,  (†)

with `tpole τ t = (tsign τ/2π)/(it - (τ - tsign τ))`.

### Numerical verification of (†) (workspace root, independent implementation)

`.lbk_spike/kfclean.py` implements `Kfun`/`tpole` independently; `_probe_kernel_spike.py` and
`_myksprobe.py` evaluate `‖K(τ,it) - tpole τ t‖`.  Results (d = 8):

* for `s ∈ {1/2,3/4,3/2,2}`, `τ = 1 - ε + i s`, `ε ∈ [10⁻²,10⁻¹⁰]`, all `t ∈ (0,3]`: value
  bounded by `60` and independent of `ε`;
* at the spike centre `t = s` for `s ∈ [0.9,1.1]` **including the degenerate height `s = 1`**
  (`τ = 1 - ε + i s`, `ε ∈ [10⁻²,10⁻⁸]`): bounded by `0.83`, independent of `ε`.

So (†) is true, uniformly even at `Im τ = 1`, where the two opposite-side orbit points
`z₀ = τ - n` and `z* = S z₀` merge.

### Proof plan for (†) (each step with the lemma it should use)

Let `z₀ := τ - n` (so `j z₀ = j τ` by `Γ(2)`-periodicity), `z* := S z₀ = -1/z₀`, and
`growthPrefactor τ ζ = Δ(τ)Δ(ζ)^e(j τ - j ζ)`, `K = KfunClear / growthPrefactor` off the
coincidences (both factors are *continuous*; `KfunClear` vanishes at `z*`).

1. **Lower bound on the `j`-difference.**  For `ζ = it`, `0 < t ≤ lowT`,
   `‖j ζ - j z₀‖ ≥ c ‖ζ - z₀‖ ‖ζ - z*‖` on `BLregion n` (`n = ±1`), equivalently
   `R(τ,ζ) := ‖jζ - jz₀‖ / (‖ζ-z₀‖‖ζ-z*‖) ≥ c`.  Numerics (`_myLprobe.py`) give
   `R ≥ 2.4·10⁴` uniformly for `s ∈ [0.95,1.05]`, `ε ∈ [10⁻⁸,10⁻²]`, `|t - s| ≤ 0.2`.
   Proof: `R` is continuous and nowhere zero on the compact set
   `{τ ∈ closure(BLregion n)} × {t ∈ (0,3]}` away from `t = 0`; at the coincidences
   (`τ₀ = n + i t₀`, `ζ₀ = i t₀`) the limit of `R` is `‖j'(i t₀)‖ / ‖t₀ - 1/t₀‖`-like and is
   `‖j''(i)‖/2` for `t₀ = 1` (where `j'(i) = 0`), using
   `Work.Asymptotics.KaxisMid.exists_j_sub_lower_lambda_near_I` /
   `Work.Asymptotics.MiddleRange.exists_diffQuotient_lower_general` /
   `Work.Asymptotics.j_sub_I_quadratic`; for `t → 0` use `j( it ) → ∞`
   (`DeltaFun_imagAxis_atZero`, `jInvariantFun_imagAxis_atZero`).
2. **Spike `|t - τ.im| ≤ 1/8`.**  `F(ζ) := KfunClear(τ,ζ)(ζ - z₀) - (n/2π) growthPrefactor(τ,ζ)`
   is holomorphic in `ζ`, continuous, and vanishes at `z₀` and at `z*` (at both points both
   terms vanish); `M := sup` of `‖F‖` on a fixed ball about `z₀` of radius
   `ρ = max 1/4 (4‖τ.re - n‖)` (compactness of `closure (BLregion n)` times the ball), so the
   two-zero bound `Work.Asymptotics.KaxisMid.norm_le_of_norm_le_of_two_zeros` /
   `three_zeros_bound_ball` gives `‖F(ζ)‖ ≤ (4M/ρ²)‖ζ-z₀‖‖ζ-z*‖`, and then
   `‖K - tpole‖ = ‖F(ζ)‖ / ‖growthPrefactor(ζ)‖ ≤ (4M/ρ²) / (c·c')` by step 1 and the lower
   bound `‖Δ(τ)‖‖Δ(ζ)‖^e ≥ c' > 0` on the region.
3. **Off spike `1/8 ≤ |t - τ.im|`.**  `‖K‖ = ‖KfunClear‖/‖growthPrefactor‖`, with
   `‖KfunClear‖ ≤ M'` (compactness) and `‖KfunClear(ζ)‖ ≤ C‖ζ - z*‖` (one-zero bound at `z*`,
   `*_eq_zero` + `Work.Asymptotics.KaxisMid.one_zero_apply`), so
   `‖K‖ ≤ C‖ζ-z*‖/(‖Δ τ‖‖Δ ζ‖^e c‖ζ-z₀‖‖ζ-z*‖) ≤ C/(c c' ‖ζ-z₀‖) ≤ C/(c c' · 1/8)`; `tpole` is
   bounded by `Work.Asymptotics.HalfFunnel.norm_tpole_le_of_sep`.  The sub-case
   `|t - 1/Im τ| ≥ η` is also covered by the already proved
   `Work.Asymptotics.middle_bound_near_bad_line`.
4. Glue 2 and 3.
-/

/-! ## The bad-line layer and its `r`-seminorm bound

The region `BLregion n` (`n = ±1`) lies inside the "low bad-line" set `HalfFunnel.lowBadSet` of
`Submission/Work/Asymptotics/HalfFunnel/`: indeed `w ∈ BLregion n` forces `w.im ∈ (9/10,11/10)`
(`BLregion_im_bounds`) and `|w.re| > 9/10` (`BLregion_re_bounds_one`/`_neg_one`), so
`1/2 ≤ w.im ≤ 2` and `|w.re| > 3/4`.

On `lowBadSet` the pole-split layer `HalfFunnel.lowF2` is available: the translate pole
`tpole τ t = (sign τ/2π)/(it - (τ - sign τ))` is extracted from the two contour integrals
(`PhiOne` over `(0,1]`, `PhiTwo` over `[1,∞)`) and added back in the explicit spike integral
`PhiSpike`; `HalfFunnel.lowBad_hsemi_of_bounds` then gives the `r`-seminorm bound on `lowBadSet`
from five analytic inputs.  It remains to

* transfer the bound to `BLregion n` and to puncture the layer at `r = 0` (where `lowF2` takes the
  value `highPart G τ 0 ≠ 0` while `kernelTransform ` is `0`), and
* check that the punctured layer still agrees with `kernelTransform` on the integrable range. -/

/-- `HalfFunnel.lowF2` is even in the radial variable. -/
lemma lowF2_neg (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (τ : ℍ) (r : ℝ) :
    Work.Asymptotics.HalfFunnel.lowF2 ℓ d τ (-r) = Work.Asymptotics.HalfFunnel.lowF2 ℓ d τ r := by
  simp only [Work.Asymptotics.HalfFunnel.lowF2, neg_sq, highPart_neg]

/-- **The bad-line layer**: `HalfFunnel.lowF2` with the single value at `r = 0` replaced by `0`.
Both `blLowF2 τ` and `Work.Kernels.kernelTransform (Kfun ℓ d) τ` vanish at `r = 0`, so the
puncture only affects the value (and not the positive-order iterated derivatives, by evenness). -/
def blLowF2 (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (τ : ℍ) (r : ℝ) : ℂ :=
  if r = 0 then 0 else Work.Asymptotics.HalfFunnel.lowF2 ℓ d τ r

lemma blLowF2_neg (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (τ : ℍ) (r : ℝ) :
    blLowF2 ℓ d τ (-r) = blLowF2 ℓ d τ r := by
  rw [blLowF2, blLowF2]
  by_cases h : r = 0
  · subst h; simp
  · rw [if_neg h, if_neg (neg_ne_zero.mpr h), lowF2_neg]

/-- **Smoothness in the radial variable.**  For `τ` in the bad-line set the pole-split layer
`HalfFunnel.lowF2 τ` is analytic in `r`: the three spike-removed pieces are analytic on `(-1,∞)`
(`HalfFunnel.contDiffOn_part`) and are composed with `r ↦ r²`, and the explicitly closed `highPart`
is analytic (`Work.Asymptotics.contDiff_omega_highPart`). -/
lemma lowF2_contDiff (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    {Cdec : ℝ} (hCdec : 0 ≤ Cdec)
    (hdec1 : ∀ (τ : ℍ), Work.Asymptotics.HalfFunnel.lowBadSet τ → ∀ t : ℝ, 0 < t →
      t ≤ Work.Asymptotics.HalfFunnel.lowT →
      ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
        - Work.Asymptotics.HalfFunnel.tpole τ t‖ ≤ Cdec)
    (hdec2 : ∀ (τ : ℍ), Work.Asymptotics.HalfFunnel.lowBadSet τ → ∀ t : ℝ, 0 < t →
      t ≤ Work.Asymptotics.HalfFunnel.lowT →
      Work.Asymptotics.HalfFunnel.lowRho ≤ |t - τ.im| →
      ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t‖ ≤ Cdec)
    (htail : ∃ Ct Mt : ℝ, 0 < Ct ∧ 0 ≤ Mt ∧
      ∀ (τ : ℍ), Work.Asymptotics.HalfFunnel.lowBadSet τ →
      ∀ t : ℝ, Work.Asymptotics.HalfFunnel.lowT ≤ t →
      ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
        - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t‖
        ≤ Ct * (1 + t) ^ Mt * Real.exp (-(Real.pi * t)))
    {τ : ℍ} (hτ : Work.Asymptotics.HalfFunnel.lowBadSet τ) :
    ContDiff ℝ ω (fun r : ℝ => Work.Asymptotics.HalfFunnel.lowF2 ℓ d τ r) := by
  have hΦ : ContDiffOn ℝ ω (fun x : ℝ => Work.Asymptotics.HalfFunnel.PhiOne ℓ d τ x
      + Work.Asymptotics.HalfFunnel.PhiTwo ℓ d τ x + Work.Asymptotics.HalfFunnel.PhiSpike τ x)
      (Set.Ioi (-1)) :=
    Work.HFN.HalfFunnel.contDiffOn_part ℓ d hd hCdec hdec1 hdec2 htail hτ
  have hΦ2 : ContDiff ℝ ω (fun s : ℝ => Work.Asymptotics.HalfFunnel.PhiOne ℓ d τ (s ^ 2)
      + Work.Asymptotics.HalfFunnel.PhiTwo ℓ d τ (s ^ 2)
      + Work.Asymptotics.HalfFunnel.PhiSpike τ (s ^ 2)) := by
    have h := hΦ.comp_contDiff (n := ω) (f := fun r : ℝ => r ^ 2) (by fun_prop)
      (fun r => by rw [Set.mem_Ioi]; nlinarith [sq_nonneg r])
    simpa [Function.comp_def] using h
  have hcos : ContDiff ℝ ω (fun s : ℝ => (2 - 2 * Real.cos (Real.pi * s ^ 2) : ℂ)) := by
    have h1 : (fun s : ℝ => (2 - 2 * Real.cos (Real.pi * s ^ 2) : ℂ))
        = fun s : ℝ => sinSq s := by
      funext s; rw [sinSq_eq_two_sub_two_cos]; push_cast; ring
    rw [h1]; exact contDiff_omega_sinSq
  have hhp : ContDiff ℝ ω
      (fun s : ℝ => Work.Asymptotics.highPart (Work.Asymptotics.Gcusp ℓ d) τ s) :=
    Work.Asymptotics.contDiff_omega_highPart (Work.Asymptotics.Gcusp ℓ d) τ
  have hfun : (fun r : ℝ => Work.Asymptotics.HalfFunnel.lowF2 ℓ d τ r)
      = fun r : ℝ => (2 - 2 * Real.cos (Real.pi * r ^ 2) : ℂ)
          * (Work.Asymptotics.HalfFunnel.PhiOne ℓ d τ (r ^ 2)
            + Work.Asymptotics.HalfFunnel.PhiTwo ℓ d τ (r ^ 2)
            + Work.Asymptotics.HalfFunnel.PhiSpike τ (r ^ 2))
          + Work.Asymptotics.highPart (Work.Asymptotics.Gcusp ℓ d) τ r := rfl
  rw [hfun]
  exact (hcos.mul hΦ2).add hhp

/-- The radial differentiability needed for the puncture at `r = 0`. -/
lemma lowF2_differentiable (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    {Cdec : ℝ} (hCdec : 0 ≤ Cdec)
    (hdec1 : ∀ (τ : ℍ), Work.Asymptotics.HalfFunnel.lowBadSet τ → ∀ t : ℝ, 0 < t →
      t ≤ Work.Asymptotics.HalfFunnel.lowT →
      ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
        - Work.Asymptotics.HalfFunnel.tpole τ t‖ ≤ Cdec)
    (hdec2 : ∀ (τ : ℍ), Work.Asymptotics.HalfFunnel.lowBadSet τ → ∀ t : ℝ, 0 < t →
      t ≤ Work.Asymptotics.HalfFunnel.lowT →
      Work.Asymptotics.HalfFunnel.lowRho ≤ |t - τ.im| →
      ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t‖ ≤ Cdec)
    (htail : ∃ Ct Mt : ℝ, 0 < Ct ∧ 0 ≤ Mt ∧
      ∀ (τ : ℍ), Work.Asymptotics.HalfFunnel.lowBadSet τ →
      ∀ t : ℝ, Work.Asymptotics.HalfFunnel.lowT ≤ t →
      ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
        - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t‖
        ≤ Ct * (1 + t) ^ Mt * Real.exp (-(Real.pi * t)))
    {τ : ℍ} (hτ : Work.Asymptotics.HalfFunnel.lowBadSet τ) :
    Differentiable ℝ (fun r : ℝ => Work.Asymptotics.HalfFunnel.lowF2 ℓ d τ r) :=
  (lowF2_contDiff ℓ d hd hCdec hdec1 hdec2 htail hτ).differentiable (by simp)

/-- **The `r`-seminorm bound for the punctured bad-line layer.**  This is
`HalfFunnel.lowBad_hsemi_of_bounds` (the bound for `lowF2` on `lowBadSet`) transported to the
punctured layer `blLowF2`: for `r ≠ 0` the two agree near `r`, and at `r = 0` the puncture is
harmless for the positive-order derivatives (`punctured_iteratedDeriv`, using the evenness
`lowF2_neg` and the smoothness `lowF2_contDiff`). -/
theorem blLowF2_seminorm (ℓ : Work.Kernels.LogLambdaData) (d : ℕ) (hd : d = 8 ∨ d = 24)
    {Cdec : ℝ} (hCdec : 0 ≤ Cdec)
    (hdec1 : ∀ (τ : ℍ), Work.Asymptotics.HalfFunnel.lowBadSet τ → ∀ t : ℝ, 0 < t →
      t ≤ Work.Asymptotics.HalfFunnel.lowT →
      ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
        - Work.Asymptotics.HalfFunnel.tpole τ t‖ ≤ Cdec)
    (hdec2 : ∀ (τ : ℍ), Work.Asymptotics.HalfFunnel.lowBadSet τ → ∀ t : ℝ, 0 < t →
      t ≤ Work.Asymptotics.HalfFunnel.lowT →
      Work.Asymptotics.HalfFunnel.lowRho ≤ |t - τ.im| →
      ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t‖ ≤ Cdec)
    (htail : ∃ Ct Mt : ℝ, 0 < Ct ∧ 0 ≤ Mt ∧
      ∀ (τ : ℍ), Work.Asymptotics.HalfFunnel.lowBadSet τ →
      ∀ t : ℝ, Work.Asymptotics.HalfFunnel.lowT ≤ t →
      ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
        - Work.Asymptotics.Aexp (Work.Asymptotics.Gcusp ℓ d) τ t‖
        ≤ Ct * (1 + t) ^ Mt * Real.exp (-(Real.pi * t)))
    (hPhiSpike : ∀ m N : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ (τ : ℍ),
      Work.Asymptotics.HalfFunnel.lowBadSet τ → ∀ x : ℝ, 0 ≤ x →
      ‖iteratedDeriv m (fun x : ℝ => Work.Asymptotics.HalfFunnel.PhiSpike τ x) x‖
        ≤ K * (1 + x) ^ (-(N : ℝ)))
    (hPhi12 : ∀ m N : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ (τ : ℍ),
      Work.Asymptotics.HalfFunnel.lowBadSet τ → ∀ x : ℝ, 0 ≤ x →
      ‖iteratedDeriv m (fun x : ℝ => Work.Asymptotics.HalfFunnel.PhiOne ℓ d τ x
        + Work.Asymptotics.HalfFunnel.PhiTwo ℓ d τ x) x‖ ≤ K * (1 + x) ^ (-(N : ℝ))) :
    ∀ k l : ℕ, ∃ C : ℝ, 0 ≤ C ∧ ∀ (τ : ℍ) (r : ℝ), Work.Asymptotics.HalfFunnel.lowBadSet τ →
      (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ => blLowF2 ℓ d τ s) r‖ ≤ C := by
  intro k l
  obtain ⟨c, hc, hb⟩ :=
    Work.HFN.HalfFunnel.lowBad_hsemi_of_bounds ℓ d hd hCdec hdec1 hdec2 htail
      hPhiSpike hPhi12 k l
  refine ⟨c, hc, fun τ r hτ => ?_⟩
  rcases eq_or_ne r 0 with hr | hr
  · subst hr
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk
      rcases Nat.eq_zero_or_pos l with hl | hl
      · subst hl
        have hz : blLowF2 ℓ d τ 0 = 0 := by rw [blLowF2]; simp
        simp only [iteratedDeriv_zero, hz, norm_zero, mul_zero]
        exact hc
      · have hfun : (fun s : ℝ => blLowF2 ℓ d τ s)
            = fun s : ℝ => (if s = 0 then 0 else Work.Asymptotics.HalfFunnel.lowF2 ℓ d τ s) := by
          funext s; rw [blLowF2]
        rw [hfun, punctured_iteratedDeriv (lowF2_neg ℓ d τ)
          (lowF2_differentiable ℓ d hd hCdec hdec1 hdec2 htail hτ) l hl]
        simpa using hb τ 0 hτ
    · have hz : (0 : ℝ) ^ k = 0 := zero_pow hk.ne'
      simp only [abs_zero, hz, zero_mul]
      exact hc
  · have heq : (fun s : ℝ => blLowF2 ℓ d τ s)
        =ᶠ[𝓝 r] (fun s : ℝ => Work.Asymptotics.HalfFunnel.lowF2 ℓ d τ s) := by
      filter_upwards [isOpen_ne.mem_nhds hr] with s hs
      rw [blLowF2, if_neg hs]
    rw [iteratedDeriv_congr_of_eventuallyEq heq l]
    exact hb τ r hτ

/-- **The `r`-seminorm bound for the CKMRV transform near the two bad lines** (the requested
lemma; the assembly described above is the remaining work). -/
theorem seminormK_cusp0_badline (ℓ : Work.Kernels.LogLambdaData) (d : ℕ)
    (hd : d = 8 ∨ d = 24) :
    ∀ k l : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ (w : UpperHalfPlane) (r : ℝ), w ∈ DomainD →
        (1 : ℝ) / 2 ≤ (ModularGroup.S • w).im → (ModularGroup.S • w).im ≤ 2 →
        (‖(w : ℂ) - ((1 : ℂ) + Complex.I)‖ < 1 / 10 ∨
          ‖(w : ℂ) - ((-1 : ℂ) + Complex.I)‖ < 1 / 10) →
        (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ =>
          Work.Kernels.kernelTransform (Work.Kernels.Kfun ℓ d) w s) r‖ ≤ C := by
  intro k l
  -- ## The analytic inputs on the bad-line set `lowBadSet`

  -- the translate-pole decomposition `K = tpole + O(1)` and the off-window bound
  obtain ⟨C₁, hC₁, hspike⟩ := Work.HFN.BadLine.kernel_spike ℓ d hd
  obtain ⟨C₂, hC₂, hoff⟩ := Work.HFN.BadLine.off_bound ℓ d hd
  set Cdec : ℝ := max C₁ C₂ with hCdecdef
  have hCdec : 0 ≤ Cdec := le_trans hC₁ (le_max_left C₁ C₂)
  have hdec1 : ∀ (τ : UpperHalfPlane), Work.Asymptotics.HalfFunnel.lowBadSet τ →
      ∀ t : ℝ, 0 < t → t ≤ Work.Asymptotics.HalfFunnel.lowT →
      ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
        - Work.Asymptotics.HalfFunnel.tpole τ t‖ ≤ Cdec :=
    fun τ hτ t ht hT => le_trans (hspike τ t hτ ht hT) (le_max_left C₁ C₂)
  have hdec2 : ∀ (τ : UpperHalfPlane), Work.Asymptotics.HalfFunnel.lowBadSet τ →
      ∀ t : ℝ, 0 < t → t ≤ Work.Asymptotics.HalfFunnel.lowT →
      Work.Asymptotics.HalfFunnel.lowRho ≤ |t - τ.im| →
      ‖Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t‖ ≤ Cdec :=
    fun τ hτ t ht hT hsep => le_trans (hoff τ t hτ ht hT hsep) (le_max_right C₁ C₂)
  -- the cusp-`i∞` expansion in the tail
  obtain ⟨Ct, Mt, hCt, hMt, htail⟩ := Work.HFN.HalfFunnel.lowBad_Aexp_tail ℓ d hd
  -- the explicit spike integral
  have hPhiSpike : ∀ m N : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ (τ : UpperHalfPlane),
      Work.Asymptotics.HalfFunnel.lowBadSet τ → ∀ x : ℝ, 0 ≤ x →
      ‖iteratedDeriv m (fun x : ℝ => Work.Asymptotics.HalfFunnel.PhiSpike τ x) x‖
        ≤ K * (1 + x) ^ (-(N : ℝ)) :=
    fun m N => Work.Asymptotics.HalfFunnel.lowBad_PhiSpike_deriv ℓ d hd m N
  -- the spike-removed amplitudes
  have hPhi12 : ∀ m N : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ (τ : UpperHalfPlane),
      Work.Asymptotics.HalfFunnel.lowBadSet τ → ∀ x : ℝ, 0 ≤ x →
      ‖iteratedDeriv m (fun x : ℝ => Work.Asymptotics.HalfFunnel.PhiOne ℓ d τ x
        + Work.Asymptotics.HalfFunnel.PhiTwo ℓ d τ x) x‖ ≤ K * (1 + x) ^ (-(N : ℝ)) :=
    fun m N => Work.HFN.HalfFunnel.lowBad_Phi12_deriv ℓ d hd Cdec hCdec hdec1 m N
  -- the `r`-seminorm bound for the punctured pole-split layer, on `lowBadSet`
  have hsemi_low := blLowF2_seminorm ℓ d hd hCdec hdec1 hdec2
    ⟨Ct, Mt, hCt, hMt, htail⟩ hPhiSpike hPhi12
  -- ## Agreement of the layer with the contour integral

  -- `lowF2 = paperLayer` on `lowBadSet` (telescoping of the split-off pole), and
  -- `paperLayer = kernelTransform` wherever the contour integral converges, by the singleton
  -- instance of the local `low + trunc + high` decomposition
  have hagr_low : ∀ (τ : UpperHalfPlane), Work.Asymptotics.HalfFunnel.lowBadSet τ →
      ∀ r : ℝ, r ≠ 0 → MeasureTheory.IntegrableOn (fun t : ℝ =>
        Work.Kernels.Kaxis (Work.Kernels.Kfun ℓ d) τ t
          * Complex.exp (-(Real.pi * (r : ℂ) ^ 2 * (t : ℂ)))) (Set.Ioi 0) →
      blLowF2 ℓ d τ r = Work.Kernels.kernelTransform (Work.Kernels.Kfun ℓ d) τ r := by
    intro τ hτ r hr hInt
    rw [blLowF2, if_neg hr,
      Work.HFN.HalfFunnel.lowF2_eq_paperLayer ℓ d hd Cdec hCdec hdec1 hdec2 τ r hτ]
    have hsub : ({τ} : Set UpperHalfPlane) ⊆ DomainD := by rintro x rfl; exact hτ.1
    have hcpt : IsCompact ({τ} : Set UpperHalfPlane) := isCompact_singleton
    exact Work.Asymptotics.Compact.local_agreement (K := ({τ} : Set UpperHalfPlane)) ℓ d hd
      (Work.Asymptotics.Gcusp ℓ d) (fun i j => Work.HFN.Gcusp_moderate ℓ d i j)
      (by
        intro h8 j
        rw [Work.Asymptotics.Gcusp, if_pos h8]
        funext x
        fin_cases j <;> simp [Work.Asymptotics.Gcusp8])
      (Work.Asymptotics.MFix.Kaxis_local_flat ℓ d hd hcpt hsub)
      (Work.HFN.cusp_expansion_of_kernel ℓ d hd hcpt hsub) τ r (by simp) hr hInt
  -- ## Transfer to the contour integral, on the two bad-line regions

  have hkey : ∀ (n : ℤ), (n = 1 ∨ n = -1) → ∃ C : ℝ, 0 ≤ C ∧
      ∀ (w : UpperHalfPlane) (r : ℝ), w ∈ BLregion n →
      (|r| ^ k) * ‖iteratedDeriv l (fun s : ℝ =>
        Work.Kernels.kernelTransform (Work.Kernels.Kfun ℓ d) w s) r‖ ≤ C := by
    intro n hn
    obtain ⟨C, hC, hb⟩ := kernelTransform_seminorm_of_layer_on_compact
      (K := BLregion n) ℓ d (blLowF2 ℓ d)
      (fun τ _ => by
        rw [blLowF2]
        simp only [if_true]
        simp [Work.Kernels.kernelTransform])
      (fun τ hτ r hr hInt => hagr_low τ (BLregion_subset_lowBadSet hn hτ) r hr hInt)
      (fun k' l' => by
        obtain ⟨C', hC', hb'⟩ := hsemi_low k' l'
        exact ⟨C', hC', fun τ r hτ => hb' τ r (BLregion_subset_lowBadSet hn hτ)⟩)
      k l
    exact ⟨C, hC, fun w r hw => hb w r hw⟩
  obtain ⟨C₁, hC₁, hb₁⟩ := hkey 1 (Or.inl rfl)
  obtain ⟨C₂, hC₂, hb₂⟩ := hkey (-1) (Or.inr rfl)
  refine ⟨max C₁ C₂, le_trans hC₁ (le_max_left C₁ C₂), ?_⟩
  intro w r hw h1 h2 h3
  rcases h3 with h3 | h3
  · refine le_trans (hb₁ w r (mem_BLregion.mpr ⟨hw, h1, h2, by simpa using h3⟩))
      (le_max_left C₁ C₂)
  · refine le_trans (hb₂ w r (mem_BLregion.mpr ⟨hw, h1, h2, by simpa using h3⟩))
      (le_max_right C₁ C₂)


end

end Work.HFN
