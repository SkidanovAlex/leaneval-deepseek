import Mathlib
import Submission.Work.Pert.Basic

namespace Work.Pert

open MandelDim Complex

/-- Membership in a two-vertex gate region, in explicit coordinates. -/
private lemma mem_Qreg_some_pair {z a b : ℂ} :
    z ∈ MandelDim.Qreg (some a) (some b) ↔
      (-|(z - a).im| < (z - a).re ∧ (z - b).re < |(z - b).im|) := by
  simp [MandelDim.Qreg]

/-- In the disc `D(η)` of (4.2.5) the real part is bounded by `|η|/4`. -/
private lemma Dsm_re_bound {η : ℝ} {z : ℂ} (hz : z ∈ MandelDim.Dsm η) :
    |z.re| ≤ |η| / 4 := by
  rw [MandelDim.Dsm, Metric.mem_closedBall, dist_eq_norm] at hz
  have h := Complex.abs_re_le_norm (z - Complex.I * η)
  rw [show (z - Complex.I * (η : ℂ)).re = z.re from by
        simp [Complex.sub_re, Complex.mul_re]] at h
  linarith

/-- In the disc `D(η)` of (4.2.5) `Im z` is `η` up to `|η|/4`. -/
private lemma Dsm_im_bound {η : ℝ} {z : ℂ} (hz : z ∈ MandelDim.Dsm η) :
    |z.im - η| ≤ |η| / 4 := by
  rw [MandelDim.Dsm, Metric.mem_closedBall, dist_eq_norm] at hz
  have h := Complex.abs_im_le_norm (z - Complex.I * η)
  rw [show (z - Complex.I * (η : ℂ)).im = z.im - η from by
        simp [Complex.sub_im, Complex.mul_im]] at h
  linarith

/-- The two discs `Dsm (η)` and `Dsm (-η)` of (4.2.5) lie inside **both** gate regions
`Qreg (some ξ₁) (some (-ξ₁ + 1/α))` and `Qreg (some (ξ₁ - 1/α)) (some (-ξ₁))`.  This is the
`D_sub`/`φ_star_close` geometry: `η` is huge compared with `ξ₁`, and `Re (1/α)` is huge compared
with `η` (the latter is what makes the perturbed coordinate indistinguishable from the unperturbed
one on the discs). -/
theorem discgate {α : ℂ} (hF1 : MandelDim.InF1 α) {ξ₁ η : ℝ} (hξ : 0 < ξ₁) (hη : 0 < η)
    (h1 : 2 * ξ₁ < η) (h2 : η / 2 + 2 * ξ₁ < (1 / α).re) :
    MandelDim.Dsm η ⊆ MandelDim.Qreg (some (ξ₁ : ℂ)) (some (-(ξ₁ : ℂ) + 1 / α)) ∧
    MandelDim.Dsm (-η) ⊆ MandelDim.Qreg (some (ξ₁ : ℂ)) (some (-(ξ₁ : ℂ) + 1 / α)) ∧
    MandelDim.Dsm η ⊆ MandelDim.Qreg (some ((ξ₁ : ℂ) - 1 / α)) (some (-(ξ₁ : ℂ))) ∧
    MandelDim.Dsm (-η) ⊆ MandelDim.Qreg (some ((ξ₁ : ℂ) - 1 / α)) (some (-(ξ₁ : ℂ))) := by
  have hunused := hF1
  have hA : η / 4 + ξ₁ < (1 / α).re := by linarith
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- `Dsm η ⊆ Qreg ξ₁ (-ξ₁ + 1/α)`
    intro z hz
    have hre : |z.re| ≤ η / 4 := by
      have h := Dsm_re_bound hz; rwa [abs_of_pos hη] at h
    have him : |z.im - η| ≤ η / 4 := by
      have h := Dsm_im_bound hz; rwa [abs_of_pos hη] at h
    rw [abs_le] at hre him
    rw [mem_Qreg_some_pair]
    refine ⟨?_, ?_⟩
    · have hpos : 0 < z.im := by linarith [him.1, hη]
      rw [show (z - (ξ₁ : ℂ)).im = z.im from by simp, abs_of_pos hpos,
        show (z - (ξ₁ : ℂ)).re = z.re - ξ₁ from by simp]
      linarith [hre.1, him.1, h1]
    · have hneg : z.re + ξ₁ - (1 / α).re < 0 := by linarith [hre.2, hA]
      have hkey : (z - (-(ξ₁ : ℂ) + 1 / α)).re = z.re + ξ₁ - (1 / α).re := by
        simp only [Complex.sub_re, Complex.add_re, Complex.neg_re, Complex.ofReal_re]
        ring
      rw [hkey]
      exact lt_of_lt_of_le hneg (abs_nonneg _)
  · -- `Dsm (-η) ⊆ Qreg ξ₁ (-ξ₁ + 1/α)`
    intro z hz
    have hre : |z.re| ≤ η / 4 := by
      have h := Dsm_re_bound hz; rwa [abs_neg, abs_of_pos hη] at h
    have him : |z.im + η| ≤ η / 4 := by
      have h := Dsm_im_bound hz
      rw [abs_neg, abs_of_pos hη, show z.im - (-η) = z.im + η from by ring] at h
      exact h
    rw [abs_le] at hre him
    rw [mem_Qreg_some_pair]
    refine ⟨?_, ?_⟩
    · have hneg : z.im < 0 := by linarith [him.2, hη]
      rw [show (z - (ξ₁ : ℂ)).im = z.im from by simp, abs_of_neg hneg,
        show (z - (ξ₁ : ℂ)).re = z.re - ξ₁ from by simp]
      linarith [hre.1, him.2, h1]
    · have hneg : z.re + ξ₁ - (1 / α).re < 0 := by linarith [hre.2, hA]
      have hkey : (z - (-(ξ₁ : ℂ) + 1 / α)).re = z.re + ξ₁ - (1 / α).re := by
        simp only [Complex.sub_re, Complex.add_re, Complex.neg_re, Complex.ofReal_re]
        ring
      rw [hkey]
      exact lt_of_lt_of_le hneg (abs_nonneg _)
  · -- `Dsm η ⊆ Qreg (ξ₁ - 1/α) (-ξ₁)`
    intro z hz
    have hre : |z.re| ≤ η / 4 := by
      have h := Dsm_re_bound hz; rwa [abs_of_pos hη] at h
    have him : |z.im - η| ≤ η / 4 := by
      have h := Dsm_im_bound hz; rwa [abs_of_pos hη] at h
    rw [abs_le] at hre him
    rw [mem_Qreg_some_pair]
    refine ⟨?_, ?_⟩
    · have hpos : 0 < z.re - ξ₁ + (1 / α).re := by linarith [hre.1, hA]
      have hkey : (z - ((ξ₁ : ℂ) - 1 / α)).re = z.re - ξ₁ + (1 / α).re := by
        simp only [Complex.sub_re, Complex.ofReal_re]; ring
      rw [hkey]
      exact lt_of_le_of_lt (neg_nonpos.mpr (abs_nonneg _)) hpos
    · have hpos : 0 < z.im := by linarith [him.1, hη]
      rw [show (z - -(ξ₁ : ℂ)).im = z.im from by simp, abs_of_pos hpos,
        show (z - -(ξ₁ : ℂ)).re = z.re + ξ₁ from by simp]
      linarith [hre.2, him.1, h1]
  · -- `Dsm (-η) ⊆ Qreg (ξ₁ - 1/α) (-ξ₁)`
    intro z hz
    have hre : |z.re| ≤ η / 4 := by
      have h := Dsm_re_bound hz; rwa [abs_neg, abs_of_pos hη] at h
    have him : |z.im + η| ≤ η / 4 := by
      have h := Dsm_im_bound hz
      rw [abs_neg, abs_of_pos hη, show z.im - (-η) = z.im + η from by ring] at h
      exact h
    rw [abs_le] at hre him
    rw [mem_Qreg_some_pair]
    refine ⟨?_, ?_⟩
    · have hpos : 0 < z.re - ξ₁ + (1 / α).re := by linarith [hre.1, hA]
      have hkey : (z - ((ξ₁ : ℂ) - 1 / α)).re = z.re - ξ₁ + (1 / α).re := by
        simp only [Complex.sub_re, Complex.ofReal_re]; ring
      rw [hkey]
      exact lt_of_le_of_lt (neg_nonpos.mpr (abs_nonneg _)) hpos
    · have hneg : z.im < 0 := by linarith [him.2, hη]
      rw [show (z - -(ξ₁ : ℂ)).im = z.im from by simp, abs_of_neg hneg,
        show (z - -(ξ₁ : ℂ)).re = z.re + ξ₁ from by simp]
      linarith [hre.2, him.2, h1]

end Work.Pert
