import Submission.Work.Drive.Neutral.StripDiskAux

/-!
# The values of the strip disk data on the annulus

On `x = e^{iσ}` with opening `s ∈ (0, π/2]` the clamped chord data of `StripDiskAux` coincides with
the workspace's symmetric chord data `symmMid, symmChordC, symmR, symmD, symmWC` of `stripTauData`:
the clamping is inactive there (`sClamp s = s`), and the divided difference is `2 · symmWC`, so the
halving (and hence the physical vector) is the same.
-/

namespace Work.Drive.Neutral

open Manifold
open scoped Manifold ContDiff

noncomputable section

lemma symmC_add (v w : ℝ × ℝ) : symmC (v + w) = symmC v + symmC w := by
  refine Complex.ext ?_ ?_ <;> simp [symmC]

lemma symmC_sub (v w : ℝ × ℝ) : symmC (v - w) = symmC v - symmC w := by
  refine Complex.ext ?_ ?_ <;> simp [symmC]

lemma symmC_div_two (v : ℝ × ℝ) : symmC (v / 2) = symmC v / 2 := by
  refine Complex.ext ?_ ?_ <;> simp [symmC, div_eq_mul_inv]

/-- The complex value of `toCirc`. -/
lemma toCirc_coe (y : ℂ) (hy : y ≠ 0) : (toCirc y hy : ℂ) = y / ((‖y‖ : ℝ) : ℂ) := rfl

/-- `toCirc (e^{iσ} · e^{i sClamp s}) = Circle.exp (σ + sClamp s)`. -/
lemma toCirc_exp_mul_exp (σ s : ℝ) :
    toCirc (Complex.exp ((σ : ℂ) * Complex.I) * Complex.exp (((sClamp s : ℝ) : ℂ) * Complex.I))
        (mul_ne_zero (Complex.exp_ne_zero _) (Complex.exp_ne_zero _))
      = Circle.exp (σ + sClamp s) := by
  have hnorm : ‖Complex.exp ((σ : ℂ) * Complex.I)
      * Complex.exp (((sClamp s : ℝ) : ℂ) * Complex.I)‖ = 1 := by
    rw [norm_mul, Complex.norm_exp, Complex.norm_exp]
    have h1 : ((σ : ℂ) * Complex.I).re = 0 := by
      simp [Complex.mul_re, Complex.I_re, Complex.I_im]
    have h2 : (((sClamp s : ℝ) : ℂ) * Complex.I).re = 0 := by
      simp [Complex.mul_re, Complex.I_re, Complex.I_im]
    rw [h1, h2]; norm_num
  refine Subtype.ext ?_
  show (Complex.exp ((σ : ℂ) * Complex.I) * Complex.exp (((sClamp s : ℝ) : ℂ) * Complex.I))
      / ((‖Complex.exp ((σ : ℂ) * Complex.I)
        * Complex.exp (((sClamp s : ℝ) : ℂ) * Complex.I)‖ : ℝ) : ℂ)
      = (Circle.exp (σ + sClamp s) : ℂ)
  rw [hnorm, Circle.coe_exp, Complex.ofReal_one, div_one, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The `+` endpoint at `x = e^{iσ}` is the curve point at `σ + sClamp s`. -/
lemma curvePtAt_exp (γ : Circle → ℝ × ℝ) (σ s : ℝ) :
    curvePtAt γ (Complex.exp ((σ : ℂ) * Complex.I)) s = symmC (curve γ (σ + sClamp s)) := by
  have hx : Complex.exp ((σ : ℂ) * Complex.I) ≠ 0 := Complex.exp_ne_zero _
  rw [curvePtAt, dif_neg hx, curve]
  exact congrArg (fun c : Circle => symmC (γ c)) (toCirc_exp_mul_exp σ s)

/-- The `+` endpoint at `x = e^{iσ}` for openings in `(0, π/2]`. -/
lemma endPlus_exp_eq (γ : Circle → ℝ × ℝ) (σ s : ℝ) (hs : 0 < s) (hs2 : s ≤ Real.pi / 2) :
    endPlus γ (Complex.exp ((σ : ℂ) * Complex.I)) s = symmC (curve γ (σ + s)) := by
  rw [endPlus, curvePtAt_exp, sClamp_eq_self (by rw [abs_of_pos hs]; exact hs2)]

/-- The `-` endpoint at `x = e^{iσ}` for openings in `(0, π/2]`. -/
lemma endMinus_exp_eq (γ : Circle → ℝ × ℝ) (σ s : ℝ) (hs : 0 < s) (hs2 : s ≤ Real.pi / 2) :
    endMinus γ (Complex.exp ((σ : ℂ) * Complex.I)) s = symmC (curve γ (σ - s)) := by
  have hsabs : |s| ≤ Real.pi / 2 := by rw [abs_of_pos hs]; exact hs2
  have hclamp : sClamp s = s := sClamp_eq_self hsabs
  rw [endMinus, curvePtAt_exp, sClamp_odd s, hclamp,
    show σ + -s = σ - s from by ring]

lemma dataMid_exp_eq (γ : Circle → ℝ × ℝ) (σ s : ℝ) (hs : 0 < s) (hs2 : s ≤ Real.pi / 2) :
    dataMid γ (Complex.exp ((σ : ℂ) * Complex.I)) s = symmC (symmMid γ σ s) := by
  rw [dataMid, endPlus_exp_eq γ σ s hs hs2, endMinus_exp_eq γ σ s hs hs2, symmMid, curve]
  rw [symmC_div_two, symmC_add]

lemma normSq_symmC (v : ℝ × ℝ) : Complex.normSq (symmC v) = v.1 ^ 2 + v.2 ^ 2 := by
  simp only [symmC, Complex.normSq_apply]
  ring

lemma dataChord_exp_eq (γ : Circle → ℝ × ℝ) (σ s : ℝ) (hs : 0 < s) (hs2 : s ≤ Real.pi / 2) :
    dataChord γ (Complex.exp ((σ : ℂ) * Complex.I)) s = symmChordC γ σ s := by
  rw [dataChord, endPlus_exp_eq γ σ s hs hs2, endMinus_exp_eq γ σ s hs hs2, symmChordC,
    chordC_eq_symmC, curve]
  rfl

lemma dataR_exp_eq (γ : Circle → ℝ × ℝ) (σ s : ℝ) (hs : 0 < s) (hs2 : s ≤ Real.pi / 2) :
    dataR γ (Complex.exp ((σ : ℂ) * Complex.I)) s = symmR γ σ s := by
  rw [dataR, symmR, symmA, dataMid_exp_eq γ σ s hs hs2, dataChord_exp_eq γ σ s hs hs2,
    normSq_symmC (symmMid γ σ s)]

end

end Work.Drive.Neutral
