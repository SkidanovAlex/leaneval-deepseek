import Mathlib
import Submission.Work.NN.Newton.FTdefs
import Submission.Work.NN.Core.holderNorm_const_mul_le

namespace Work.NN.Newton.FTscale

/-- **Dilation bounds for the flat Hölder norms.**

(1) If `lam * r = 1`, `lam > 0`, `r > 0`, then for every `f` the pullback of `f` under the
dilation `z ↦ lam⁻¹ • z` followed by multiplication by `lam` scales the `C^{0,α}` norm on the
unit polydisc by at most `lam * max 1 (r ^ α)` when measured against the polydisc of radius `r`.

(2) Multiplying by `(r : ℂ) ^ 2` after dilating by `lam` scales the `C^{1,α}` norm on the
polydisc of radius `r * (1 - δ)` by at most `r ^ 2 * max 1 (lam ^ (1 + α))` when measured
against the polydisc of radius `1 - δ`.

Both bounds are the *exact* constants: the two factors are the homogeneity constants of the
constant multiplication and of the dilation, and they multiply. -/
theorem dilateNorm_le {n : ℕ} {α : ℝ} (hα0 : 0 ≤ α) {lam r : ℝ} (hlam : 0 < lam)
    (hr : 0 < r) (hlr : lam * r = 1) :
    (∀ (f : (Fin n → ℂ) → ℂ),
      Work.CR.Flat.holderNorm 0 α (fun w : Fin n → ℂ => (lam : ℂ) * f (lam⁻¹ • w))
          (Work.CR.Flat.polydisc 0 (fun _ => 1))
        ≤ ENNReal.ofReal (lam * max 1 (r ^ α))
          * Work.CR.Flat.holderNorm 0 α f (Work.CR.Flat.polydisc 0 (fun _ => r))) ∧
    (∀ {δ : ℝ} (hδ : 0 < δ) (f : (Fin n → ℂ) → ℂ),
      Work.CR.Flat.holderNorm 1 α (fun z : Fin n → ℂ => (r : ℂ) ^ 2 * f (lam • z))
          (Work.CR.Flat.polydisc 0 (fun _ => r * (1 - δ)))
        ≤ ENNReal.ofReal (r ^ 2 * max 1 (lam ^ ((1 : ℝ) + α)))
          * Work.CR.Flat.holderNorm 1 α f (Work.CR.Flat.polydisc 0 (fun _ => 1 - δ))) := by
  have hlam0 : lam ≠ 0 := ne_of_gt hlam
  have hr0 : r ≠ 0 := ne_of_gt hr
  have hlinv : lam⁻¹ = r := inv_eq_of_mul_eq_one_right hlr
  have hnormlam : ‖(lam : ℂ)‖ = lam := by simp [abs_of_pos hlam]
  have hnormr2 : ‖(r : ℂ) ^ 2‖ = r ^ 2 := by simp [abs_of_pos hr]
  have habslinv : |lam⁻¹| = r := by
    rw [abs_of_pos (inv_pos.mpr hlam), hlinv]
  constructor
  · intro f
    set P1 : Set (Fin n → ℂ) := Work.CR.Flat.polydisc 0 (fun _ => 1) with hP1
    set Pr : Set (Fin n → ℂ) := Work.CR.Flat.polydisc 0 (fun _ => r) with hPr
    have hud1 : UniqueDiffOn ℝ P1 := by
      rw [hP1]
      exact (Work.CR.Flat.isOpen_polydisc (0 : Fin n → ℂ) (fun _ => 1)).uniqueDiffOn
    have hstep1 : Work.CR.Flat.holderNorm 0 α (fun w => (lam : ℂ) * f (lam⁻¹ • w)) P1
        ≤ ENNReal.ofReal ‖(lam : ℂ)‖
            * Work.CR.Flat.holderNorm 0 α (fun w => f (lam⁻¹ • w)) P1 :=
      Work.NN.Core.holderNorm_const_mul_le hud1 (lam : ℂ) (fun w => f (lam⁻¹ • w))
    have hrad1 : (fun _ : Fin n => r / lam⁻¹) = (fun _ : Fin n => (1 : ℝ)) := by
      funext j
      rw [hlinv, div_self hr0]
    have hset1 : {z : Fin n → ℂ | lam⁻¹ • z ∈ Pr} = P1 := by
      have h1 : {z : Fin n → ℂ | lam⁻¹ • z ∈ Pr}
          = Work.CR.Flat.polydisc 0 (fun _ : Fin n => r / lam⁻¹) := by
        rw [hPr]
        ext z
        exact Work.NN.Newton.smul_mem_polydisc_iff (inv_pos.mpr hlam) (fun _ => r) z
      rw [h1, hrad1]
    have hstep2 : Work.CR.Flat.holderNorm 0 α (fun w => f (lam⁻¹ • w)) P1
        ≤ ENNReal.ofReal (max 1 (|lam⁻¹| ^ (((0 : ℕ) : ℝ) + α)))
            * Work.CR.Flat.holderNorm 0 α f Pr := by
      have h := Work.NN.Newton.holderNorm_comp_smul_le (X := Fin n → ℂ) 0 (α := α) hα0
        (c := lam⁻¹) (inv_ne_zero hlam0) (Ω := Pr)
        (Work.CR.Flat.isOpen_polydisc (0 : Fin n → ℂ) (fun _ => r)) f
      rwa [hset1] at h
    have hmax1 : max 1 (|lam⁻¹| ^ (((0 : ℕ) : ℝ) + α)) = max 1 (r ^ α) := by
      have h2 : (((0 : ℕ) : ℝ) + α) = α := by simp
      rw [h2, habslinv]
    calc Work.CR.Flat.holderNorm 0 α (fun w => (lam : ℂ) * f (lam⁻¹ • w)) P1
        ≤ ENNReal.ofReal ‖(lam : ℂ)‖
            * Work.CR.Flat.holderNorm 0 α (fun w => f (lam⁻¹ • w)) P1 := hstep1
      _ ≤ ENNReal.ofReal ‖(lam : ℂ)‖
            * (ENNReal.ofReal (max 1 (|lam⁻¹| ^ (((0 : ℕ) : ℝ) + α)))
                * Work.CR.Flat.holderNorm 0 α f Pr) :=
          mul_le_mul_right hstep2 _
      _ = ENNReal.ofReal (lam * max 1 (r ^ α)) * Work.CR.Flat.holderNorm 0 α f Pr := by
          rw [hnormlam, hmax1, ← mul_assoc, ← ENNReal.ofReal_mul hlam.le]
  · intro δ hδ f
    set Oh : Set (Fin n → ℂ) := Work.CR.Flat.polydisc 0 (fun _ => 1 - δ) with hOh
    set Ot : Set (Fin n → ℂ) := Work.CR.Flat.polydisc 0 (fun _ => r * (1 - δ)) with hOt
    have hudt : UniqueDiffOn ℝ Ot := by
      rw [hOt]
      exact (Work.CR.Flat.isOpen_polydisc (0 : Fin n → ℂ) (fun _ => r * (1 - δ))).uniqueDiffOn
    have hstep1 : Work.CR.Flat.holderNorm 1 α (fun z => (r : ℂ) ^ 2 * f (lam • z)) Ot
        ≤ ENNReal.ofReal ‖(r : ℂ) ^ 2‖
            * Work.CR.Flat.holderNorm 1 α (fun z => f (lam • z)) Ot :=
      Work.NN.Core.holderNorm_const_mul_le hudt ((r : ℂ) ^ 2) (fun z => f (lam • z))
    have hrad2 : (fun _ : Fin n => (1 - δ) / lam) = (fun _ : Fin n => r * (1 - δ)) := by
      funext j
      rw [div_eq_iff hlam0]
      rw [show r * (1 - δ) * lam = (lam * r) * (1 - δ) by ring, hlr, one_mul]
    have hset2 : {z : Fin n → ℂ | lam • z ∈ Oh} = Ot := by
      have h1 : {z : Fin n → ℂ | lam • z ∈ Oh}
          = Work.CR.Flat.polydisc 0 (fun _ : Fin n => (1 - δ) / lam) := by
        rw [hOh]
        ext z
        exact Work.NN.Newton.smul_mem_polydisc_iff hlam (fun _ => 1 - δ) z
      rw [h1, hrad2]
    have hstep2 : Work.CR.Flat.holderNorm 1 α (fun z => f (lam • z)) Ot
        ≤ ENNReal.ofReal (max 1 (|lam| ^ (((1 : ℕ) : ℝ) + α)))
            * Work.CR.Flat.holderNorm 1 α f Oh := by
      have h := Work.NN.Newton.holderNorm_comp_smul_le (X := Fin n → ℂ) 1 (α := α) hα0
        (c := lam) hlam0 (Ω := Oh)
        (Work.CR.Flat.isOpen_polydisc (0 : Fin n → ℂ) (fun _ => 1 - δ)) f
      rwa [hset2] at h
    have hmax2 : max 1 (|lam| ^ (((1 : ℕ) : ℝ) + α)) = max 1 (lam ^ ((1 : ℝ) + α)) := by
      have h2 : (((1 : ℕ) : ℝ) + α) = ((1 : ℝ) + α) := by simp
      rw [h2, abs_of_pos hlam]
    calc Work.CR.Flat.holderNorm 1 α (fun z => (r : ℂ) ^ 2 * f (lam • z)) Ot
        ≤ ENNReal.ofReal ‖(r : ℂ) ^ 2‖
            * Work.CR.Flat.holderNorm 1 α (fun z => f (lam • z)) Ot := hstep1
      _ ≤ ENNReal.ofReal ‖(r : ℂ) ^ 2‖
            * (ENNReal.ofReal (max 1 (|lam| ^ (((1 : ℕ) : ℝ) + α)))
                * Work.CR.Flat.holderNorm 1 α f Oh) :=
          mul_le_mul_right hstep2 _
      _ = ENNReal.ofReal (r ^ 2 * max 1 (lam ^ ((1 : ℝ) + α)))
            * Work.CR.Flat.holderNorm 1 α f Oh := by
          rw [hnormr2, hmax2, ← mul_assoc, ← ENNReal.ofReal_mul (sq_nonneg r)]

end Work.NN.Newton.FTscale
