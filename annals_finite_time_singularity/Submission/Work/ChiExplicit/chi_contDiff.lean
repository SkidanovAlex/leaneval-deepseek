import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Submission.Work.ChiExplicit.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open Set

namespace Work.ChiExplicit

/-- **`chi` is `C^n` for every `n`.**  The argument `x ↦ 2 - ‖x‖` is not differentiable at `0`, but
the singularity is harmless: on the open half-lines `x > 0` and `x < 0` the function agrees with
`Real.smoothTransition (2 - x)` resp. `Real.smoothTransition (2 + x)`, both smooth, while on the
neighbourhood `(-1, 1)` of the origin it is the constant `1`.  These three open sets cover `ℝ`. -/
theorem chi_contDiff (n : ℕ∞) : ContDiff ℝ n Work.ChiExplicit.chi := by
  -- On `x > 0`, `chi x = smoothTransition (2 - x)`.
  have hpos : ContDiffOn ℝ n chi (Ioi (0 : ℝ)) := by
    have h : ContDiffOn ℝ n (fun x => Real.smoothTransition (2 - x)) (Ioi (0 : ℝ)) :=
      (Real.smoothTransition.contDiff.comp (contDiff_const.sub contDiff_id)).contDiffOn
    exact h.congr (fun x hx => by rw [chi_apply_abs, abs_of_pos hx])
  -- On `x < 0`, `chi x = smoothTransition (2 + x)`.
  have hneg : ContDiffOn ℝ n chi (Iio (0 : ℝ)) := by
    have h : ContDiffOn ℝ n (fun x => Real.smoothTransition (2 + x)) (Iio (0 : ℝ)) :=
      (Real.smoothTransition.contDiff.comp (contDiff_const.add contDiff_id)).contDiffOn
    exact h.congr (fun x hx => by rw [chi_apply_abs, abs_of_neg hx]; ring_nf)
  -- On `(-1, 1)`, `chi` is the constant `1`.
  have hzero : ContDiffOn ℝ n chi (Ioo (-1 : ℝ) 1) :=
    contDiffOn_const.congr (fun x hx => by
      rw [chi_eq_one (le_of_lt (abs_lt.mpr ⟨hx.1, hx.2⟩))])
  -- The three open sets cover `ℝ`.
  have h12 : ContDiffOn ℝ n chi (Ioi (0 : ℝ) ∪ Iio (0 : ℝ)) :=
    hpos.union_of_isOpen hneg isOpen_Ioi isOpen_Iio
  have h3 : ContDiffOn ℝ n chi ((Ioi (0 : ℝ) ∪ Iio (0 : ℝ)) ∪ Ioo (-1 : ℝ) 1) :=
    h12.union_of_isOpen hzero (isOpen_Ioi.union isOpen_Iio) isOpen_Ioo
  rw [show (Ioi (0 : ℝ) ∪ Iio (0 : ℝ)) ∪ Ioo (-1 : ℝ) 1 = univ from ?_] at h3
  · exact contDiffOn_univ.mp h3
  · ext x; simp only [mem_union, mem_Ioi, mem_Iio, mem_Ioo, mem_univ]
    constructor
    · intro _; trivial
    · intro _
      rcases lt_trichotomy x 0 with h | h | h
      · exact Or.inl (Or.inr h)
      · exact Or.inr ⟨by linarith, by linarith⟩
      · exact Or.inl (Or.inl h)

end Work.ChiExplicit
