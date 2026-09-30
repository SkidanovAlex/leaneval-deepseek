import Mathlib
import Submission.Work.BMF.halasz_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.mrlas

open Complex Finset

/-- The prime sum `vF f x s` is continuous as a function of `s : ℂ`. -/
theorem continuous_vF (f : ℕ → ℂ) (x : ℝ) : Continuous (fun s : ℂ => Work.BMF.vF f x s) := by
  simp only [Work.BMF.vF]
  apply continuous_finsetSum
  intro p hp
  have hp0 : (p : ℂ) ≠ 0 := by
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast Nat.two_le_of_mem_primesLE hp
    have : (p : ℝ) ≠ 0 := by positivity
    exact_mod_cast this
  exact continuous_const.mul (continuous_neg.const_cpow (Or.inl hp0))

theorem Wsup_measurable (f : ℕ → ℂ) (x T : ℝ) :
    Measurable (fun α : ℝ => Work.BMF.Wsup f x α T) := by
  -- `α ↦ Wsup f x α T` is in fact continuous, being the supremum over the compact set
  -- `{t : ℝ | |t| ≤ T}` of a jointly continuous function.
  have hg : Continuous (fun p : ℝ × ℝ =>
      (Work.BMF.vF f x (((1 + p.1 : ℝ) : ℂ) + (p.2 : ℂ) * Complex.I)).re) := by
    apply Complex.continuous_re.comp
    apply (continuous_vF f x).comp
    apply Continuous.add
    · exact Complex.continuous_ofReal.comp (continuous_const.add continuous_fst)
    · exact (Complex.continuous_ofReal.comp continuous_snd).mul continuous_const
  have hK : IsCompact {t : ℝ | |t| ≤ T} := by
    rw [show {t : ℝ | |t| ≤ T} = Set.Icc (-T) T by ext t; simp [abs_le]]
    exact isCompact_Icc
  have hcont := hK.continuous_sSup (f := fun (α : ℝ) (t : ℝ) =>
      (Work.BMF.vF f x (((1 + α : ℝ) : ℂ) + (t : ℂ) * Complex.I)).re) hg
  have heq : (fun α : ℝ => Work.BMF.Wsup f x α T)
      = fun α : ℝ => sSup ((fun t : ℝ =>
          (Work.BMF.vF f x (((1 + α : ℝ) : ℂ) + (t : ℂ) * Complex.I)).re)
            '' {t : ℝ | |t| ≤ T}) := by
    funext α
    unfold Work.BMF.Wsup
    rw [show (⨆ (t : {t : ℝ // |t| ≤ T}),
          (Work.BMF.vF f x ((1 + α : ℝ) + t.1 * Complex.I)).re)
        = sSup (Set.range (fun (t : {t : ℝ // |t| ≤ T}) =>
            (Work.BMF.vF f x ((1 + α : ℝ) + t.1 * Complex.I)).re)) from rfl]
    congr 1
    rw [Set.image_eq_range]
    rfl
  rw [heq]
  exact hcont.measurable

end Work.BMF.mrlas
