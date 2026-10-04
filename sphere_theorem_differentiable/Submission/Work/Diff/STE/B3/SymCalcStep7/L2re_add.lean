import Mathlib
import Submission.Work.Diff.STE.Torus
import Submission.Work.Diff.STE.B3.SymCalcStep1.conj_cut_aux

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open MeasureTheory

namespace Work.Diff.STE.B3.SymCalcStep7

/-- Additivity of the real `L²` pairing in its first argument. -/
lemma L2re_add_fst {ι : Type*} [Fintype ι] [DecidableEq ι]
    {y₁ y₂ g : (ι → ℝ) → ℂ} (hy₁ : Continuous y₁) (hy₂ : Continuous y₂) (hg : Continuous g) :
    Work.Diff.STE.L2re (y₁ + y₂) g =
      Work.Diff.STE.L2re y₁ g + Work.Diff.STE.L2re y₂ g := by
  have h1 : Integrable (fun x : ι → ℝ => y₁ x * star (g x))
      (volume.restrict (Work.Diff.STE.unitCube (ι := ι))) :=
    Work.Diff.STE.integrableOn_unitCube_of_continuous (hy₁.mul (continuous_star.comp hg))
  have h2 : Integrable (fun x : ι → ℝ => y₂ x * star (g x))
      (volume.restrict (Work.Diff.STE.unitCube (ι := ι))) :=
    Work.Diff.STE.integrableOn_unitCube_of_continuous (hy₂.mul (continuous_star.comp hg))
  simp only [Work.Diff.STE.L2re]
  rw [show (fun x : ι → ℝ => (y₁ + y₂) x * star (g x))
        = fun x => y₁ x * star (g x) + y₂ x * star (g x) by
      funext x; simp only [Pi.add_apply]; ring]
  rw [integral_add h1 h2]
  exact Complex.add_re _ _

/-- Additivity of the real `L²` pairing in its second argument. -/
lemma L2re_add_snd {ι : Type*} [Fintype ι] [DecidableEq ι]
    {y g₁ g₂ : (ι → ℝ) → ℂ} (hy : Continuous y) (hg₁ : Continuous g₁) (hg₂ : Continuous g₂) :
    Work.Diff.STE.L2re y (g₁ + g₂) =
      Work.Diff.STE.L2re y g₁ + Work.Diff.STE.L2re y g₂ := by
  have h1 : Integrable (fun x : ι → ℝ => y x * star (g₁ x))
      (volume.restrict (Work.Diff.STE.unitCube (ι := ι))) :=
    Work.Diff.STE.integrableOn_unitCube_of_continuous (hy.mul (continuous_star.comp hg₁))
  have h2 : Integrable (fun x : ι → ℝ => y x * star (g₂ x))
      (volume.restrict (Work.Diff.STE.unitCube (ι := ι))) :=
    Work.Diff.STE.integrableOn_unitCube_of_continuous (hy.mul (continuous_star.comp hg₂))
  simp only [Work.Diff.STE.L2re]
  rw [show (fun x : ι → ℝ => y x * star ((g₁ + g₂) x))
        = fun x => y x * star (g₁ x) + y x * star (g₂ x) by
      funext x; simp only [Pi.add_apply, star_add]; ring]
  rw [integral_add h1 h2]
  exact Complex.add_re _ _

theorem L2re_add {ι : Type*} [Fintype ι] [DecidableEq ι] :
    (∀ {y₁ y₂ g : (ι → ℝ) → ℂ}, Continuous y₁ → Continuous y₂ → Continuous g →
      Work.Diff.STE.L2re (y₁ + y₂) g = Work.Diff.STE.L2re y₁ g + Work.Diff.STE.L2re y₂ g)
    ∧ (∀ {y g₁ g₂ : (ι → ℝ) → ℂ}, Continuous y → Continuous g₁ → Continuous g₂ →
      Work.Diff.STE.L2re y (g₁ + g₂) = Work.Diff.STE.L2re y g₁ + Work.Diff.STE.L2re y g₂) :=
  ⟨fun hy₁ hy₂ hg => L2re_add_fst hy₁ hy₂ hg, fun hy hg₁ hg₂ => L2re_add_snd hy hg₁ hg₂⟩

end Work.Diff.STE.B3.SymCalcStep7
