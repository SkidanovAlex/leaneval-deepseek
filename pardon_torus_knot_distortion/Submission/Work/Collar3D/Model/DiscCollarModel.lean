import Submission.Work.Collar3D.Model.discChartHomeo
import Submission.Work.Collar3D.PushOff.Defs

/-!
# The flat model disc has a collar

`Work.Collar3D.modelDiscCollar : DiscCollar modelDisc`, the explicit collar of the flat model disc
with the trivial chart `p ↦ (p 0 + p 1 · i, p 2)` of the whole of `ℝ³` (on the plane `{p 2 = 0}`
this chart is the identity, so the model disc is carried to the standard parametrisation
`z ↦ (z, 0)` of `ℂ × ℝ`), and hence the non-vacuity certificate
`Work.Collar3D.hasDiscCollar_modelDisc : HasDiscCollar modelDisc`.

The chart of `modelDiscCollar` is exposed as `Work.Collar3D.modelDiscCollar_chart`, so that the
model configurations of the push-off can compute with it.
-/

open Set

namespace Work.Collar3D

noncomputable section

open Classical

theorem discChartFun_modelDisc (z : Disc) :
    discChartFun ⟨modelDisc z, Set.mem_univ _⟩ = ((z : ℂ), 0) := by
  have h : ((z : ℂ)) = (modelDisc z 0 : ℂ) + (modelDisc z 1 : ℂ) * Complex.I := by
    simp [modelDisc_zero, modelDisc_one, Complex.re_add_im]
  refine Prod.ext ?_ ?_
  · simpa [discChartFun, modelDisc_zero, modelDisc_one] using h
  · simp [discChartFun, modelDisc_two]

/-- **The explicit collar of the flat model disc**, with the trivial chart `p ↦ (p 0 + p 1 · i, p 2)`
of the whole space. -/
noncomputable def modelDiscCollar : DiscCollar modelDisc :=
  { U := Set.univ
    isOpen_U := isOpen_univ
    mem_range := fun _ _ => trivial
    Φ := Classical.choose (Work.Collar3D.Model.discChartHomeo)
    Φ_e := fun z => by
      show Classical.choose (Work.Collar3D.Model.discChartHomeo) ⟨modelDisc z, Set.mem_univ _⟩
        = ((z : ℂ), 0)
      rw [Classical.choose_spec (Work.Collar3D.Model.discChartHomeo)]
      exact discChartFun_modelDisc z
    Φ_range := fun u => by
      show ((u : R3) ∈ Set.range modelDisc ↔
        ∃ z : Disc, Classical.choose (Work.Collar3D.Model.discChartHomeo) u = ((z : ℂ), 0))
      rw [Classical.choose_spec (Work.Collar3D.Model.discChartHomeo)]
      constructor
      · rintro ⟨w, hw⟩
        refine ⟨w, ?_⟩
        have hu : u = ⟨modelDisc w, Set.mem_univ _⟩ := Subtype.ext hw.symm
        subst hu
        exact discChartFun_modelDisc w
      · rintro ⟨z, hz⟩
        refine ⟨z, ?_⟩
        have h1 : ((u : R3) 0 : ℂ) + (u : R3) 1 * Complex.I = (z : ℂ) := congrArg Prod.fst hz
        have h2 : (u : R3) 2 = 0 := congrArg Prod.snd hz
        have h3 : (u : R3) 0 = (z : ℂ).re := by
          have := congrArg Complex.re h1
          simpa [Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_re,
            Complex.ofReal_im] using this
        have h4 : (u : R3) 1 = (z : ℂ).im := by
          have := congrArg Complex.im h1
          simpa [Complex.add_im, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
            Complex.ofReal_im] using this
        ext i
        fin_cases i
        · simpa [modelDisc_zero] using h3.symm
        · simpa [modelDisc_one] using h4.symm
        · simpa [modelDisc_two] using h2.symm }

/-- The chart of `Work.Collar3D.modelDiscCollar` is the explicit chart `discChartFun`. -/
theorem modelDiscCollar_chart (p : (Set.univ : Set R3)) :
    modelDiscCollar.Φ p = discChartFun p :=
  Classical.choose_spec (Work.Collar3D.Model.discChartHomeo) p

/-- **The flat model disc has a collar.** -/
theorem hasDiscCollar_modelDisc : HasDiscCollar modelDisc := ⟨modelDiscCollar⟩

end

end Work.Collar3D
