import Mathlib
import Submission.Work.Mostow.stdFermiDefs
import Submission.Work.Mostow.areaFormula
import Submission.Work.Mostow.VolDefs
import Submission.Work.Mostow.stdFermiCoordFacts
import Submission.Work.Mostow.stdFermiSelfInjective
import Submission.Work.Mostow.stdFermiSelfTpart
import Submission.Work.Mostow.stdCoshLintegralIoo
import Submission.Work.Mostow.stdFermiSelfHjacLeb
import Submission.Work.Mostow.stdFermiCoordMapMap
import Submission.Work.Mostow.stdFermiSelfFderivDet

/-!
# The hyperbolic area of the standard Fermi rectangle in `ℍ²`

`Work.Mostow.stdFermiVolume`: the area of the image under the standard Fermi chart
`stdFermi (s,r) = cosh r • lineStd s + sinh r • axisPerp` of the rectangle
`[0,L) × (-ρ,ρ)` is `L * 2 sinh ρ`.  In the Fermi coordinates the hyperbolic area element is
`cosh r ds dr`, so the area is `∫₀^L ∫_{-ρ}^{ρ} cosh r dr ds = L (sinh ρ - sinh (-ρ))`.

The chart splits as `stdFermi = fermiSelf ∘ coordMap` with `coordMap` the linear coordinate
identification `ℝ × ℝ ≅ E 2` (measure preserving) and `fermiSelf` the chart read in the chart
coordinates of `ℍ²`; the change of variables formula `volH_image_of_injOn` then reduces the
computation to a one-dimensional integral of `cosh`.
-/

namespace Work.Mostow

set_option linter.unusedSimpArgs false

open Submission.Mostow LeanEval.Geometry.MostowRigidity MeasureTheory
open scoped ENNReal

noncomputable section

/-- The standard Fermi chart of `ℍ²`, read in the coordinates of `E 2`, is `C¹`. -/
lemma stdFermiSelf_contDiff : ContDiff ℝ 1 FermiTwo.fermiSelf := by
  unfold FermiTwo.fermiSelf
  fun_prop

/-- **The coordinate box integral.** With respect to Lebesgue measure on `E 2`,
`∫⁻ x in boxSq L ρ, cosh (x 1) = L * 2 sinh ρ`. -/
lemma stdFermiBoxIntegral (L ρ : ℝ) (hL : 0 < L) (hρ : 0 < ρ) :
    ∫⁻ x in FermiTwo.boxSq L ρ, ENNReal.ofReal (Real.cosh (x 1)) ∂(volume : Measure (E 2))
      = ENNReal.ofReal (L * (2 * Real.sinh ρ)) := by
  obtain ⟨hcf, _hexp, _hinjc, _himg, hmeas, _hstd⟩ := stdFermiCoordFacts
  have hmap := stdFermiCoordMapMap
  have hpre : FermiTwo.coordMap ⁻¹' FermiTwo.boxSq L ρ = Set.Ico 0 L ×ˢ Set.Ioo (-ρ) ρ := by
    ext p
    simp only [Set.mem_preimage, FermiTwo.boxSq, Set.mem_setOf_eq, Set.mem_prod, Set.mem_Ico,
      Set.mem_Ioo, (hcf p).1, (hcf p).2]
  have hfc : Measurable (fun x : E 2 => ENNReal.ofReal (Real.cosh (x 1))) := by fun_prop
  have hcm : Measurable FermiTwo.coordMap := by
    rw [show FermiTwo.coordMap = fun p : ℝ × ℝ =>
      p.1 • FermiTwo.axis + p.2 • FermiTwo.axisPerp from rfl]
    fun_prop
  rw [← hmap, setLIntegral_map (hmeas L ρ) hfc hcm, hpre]
  rw [setLIntegral_congr_fun ((measurableSet_Ico).prod measurableSet_Ioo)
      (fun p _ => by rw [(hcf p).2])]
  rw [setLIntegral_prod (fun p : ℝ × ℝ => ENNReal.ofReal (Real.cosh p.2)) (by fun_prop)]
  -- in the inner integral the integrand is already independent of the outer variable
  have hinner : ∀ a : ℝ, ∫⁻ b in Set.Ioo (-ρ) ρ, ENNReal.ofReal (Real.cosh (a, b).2) ∂volume
      = ∫⁻ b in Set.Ioo (-ρ) ρ, ENNReal.ofReal (Real.cosh b) ∂volume := by
    intro a
    exact setLIntegral_congr_fun measurableSet_Ioo (fun b _ => rfl)
  simp only [hinner]
  rw [setLIntegral_const, stdCoshLintegralIoo ρ hρ, Real.volume_Ico, sub_zero,
    mul_comm (ENNReal.ofReal (2 * Real.sinh ρ)) (ENNReal.ofReal L),
    ← ENNReal.ofReal_mul (le_of_lt hL)]

/-- The hyperbolic Jacobian of the Fermi chart, read in the coordinates of `E 2`. -/
lemma stdFermiSelf_hjacLeb (x : E 2) :
    hjacLeb FermiTwo.fermiSelf x = ENNReal.ofReal (Real.cosh (x 1)) := by
  exact stdFermiSelfHjacLeb x (stdFermiSelfFderivDet x) (stdFermiSelfTpart x)

theorem stdFermiVolume (L ρ : ℝ) (hL : 0 < L) (hρ : 0 < ρ) :
    Submission.Mostow.volH 2 (Work.Mostow.FermiTwo.stdFermi '' (Set.Ico 0 L ×ˢ Set.Ioo (-ρ) ρ))
      = ENNReal.ofReal (L * (2 * Real.sinh ρ)) := by
  obtain ⟨_hcf, _hexp, _hinjc, himg, hmeas, hstd⟩ := stdFermiCoordFacts
  have hset : FermiTwo.stdFermi '' (Set.Ico 0 L ×ˢ Set.Ioo (-ρ) ρ)
      = FermiTwo.fermiSelf '' FermiTwo.boxSq L ρ := by
    rw [show FermiTwo.stdFermi = FermiTwo.fermiSelf ∘ FermiTwo.coordMap from funext hstd,
      Set.image_comp, himg L ρ]
  rw [hset, volH_image_of_injOn stdFermiSelf_contDiff (hmeas L ρ)
    (stdFermiSelfInjective.injOn)]
  rw [setLIntegral_congr_fun (hmeas L ρ) (fun x _ => stdFermiSelf_hjacLeb x)]
  exact stdFermiBoxIntegral L ρ hL hρ

end

end Work.Mostow
