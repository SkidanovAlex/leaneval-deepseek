import Mathlib
import Submission.Work.LinnikAreas.BGTZ.SelbergSieveAux

namespace Work.LinnikAreas.BGTZ

open Work.LinnikAreas

/-- **Upper bound for the smoothed sum from the critical-line shift.**

This is the twin of `Ssm_ge_res_sub_J`: the contour shift of `SelbergSieveAux` writes
`SsmC ψ β x = triPerronRes ψ β x + J` with `J` the critical-line integral, and taking real parts
gives `Ssm ψ β x = Re L(1,ψ)·x^{1-β}/((1-β)(2-β)) + J.re`.  Since `J.re ≤ ‖J‖ ≤ K`, the smoothed
sum is at most the residue term plus `K`. -/
theorem Ssm_le_res_add_J {N : ℕ} [NeZero N] (ψ : DirichletCharacter ℂ N) (hψ : ψ ≠ 1)
    (hψ2 : ψ ^ 2 = 1) {β x K : ℝ} (hβ : 1 / 2 < β) (hβ1 : β < 1) (hx : 1 < x)
    (hxnn : ∀ n : ℕ, (n : ℝ) ≠ x) (hL0 : DirichletCharacter.LFunction ψ (β : ℂ) = 0)
    (hint : MeasureTheory.Integrable
      (fun y : ℝ => Work.LinnikAreas.triFun ψ β x (((1 / 2 - β : ℝ)) + (y : ℂ) * Complex.I)))
    (hperr : Filter.Tendsto (fun T : ℝ => Work.LinnikAreas.perrErr ψ β x T) Filter.atTop (nhds 0))
    (hH : Filter.Tendsto (fun T : ℝ => (1 / (2 * Real.pi * Complex.I)) *
        ((∫ u in ((1 / 2 - β : ℝ))..1, Work.LinnikAreas.triFun ψ β x ((u : ℂ) + T * Complex.I))
         - (∫ u in ((1 / 2 - β : ℝ))..1, Work.LinnikAreas.triFun ψ β x ((u : ℂ) - T * Complex.I))))
        Filter.atTop (nhds 0))
    (hJ : ‖(1 / (2 * Real.pi)) *
        (∫ y : ℝ, Work.LinnikAreas.triFun ψ β x (((1 / 2 - β : ℝ)) + (y : ℂ) * Complex.I))‖ ≤ K) :
    Work.LinnikAreas.Ssm ψ β x - K
      ≤ (DirichletCharacter.LFunction ψ 1).re * (x ^ (1 - β) / ((1 - β) * (2 - β))) := by
  have hx0 : 0 ≤ x := le_of_lt (lt_trans zero_lt_one hx)
  -- the contour-shift identity: `SsmC = triPerronRes + J`
  have hid := SsmC_sub_res_eq_critIntegral ψ hψ hψ2 hβ hβ1 hx hxnn hL0 hint hperr hH
  have hsplit : Work.LinnikAreas.SsmC ψ β x
      = Work.LinnikAreas.triPerronRes ψ β x
        + (1 / (2 * Real.pi)) *
            (∫ y : ℝ, Work.LinnikAreas.triFun ψ β x (((1 / 2 - β : ℝ)) + (y : ℂ) * Complex.I)) := by
    rw [← hid]; ring
  -- take real parts
  have hre : Work.LinnikAreas.Ssm ψ β x
      = (Work.LinnikAreas.triPerronRes ψ β x).re
        + ((1 / (2 * Real.pi)) *
            (∫ y : ℝ, Work.LinnikAreas.triFun ψ β x
              (((1 / 2 - β : ℝ)) + (y : ℂ) * Complex.I))).re := by
    rw [Ssm_eq_re_SsmC', hsplit, Complex.add_re]
  -- the real part of the critical-line integral is at most `K`
  have hle : ((1 / (2 * Real.pi)) *
      (∫ y : ℝ, Work.LinnikAreas.triFun ψ β x (((1 / 2 - β : ℝ)) + (y : ℂ) * Complex.I))).re
      ≤ K := le_trans (Complex.re_le_norm _) hJ
  rw [hre, triPerronRes_re (β := β) (x := x) ψ hx0]
  linarith

end Work.LinnikAreas.BGTZ
