import Mathlib
import Submission.Work.LinnikAreas.BGTZSetup
import Submission.Work.LinnikAreas.SiegelBase
import Submission.Work.LinnikAreas.boxMaxZero
import Submission.Commons.NumberTheory.Zeta.riemannZeta_neg_of_Ioo_half_one

namespace Work.LinnikAreas.BGTZ

/-- **`ζ` has no real zero in `(1/2,1)`.**  The completed Riemann zeta function does not vanish at
any real `β` with `1/2 < β < 1` (since `ζ(β) < 0` there, via the alternating-series representation
`ζ(σ) = η(σ)/(1-2^{1-σ})` with `η(σ) > 0`; the file
`Submission/Commons/NumberTheory/Zeta/riemannZeta_neg_of_Ioo_half_one.lean` contains exactly this,
as `Commons.NumberTheory.Zeta.riemannZeta_neg_of_Ioo_half_one`).  In particular the principal
character cannot share the exceptional zero `β₁` of a real `χ₁`. -/
theorem PrincipalNoRealZero {q : ℕ} [NeZero q] {β : ℝ} (hβ0 : 1 / 2 < β) (hβ1 : β < 1)
    (hz : Work.LinnikContract.zeroMult (1 : DirichletCharacter ℂ q) (β : ℂ) ≠ 0) : False := by
  have hβpos : (0 : ℝ) < β := by linarith
  have hβne : (β : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hβpos)
  -- `zeroMult 1` is the vanishing order of the completed Riemann zeta function
  have hΛ : completedRiemannZeta (β : ℂ) = 0 := by
    rw [Work.LinnikAreas.boxMaxZeroAux.zeroMult_one_eq_completedRiemannZeta q (β : ℂ)] at hz
    exact apply_eq_zero_of_analyticOrderNatAt_ne_zero hz
  -- hence `ζ β = 0`
  have hζ : riemannZeta (β : ℂ) = 0 := by
    rw [riemannZeta_def_of_ne_zero hβne, hΛ, zero_div]
  -- but `ζ` is strictly negative on `(1/2,1)`
  obtain ⟨c, hc, hcz⟩ := Commons.NumberTheory.Zeta.riemannZeta_neg_of_Ioo_half_one hβ0 hβ1
  rw [hcz] at hζ
  exact hc.ne (Complex.ofReal_injective (hζ.trans Complex.ofReal_zero.symm))

end Work.LinnikAreas.BGTZ
