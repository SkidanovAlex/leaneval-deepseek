import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.PhiStar.Honesty.Fstar_psiSeries_eq_zero
import Submission.Work.FTS.PhiStar.Series.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.FTS.EllipticEst.TT.WeakDefs
import Submission.Work.FTS.PhiStar.Honesty.psiSeries_slice_tendsto

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS.PhiStar.Honesty.ellWeakPos_seven_of_slots`

The mode series `Ψ = psiSeries α F` is put in the weak hypothesis class
`EllWeakPos α 7 F Ψ` from the slot hypotheses that the surrounding `PhiStar` development
supplies:

* the equation `bslOp α Ψ = F` on the open quadrant (`heq`),
* the source's angular moment `F_* F ≡ 0` on `z > 0` (`hFstar`),
* the weighted summability of the mode coefficients (`hcoef`),
* `C^∞`-smoothness of `Ψ` on the open quadrant (`hsm`),
* the four honesty (`HkMem`) slots (`hF`, `hmemA`, `hmemB`, `hmemMix`).

The only conjuncts *not* among the hypotheses are the two Dirichlet traces of `Ψ`
(`Ψ z 0 = 0`, `Ψ z (π/2) = 0`, for **every** real `z`, not merely `z > 0`) and the vanishing of
the *solution's* moment `F_* Ψ`.  The traces are immediate: every basis function `eFam m` vanishes
at `θ = 0` (`gC (2m+1) 0 = 0`, `gC` odd) and at `θ = π/2` (`cos (π/2) = 0`), so every term of the
series vanishes there and hence so does the series — no summability is needed.  The moment is
`Fstar_psiSeries_eq_zero`, which needs exactly `hcoef` and `hFstar` on `z > 0`.
-/

namespace Work.FTS.PhiStar.Honesty

open MeasureTheory Set Filter

/-- `eFam m 0 = 0`: the angular basis vanishes at the right endpoint
(`gC (2m+1)` is `odd`, hence zero at the origin). -/
private lemma eFam_zero_theta_zero (m : ℕ) : Work.FTS.PhiStar.Gegenbauer.eFam m 0 = 0 := by
  simp only [Work.FTS.PhiStar.Gegenbauer.eFam, Real.sin_zero, Real.cos_zero, one_mul]
  exact Work.FTS.PhiStar.Gegenbauer.gC_odd_zero m

/-- `eFam m (π/2) = 0`: the angular basis vanishes at the left endpoint (`cos (π/2) = 0`). -/
private lemma eFam_zero_theta_pi_half (m : ℕ) :
    Work.FTS.PhiStar.Gegenbauer.eFam m (Real.pi / 2) = 0 := by
  simp only [Work.FTS.PhiStar.Gegenbauer.eFam, Real.cos_pi_div_two, zero_mul]

/-- **The convolution trace `Ψ z 0 = 0` of the mode series** (conjunct 3 of `EllWeakPos`).  Every
term of the series vanishes, so the series does, for every real `z` — in particular for `z ≤ 0`,
where no honesty hypothesis is available. -/
theorem psiSeries_zero_theta_zero (α : ℝ) (F : ℝ → ℝ → ℝ) (z : ℝ) :
    Work.FTS.PhiStar.Series.psiSeries α F z 0 = 0 := by
  simp only [Work.FTS.PhiStar.Series.psiSeries, eFam_zero_theta_zero, mul_zero, tsum_zero]

/-- **The convolution trace `Ψ z (π/2) = 0` of the mode series** (conjunct 4 of `EllWeakPos`). -/
theorem psiSeries_zero_theta_pi_half (α : ℝ) (F : ℝ → ℝ → ℝ) (z : ℝ) :
    Work.FTS.PhiStar.Series.psiSeries α F z (Real.pi / 2) = 0 := by
  simp only [Work.FTS.PhiStar.Series.psiSeries, eFam_zero_theta_pi_half, mul_zero, tsum_zero]

/-- **The mode series lies in the weak hypothesis class of the `ℋ^7` elliptic estimate**, from
the slot hypotheses supplied by the `PhiStar` development.

The ten conjuncts of `EllWeakPos α 7 F Ψ` are, in order: the equation on the open quadrant
(`heq`), the two Dirichlet traces (proved here), the two moment conditions (`hFstar` for the
source, `Fstar_psiSeries_eq_zero` for the solution — using `hcoef`), the open-quadrant
smoothness (`hsm`, through `SmoothOpen.forall`), and the four `HkMem` slots
(`hF`, `hmemA`, `hmemB`, `hmemMix`). -/
theorem ellWeakPos_seven_of_slots {α : ℝ} {F : ℝ → ℝ → ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4)
    (hF : Work.Spaces.HkMem α 7 F)
    (hsm : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.PhiStar.Series.psiSeries α F))
    (heq : ∀ z : ℝ, 0 < z → ∀ θ : ℝ, 0 < θ → θ < Real.pi / 2 →
      Work.Elliptic.bslOp α (Work.FTS.PhiStar.Series.psiSeries α F) z θ = F z θ)
    (hFstar : ∀ z : ℝ, 0 < z → Work.Elliptic.Fstar F z = 0)
    (hcoef : ∀ z : ℝ, 0 < z → Summable (fun m : ℕ =>
      ((m : ℝ) + 1) * |Work.FTS.PhiStar.Series.acoeff α m F z|))
    (hmemA : Work.Spaces.HkMem α 7 (fun z θ =>
      z ^ 2 * Work.Spaces.pzIter 2 (Work.FTS.PhiStar.Series.psiSeries α F) z θ))
    (hmemB : Work.Spaces.HkMem α 7 (Work.Spaces.pthIter 2 (Work.FTS.PhiStar.Series.psiSeries α F)))
    (hmemMix : Work.Spaces.HkMem α 7 (fun z θ =>
      z * Work.Spaces.pz (Work.Spaces.pthIter 2 (Work.FTS.PhiStar.Series.psiSeries α F)) z θ)) :
    Work.FTS.EllipticEst.TT.EllWeakPos α 7 F (Work.FTS.PhiStar.Series.psiSeries α F) := by
  refine ⟨heq, fun z => psiSeries_zero_theta_zero α F z,
    fun z => psiSeries_zero_theta_pi_half α F z, hFstar,
    fun z hz => Fstar_psiSeries_eq_zero hz (hcoef z hz) hFstar,
    fun n => Work.FTS.EllipticEst.SmoothOpen.forall hsm n, hF, hmemA, hmemB, hmemMix⟩

end Work.FTS.PhiStar.Honesty
