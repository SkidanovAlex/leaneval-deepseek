import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.PhiStar.Honesty.HkMem_K_slots_of_vanishing_family
import Submission.Work.FTS.PhiStar.Honesty.ellWeakPos_seven_of_slots
import Submission.Work.FTS.PhiStar.Honesty.Fstar_psiSeries_eq_zero
import Submission.Work.FTS.PhiStar.Series.Defs
import Submission.Work.FTS.EllipticEst.TT.WeakDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.PhiStar.Honesty

theorem ellWeakPos_K_psiSeries_of_level0 (K : ℕ) {α : ℝ} {F : ℝ → ℝ → ℝ}
    (hα : 0 < α) (hα4 : α ≤ 1 / 4) (hγ : Work.Spaces.gam α ≤ 3 / 2)
    (hF : Work.Spaces.HkMem α K F)
    (hsm : Work.FTS.EllipticEst.SmoothOpen (Work.FTS.PhiStar.Series.psiSeries α F))
    (heq : ∀ z : ℝ, 0 < z → ∀ θ : ℝ, 0 < θ → θ < Real.pi / 2 →
      Work.Elliptic.bslOp α (Work.FTS.PhiStar.Series.psiSeries α F) z θ = F z θ)
    (hFstar : ∀ z : ℝ, 0 < z → Work.Elliptic.Fstar F z = 0)
    (hcoef : ∀ z : ℝ, 0 < z → Summable (fun m : ℕ =>
      ((m : ℝ) + 1) * |Work.FTS.PhiStar.Series.acoeff α m F z|))
    (hσ : ∀ l m : ℕ, l ≤ K + 2 → m ≤ 2 → Work.Spaces.HkMem α 0
      (Work.Spaces.DzIter l (Work.Spaces.pthIter m
        (Work.FTS.PhiStar.Series.psiSeries α F))))
    (hV : ∀ t l : ℕ, 3 ≤ t → t ≤ K + 2 → l ≤ K + 2 →
      (∀ z ∈ Work.Spaces.Iz, MeasureTheory.IntegrableOn (fun θ =>
          (Work.Spaces.DzIter l (Work.Spaces.pthIter t
              (Work.FTS.PhiStar.Series.psiSeries α F)) z θ * Work.Spaces.w z) ^ 2
            * (Real.sin (2 * θ)) ^ (2 * (t : ℝ) - 4 - Work.Spaces.gam α)) Work.Spaces.Iθ) ∧
      MeasureTheory.IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.DzIter l (Work.Spaces.pthIter t
              (Work.FTS.PhiStar.Series.psiSeries α F)) z θ * Work.Spaces.w z) ^ 2
            * (Real.sin (2 * θ)) ^ (2 * (t : ℝ) - 4 - Work.Spaces.gam α)) Work.Spaces.Iz) :
    Work.FTS.EllipticEst.TT.EllWeakPos α K F (Work.FTS.PhiStar.Series.psiSeries α F) := by
  -- The three elliptic honesty slots `z²∂_z²Ψ`, `∂_θ²Ψ`, `z∂_z∂_θ²Ψ` at level `K`, from the
  -- pure-radial family `hσ` and the vanishing-weight family `hV` through the grid majorant.
  obtain ⟨hmemA, hmemB, hmemMix⟩ :=
    HkMem_K_slots_of_vanishing_family K hα hγ hsm hσ hV
  -- The ten conjuncts of the weak class: the equation, the two Dirichlet traces (elementary for
  -- the mode series), the two moments (the source's is `hFstar`, the solution's is
  -- `Fstar_psiSeries_eq_zero`), the open-quadrant smoothness, and the four `HkMem` slots.
  exact ⟨heq, fun z => psiSeries_zero_theta_zero α F z,
    fun z => psiSeries_zero_theta_pi_half α F z, hFstar,
    fun z hz => Fstar_psiSeries_eq_zero hz (hcoef z hz) hFstar,
    fun n => Work.FTS.EllipticEst.SmoothOpen.forall hsm n, hF, hmemA, hmemB, hmemMix⟩

end Work.FTS.PhiStar.Honesty
