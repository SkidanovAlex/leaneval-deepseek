import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Topology.Separation.CompletelyRegular
import Submission.Work.FTS.H2.DivQ.Defs
import Submission.Work.FTS.H2.DivQ.thetaOfSubst
import Submission.Work.FTS.H2.DivQ.inversionNear
import Submission.Work.FTS.H2.DivQ.aCoeff_diag
import Submission.Work.FTS.H2.DivQ.aCoeff_bounds
import Submission.Work.FTS.H2.DivQ.WDefs
import Submission.Work.FTS.H2.DivQ.Wide_le_Dom
import Submission.Work.FTS.H2.DivQ.exists_Cm_aCoeffBnd

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.H2.DivQ

open scoped Real Topology
open MeasureTheory Set Filter

/-- **Integrability and the integral bound for the `x`-weighted derivatives of a slice.**

`Submission/Work/FTS/H2/DivQ/inversionNear.lean` gives the *integral* bound
`B_m = ∫_0^{x₁} x^{2m-γ}(∂_x^{m+1}(sliceX h))² ≤ C (Denη + Σ_{1≤n≤m} Denγ n)` for the honest
angular data of a smooth slice `h`; this theorem adds the **honesty** of `B_m`, i.e. the
integrability of the integrand itself, which is what a consumer needs in order to apply the
inequality (Lean's integral of a non-integrable nonnegative function is the junk value `0`).

The route is the one of `inversionNear`: `B_m`'s integrand is `Wide α h m`, and the triangular
inversion of §4 of `Submission/Work/FTS/H2/DivQ/NOTES.md` produces, through the `aCoeff`
expansion `D_θ^m(∂_θh)(θ x) = Σ_{l≤m} a m l x · x^l ∂_x^{l+1}(sliceX h)(x)`, the pointwise
domination `Wide α h m ≤ Dom α h Cm m` (`Wide_le_Dom`), where `Dom α h Cm m` is a nonnegative
combination of the `x`-pullbacks of the two honest data integrands (`HonGam`, `SubEta`) and is
therefore integrable (`dom_integrable`); continuity of `Wide α h m` on `(0,x₁)` then gives the
integrability.  The `Ioc`-to-`Ioo` bookkeeping is `integrableOn_Ioc_iff_integrableOn_Ioo`, the
unit `{0}` being null. -/
theorem W_integrable :
    ∃ C : ℝ, 0 < C ∧ ∀ (α : ℝ) (h : ℝ → ℝ), 0 < α → α ≤ 1 →
      ContDiffOn ℝ (⊤ : ℕ∞) h (Set.Ioo 0 (Real.pi / 2)) →
      MeasureTheory.IntegrableOn
        (fun θ : ℝ => (deriv h θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta))) Work.Spaces.Iθ →
      (∀ m : ℕ, m ∈ Finset.Icc 1 4 → MeasureTheory.IntegrableOn
        (fun θ : ℝ => (Work.Elliptic.Dth1Iter m (deriv h) θ) ^ 2
          * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α))) Work.Spaces.Iθ) →
      ∀ m : ℕ, m ∈ Finset.Icc 1 4 →
        MeasureTheory.IntegrableOn
          (fun x : ℝ => x ^ (2 * (m : ℝ) - Work.Spaces.gam α)
            * (iteratedDeriv (m + 1) (Work.FTS.H2.DivQ.sliceX h) x) ^ 2) (Set.Ioc 0 Work.FTS.H2.DivQ.xNear) ∧
        (∫ x in (0 : ℝ)..Work.FTS.H2.DivQ.xNear,
            x ^ (2 * (m : ℝ) - Work.Spaces.gam α)
              * (iteratedDeriv (m + 1) (Work.FTS.H2.DivQ.sliceX h) x) ^ 2)
          ≤ C * ((∫ θ in Work.Spaces.Iθ,
                (deriv h θ) ^ 2 * (Real.sin (2 * θ)) ^ (-(Work.Spaces.eta)))
              + ∑ n ∈ Finset.Icc 1 m, (∫ θ in Work.Spaces.Iθ,
                  (Work.Elliptic.Dth1Iter n (deriv h) θ) ^ 2
                    * (Real.sin (2 * θ)) ^ (-(Work.Spaces.gam α)))) := by
  -- the integral conjunct is verbatim `inversionNear`
  obtain ⟨Cinv, hCinvpos, hCinv⟩ := inversionNear
  refine ⟨Cinv, hCinvpos, ?_⟩
  intro α h hα0 hα1 hsm hDenEta hDenGam m hm
  obtain ⟨hm1, hm4⟩ := Finset.mem_Icc.mp hm
  -- a uniform bound for the finitely many coefficients `aCoeff n l`, `1 ≤ n ≤ 4`, `l ≤ n`
  obtain ⟨Cm, hCmnn, hCb, hC0⟩ := exists_Cm_aCoeffBnd
  -- the two building blocks of `Dom` are integrable: they are the pullbacks of the honest data
  have hEtaInt : MeasureTheory.IntegrableOn (SubEta h) (Set.Ioo 0 xNear) :=
    subEta_integrable hDenEta
  have hGamInt : ∀ n ∈ Finset.Icc 1 4,
      MeasureTheory.IntegrableOn (HonGam α h n) (Set.Ioo 0 xNear) :=
    fun n hn => honGam_integrable (hDenGam n hn)
  have hDomInt : ∀ l ≤ 4, MeasureTheory.IntegrableOn (Dom α h Cm l) (Set.Ioo 0 xNear) :=
    (dom_integrable hEtaInt hGamInt).1
  -- the integrand of `B_m` is `Wide α h m`, continuous on the near interval
  have hcont : ContinuousOn (Wide α h m) (Set.Ioo (0 : ℝ) xNear) := by
    refine ContinuousOn.mul ?_ ?_
    · exact ContinuousOn.rpow_const continuousOn_id
        (fun x hx => Or.inl (ne_of_gt hx.1))
    · exact ((contDiffOn_iteratedDeriv_sliceX hsm (m + 1)).continuousOn).pow 2
  have hle : ∀ x ∈ Set.Ioo (0 : ℝ) xNear, Wide α h m x ≤ Dom α h Cm m x :=
    fun x hx => Wide_le_Dom hα1 hCmnn hsm hCb hC0 hm1 hm4 hx
  have hWideIntIoo : MeasureTheory.IntegrableOn (Wide α h m) (Set.Ioo 0 xNear) := by
    refine Integrable.mono' (hDomInt m hm4)
      (hcont.aestronglyMeasurable measurableSet_Ioo) ?_
    rw [ae_restrict_iff' measurableSet_Ioo]
    exact Filter.Eventually.of_forall (fun x hx => by
      rw [Real.norm_of_nonneg (Wide_nonneg α h m (le_of_lt hx.1))]
      exact hle x hx)
  have hWideInt : MeasureTheory.IntegrableOn (Wide α h m) (Set.Ioc 0 xNear) := by
    rw [integrableOn_Ioc_iff_integrableOn_Ioo]
    exact hWideIntIoo
  exact ⟨hWideInt, hCinv α h hα0 hα1 hsm hDenEta hDenGam m hm⟩

end Work.FTS.H2.DivQ
