import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.Topology.UniformSpace.Uniformizable
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseBoxFock.boxRealise_regular
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock

/-- **The regularity package of the box realisation.**  `boxRealise e d Ψ = Σ_α Ψ_α (α!/√d!) M_α`
is a *finite* combination of products of the mode functions `e l`, so if every `e l` is
continuous with compact support and supported in the box then so is `boxRealise e d Ψ`
(`Work.BoseBoxFock.boxRealise_regular` already gives support ⊆ `abox d ℓ`, a.e. strong
measurability and an a.e. bound); the pointwise bound and integrability are the corollaries.

This is the API the BF3c model assembly (`boxSlotSum_finset_sum`, `integrable_mul_of_...`) consumes:
it needs `Measurable` (for `boxSlotSum_finset_sum`), a *pointwise* bound (the same lemma) and
`Integrable` (for the four dictionary pairings of `exists_binary_le_apply`). -/
theorem boxRealise_reg {m d : ℕ} {ℓ : ℝ} (hℓ : 0 < ℓ) {e : Fin m → Work.BoseDict.Sp → ℂ}
    (he : ∀ l, Continuous (e l)) (hbdd : ∀ l, MeasureTheory.MemLp (e l) ⊤)
    (hsupp : ∀ l, Function.support (e l) ⊆ Work.BoseK15.corpusBox.boxL ℓ)
    (Ψ : Work.BoseB4.RealFock m) :
    Continuous (Work.BoseDict.boxRealise e d Ψ)
      ∧ HasCompactSupport (Work.BoseDict.boxRealise e d Ψ)
      ∧ (∃ C : ℝ, ∀ x : Work.BoseDict.Xn d, ‖Work.BoseDict.boxRealise e d Ψ x‖ ≤ C)
      ∧ MeasureTheory.Integrable (Work.BoseDict.boxRealise e d Ψ) := by
  classical
  -- the finite expansion of the realisation on the support of `Ψ`
  have hsum := Work.BoseDict.boxRealise_eq_sum_gen (e := e) (d := d) Ψ
  -- each mode product is continuous
  have hmode_cont : ∀ α : Fin m →₀ ℕ,
      Continuous (fun x : Work.BoseDict.Xn d => Work.BoseDict.modeProd e d α x) := by
    intro α
    have hα : (fun x : Work.BoseDict.Xn d => Work.BoseDict.modeProd e d α x)
        = fun x : Work.BoseDict.Xn d => ∑ σ : Fin d → Fin m,
            (if Work.BoseDict.modeMult σ = α then (1 : ℂ) else 0)
              * ∏ i : Fin d, e (σ i) (x i) := by
      funext x
      rw [Work.BoseDict.modeProd]
    rw [hα]
    refine continuous_finsetSum _ fun σ _ => ?_
    refine Continuous.const_mul ?_ _
    exact continuous_finsetProd _ fun i _ => (he (σ i)).comp (continuous_apply i)
  have hcont : Continuous (Work.BoseDict.boxRealise e d Ψ) := by
    rw [hsum]
    exact continuous_finsetSum _ fun α _ => Continuous.const_mul (hmode_cont α) _
  -- the box is compact, and the support of the realisation lies in it
  have hsupp_abox : Function.support (Work.BoseDict.boxRealise e d Ψ)
      ⊆ Submission.BoseGases.abox d ℓ :=
    (Work.BoseBoxFock.boxRealise_regular (e := e) (d := d) hℓ hbdd hsupp Ψ).1
  have habox : IsCompact (Submission.BoseGases.abox d ℓ) := by
    rw [Submission.BoseGases.abox_eq_pi_acube]
    exact isCompact_univ_pi (fun _ => Submission.BoseGases.acube_compact hℓ)
  have hcs : HasCompactSupport (Work.BoseDict.boxRealise e d Ψ) :=
    HasCompactSupport.of_support_subset_isCompact habox hsupp_abox
  obtain ⟨C, hC⟩ := hcs.exists_bound_of_continuous hcont
  exact ⟨hcont, hcs, ⟨C, hC⟩, hcont.integrable_of_hasCompactSupport hcs⟩

end Work.BoseBoxFock
