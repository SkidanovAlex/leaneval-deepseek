import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BSKinetic.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

namespace Work.BSKinetic

open MeasureTheory

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

set_option linter.unusedVariables false

/-- If a function vanishes off the closed centred box `acube ℓ`, then — because the complement of
that box is open — its Fréchet derivative vanishes off the box as well (the function is *locally*
zero there). -/
lemma fderiv_eq_zero_of_notMem_acube {ℓ : ℝ} {ψ : ℝ³ → ℝ}
    (hsupp : ∀ x : ℝ³, x ∉ Submission.BoseGases.acube ℓ → ψ x = 0) :
    ∀ x : ℝ³, x ∉ Submission.BoseGases.acube ℓ → fderiv ℝ ψ x = 0 := by
  intro x hx
  have hopen : IsOpen (Submission.BoseGases.acube ℓ)ᶜ :=
    (Submission.BoseGases.acube_isClosed ℓ).isOpen_compl
  have hev : ψ =ᶠ[nhds x] (fun _ : ℝ³ => (0 : ℝ)) := by
    filter_upwards [hopen.mem_nhds (by simpa using hx)] with y hy
    exact hsupp y (by simpa using hy)
  rw [hev.fderiv_eq]
  exact fderiv_const_apply 0

theorem dSpace_eq_dBox_of_supp {ℓ : ℝ} (hℓ : 0 < ℓ) {ψ : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hψ : ContDiff ℝ (⊤ : ENat) ψ)
    (hsupp : ∀ x : EuclideanSpace ℝ (Fin 3), x ∉ Submission.BoseGases.acube ℓ → ψ x = 0) :
    Work.BSKinetic.dSpace ψ = Work.BSKinetic.dBox ℓ ψ := by
  have hzero := fderiv_eq_zero_of_notMem_acube (ℓ := ℓ) hsupp
  unfold dSpace dBox
  refine Finset.sum_congr rfl (fun k _ => ?_)
  exact (setIntegral_eq_integral_of_forall_compl_eq_zero
    (s := Submission.BoseGases.acube ℓ)
    (f := fun x : ℝ³ => (fderiv ℝ ψ x (Submission.BoseGases.kcStdBasis k)) ^ 2)
    (fun x hx => by rw [hzero x hx]; simp)).symm

end Work.BSKinetic
