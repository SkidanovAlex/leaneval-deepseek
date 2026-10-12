import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1S.n0FunOp_eq_sum_card
import Submission.Work.BoseFixB1S.n0SpectralMomentsB1
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

namespace Work.BoseFixB1S

open Submission.BoseGases

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- **The affine `n₀`-calculus identity for a `GoodState`** (measurable and bounded on the
analysis box — the weakest hypothesis under which the sector eigenvalue identity
`n0Op_eq_sum_card_mul` is available). -/
theorem n0FunOp_affineB1_of_goodState {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set E3} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ acube ℓ)
    (c : ℝ) {Ψ : X N → ℝ} (hΨG : GoodState ℓ Ψ) :
    (fun x => n0FunOp volA A (fun r : ℝ => r + 1 - c) Ψ x)
      =ᵐ[MeasureTheory.volume.restrict (abox N ℓ)]
      fun x => n0Op volA A Ψ x + (1 - c) * Ψ x := by
  filter_upwards [self_mem_ae_restrict (abox_measurable N ℓ)] with x hx
  have hL := congrFun (n0FunOp_eq_sum_card volA A (fun r : ℝ => r + 1 - c) Ψ) x
  have h1 := n0Op_eq_sum_card_mul hℓ hvol hA hvolA hAc hΨG x hx
  have h2 := congrFun (n0ProjOp_sum_eq volA A Ψ) x
  rw [hL, h1, ← h2, Finset.sum_apply, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun S _ => ?_)
  ring

/-- **The affine `n₀`-calculus identity for a continuous state** — the form in which the sibling
lemmas of the layer (`n0FunOp_compB1`, `n0FunOp_eq_flatFunOp`) state their hypotheses. -/
theorem n0FunOp_affineB1_of_continuous {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set E3} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ acube ℓ)
    (c : ℝ) {Ψ : X N → ℝ} (hΨc : Continuous Ψ) :
    (fun x => n0FunOp volA A (fun r : ℝ => r + 1 - c) Ψ x)
      =ᵐ[MeasureTheory.volume.restrict (abox N ℓ)]
      fun x => n0Op volA A Ψ x + (1 - c) * Ψ x := by
  obtain ⟨C, _hC0, hCb⟩ := exists_abox_bound hℓ hΨc
  exact n0FunOp_affineB1_of_goodState hℓ hvol hA hvolA hAc c ⟨hΨc.measurable, C, hCb⟩

end Work.BoseFixB1S
