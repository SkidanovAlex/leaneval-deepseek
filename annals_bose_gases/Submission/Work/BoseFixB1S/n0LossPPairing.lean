import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1S.boxPIndCommStep
import Submission.Work.BoseFixB1S.boxPInd_finset_sum_gen
import Submission.Work.BoseFixB1S.n0ProjOpPartitionEigen
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1S.n0LossPPairing` — the `n₀`-spectral commutation of the slot
# projections (ledger-line-3 ingredient)

**This file is now `sorry`-free and axiom-clean.**  The (superseded, `sorry`-carrying) sandwich
identity `n0LossPFib_eq` (`SKELETON_n0LossPFib_eq`, kept below as a comment for the record) has
been removed from the live tree; it is now **proved** — together with the corrected `(FS-P)` it
feeds — in

* `Submission/Work/BoseFixB1S/fsPSpectralB1.lean`  (`boxPInd_sandwich`, `fsP_spectral`, …) and
* `Submission/Work/BoseFixB1S/fsPCorpusB1.lean`    (`fsPLossFib_eq`, the sandwich chain).

What remains here is the one ingredient that is *only* about the `n₀` spectral layer:

**(line-3 ingredient) `boxPInd_comm_n0FunOp`** — every `P_{B,i}` commutes with `n0FunOp g`.
Reason: `PᵢQᵢ = QᵢPᵢ = 0` (`Qᵢ = 1_{A,i} − Pᵢ` restricted to the box) and, for `j ≠ i`,
`PᵢPⱼ = PⱼPᵢ`; hence `Pᵢ` commutes with every `n0ProjOp S`, every `n0LagrangeOp k` and finally with
`n0FunOp g`.  (This is *not* `n0OpSlotComm`, which moves the *multiplication* `f(xᵢ)` past `n₀`;
here a *projection* moves past a *function of `n₀`*.)

```
/-- **(line 3)** the exact sandwich … (SUPERSEDED — proved at `fsPCorpusB1.fsPLossFib_eq`) -/
theorem n0LossPFib_eq {N : ℕ} {ℓ volA c : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set E3} (hA : MeasurableSet A) (hvolA : volA = (volume A).toReal)
    (hAc : A ⊆ acube ℓ) {f : E3 → ℝ} (hf : IntegrableOn f A volume) {Φ : X N → ℝ}
    (hΦc : Continuous Φ) :
    n0LossPFib volA c ℓ A f Φ = (∫ z in A, f z) / volA * n0LossP volA c ℓ A Φ
```
-/

noncomputable section

open MeasureTheory
open scoped BigOperators ENNReal

namespace Work.BoseFixB1S

open Submission.BoseGases

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- **(line-3 ingredient)** `P_{B,i}` commutes with the spectral operator `n0FunOp g`. -/
theorem boxPInd_comm_n0FunOp {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set E3} (hA : MeasurableSet A) (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ acube ℓ) (g : ℝ → ℝ) (i : Fin N) {Ψ : X N → ℝ} (hΨc : Continuous Ψ) :
    (fun x => Work.UBBInputs8.boxPInd volA A i (n0FunOp volA A g Ψ) x)
      =ᵐ[MeasureTheory.volume.restrict (abox N ℓ)]
        fun x => n0FunOp volA A g (fun y => Work.UBBInputs8.boxPInd volA A i Ψ y) x := by
  have hΨ : GoodState ℓ Ψ := continuous_goodState hℓ hΨc
  filter_upwards [self_mem_ae_restrict (abox_measurable N ℓ)] with x hx
  set F : ℝ := ∑ S : Finset (Fin N), g (S.card : ℝ) *
      (if i ∈ S then Work.BoseFixB1S.n0ProjOp volA A S Ψ x else 0) with hF
  have hint : ∀ S : Finset (Fin N),
      IntegrableOn (fun z => (fun y : X N => g (S.card : ℝ) *
        Work.BoseFixB1S.n0ProjOp volA A S Ψ y) (Function.update x i z)) A volume := by
    intro S
    have hGS : GoodState ℓ (Work.BoseFixB1S.n0ProjOp volA A S Ψ) := by
      simp only [Work.BoseFixB1S.n0ProjOp]
      exact goodState_n0Iter hℓ hvol hA hvolA hAc _ _ hΨ
    obtain ⟨hmS, CS, hbS⟩ := hGS
    refine slotInt_of_bound (N := N) hℓ hA hAc i x hx (measurable_const.mul hmS) (C :=
      |g (S.card : ℝ)| * max CS 0) (fun y hy => ?_)
    simp only [Pi.mul_apply, abs_mul]
    exact mul_le_mul_of_nonneg_left (le_trans (hbS y hy) (le_max_left CS 0)) (abs_nonneg _)
  have hsc : ∀ (c : ℝ) (Φ : X N → ℝ),
      Work.UBBInputs8.boxPInd volA A i (fun y => c * Φ y) x
        = c * Work.UBBInputs8.boxPInd volA A i Φ x := by
    intro c Φ
    simp only [Work.UBBInputs8.boxPInd]
    rw [MeasureTheory.integral_const_mul]
    ring
  have hL : Work.UBBInputs8.boxPInd volA A i (n0FunOp volA A g Ψ) x = F := by
    rw [n0FunOp_eq_sum_card volA A g Ψ]
    rw [boxPInd_finset_sum_gen volA A i x Finset.univ
      (fun S y => g (S.card : ℝ) * Work.BoseFixB1S.n0ProjOp volA A S Ψ y)
      (fun S _ => hint S)]
    rw [hF]
    refine Finset.sum_congr rfl (fun S _ => ?_)
    rw [hsc]
    rw [n0IterEigen hℓ hvol hA hvolA hAc S hΨ i x hx]
  have hR : n0FunOp volA A g (fun y => Work.UBBInputs8.boxPInd volA A i Ψ y) x = F := by
    rw [n0FunOp_eq_sum_card volA A g (fun y => Work.UBBInputs8.boxPInd volA A i Ψ y)]
    rw [hF]
    refine Finset.sum_congr rfl (fun S _ => ?_)
    have hcomm : Work.BoseFixB1S.n0ProjOp volA A S
          (fun y => Work.UBBInputs8.boxPInd volA A i Ψ y) x
        = Work.UBBInputs8.boxPInd volA A i (Work.BoseFixB1S.n0ProjOp volA A S Ψ) x := by
      simp only [Work.BoseFixB1S.n0ProjOp]
      exact n0Iter_comm_boxPInd_local hℓ hvol hA hvolA hAc _ i _ hΨ x hx
    rw [hcomm, n0IterEigen hℓ hvol hA hvolA hAc S hΨ i x hx]
  rw [hL, hR]

end Work.BoseFixB1S
