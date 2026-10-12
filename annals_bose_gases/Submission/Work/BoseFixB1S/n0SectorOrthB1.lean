import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1S.boxPIndSelfAdjoint
import Submission.Work.BoseFixB1S.n0IterEigen
import Submission.Work.BoseFixB1S.n0SlotDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1S

open MeasureTheory
open scoped BigOperators ENNReal

open Submission.BoseGases

/-- Auxiliary form of the orthogonality: for a slot `j ∈ S \ T` the pairing `∫ u_S u_T` vanishes.
On the box `P_j u_S = u_S` (`n0IterEigen`, eigenvalue `1`) and `P_j u_T = 0` (eigenvalue `0`), while
`P_j` is self-adjoint (`boxPIndSelfAdjoint`); hence
`∫ u_S u_T = ∫ (P_j u_S) u_T = ∫ u_S (P_j u_T) = ∫ u_S · 0 = 0`. -/
theorem n0SectorOrthB1_aux {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    {Φ : Submission.BoseGases.X N → ℝ} (hGΦ : GoodState ℓ Φ)
    (S T : Finset (Fin N)) (j : Fin N) (hjS : j ∈ S) (hjT : j ∉ T) :
    (∫ x in Submission.BoseGases.abox N ℓ,
        Work.BoseFixB1S.n0ProjOp volA A S Φ x
          * Work.BoseFixB1S.n0ProjOp volA A T Φ x) = 0 := by
  have hSG : GoodState ℓ (n0ProjOp volA A S Φ) :=
    goodState_n0Iter hℓ hvol hA hvolA hAc (fun i => decide (i ∈ S))
      (List.ofFn (fun i : Fin N => i)) hGΦ
  have hTG : GoodState ℓ (n0ProjOp volA A T Φ) :=
    goodState_n0Iter hℓ hvol hA hvolA hAc (fun i => decide (i ∈ T))
      (List.ofFn (fun i : Fin N => i)) hGΦ
  have hae1 : (fun x => UBBInputs8.boxPInd volA A j (n0ProjOp volA A S Φ) x
        * n0ProjOp volA A T Φ x)
      =ᵐ[MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ)]
        fun x => n0ProjOp volA A S Φ x * n0ProjOp volA A T Φ x := by
    filter_upwards [self_mem_ae_restrict (abox_measurable N ℓ)] with x hx
    rw [n0IterEigen hℓ hvol hA hvolA hAc S hGΦ j x hx, if_pos hjS]
  have hae2 : (fun x => n0ProjOp volA A S Φ x
        * UBBInputs8.boxPInd volA A j (n0ProjOp volA A T Φ) x)
      =ᵐ[MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ)]
        fun _ => (0 : ℝ) := by
    filter_upwards [self_mem_ae_restrict (abox_measurable N ℓ)] with x hx
    rw [n0IterEigen hℓ hvol hA hvolA hAc T hGΦ j x hx, if_neg hjT, mul_zero]
  obtain ⟨C₁, hC₁⟩ := hSG.2
  obtain ⟨C₂, hC₂⟩ := hTG.2
  calc (∫ x in Submission.BoseGases.abox N ℓ,
          n0ProjOp volA A S Φ x * n0ProjOp volA A T Φ x)
      = ∫ x in Submission.BoseGases.abox N ℓ,
          UBBInputs8.boxPInd volA A j (n0ProjOp volA A S Φ) x
            * n0ProjOp volA A T Φ x := (integral_congr_ae hae1).symm
    _ = ∫ x in Submission.BoseGases.abox N ℓ, n0ProjOp volA A S Φ x
          * UBBInputs8.boxPInd volA A j (n0ProjOp volA A T Φ) x :=
          boxPIndSelfAdjoint hℓ hvol hA hvolA hAc j hSG.1 hC₁ hTG.1 hC₂
    _ = 0 := by
          rw [integral_congr_ae hae2]
          simp

/-- **Orthogonality of the `n₀`-sectors.**  The subset idempotents `n0ProjOp volA A S` of the FS box projections `P_{B,i} = UBBInputs8.boxPInd volA A i` have orthogonal ranges in `L²(abox N ℓ)`: for `S ≠ T` their pairing vanishes.

Ingredients already in the corpus (import them; do not reprove):
* `Work.BoseFixB1S.n0IterEigen` (`Submission.Work.BoseFixB1S.n0IterEigen`) — for `Ψ` measurable and bounded on the box (`GoodState ℓ Ψ`, aka `BoxNice`, from `Submission.Work.BoseFixB1S.boxPInd_boxComp`), for every `j : Fin N` and `x ∈ abox N ℓ`,
  `boxPInd volA A j (n0ProjOp volA A S Ψ) x = if j ∈ S then n0ProjOp volA A S Ψ x else 0`.
* `Work.BoseFixB1S.boxPIndSelfAdjoint` (`Submission.Work.BoseFixB1S.boxPIndSelfAdjoint`) — self-adjointness of one slot projection on the box for measurable, box-bounded states.
* `Work.BoseFixB1S.exists_abox_bound` (`Submission.Work.BoseFixB1S.BoxPotOper`) — `Continuous Ψ` is box-bounded; `goodState_n0Iter` (`Submission.Work.BoseFixB1S.n0SlotDefs`) — the derived states are again in the class.

Proof plan: from `S ≠ T` extract a slot `j` with `j ∈ S` and `j ∉ T` (or symmetrically). If `j ∈ S \ T`, then pointwise on the box `P_j u_S = u_S` and `P_j u_T = 0`, so
`∫ u_S·u_T = ∫ (P_j u_S)·u_T = ∫ u_S·(P_j u_T) = ∫ u_S·0 = 0` (middle step: single-slot self-adjointness). The other case is symmetric. -/
theorem n0SectorOrthB1 {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    {Φ : Submission.BoseGases.X N → ℝ} (hΦc : Continuous Φ)
    {S T : Finset (Fin N)} (hST : S ≠ T) :
    (∫ x in Submission.BoseGases.abox N ℓ,
        Work.BoseFixB1S.n0ProjOp volA A S Φ x
          * Work.BoseFixB1S.n0ProjOp volA A T Φ x) = 0 := by
  have hGΦ : GoodState ℓ Φ := by
    obtain ⟨C, hC⟩ := (abox_compact N hℓ).exists_bound_of_continuousOn hΦc.continuousOn
    exact ⟨hΦc.measurable, C, fun x hx => by simpa [Real.norm_eq_abs] using hC x hx⟩
  by_cases h : ∃ j : Fin N, j ∈ S ∧ j ∉ T
  · obtain ⟨j, hjS, hjT⟩ := h
    exact n0SectorOrthB1_aux hℓ hvol hA hvolA hAc hGΦ S T j hjS hjT
  · push_neg at h
    have hex : ∃ j : Fin N, j ∈ T ∧ j ∉ S := by
      by_contra hc
      push_neg at hc
      exact hST (Finset.Subset.antisymm h hc)
    obtain ⟨j, hjT, hjS⟩ := hex
    have hkey := n0SectorOrthB1_aux hℓ hvol hA hvolA hAc hGΦ T S j hjT hjS
    have hswap : (∫ x in Submission.BoseGases.abox N ℓ,
          n0ProjOp volA A T Φ x * n0ProjOp volA A S Φ x)
        = ∫ x in Submission.BoseGases.abox N ℓ,
          n0ProjOp volA A S Φ x * n0ProjOp volA A T Φ x := by
      apply integral_congr_ae
      filter_upwards with x
      ring
    rw [hswap] at hkey
    exact hkey

end Work.BoseFixB1S
