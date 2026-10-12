import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1S.boxPIndSelfAdjoint
import Submission.Work.BoseFixB1S.n0IterEigen
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1S.n0ProjOp_pairing_zero` — orthogonality of the `n₀` subset idempotents

The FS box projections `P_i = UBBInputs8.boxPInd volA A i` (`i : Fin N`) are commuting
self-adjoint projections on `L²(abox N ℓ)` (`boxPIndSelfAdjoint`, `boxPInd_boxPInd_comm_good`),
and the subset idempotents

  `n0ProjOp volA A S = ∏_{i∈S} P_i · ∏_{i∉S} (1 − P_i)`   (composition, in slot order)

satisfy `P_i (n0ProjOp volA A S Ψ) = if i ∈ S then n0ProjOp volA A S Ψ else 0` on the box
(`n0IterEigen`).  Hence for `S ≠ T` the idempotents have **orthogonal ranges**: the pairing

  `∫_{abox N ℓ} (n0ProjOp volA A S Ψ) · (n0ProjOp volA A T Ψ)`

vanishes.  This is the orthogonality of the `n₀` spectral decomposition (the subsets `S` are the
joint eigenvalue labels of the `P_i`), consumed by the `√`-functional calculus of the sharp
completion of squares (FS `lm:appinteractionestimate`, see `FINDING_perBoxFWeightB1.md` §7.7).

## Proof

Pick a slot `i` in which `S` and `T` differ, say `i ∈ S`, `i ∉ T` (the other case is symmetric).
Writing `Φ := n0ProjOp volA A S Ψ`, `Θ := n0ProjOp volA A T Ψ`:

* `P_iΦ = Φ` and `P_iΘ = 0` pointwise on the box (`n0IterEigen`);
* `P_i` is self-adjoint on the box (`boxPIndSelfAdjoint`),

so `∫ Φ Θ = ∫ (P_iΦ) Θ = ∫ Φ (P_iΘ) = 0`.  Measurability and box-boundedness of `Φ`, `Θ`
(which is what self-adjointness and the eigen-identity need) come from `Continuous Ψ` through
`BoxNice.of_continuous` and closure of that class under the slot iteration (`BoxNice.iter`).

The body below is complete; every ingredient is a theorem already present in the corpus.
-/

namespace Work.BoseFixB1S

open MeasureTheory
open scoped BigOperators ENNReal

open Submission.BoseGases

theorem n0ProjOp_pairing_zero {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    {Ψ : Submission.BoseGases.X N → ℝ} (hΨc : Continuous Ψ)
    {S T : Finset (Fin N)} (hST : S ≠ T) :
    (∫ x in Submission.BoseGases.abox N ℓ,
        Work.BoseFixB1S.n0ProjOp volA A S Ψ x * Work.BoseFixB1S.n0ProjOp volA A T Ψ x) = 0 := by
  have hg : GoodState ℓ Ψ := BoxNice.of_continuous hℓ hΨc
  have hSnice : GoodState ℓ (n0ProjOp volA A S Ψ) := by
    have h := BoxNice.iter hℓ hvol hA hvolA hAc (fun i => decide (i ∈ S)) hg
      (List.ofFn (fun i : Fin N => i))
    simpa only [n0ProjOp, GoodState, BoxNice] using h
  have hTnice : GoodState ℓ (n0ProjOp volA A T Ψ) := by
    have h := BoxNice.iter hℓ hvol hA hvolA hAc (fun i => decide (i ∈ T)) hg
      (List.ofFn (fun i : Fin N => i))
    simpa only [n0ProjOp, GoodState, BoxNice] using h
  obtain ⟨hΦm, CΦ, hΦb⟩ := hSnice
  obtain ⟨hΘm, CΘ, hΘb⟩ := hTnice
  -- a slot in which the two subsets differ
  have hex : ∃ i : Fin N, (i ∈ S ∧ i ∉ T) ∨ (i ∈ T ∧ i ∉ S) := by
    by_cases h : S ⊆ T
    · have h2 : ¬ T ⊆ S := fun hts => hST (Finset.Subset.antisymm h hts)
      obtain ⟨i, hiT, hiS⟩ := Finset.not_subset.mp h2
      exact ⟨i, Or.inr ⟨hiT, hiS⟩⟩
    · obtain ⟨i, hiS, hiT⟩ := Finset.not_subset.mp h
      exact ⟨i, Or.inl ⟨hiS, hiT⟩⟩
  obtain ⟨i, hi | hi⟩ := hex
  · -- `i ∈ S`, `i ∉ T`: `P_iΦ = Φ` and `P_iΘ = 0`
    obtain ⟨hiS, hiT⟩ := hi
    have hSA := boxPIndSelfAdjoint hℓ hvol hA hvolA hAc i hΦm hΦb hΘm hΘb
    have hL : (∫ x in abox N ℓ,
        UBBInputs8.boxPInd volA A i (n0ProjOp volA A S Ψ) x * n0ProjOp volA A T Ψ x)
        = ∫ x in abox N ℓ, n0ProjOp volA A S Ψ x * n0ProjOp volA A T Ψ x := by
      apply integral_congr_ae
      filter_upwards [self_mem_ae_restrict (abox_measurable N ℓ)] with x hx
      rw [n0IterEigen hℓ hvol hA hvolA hAc S hg i x hx, if_pos hiS]
    have hR : (∫ x in abox N ℓ,
        n0ProjOp volA A S Ψ x * UBBInputs8.boxPInd volA A i (n0ProjOp volA A T Ψ) x) = 0 := by
      rw [show (∫ x in abox N ℓ,
          n0ProjOp volA A S Ψ x * UBBInputs8.boxPInd volA A i (n0ProjOp volA A T Ψ) x)
          = ∫ x in abox N ℓ, (0 : ℝ) from by
        apply integral_congr_ae
        filter_upwards [self_mem_ae_restrict (abox_measurable N ℓ)] with x hx
        rw [n0IterEigen hℓ hvol hA hvolA hAc T hg i x hx, if_neg hiT, mul_zero]]
      simp
    rw [← hL, hSA, hR]
  · -- `i ∈ T`, `i ∉ S`: the mirror image
    obtain ⟨hiT, hiS⟩ := hi
    have hSA := boxPIndSelfAdjoint hℓ hvol hA hvolA hAc i hΘm hΘb hΦm hΦb
    have hL : (∫ x in abox N ℓ,
        UBBInputs8.boxPInd volA A i (n0ProjOp volA A T Ψ) x * n0ProjOp volA A S Ψ x)
        = ∫ x in abox N ℓ, n0ProjOp volA A T Ψ x * n0ProjOp volA A S Ψ x := by
      apply integral_congr_ae
      filter_upwards [self_mem_ae_restrict (abox_measurable N ℓ)] with x hx
      rw [n0IterEigen hℓ hvol hA hvolA hAc T hg i x hx, if_pos hiT]
    have hR : (∫ x in abox N ℓ,
        n0ProjOp volA A T Ψ x * UBBInputs8.boxPInd volA A i (n0ProjOp volA A S Ψ) x) = 0 := by
      rw [show (∫ x in abox N ℓ,
          n0ProjOp volA A T Ψ x * UBBInputs8.boxPInd volA A i (n0ProjOp volA A S Ψ) x)
          = ∫ x in abox N ℓ, (0 : ℝ) from by
        apply integral_congr_ae
        filter_upwards [self_mem_ae_restrict (abox_measurable N ℓ)] with x hx
        rw [n0IterEigen hℓ hvol hA hvolA hAc S hg i x hx, if_neg hiS, mul_zero]]
      simp
    rw [show (∫ x in abox N ℓ, n0ProjOp volA A S Ψ x * n0ProjOp volA A T Ψ x)
        = ∫ x in abox N ℓ, n0ProjOp volA A T Ψ x * n0ProjOp volA A S Ψ x from by
      apply integral_congr_ae
      filter_upwards with x
      exact mul_comm _ _]
    rw [← hL, hSA, hR]

end Work.BoseFixB1S
