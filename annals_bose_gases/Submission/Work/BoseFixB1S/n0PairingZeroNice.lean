import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1S.n0ProjOp_pairing_zero
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1S.n0PairingZeroNice`

Orthogonality of the `n₀` subset idempotents `n0ProjOp volA A S` for **merely measurable,
box-bounded** states.

The companion lemma `Work.BoseFixB1S.n0ProjOp_pairing_zero` proves

  `∫_{abox N ℓ} (n0ProjOp volA A S Ψ) · (n0ProjOp volA A T Ψ) = 0`   (`S ≠ T`)

under the hypothesis `Continuous Ψ`.  Its proof, however, only ever consumes the *state class*
`GoodState ℓ Ψ := Measurable Ψ ∧ ∃ C, ∀ x ∈ abox N ℓ, |Ψ x| ≤ C` (measurable and bounded on the
analysis box): that is what supplies the `IntegrableOn` side conditions of the slot identities
used by `n0IterEigen` and by the self-adjointness `boxPIndSelfAdjoint`, and it is the class
preserved by the slot iteration `n0Iter` (`BoxNice.iter`, `BoxNice` being the same class).

So continuity is never used where it matters, and the statement holds verbatim under the weaker
(and more useful) hypothesis pair `hΨm : Measurable Ψ`, `hΨb : ∀ x ∈ abox N ℓ, |Ψ x| ≤ CΨ`,
which literally *is* `GoodState ℓ Ψ`.  The body below is the proof of `n0ProjOp_pairing_zero`
with that single substitution: the continuity-to-`GoodState` step becomes the direct
construction `⟨hΨm, CΨ, hΨb⟩`.

## Proof sketch

Pick a slot `i` in which `S` and `T` differ, say `i ∈ S`, `i ∉ T` (the other case is symmetric).
With `Φ := n0ProjOp volA A S Ψ`, `Θ := n0ProjOp volA A T Ψ`:

* `P_iΦ = Φ` and `P_iΘ = 0` pointwise on the box (`n0IterEigen`);
* `P_i` is self-adjoint on the box (`boxPIndSelfAdjoint`),

so `∫ Φ Θ = ∫ (P_iΦ) Θ = ∫ Φ (P_iΘ) = 0`.  Measurability and box-boundedness of `Φ`, `Θ` follow
from the closure of the state class under the slot iteration.
-/

namespace Work.BoseFixB1S

open MeasureTheory
open scoped BigOperators ENNReal

open Submission.BoseGases

theorem n0PairingZeroNice {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal)
    (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    {Ψ : Submission.BoseGases.X N → ℝ} (hΨm : Measurable Ψ) {CΨ : ℝ}
    (hΨb : ∀ x ∈ Submission.BoseGases.abox N ℓ, |Ψ x| ≤ CΨ)
    {S T : Finset (Fin N)} (hST : S ≠ T) :
    (∫ x in Submission.BoseGases.abox N ℓ,
        Work.BoseFixB1S.n0ProjOp volA A S Ψ x * Work.BoseFixB1S.n0ProjOp volA A T Ψ x) = 0 := by
  have hg : GoodState ℓ Ψ := ⟨hΨm, CΨ, hΨb⟩
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
