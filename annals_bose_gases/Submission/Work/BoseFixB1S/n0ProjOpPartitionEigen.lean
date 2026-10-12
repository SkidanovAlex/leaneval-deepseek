import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixB1S.n0IterEigen
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseFixB1S.n0ProjOpPartitionEigen`

The `n₀` spectral layer: the subset idempotents `n0ProjOp volA A S` of the box projections
`P_{B,i} = UBBInputs8.boxPInd volA A i` (FS `eq:HBU`)

* sum to the identity (`n0ProjOp_sum_eq`, the expansion of `∏ᵢ(Pᵢ + (1 − Pᵢ))`), and
* are eigenfunctions of `n₀ = ΣᵢPᵢ` (`n0Op`) with eigenvalue `S.card` (`n0IterEigen`).

The two halves are the obligations `(Q1-b)(i)` of `FINDING_perBoxFWeightB1.md` §7.7.
-/

namespace Work.BoseFixB1S

open MeasureTheory
open scoped BigOperators ENNReal

open Submission.BoseGases

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- **Partition of unity**: the subset idempotents sum to the identity.  (Pointwise identity of
functions, valid for every `Ψ` — pure composition algebra.) -/
theorem n0ProjOp_sum_eq {N : ℕ} (volA : ℝ) (A : Set E3) (Ψ : X N → ℝ) :
    (∑ S : Finset (Fin N), n0ProjOp volA A S Ψ) = Ψ := by
  have hl : (List.ofFn (fun i : Fin N => i)).Nodup :=
    List.nodup_ofFn.mpr (fun _ _ hij => hij)
  have h := n0IterPowersetSum volA A (List.ofFn (fun i : Fin N => i)) hl Ψ
  have htf : (List.ofFn (fun i : Fin N => i)).toFinset = (Finset.univ : Finset (Fin N)) := by
    ext i
    simp [List.mem_toFinset]
  rw [htf, Finset.powerset_univ] at h
  simpa [n0ProjOp] using h

theorem n0ProjOpPartitionEigen {N : ℕ} {ℓ volA : ℝ} (hℓ : 0 < ℓ) (hvol : 0 < volA)
    {A : Set (EuclideanSpace ℝ (Fin 3))} (hA : MeasurableSet A)
    (hvolA : volA = (MeasureTheory.volume A).toReal) (hAc : A ⊆ Submission.BoseGases.acube ℓ)
    {Ψ : Submission.BoseGases.X N → ℝ} (hΨc : Continuous Ψ) :
    (∀ᵐ x ∂(MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ)),
        (∑ S : Finset (Fin N), (Work.BoseFixB1S.n0ProjOp volA A S) Ψ x) = Ψ x)
      ∧ ∀ S : Finset (Fin N),
          (fun x => Work.BoseFixB1S.n0Op volA A ((Work.BoseFixB1S.n0ProjOp volA A S) Ψ) x)
            =ᵐ[MeasureTheory.volume.restrict (Submission.BoseGases.abox N ℓ)]
              fun x => (S.card : ℝ) * ((Work.BoseFixB1S.n0ProjOp volA A S) Ψ x) := by
  obtain ⟨C, _hC0, hCb⟩ := exists_abox_bound hℓ hΨc
  have hg : GoodState ℓ Ψ := ⟨hΨc.measurable, C, hCb⟩
  have heig : ∀ (S : Finset (Fin N)) (j : Fin N) (x : X N), x ∈ abox N ℓ →
      UBBInputs8.boxPInd volA A j (n0ProjOp volA A S Ψ) x
        = (if j ∈ S then n0ProjOp volA A S Ψ x else 0) :=
    fun S j x hx => n0IterEigen hℓ hvol hA hvolA hAc S hg j x hx
  constructor
  · filter_upwards with x
    simpa only [Finset.sum_apply] using congrFun (n0ProjOp_sum_eq volA A Ψ) x
  · intro S
    filter_upwards [self_mem_ae_restrict (abox_measurable N ℓ)] with x hx
    have hstep : (∑ j : Fin N, UBBInputs8.boxPInd volA A j (n0ProjOp volA A S Ψ) x)
        = ∑ j : Fin N, (if j ∈ S then n0ProjOp volA A S Ψ x else 0) :=
      Finset.sum_congr rfl (fun j _ => heig S j x hx)
    show (∑ j : Fin N, UBBInputs8.boxPInd volA A j (n0ProjOp volA A S Ψ) x)
      = (S.card : ℝ) * (n0ProjOp volA A S Ψ x)
    rw [hstep, Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, nsmul_eq_mul]

end Work.BoseFixB1S
