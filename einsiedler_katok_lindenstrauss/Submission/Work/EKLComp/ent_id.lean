import Mathlib
import Submission.Work.EKLComp.Entropy

/-!
# The Kolmogorov–Sinai entropy of the identity map is zero

`ent μ id = 0` for every probability measure `μ` on a measurable space `X`.

The proof is the textbook computation.  For `T = id` the `N`-fold join
`joinSets id P N w = ⋂_{k<N} P_{w k}` collapses: every term of the intersection is the same
atom of `P`, so the join of `(N+1)` copies of `P` carries exactly the same information as `P`
itself, i.e. `Hfam μ (joinSets id P (N+1)) = Hfam μ (joinSets id P 1)` for every `N`
(this is where both directions of `Hfam_mono` are used).  Hence

`hPart μ id P = ⨅ N, Hfam μ (joinSets id P (N+1)) / (N+1) = ⨅ N, S / (N+1)`

for the fixed nonnegative number `S = Hfam μ (joinSets id P 1)`, and this infimum is `0`
because `S / (N+1) → 0`.  Taking the supremum over all finite partitions gives `ent μ id = 0`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal BigOperators

noncomputable section

namespace Work.EKLComp

open Work.EKLContract
open Work.EKLComp.Core

variable {X : Type} [mX : MeasurableSpace X]

/-! ## Atom computations for `joinSets` along the identity -/

/-- For `T = id` the join `⋁_{k<N} T^{-k} P` is the plain intersection of the selected atoms. -/
theorem joinSets_id (P : FinPart X) (N : ℕ) (w : Fin N → Fin P.n) :
    joinSets (id : X → X) P N w = ⋂ k : Fin N, P.parts (w k) := by
  simp [joinSets]

/-- The join `⋁_{k<M} (id)^{-k} P` of a constant word (`M ≥ 1`) is the corresponding atom. -/
theorem joinSets_id_const (P : FinPart X) {M : ℕ} (hM : M ≠ 0) (i : Fin P.n) :
    joinSets (id : X → X) P M (fun _ => i) = P.parts i := by
  have h : joinSets (id : X → X) P M (fun _ : Fin M => i)
      = Set.iInter (fun _ : Fin M => P.parts i) := by
    simp [joinSets]
  rw [h]
  exact Set.Subset.antisymm (Set.iInter_subset _ ⟨0, Nat.pos_of_ne_zero hM⟩)
    (Set.subset_iInter fun _ => Set.Subset.refl _)

/-- Joining `N+1` copies of `P` along the identity adds no information over `P` itself. -/
theorem Hfam_joinSets_id (μ : Measure X) [IsProbabilityMeasure μ] (P : FinPart X) (N : ℕ) :
    Hfam μ (joinSets (id : X → X) P (N + 1)) = Hfam μ (joinSets (id : X → X) P 1) := by
  have hN : IsMPart (joinSets (id : X → X) P (N + 1)) :=
    joinSets_isMPart measurable_id P (N + 1)
  have h1 : IsMPart (joinSets (id : X → X) P 1) :=
    joinSets_isMPart measurable_id P 1
  refine le_antisymm ?_ ?_
  · -- `P ∨ … ∨ P` refines `P`; the constant words show the reverse inclusion of atoms.
    refine Hfam_mono μ hN h1 (fun v : Fin 1 → Fin P.n => (fun _ : Fin (N+1) => v 0)) ?_
    intro v
    rw [joinSets_one, joinSets_id_const P (Nat.succ_ne_zero N)]
  · refine Hfam_mono μ h1 hN (fun w : Fin (N+1) → Fin P.n => (fun _ : Fin 1 => w 0)) ?_
    intro w
    rw [joinSets_one, joinSets_id]
    exact Set.iInter_subset _ 0

/-- The partition entropy of the identity map vanishes. -/
theorem hPart_id (μ : Measure X) [IsProbabilityMeasure μ] (P : FinPart X) :
    hPart μ (id : X → X) P = 0 := by
  have hSnn : 0 ≤ Hfam μ (joinSets (id : X → X) P 1) := Hfam_nonneg μ _
  have hfun : (fun N : ℕ => Hfam μ (joinSets (id : X → X) P (N + 1)) / ((N : ℝ) + 1))
      = fun N : ℕ => Hfam μ (joinSets (id : X → X) P 1) / ((N : ℝ) + 1) := by
    funext N
    rw [Hfam_joinSets_id μ P N]
  show (⨅ N : ℕ, Hfam μ (joinSets (id : X → X) P (N + 1)) / ((N : ℝ) + 1)) = 0
  rw [hfun]
  refine ciInf_eq_of_forall_ge_of_forall_gt_exists_lt (fun N => ?_) (fun w hw => ?_)
  · exact div_nonneg hSnn (by positivity)
  · obtain ⟨N, hN⟩ := exists_nat_gt (Hfam μ (joinSets (id : X → X) P 1) / w)
    refine ⟨N, ?_⟩
    have h1 : Hfam μ (joinSets (id : X → X) P 1) < (N : ℝ) * w := (div_lt_iff₀ hw).mp hN
    rw [div_lt_iff₀ (by positivity : (0 : ℝ) < (N : ℝ) + 1)]
    nlinarith [hSnn, hw.le]

/-! ## The main statement -/

theorem ent_id {X : Type} [mX : MeasurableSpace X] (μ : MeasureTheory.Measure X)
    [MeasureTheory.IsProbabilityMeasure μ] :
    Work.EKLContract.ent μ (id : X → X) = 0 := by
  have h : ∀ P : FinPart X, ENNReal.ofReal (hPart μ (id : X → X) P) = 0 := by
    intro P
    rw [hPart_id μ P, ENNReal.ofReal_zero]
  rw [Work.EKLContract.ent]
  simp only [h]
  exact le_antisymm (iSup_le fun _ => le_refl 0) bot_le

end Work.EKLComp
