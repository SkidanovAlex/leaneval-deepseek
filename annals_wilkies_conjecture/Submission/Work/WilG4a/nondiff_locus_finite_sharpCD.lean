import Mathlib
import Submission.Work.Wilkies.Defs
import Submission.Work.WilG4a.derivGraph_mem
import Submission.Work.WilG4a.diffLocus_mem
import Submission.Work.WilG4a.cont_off_finite
import Submission.Work.WilG4a.nondiff_interval_free
import Submission.Work.WilG1.Calc.finite_of_interior_empty
import Submission.Work.WilG4a.oneDim_nonCk_finite

set_option autoImplicit false
noncomputable section
open Classical
namespace Work.WilG4a

open WilkiesDesign

/-!
# `nondiff_locus_finite_sharpCD`

`SharpCD` alone (no `SharpDeriv`) forces the non-differentiability locus of a one-variable
function with `Ω`-definable graph to be finite.

The route is the "one-dimensional sandwich":

1. the differentiability locus is `Ω`-definable (`diffLocus_mem`, which needs only the `ε`-`δ`
   plumbing and the elementary `Ω`-closure axioms of `SOMin`), so the non-differentiability
   locus is `Ω (a₁+1) (b₁.eval D) 1` as well;
2. an `Ω`-set of empty interior in `ℝ¹` is finite (`WilG1.Calc.finite_of_interior_empty`,
   from `SOMin.comps`) — so it suffices to show the non-differentiability locus has empty
   interior;
3. an interval of non-differentiability would (by `cont_off_finite`, the `SharpCD`-only
   finiteness of the discontinuity locus) contain a sub-interval of continuity, contradicting
   `nondiff_interval_free`.

Nothing here uses `SharpDeriv`; indeed the theorem `nondiff_locus_finite` of
`Submission/Work/WilG4a/oneDim_nonCk_finite.lean` takes `hder` as an argument but never
consumes it.  This file records that fact.
-/

theorem nondiff_locus_finite_sharpCD (S : WilkiesDesign.SOMin) (hcd : S.SharpCD) {F D : ℕ}
    (g : ℝ → ℝ) (hg : WilkiesDesign.graphOf (fun x : Fin 1 → ℝ => g (x 0)) ∈ S.Ω F D 2) :
    {x : ℝ | ¬ DifferentiableAt ℝ g x}.Finite := by
  classical
  obtain ⟨a₁, b₁, hD⟩ := diffLocus_mem S F
  have hDloc : Work.WilG1.liftR {x : ℝ | DifferentiableAt ℝ g x} ∈ S.Ω a₁ (b₁.eval D) 1 :=
    (hD D g hg).1
  have hNmem : Work.WilG1.liftR {x : ℝ | ¬ DifferentiableAt ℝ g x}
      ∈ S.Ω (a₁ + 1) (b₁.eval D) 1 := by
    have h := S.compl hDloc
    rw [liftR_compl'] at h
    exact h
  have hno : interior (Work.WilG1.liftR {x : ℝ | ¬ DifferentiableAt ℝ g x}) = ∅ := by
    rw [Set.eq_empty_iff_forall_notMem]
    intro z hz
    rw [mem_interior_liftR_iff] at hz
    obtain ⟨c, d, hcd', hsub⟩ := exists_Ioo_subset_of_mem_interior hz
    have hcont_fin : {x : ℝ | ¬ ContinuousAt g x}.Finite := cont_off_finite S hcd g hg
    have hex : ∃ x₀ : ℝ, x₀ ∈ Set.Ioo c d ∧ ContinuousAt g x₀ := by
      by_contra hcon
      push_neg at hcon
      have hsub' : Set.Ioo c d ⊆ {x : ℝ | ¬ ContinuousAt g x} := fun x hx => hcon x hx
      exact (Set.Ioo_infinite hcd') (hcont_fin.subset hsub')
    obtain ⟨x₀, hx₀Ioo, hx₀cont⟩ := hex
    have hx₀c : x₀ ∈ Set.Ioo c d := hx₀Ioo
    obtain ⟨η, hη, hηsub⟩ :=
      exists_Ioo_disjoint_finite hcont_fin (by simpa only [Set.mem_ofPred_eq, not_not] using hx₀cont)
    have hmaxlt : max c (x₀ - η) < min d (x₀ + η) := by
      have hmax : max c (x₀ - η) < x₀ := max_lt hx₀c.1 (by linarith [hη])
      have hmin : x₀ ≤ min d (x₀ + η) := le_min hx₀c.2.le (by linarith [hη])
      exact lt_of_lt_of_le hmax hmin
    refine @nondiff_interval_free S F D g hg (max c (x₀ - η)) (min d (x₀ + η)) hmaxlt
      (fun t ht => ?_) (fun t ht => ?_)
    · by_contra htc
      have hS : t ∈ {x : ℝ | ¬ ContinuousAt g x} := by
        simpa only [Set.mem_ofPred_eq] using htc
      have hI : t ∈ Set.Ioo (x₀ - η) (x₀ + η) :=
        ⟨lt_of_le_of_lt (le_max_right _ _) ht.1, lt_of_lt_of_le ht.2 (min_le_right _ _)⟩
      exact absurd (show t ∈ Set.Ioo (x₀ - η) (x₀ + η) ∩ {x : ℝ | ¬ ContinuousAt g x}
        from ⟨hI, hS⟩) (by rw [hηsub]; exact Set.notMem_empty t)
    · exact hsub ⟨lt_of_le_of_lt (le_max_left _ _) ht.1, lt_of_lt_of_le ht.2 (min_le_left _ _)⟩
  have hfinl : (Work.WilG1.liftR {x : ℝ | ¬ DifferentiableAt ℝ g x}).Finite :=
    Work.WilG1.Calc.finite_of_interior_empty hNmem hno
  exact (finite_liftR_iff _).mp hfinl

end Work.WilG4a
