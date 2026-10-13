/-
  Area G4b: the two small bookkeeping lemmas of the final assembly, detached from
  `Submission/Work/WilG4b/Main.lean` (whose import list mixes `badSet_mem` with
  `nondiff_finite`, two modules that both declare `Work.WilG4b.derivGraph_mem`).

  * `badSet_finite_zero`   : for `n = 0` the bad set is empty;
  * `conclusion_of_finite_badSet` : finiteness of the bad set gives the conclusion of
    `G4_bdd_dx`.
-/
import Submission.Work.WilG4b.Basic

set_option autoImplicit false
set_option maxHeartbeats 4000000

noncomputable section

open Classical MeasureTheory

namespace Work.WilG4b

open WilkiesDesign WilkiesConjecture

/-- For `n = 0` the bad set is empty (the fibre is a single point). -/
theorem badSet_finite_zero {f : (Fin (0 + 1) → ℝ) → ℝ} (s : Finset ℝ) :
    (badSet f s).Finite :=
  Set.Finite.subset Set.finite_empty fun _ hx => by
    have h := badSet_subset_badCore f s hx
    rwa [badCore_zero] at h

/-- The frozen conclusion of `G4_bdd_dx` follows from finiteness of the bad set. -/
theorem conclusion_of_finite_badSet {n : ℕ} (f : (Fin (n + 1) → ℝ) → ℝ) (s : Finset ℝ)
    (hfin : (badSet f s).Finite) :
    ∃ s' : Finset ℝ, ∀ x ∈ Set.Ioo (0 : ℝ) 1, x ∉ s' → ∃ B : ℝ,
      ∀ y ∈ openCube n, Fin.cons x y ∈ interior {z | ContDiffAt ℝ 1 f z} →
        |fderiv ℝ f (Fin.cons x y) (Pi.single 0 1)| ≤ B := by
  obtain ⟨s', hs'⟩ := exists_goodX_of_finite_badSet f s hfin
  refine ⟨s', fun x hx hxs => ?_⟩
  obtain ⟨B, hB⟩ := hs' x hx hxs
  exact ⟨B, fun y hy hcy => hB y hy hcy⟩

end Work.WilG4b
