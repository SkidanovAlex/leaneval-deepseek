import Mathlib
import Submission.Work.WilG4c.AlSliceBase
import Submission.Work.WilG1.Cell.smooth_k_cover

set_option autoImplicit false
noncomputable section
open Classical
open scoped Topology

namespace Work.WilG4c

open WilkiesDesign WilkiesDesign.CG

/-!
## `JBadThin`

`Work.WilkG4c.jBad p n f k` is the complement of the *interior of the joint `C^k`-locus* of
`famFunHat f` in `ℝ^{p + (n+1)}` (see `AlSliceBase`).  Since at every finite order the `C^k`-locus
of a function is already open, that complement is exactly the non-`C^k` locus, and the theorem
says that it has empty interior: the `C^k`-locus is dense.

That is the "generic smoothness" fact for sharply o-minimal structures, and it is exactly what
`Work.WilG1.Cell.smooth_k_cover` (BNZ §2.2, used with only `S.SharpCD`) provides: the non-`C^k`
locus of a definable function is covered by finitely many `Ω`-definable sets of empty interior.
Passing to closures with `Work.WilG1.Cell.thin_closure` turns each of them into a nowhere dense
set, and a finite union of nowhere dense sets is nowhere dense, so the closure of the non-`C^k`
locus has empty interior; a fortiori the non-`C^k` locus does.
-/

/-- At a finite order the joint `C^k`-locus of a function is open. -/
theorem jBad_isOpen_contDiffAt_locus {N : ℕ} (m : ℕ) (g : (Fin N → ℝ) → ℝ) :
    IsOpen {z : Fin N → ℝ | ContDiffAt ℝ m g z} := by
  rw [isOpen_iff_mem_nhds]
  intro z hz
  have hz' : ContDiffAt ℝ m g z := by simpa using hz
  exact Filter.mem_of_superset (hz'.eventually (by simp)) (fun y hy => hy)

/-- The closure of the non-`C^k` locus of a definable function has empty interior. -/
theorem jBad_interior_closure_nonCk_empty (S : WilkiesDesign.SOMin) (hcd : S.SharpCD)
    {N F D k : ℕ} (g : (Fin N → ℝ) → ℝ) (hg : WilkiesDesign.graphOf g ∈ S.Ω F D (N + 1)) :
    interior (closure {z : Fin N → ℝ | ¬ ContDiffAt ℝ k g z}) = ∅ := by
  obtain ⟨m, a, b, A, hA, hint, hsub⟩ :=
    Work.WilG1.Cell.smooth_k_cover (S := S) (hcd := hcd) (n := N) (F := F) (D := D)
      (k := k) (f := g) (hf := hg)
  -- each piece has nowhere dense closure
  have hnw : ∀ i : Fin m, IsNowhereDense (A i) := fun i =>
    Work.WilG1.Cell.thin_closure (S := S) hcd (hA i) (hint i)
  have hnwU : IsNowhereDense (⋃ i : Fin m, A i) := IsNowhereDense.iUnion hnw
  exact Set.eq_empty_of_subset_empty
    (le_trans (interior_mono (closure_mono hsub)) (le_of_eq hnwU))

theorem JBadThin (S : WilkiesDesign.SOMin) (hcd : S.SharpCD) (p n F0 : ℕ) :
    ∀ (D k : ℕ) (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ),
      WilkiesDesign.CG.famGraph f ∈ S.Ω F0 D (p + (n + 1) + 1) →
      interior (Work.WilkG4c.jBad p n f k) = ∅ := by
  intro D k f hf
  -- the graph of `famFunHat f` is `famGraph f`, so it is `Ω`-definable
  have hg : WilkiesDesign.graphOf (Work.WilkG4c.famFunHat f) ∈
      S.Ω F0 D (p + (n + 1) + 1) := by
    rwa [← Work.WilkG4c.famGraph_eq_graphOf_famFunHat]
  have hthin := jBad_interior_closure_nonCk_empty (S := S) (hcd := hcd) (N := p + (n + 1))
    (F := F0) (D := D) (k := k) (g := Work.WilkG4c.famFunHat f) (hg := hg)
  -- at the finite order `k` the locus is open, so `jBad` is the non-`C^k` locus
  have hjbad : Work.WilkG4c.jBad p n f k
      = {z : Fin (p + (n + 1)) → ℝ | ¬ ContDiffAt ℝ k (Work.WilkG4c.famFunHat f) z} := by
    have hjloc : Work.WilkG4c.jLoc p n f k
        = {z : Fin (p + (n + 1)) → ℝ | ContDiffAt ℝ k (Work.WilkG4c.famFunHat f) z} :=
      (jBad_isOpen_contDiffAt_locus k (Work.WilkG4c.famFunHat f)).interior_eq
    unfold Work.WilkG4c.jBad
    rw [hjloc]
    rfl
  rw [hjbad]
  exact Set.eq_empty_of_subset_empty
    (le_trans (interior_mono subset_closure) (le_of_eq hthin))

end Work.WilG4c
