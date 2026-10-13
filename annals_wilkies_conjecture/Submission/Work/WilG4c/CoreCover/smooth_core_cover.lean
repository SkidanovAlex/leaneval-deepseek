import Mathlib
import Submission.Work.WilG4c.FibreCoreDefs
import Submission.Work.WilG1.Cell.smooth_k_cover

namespace Work.WilG4c.CoreCover

open Work.WilG1.Cell
open WilkiesDesign

/-- `smooth_core_cover`: the non-`C¹` locus of a member `h` of an `Ω`-set of the sharply
o-minimal structure `S` is covered by the closures of the four families of *fibre cores* of `h`:
the fibre-bad sets of `h` itself, the fibre-bad sets of the one-step junk partials of `h`, the
discontinuity loci of those junk partials, and the discontinuity locus of `h` itself.

This is the `k = 1` case of the junk criterion `contDiffOn_of_avoids`: off the union the function
is `C¹`; if it were not `C¹` at a point off the union then, on the open complement, one of the
four pieces fails. -/
theorem smooth_core_cover (S : WilkiesDesign.SOMin) (n : ℕ) :
    ∀ (F D : ℕ) (h : (Fin n → ℝ) → ℝ),
      WilkiesDesign.graphOf h ∈ S.Ω F D (n + 1) →
      {x : Fin n → ℝ | ¬ ContDiffAt ℝ 1 h x}
        ⊆ ⋃ a : Work.WilG4c.CoreIx n, closure (Work.WilG4c.fibCore h a) := by
  intro F D h hh
  -- the union of the four families of closures
  set Z : Set (Fin n → ℝ) := ⋃ a : Work.WilG4c.CoreIx n, closure (Work.WilG4c.fibCore h a)
    with hZ
  have hZcl : IsClosed Z := isClosed_iUnion_of_finite fun a => isClosed_closure
  -- every piece of the `k = 1` criterion sits inside `Z`
  have hmem : ∀ w : List (Fin n), w.length ≤ 1 →
      (∀ i : Fin n, fibBad (junkIt h w) i ⊆ Z) ∧ disc (junkIt h w) ⊆ Z := by
    intro w hw
    rcases w with _ | ⟨a, w⟩
    · -- the empty word: the pieces are the fibre-bad sets and the discontinuity locus of `h`
      refine ⟨fun i => ?_, ?_⟩
      · intro z hz
        exact Set.subset_iUnion (fun a : Work.WilG4c.CoreIx n =>
          closure (Work.WilG4c.fibCore h a)) (Work.WilG4c.CoreIx.fbad i)
          (subset_closure (by simpa [Work.WilG4c.fibCore] using hz))
      · intro z hz
        exact Set.subset_iUnion (fun a : Work.WilG4c.CoreIx n =>
          closure (Work.WilG4c.fibCore h a)) (Work.WilG4c.CoreIx.disc0)
          (subset_closure (by simpa [Work.WilG4c.fibCore] using hz))
    · rcases w with _ | ⟨b, t⟩
      · -- the one-letter word: the pieces are those of the junk partial `junkP h a`
        refine ⟨fun i => ?_, ?_⟩
        · intro z hz
          exact Set.subset_iUnion (fun a : Work.WilG4c.CoreIx n =>
            closure (Work.WilG4c.fibCore h a)) (Work.WilG4c.CoreIx.fbadJ a i)
            (subset_closure (by simpa [Work.WilG4c.fibCore, junkIt] using hz))
        · intro z hz
          exact Set.subset_iUnion (fun a : Work.WilG4c.CoreIx n =>
            closure (Work.WilG4c.fibCore h a)) (Work.WilG4c.CoreIx.discJ a)
            (subset_closure (by simpa [Work.WilG4c.fibCore, junkIt] using hz))
      · -- longer words do not occur
        exfalso
        simp at hw
  -- the junk criterion, with `k = 1`, applies off the union
  have hcrit : ContDiffOn ℝ (1 : ℕ) h Zᶜ := by
    refine contDiffOn_of_avoids h hh hZcl.isOpen_compl ?_ ?_
    · intro w hw i
      rw [Set.eq_empty_iff_forall_notMem]
      rintro z ⟨hz, hzb⟩
      exact hz ((hmem w hw).1 i hzb)
    · intro w hw
      refine hZcl.isOpen_compl.continuousOn_iff.mpr fun y hy => ?_
      by_contra hcon
      exact hy ((hmem w hw).2 hcon)
  intro x hx
  by_contra hxb
  exact hx (hcrit.contDiffAt (hZcl.isOpen_compl.mem_nhds hxb))

end Work.WilG4c.CoreCover
