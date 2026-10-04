import Mathlib
import Submission.Work.Diff.EXT.evolX.lapCommAuxDefs
import Submission.Work.Diff.EXT.jetSmoothDefs
import Submission.Work.Diff.EXT.evolX.ladderAtoms
import Submission.Work.Diff.EXT.evolX.swapDiffDefs
import Submission.Work.Diff.EXT.evolX.ladderSumW

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.EXT.evolX

theorem ckt_adjacent_swap_boundW
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M) (d p : ℕ) (hp : p + 2 ≤ d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (g : Submission.Diff.SMet I M) (x : M)
      (G : Fin (d + 4) → Work.Diff.EXT.TField (I := I) (M := M)),
      (∀ i, Work.Diff.GE.SmoothFieldT (I := I) (M := M) (G i)) →
      |Work.Diff.EXT.ckt g d G x
          - Work.Diff.EXT.ckt g d (Work.Diff.EXT.evolX.tupSwap (I := I) (M := M) d p hp G) x|
        ≤ C * Work.Diff.EXT.Shape g x (d - 2)
            * ∏ r : Fin (d + 4), Work.Diff.EXT.gNrm g x (G r x) := by
  refine ⟨((((d - 2 - p : ℕ) : ℝ)) + 4) * 2 ^ p * (Module.finrank ℝ E : ℝ), by positivity, ?_⟩
  intro g x G hG
  obtain ⟨W, hW, hON, -, -⟩ := Work.Diff.GE.kato_geodesic_frame (I := I) (M := M) g x
  have hswap := ckt_sub_tupSwap_eq (I := I) (M := M) hLC g x d p hp G hG
  rw [hswap, abs_neg]
  have hb := ladder_bound_w (I := I) (M := M) hLC g x (d - 2 - p) p W hW hON
    (fun r : Fin (((d - 2 - p) + 2 + p) + 4) => G (Fin.cast (by omega) r))
    (fun r => hG _)
  have hprod : (∏ r : Fin (((d - 2 - p) + 2 + p) + 4),
        Work.Diff.EXT.gNrm g x (G (Fin.cast (by omega : ((d - 2 - p) + 2 + p) + 4 = d + 4) r) x))
      = ∏ r : Fin (d + 4), Work.Diff.EXT.gNrm g x (G r x) :=
    Function.Bijective.prod_comp
      (e := Fin.cast (by omega : ((d - 2 - p) + 2 + p) + 4 = d + 4))
      ⟨Fin.cast_injective _, fun b => ⟨⟨b.val, by omega⟩, Fin.ext rfl⟩⟩
      (fun r : Fin (d + 4) => Work.Diff.EXT.gNrm g x (G r x))
  refine le_trans hb ?_
  rw [show (d - 2 - p) + p = d - 2 from by omega]
  exact le_of_eq (congrArg (fun s : ℝ =>
    ((↑(d - 2 - p) + 4) * 2 ^ p * ↑(Module.finrank ℝ E))
      * Work.Diff.EXT.Shape g x (d - 2) * s) hprod)

end Work.Diff.EXT.evolX
