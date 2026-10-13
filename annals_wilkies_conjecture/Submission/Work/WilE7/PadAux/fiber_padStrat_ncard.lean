import Mathlib
import Submission.Work.WilE7.PadDefs

namespace Work.WilE7.PadAux

open WilkiesDesign.E Work.WilE7

/-- Every point of `Fin (d + q) → ℝ` is the `Fin.append` of its `projFirst` part and its
`projSnd` part (restated for the `projFirst`/`projSnd` vocabulary). -/
theorem append_projFirst_projSnd {d q : ℕ} (v : Fin (d + q) → ℝ) :
    Fin.append (projFirst d q v) (projSnd d q v) = v :=
  Fin.append_castAdd_natAdd

/-- `padSection q d` (append `d` zeroes) is injective. -/
theorem padSection_injective (q d : ℕ) : Function.Injective (padSection q d) := by
  intro s t h
  have hh := congrArg (projSnd d q) h
  rwa [projSnd_padSection, projSnd_padSection] at hh

/-- The fibre over `x ∈ ℝ^p` of the padded set `padStrat p q d X` has the same cardinality as
the fibre of `X`: both are parameterised by the fibre coordinates `Fin q → ℝ`, the inserted
`d`-block being forced to vanish. -/
theorem fiber_padStrat_ncard (p q d : ℕ) (X : WilkiesDesign.E.SemiPf (p + q)) (x : Fin p → ℝ) :
    (WilkiesDesign.E.fiber (Work.WilE7.padStrat p q d X).set x).ncard =
      (WilkiesDesign.E.fiber X.set x).ncard := by
  refine Set.ncard_congr (fun v _ => projSnd d q v) ?_ ?_ ?_
  · -- the image lies in the fibre of `X`
    intro v hv
    exact ((mem_padStrat_append X x v).mp hv).1
  · -- injectivity on the padded fibre: the inserted block is pinned to `0`
    intro v w hv hw h
    have hv0 : projFirst d q v = 0 := ((mem_padStrat_append X x v).mp hv).2
    have hw0 : projFirst d q w = 0 := ((mem_padStrat_append X x w).mp hw).2
    have hv' : v = Fin.append (projFirst d q v) (projSnd d q v) :=
      (append_projFirst_projSnd v).symm
    have hw' : w = Fin.append (projFirst d q w) (projSnd d q w) :=
      (append_projFirst_projSnd w).symm
    rw [hv0] at hv'
    rw [hw0] at hw'
    rw [hv', hw', h]
  · -- surjectivity: pad a fibre point with `d` zeroes
    intro y hy
    refine ⟨padSection q d y, ?_, projSnd_padSection q d y⟩
    change Fin.append x (padSection q d y) ∈ (padStrat p q d X).set
    rw [mem_padStrat_append, projSnd_padSection, projFirst_padSection]
    exact ⟨hy, rfl⟩

end Work.WilE7.PadAux
