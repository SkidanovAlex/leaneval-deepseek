import Mathlib
import Submission.Work.Peluse.SwapE.Defs
import Submission.Work.Peluse.Prop36SW.boxNormPow_arithIcc_shrink

namespace Work.Peluse.SwapE

/-- **`WindowShrink`** — the box norm at a long window controls the box norm at any shorter
window, at the cost of a constant.

This is `Work.Peluse.Prop36SW.boxNormPow_arithIcc_shrink` at the constant step `q := fun _ => 1`
(longer length `L' := L`, shorter length `L := D`), using
`uNormPow t Q S f = boxNormPow t (fun _ => Q) S f` (definitional) and
`FinSuppZ.of_supportIn` to turn `SupportIn f N` into `FinSuppZ f`.  Note the shrink loses only the
constant `(4 : ℝ)^(-(s:ℤ))` — no datum dependence, which is exactly what makes the endgame's
regime factor come out as `M/(M+H)` and nothing worse. -/
theorem windowShrink : Work.Peluse.SwapE.WindowShrink := by
  intro s hs
  obtain ⟨C, hCpos, hC⟩ := Work.Peluse.Prop36SW.boxNormPow_arithIcc_shrink (t := s) hs
  refine ⟨C, hCpos, ?_⟩
  intro L D N f hD hDL hsup
  have h := hC (fun _ => (1 : ℤ)) D L hD hDL (Work.Peluse.symIcc N) f
      (Work.Peluse.FinSuppZ.of_supportIn hsup)
  simpa [Work.Peluse.uNormPow] using h

end Work.Peluse.SwapE
