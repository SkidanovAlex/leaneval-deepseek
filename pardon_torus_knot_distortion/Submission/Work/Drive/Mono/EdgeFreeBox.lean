import Mathlib
import Submission.Work.Drive.Mono.JunctionGenC

/-!
# `EdgeFreeBox`: the box-restricted spelling of `EdgeFree`

Project lead, 20:5x: `Work.Drive.Mono.EdgeFree` must not quantify over the **extended** edge lines
(two extremal box coordinates, third coordinate free, arbitrarily far from `c`), because on such
points the slab functional can be small while `boxNorm c σ z ≠ s` (e.g. `(0,3,0)` for the standard
torus, where `boxNorm = 2`).  Its consumers only evaluate it at points of the **box sphere / closed
box**, so the honest hypothesis carries `boxNorm c σ z = s` — which is now the definition of
`Work.Drive.Mono.EdgeFree` itself (see `Mono/JunctionGenC.lean`).

This file keeps the name `Work.Drive.Mono.EdgeFreeBox` as a synonym of the corrected
`Work.Drive.Mono.EdgeFree`, so that the producer-side margin result
`Work.Drive.Mono.edgeFreeBox_of_margin` (which uses the *box* radius `5 s / 2` instead of the radius
of the whole carrier) has a home.
-/

open LeanEval.KnotTheory.PardonDistortion Set
open scoped RealInnerProductSpace

namespace Work.Drive.Mono

noncomputable section

/-- **The box-restricted `EdgeFree`** — by definition the corrected `Work.Drive.Mono.EdgeFree`
(which already carries the antecedent `boxNorm c σ z = s`). -/
abbrev EdgeFreeBox (ψ : Submission.Diffeo) (s : ℝ) (c : R3) (σ : Equiv.Perm (Fin 3)) (u : ℝ)
    (v : R3) (h : ℝ) : Prop :=
  EdgeFree ψ s c σ u v h

/-- **The two spellings are the same.** -/
theorem edgeFreeBox_of_edgeFree {ψ : Submission.Diffeo} {s u h : ℝ} {c v : R3}
    {σ : Equiv.Perm (Fin 3)}
    (hEF : EdgeFree ψ s c σ u v h) : EdgeFreeBox ψ s c σ u v h :=
  hEF

end

end Work.Drive.Mono
