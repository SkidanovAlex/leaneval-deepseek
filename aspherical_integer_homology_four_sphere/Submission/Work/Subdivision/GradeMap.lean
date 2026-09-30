/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license.
-/
import Mathlib
import Submission.Work.Subdivision.PieceInduction
import Submission.Work.Subdivision.SkelInduction
import Submission.Work.Subdivision.shortComplexOf_shortExact
import Submission.Work.Subdivision.SkelLevel
import Submission.Work.Subdivision.cellRelIso_subdivSkel
import Submission.Work.Subdivision.rel_hf

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The graded pieces of the subdivision, from the per-cell condition

`PolyCW.subdiv_quasiIso` (`SkelInduction`) takes as hypothesis the
quasi-isomorphism of the graded pieces `gradeMap P hdd haug n`; this file derives
that hypothesis from the per-cell local condition `LocallySpherical`, completing
the picture:

* `PolyCW.gradeMap_quasiIso_of_skeleta` — the companion of `subdivSkel_succ`: if
  the subdivision is a quasi-isomorphism on the two neighbouring skeleta (and on
  the relative subcomplex of the smaller one in the bigger one), then it is one on
  the graded piece.  This is the five lemma for the *third* term of the short
  exact sequence (`HomologicalComplex.HomologySequence.quasiIso_τ₃`).
* `PolyCW.gradeMap_quasiIso_of_local` — consequently `hlocal` of
  `PolyCW.subdiv_quasiIso` holds under `LocallySpherical` alone, and
  `PolyCW.subdiv_quasiIso_of_local'` re-derives the main theorem through that
  route.
-/

namespace Work.Subdivision

open CategoryTheory

universe u

noncomputable section

namespace PolyCW

variable (P : PolyCW.{u})

/-- **The graded piece of the subdivision is a quasi-isomorphism** as soon as the
subdivision is one on the restricted smaller skeleton and on the bigger skeleton. -/
theorem gradeMap_quasiIso_of_skeleta (hdd : P.HasDdZero) (haug : P.HasAugZero) (n : ℕ)
    (h₁ : QuasiIso ((cellRel P hdd n).restrictMap (sdRel P n) (subdivSkel P hdd haug (n + 1))
      (rel_hf P hdd haug n)))
    (h₂ : QuasiIso (subdivSkel P hdd haug (n + 1))) :
    QuasiIso (gradeMap P hdd haug n) := by
  have h := HomologicalComplex.HomologySequence.quasiIso_τ₃
    (φ := (cellRel P hdd n).shortComplexHom (sdRel P n) (subdivSkel P hdd haug (n + 1))
      (rel_hf P hdd haug n) (incl_proj _) (incl_proj _))
    (hS₁ := shortComplexOf_shortExact _ _) (hS₂ := shortComplexOf_shortExact _ _) ?_ h₂
  · rwa [SubData.shortComplexHom_τ₃] at h
  · rw [SubData.shortComplexHom_τ₁]
    exact h₁

/-- **`hlocal` holds under the per-cell local condition.**  The graded piece of
the subdivision is a quasi-isomorphism for every `n`. -/
theorem gradeMap_quasiIso_of_local (hdd : P.HasDdZero) (haug : P.HasAugZero)
    (hsp : LocallySpherical P hdd haug) (n : ℕ) : QuasiIso (gradeMap P hdd haug n) :=
  gradeMap_quasiIso_of_skeleta P hdd haug n
    (quasiIso_of_iso_square (cellRelIso P hdd n) (sdRelIso P n) (subdivSkel P hdd haug n)
      ((cellRel P hdd n).restrictMap (sdRel P n) (subdivSkel P hdd haug (n + 1))
        (rel_hf P hdd haug n))
      (cellRelIso_subdivSkel P hdd haug n (rel_hf P hdd haug n))
      (subdivSkel_quasiIso_of_local P hdd haug hsp n))
    (subdivSkel_quasiIso_of_local P hdd haug hsp (n + 1))

/-- **The subdivision chain map is a quasi-isomorphism**, via the blueprinted
`subdiv_quasiIso` with the graded-map hypothesis derived per cell. -/
theorem subdiv_quasiIso_of_local' (hdd : P.HasDdZero) (haug : P.HasAugZero)
    (hsp : LocallySpherical P hdd haug) : QuasiIso (subdiv P hdd haug) :=
  subdiv_quasiIso P hdd haug (gradeMap_quasiIso_of_local P hdd haug hsp)

end PolyCW

end

end Work.Subdivision
